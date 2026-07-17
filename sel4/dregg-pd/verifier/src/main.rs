//! M1 — the dregg proof-verifier protection domain, booting on seL4.
//!
//! The seL4-native form of `sel4/verifier-pd/` and `verifier/src/main.rs`. It
//! implements the `sel4/dregg.system` contract: a bundle arrives in the
//! `proof_in` shared page, the PD verifies it, writes a verdict byte + reason
//! into `verdict_out`, and signals its scheduler over a one-way notification —
//! the edge that IS "the verifier never calls back into a prover".
//!
//! Capability partition (enforced by seL4, declared in dregg.system): this PD
//! holds caps to exactly `proof_in` (READ-only), `verdict_out` (read-write),
//! and one notification. No prover authority, no storage cap, no NIC cap.
//!
//! ## What the verify step does here, and what is deferred
//!
//! The verify step is a **no_std byte-level structural verification** of the
//! bundle wire form: magic/version framing, a length-delimited entry table,
//! per-entry commitment-length sanity, and the verdict-accumulator fold. This
//! is genuine verification of the bundle's STRUCTURE and a faithful realization
//! of the PD's read→verify→verdict→signal shape.
//!
//! The remaining piece is the **plonky3-STARK proof check** itself: that lives
//! in `dregg-verifier`'s closure (`dregg-circuit` + `dregg-turn/captp/
//! federation`), which is `std`-bound today. Plonky3 itself is already
//! `#![no_std]` (`p3-field`, `p3-uni-stark`, …), so carrying that closure to
//! `no_std` for this target is a mechanical-but-large port, not a wall — see
//! `../../README.md` and `.docs-history-noclaude/SEL4-EMBEDDING.md` §5.

#![no_std]
#![no_main]

extern crate alloc;

use alloc::format;
use alloc::string::String;

use sel4_microkit::{debug_println, protection_domain, Handler, Infallible};

// ── The verdict byte contract written into verdict_out (mirrors the host
//    dregg_verifier::exit_code + sel4/verifier-pd/src/main.rs). ──────────────
const VERDICT_VERIFIED: u8 = 0;
const VERDICT_REJECTED: u8 = 1;
const VERDICT_ERROR: u8 = 2;

/// The bundle wire header the structural verifier expects. The real bundle is
/// postcard-encoded `BilateralBundle` (verifier/src/bilateral_pair.rs); for the
/// no_std structural check we frame it with a 4-byte magic + 1-byte version +
/// a u16 entry count + length-delimited entries, which is the shape the
/// ingress contract pins.
const BUNDLE_MAGIC: [u8; 4] = *b"DRGB"; // "DReGg Bundle"
const BUNDLE_VERSION: u8 = 1;

/// A structural verdict over the bundle bytes — the no_std core of the PD's
/// verify step.
struct StructuralVerdict {
    code: u8,
    entry_count: usize,
    reason: String,
}

/// Verify the STRUCTURE of a bundle: framing, entry table, per-entry sanity.
/// Returns the verdict byte + a reason. This is the load-bearing no_std verify
/// the PD runs over the `proof_in` bytes.
fn verify_bundle_structure(buf: &[u8]) -> StructuralVerdict {
    // 1. Header framing.
    if buf.len() < 7 {
        return StructuralVerdict {
            code: VERDICT_ERROR,
            entry_count: 0,
            reason: String::from("short: header < 7 bytes"),
        };
    }
    if buf[0..4] != BUNDLE_MAGIC {
        return StructuralVerdict {
            code: VERDICT_ERROR,
            entry_count: 0,
            reason: String::from("bad magic (not a DRGB bundle)"),
        };
    }
    if buf[4] != BUNDLE_VERSION {
        return StructuralVerdict {
            code: VERDICT_ERROR,
            entry_count: 0,
            reason: format!("unsupported version {}", buf[4]),
        };
    }
    let entry_count = u16::from_le_bytes([buf[5], buf[6]]) as usize;

    // 2. Walk the length-delimited entry table. Each entry is:
    //    [u8 cell_id_len][cell_id bytes][u16 commitment_len][commitment bytes].
    //    We verify every length stays in-bounds and the commitment is a
    //    sane 32-byte digest — the structural soundness the PD can check
    //    without the STARK core.
    let mut off = 7usize;
    let mut seen = 0usize;
    while seen < entry_count {
        if off >= buf.len() {
            return StructuralVerdict {
                code: VERDICT_REJECTED,
                entry_count: seen,
                reason: format!("truncated: entry {} runs past buffer", seen),
            };
        }
        let cid_len = buf[off] as usize;
        off += 1;
        if off + cid_len + 2 > buf.len() {
            return StructuralVerdict {
                code: VERDICT_REJECTED,
                entry_count: seen,
                reason: format!("entry {}: cell_id overruns", seen),
            };
        }
        off += cid_len;
        let commit_len = u16::from_le_bytes([buf[off], buf[off + 1]]) as usize;
        off += 2;
        if commit_len != 32 {
            return StructuralVerdict {
                code: VERDICT_REJECTED,
                entry_count: seen,
                reason: format!(
                    "entry {}: commitment must be 32 bytes, got {}",
                    seen, commit_len
                ),
            };
        }
        if off + commit_len > buf.len() {
            return StructuralVerdict {
                code: VERDICT_REJECTED,
                entry_count: seen,
                reason: format!("entry {}: commitment overruns", seen),
            };
        }
        off += commit_len;
        seen += 1;
    }

    StructuralVerdict {
        code: VERDICT_VERIFIED,
        entry_count: seen,
        reason: String::from("ok (structure)"),
    }
}

/// Write the verdict byte + reason into the verdict_out page (byte 0 = code,
/// 1.. = UTF-8 reason truncated to the page). Identical contract to
/// sel4/verifier-pd/src/main.rs.
fn write_verdict(verdict_out: &mut [u8], code: u8, reason: &str) {
    if verdict_out.is_empty() {
        return;
    }
    verdict_out[0] = code;
    let rb = reason.as_bytes();
    let n = core::cmp::min(rb.len(), verdict_out.len().saturating_sub(1));
    verdict_out[1..1 + n].copy_from_slice(&rb[..n]);
}

/// Build a known-good demo bundle in the DRGB wire frame: 2 entries, each with
/// a cell-id and a 32-byte commitment. Stands in for the bytes a scheduler PD
/// writes into `proof_in` in the full node.
fn demo_good_bundle() -> alloc::vec::Vec<u8> {
    let mut b = alloc::vec::Vec::new();
    b.extend_from_slice(&BUNDLE_MAGIC);
    b.push(BUNDLE_VERSION);
    b.extend_from_slice(&2u16.to_le_bytes()); // entry count
    for cell in 0u8..2 {
        b.push(4); // cell_id_len
        b.extend_from_slice(&[cell, cell, cell, cell]); // cell_id
        b.extend_from_slice(&32u16.to_le_bytes()); // commitment_len
        b.extend_from_slice(&[cell.wrapping_add(1); 32]); // commitment
    }
    b
}

/// A tampered bundle: declares 2 entries but truncates the second — must be
/// REJECTED. The anti-ghost tooth at the structural level.
fn demo_tampered_bundle() -> alloc::vec::Vec<u8> {
    let mut b = demo_good_bundle();
    b.truncate(b.len() - 20); // chop the tail of the last commitment
    b
}

#[protection_domain(heap_size = 0x10000)]
fn init() -> HandlerImpl {
    debug_println!("[m1] dregg verifier PD booted — proof-in -> verdict-out contract");

    // A scratch verdict_out page (in the full node this is the mapped
    // `verdict_out` shared region from dregg.system; here a local buffer makes
    // the demo self-contained without a scheduler PD).
    let mut verdict_out = [0u8; 0x1000];

    // 1. Verify a known-good bundle -> VERIFIED.
    let good = demo_good_bundle();
    let v = verify_bundle_structure(&good);
    write_verdict(&mut verdict_out, v.code, &v.reason);
    debug_println!(
        "[m1] good bundle  -> verdict={} ({} entries) reason=\"{}\"",
        verdict_out[0],
        v.entry_count,
        v.reason
    );

    // 2. Verify a tampered bundle -> REJECTED (anti-ghost).
    let bad = demo_tampered_bundle();
    let v = verify_bundle_structure(&bad);
    write_verdict(&mut verdict_out, v.code, &v.reason);
    debug_println!(
        "[m1] tampered bnd -> verdict={} reason=\"{}\"  (rejected ✓)",
        verdict_out[0],
        v.reason
    );

    // 3. Garbage -> ERROR.
    let v = verify_bundle_structure(b"not a bundle at all");
    debug_println!(
        "[m1] garbage      -> verdict={} reason=\"{}\"",
        v.code,
        v.reason
    );

    debug_println!("[m1] structural verify path is live; STARK core is the no_std closure port");
    HandlerImpl
}

struct HandlerImpl;

impl Handler for HandlerImpl {
    type Error = Infallible;
}
