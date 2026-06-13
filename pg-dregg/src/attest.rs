//! Tier-C PROOF gate — the whole-chain IVC range attestation (`docs/PG-DREGG.md`
//! §10.2), the crate-side shape behind the `tier-c` feature.
//!
//! # The two halves of Tier C, and which one this is
//!
//! Tier C's spine is "no state row exists except as a verified-turn post-image".
//! It has TWO independent enforcement halves, and they live in different places:
//!
//! 1. **The per-row STRUCTURAL chain re-validation** — [`crate::mirror::
//!    verify_chain_step`], lifted into SQL as the `dregg_verify_turn` extern and
//!    the `dregg.commit_log` `BEFORE INSERT` trigger. It runs UNCONDITIONALLY (no
//!    feature), is circuit-free, and is the realizable per-row gate: a turn's
//!    `ordinal` is the next expected one AND its `prev_root` equals the head, so a
//!    tampered/reordered/forged batch is refused by the database engine. This is
//!    the load-bearing half that ships in every build.
//!
//! 2. **The whole-chain PROOF attestation** — THIS module. A `CommitRecord`
//!    carries no per-turn STARK (§10.2), so the per-row gate can NOT re-prove a
//!    turn's execution. The *proof* soundness is the whole-chain IVC light client
//!    (`circuit::ivc_turn_chain::verify_turn_chain_recursive`): ONE succinct
//!    recursive proof attesting that ALL K finalized turns in a receipt RANGE
//!    executed correctly and the root chain advanced from `genesis_root` to
//!    `final_root`. The verifier checks only the root; cost is independent of K.
//!    This is the orthogonal M3 item the doc names — surfaced here, behind
//!    `tier-c`, as a *range-attest* set-returning function (NOT a per-row STARK,
//!    which would be both impossible — no per-turn proof exists — and the wrong
//!    cost model).
//!
//! # Why a RANGE attestation, not a per-row one
//!
//! The IVC artifact is whole-chain by construction: a single recursive fold over
//! a *window* of finalized turns. Its natural SQL shape is therefore a function
//! that takes (the serialized proof, the trust-anchor VK, the claimed range
//! bounds) and, if the proof verifies against the anchor, RETURNS the attested
//! range as rows — `(ordinal, prev_root, ledger_root)` for each turn the range
//! covers, every row tagged `proof_attested = true`. A consumer JOINs that
//! against `dregg.turns` to learn "these ordinals are not merely chain-consistent
//! (the structural tooth) but PROOF-attested (every turn executed correctly,
//! verified in-circuit)". One proof attests a whole window; the SRF explodes the
//! window into rows so SQL can use it.
//!
//! # The honest boundary (named, not hidden) — the circuit-link settle item
//!
//! The IVC verifier `verify_turn_chain_recursive(proof: &WholeChainProof,
//! expected_vk: &RecursionVk)` takes an **in-memory** `WholeChainProof` — a Rust
//! struct holding plonky3 proof objects (`RecursionOutput`,
//! `RecursionCompatibleProof`). That struct is **not** `Serialize`/`Deserialize`
//! today, so a `WholeChainProof` cannot yet cross the SQL boundary as `bytea`.
//! What CAN cross now is:
//!
//! * the **VK anchor** — `RecursionVk(pub [u8; 32])`, a 32-byte fingerprint the
//!   honest-setup party publishes as the light client's trust root (exactly like
//!   a SNARK VK), and
//! * the **claimed publics** — `genesis_root` / `final_root` / `num_turns` /
//!   `chain_digest`, the bound window summary.
//!
//! So this module ships the **range-attest SRF shape** in full — the
//! [`RangeAttestation`] request/verdict types, the [`AttestedTurn`] row the SRF
//! returns, the [`attest_range`] entry the pg-extern calls, and the fail-closed
//! discipline — with the proof-bytes leg STUBBED behind a single, loud seam:
//! [`verify_serialized_proof`]. Wiring that leg is a *bounded* settle item, named
//! precisely below and in `docs/PG-DREGG.md` §10.2:
//!
//!   (S1) add a serialization to `circuit::ivc_turn_chain::WholeChainProof` (the
//!        plonky3 proof objects are postcard/serde-encodable; the struct just
//!        needs the derives + a versioned envelope), so the node can ship a proof
//!        as `bytea` and the SRF can `decode → verify_turn_chain_recursive`;
//!   (S2) the node-side PRODUCER: when finality advances, fold the new finalized
//!        turns (`prove_turn_chain_recursive` / the `fold_two_turns` accumulator)
//!        and write the serialized proof + its window bounds into a
//!        `dregg.turn_proofs(lo, hi, genesis_root, final_root, proof bytea, vk)`
//!        table the SRF reads;
//!   (S3) the `tier-c` feature pulls `dregg-circuit` (Lean-free — `--features
//!        verifier`/`recursion`, NO executor, NO Lean runtime; §8.1 authorizes the
//!        circuit link for Tier C) so [`verify_serialized_proof`] becomes the real
//!        `verify_turn_chain_recursive` instead of the stub.
//!
//! Until S1–S3 land, the SRF FAILS CLOSED: with the stub it attests nothing
//! (`verify_serialized_proof` returns "not yet wired" and the SRF returns zero
//! rows / an honest verdict), which is the only safe default — a labeled proof
//! gate that does NOT yet verify must return "unattested", never "attested". That
//! is the §10.3 discipline (a stubbed verifier that returns TRUE is the forbidden
//! failure mode; this stub returns the SAFE direction).
//!
//! Everything here is plain Rust, postgres-free, `cargo test`-proven. The
//! `#[pg_extern]` SRF in [`crate`] marshals `bytea`/`bigint` into [`attest_range`].

use serde::{Deserialize, Serialize};

/// The 32-byte recursion VK fingerprint — the light client's trust anchor, the
/// SQL-crossable mirror of `circuit::plonky3_recursion_impl::RecursionVk`. An
/// honest-setup party extracts it ONCE from a locally produced fold and publishes
/// it; a verifier compares the presented proof's root fingerprint against THIS
/// (never against an anchor taken from the artifact being verified — that is the
/// whole point of a pinned VK). Here it is opaque bytes; the `tier-c` build
/// converts it into the circuit's `RecursionVk` for the real check.
pub type VkAnchor = [u8; 32];

/// A turn the range attestation covers, exploded into a SQL row. The SRF returns
/// one of these per ordinal in `[lo, hi]` when the proof verifies, each tagged
/// `proof_attested = true` so a consumer JOINs it against `dregg.turns` to mark
/// the proof-attested prefix (distinct from the merely chain-consistent rows the
/// structural tooth admits).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestedTurn {
    /// The turn ordinal (a row of `dregg.turns`).
    pub ordinal: u64,
    /// The pre-state root the turn chained onto.
    pub prev_root: [u8; 32],
    /// The post-state root the turn produced (the next turn's `prev_root`).
    pub ledger_root: [u8; 32],
    /// Always `true` for a row the SRF emits — it is emitted ONLY when the
    /// whole-chain proof verified the window this ordinal lies in. (The column
    /// exists so a `UNION` with un-attested `dregg.turns` rows is unambiguous.)
    pub proof_attested: bool,
}

/// The request a caller makes of the range-attest SRF: the serialized whole-chain
/// proof, the trust anchor to verify it against, and the window bounds the caller
/// claims it attests. The bounds are checked AGAINST the proof's own attested
/// publics (a caller cannot claim a wider window than the proof covers — that is
/// the anti-overclaim tooth, [`RangeAttestation::check_window`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttestRequest<'a> {
    /// The serialized `WholeChainProof` bytes (the node-produced artifact). Empty
    /// / malformed ⇒ fail closed.
    pub proof_bytes: &'a [u8],
    /// The light client's published VK anchor.
    pub vk_anchor: VkAnchor,
    /// The inclusive lower ordinal the caller asks the SRF to attest.
    pub lo: u64,
    /// The inclusive upper ordinal the caller asks the SRF to attest.
    pub hi: u64,
}

/// The verdict of attempting a range attestation. Either the proof verified and
/// the SRF should emit the [`AttestedTurn`] rows for the attested window, or it
/// was refused with a named reason (fail-closed — the SRF emits NO rows on a
/// refusal, never a partial or an unverified row).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RangeAttestation {
    /// The proof verified against the anchor and covers `[lo, hi]`. The carried
    /// window publics (`genesis_root` is the pre-root of `lo`, `final_root` is the
    /// post-root of `hi`, `num_turns` is the count) are what the proof bound under
    /// Fiat–Shamir, so they are trustworthy.
    Attested {
        lo: u64,
        hi: u64,
        genesis_root: [u8; 32],
        final_root: [u8; 32],
        num_turns: u64,
    },
    /// The attestation was refused; the string names which requirement failed
    /// (bad anchor, proof did not verify, claimed window not covered, malformed
    /// bytes, or — until the circuit link lands — "proof verification not yet
    /// wired (Tier-C circuit-link settle item)").
    Refused(String),
}

impl RangeAttestation {
    /// `true` iff the proof verified for the requested window.
    pub fn attested(&self) -> bool {
        matches!(self, RangeAttestation::Attested { .. })
    }

    /// The human-readable reason, for the explain/audit surface.
    pub fn reason(&self) -> String {
        match self {
            RangeAttestation::Attested { lo, hi, num_turns, .. } => {
                format!("attested: turns [{lo}, {hi}] ({num_turns} turns) proof-verified")
            }
            RangeAttestation::Refused(r) => r.clone(),
        }
    }

    /// The anti-overclaim tooth: a verified proof attests EXACTLY the window its
    /// publics bind. A caller's claimed `[lo, hi]` is honoured only if it lies
    /// within the proof's covered window — i.e. the proof's `num_turns` spans at
    /// least `hi - lo + 1` turns ending at the proof's `final_root`. This stops a
    /// caller presenting a proof for turns [0, 100] and claiming it attests
    /// [0, 1000]. (The exact ordinal binding is sharpened when S2 ties the proof's
    /// window publics to concrete ordinals; today the proof publics carry the
    /// root pair + count, and the SRF binds the claimed count to them.)
    fn check_window(claimed_lo: u64, claimed_hi: u64, proof_num_turns: u64) -> Result<(), String> {
        if claimed_hi < claimed_lo {
            return Err(format!(
                "claimed window is empty/inverted: lo={claimed_lo} > hi={claimed_hi}"
            ));
        }
        let claimed_span = claimed_hi - claimed_lo + 1;
        if claimed_span > proof_num_turns {
            return Err(format!(
                "claimed window spans {claimed_span} turns but the proof attests only \
                 {proof_num_turns} — a proof cannot attest more than it covers"
            ));
        }
        Ok(())
    }
}

/// The publics a verified whole-chain proof binds (the SQL-crossable summary of
/// `circuit::ivc_turn_chain::WholeChainProof`'s attested fields). The real
/// `tier-c` verify path fills this from the verified proof; the stub fills it from
/// nothing (it never reaches here). Fiat–Shamir binds these into the proof, so a
/// verified proof's publics are trustworthy.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofPublics {
    pub genesis_root: [u8; 32],
    pub final_root: [u8; 32],
    pub chain_digest: [u8; 32],
    pub num_turns: u64,
}

/// The ONE seam the circuit link plugs into. Verify a serialized whole-chain
/// proof against the VK anchor and, on success, return the publics it bound.
///
/// * **`tier-c` OFF (default, the stub):** returns `Err("…not yet wired…")` — the
///   SAFE direction. The Tier-A/B/chain-gate build stays circuit-free, and the
///   range-attest SRF honestly attests nothing (fail-closed). This is NOT the
///   §10.3 forbidden failure mode: that is a stub returning *success* (attesting
///   forged state); this stub returns *refusal* (attesting nothing).
///
/// * **`tier-c` ON (the settle item S1–S3):** deserializes `proof_bytes` into a
///   `circuit::ivc_turn_chain::WholeChainProof` (needs S1, the serialization),
///   converts `vk_anchor` into `circuit::plonky3_recursion_impl::RecursionVk`,
///   runs `circuit::ivc_turn_chain::verify_turn_chain_recursive(&proof, &vk)`,
///   and on `Ok(())` returns the proof's `{genesis_root, final_root,
///   chain_digest, num_turns}` (mapped from `BabyBear`/`usize` to the bytes form
///   here). On any error returns `Err(reason)`.
///
/// The signature is identical in both builds, so the SRF logic above is written
/// ONCE against this seam and does not branch on the feature.
pub fn verify_serialized_proof(
    proof_bytes: &[u8],
    vk_anchor: &VkAnchor,
) -> Result<ProofPublics, String> {
    // Fail-closed input hygiene shared by both builds: empty bytes never verify.
    if proof_bytes.is_empty() {
        return Err("empty proof bytes".to_string());
    }
    let _ = vk_anchor;

    #[cfg(not(feature = "tier-c"))]
    {
        // THE STUB (safe direction). The circuit verifier is not linked in the
        // default build; attest nothing. Wiring S1–S3 replaces this arm.
        Err(
            "proof verification not yet wired (Tier-C circuit-link settle item \
             S1–S3, docs/PG-DREGG.md §10.2): the whole-chain IVC verifier \
             (circuit::ivc_turn_chain::verify_turn_chain_recursive) is not linked \
             in this build — the range-attest SRF fails closed (attests nothing)"
                .to_string(),
        )
    }

    #[cfg(feature = "tier-c")]
    {
        // THE REAL LEG (settle item). When the `tier-c` feature is on, this arm
        // links the Lean-FREE circuit verifier (§8.1) and runs the real check.
        // The body is written against the named circuit API; it compiles once the
        // `dregg-circuit` dep is wired into the `tier-c` feature (S3) AND
        // `WholeChainProof` gains its serialization (S1). Until then the feature
        // is declared-but-depless, so this arm is dead behind the cfg and the
        // default (stub) build is what ships — the honest staged shape.
        //
        // ```ignore
        // use dregg_circuit::ivc_turn_chain::{verify_turn_chain_recursive, WholeChainProof};
        // use dregg_circuit::plonky3_recursion_impl::RecursionVk;
        // let proof: WholeChainProof = WholeChainProof::from_bytes(proof_bytes)   // S1
        //     .map_err(|e| format!("proof does not decode: {e}"))?;
        // let vk = RecursionVk(*vk_anchor);
        // verify_turn_chain_recursive(&proof, &vk)
        //     .map_err(|e| format!("proof did not verify against the anchor: {e:?}"))?;
        // return Ok(ProofPublics {
        //     genesis_root: babybear_to_bytes(proof.genesis_root),
        //     final_root:   babybear_to_bytes(proof.final_root),
        //     chain_digest: babybear_to_bytes(proof.chain_digest),
        //     num_turns:    proof.num_turns as u64,
        // });
        // ```
        Err(
            "tier-c feature is enabled but the circuit dep is not yet wired (settle \
             item S3, docs/PG-DREGG.md §10.2) — fails closed"
                .to_string(),
        )
    }
}

/// The range-attest entry the pg-extern SRF calls. Verifies the proof against the
/// anchor (via [`verify_serialized_proof`]), checks the claimed window does not
/// over-claim the proof's coverage, and returns the verdict. The SRF emits
/// [`AttestedTurn`] rows ONLY on [`RangeAttestation::Attested`]; on
/// [`RangeAttestation::Refused`] it emits nothing (fail-closed).
///
/// This is the load-bearing logic, written ONCE against the [`verify_serialized_proof`]
/// seam, so it is the SAME in the stub and the wired build. The settle item flips
/// the seam, not this function.
pub fn attest_range(req: &AttestRequest<'_>) -> RangeAttestation {
    if req.hi < req.lo {
        return RangeAttestation::Refused(format!(
            "empty/inverted window: lo={} > hi={}",
            req.lo, req.hi
        ));
    }
    let publics = match verify_serialized_proof(req.proof_bytes, &req.vk_anchor) {
        Ok(p) => p,
        Err(e) => return RangeAttestation::Refused(e),
    };
    if let Err(e) = RangeAttestation::check_window(req.lo, req.hi, publics.num_turns) {
        return RangeAttestation::Refused(e);
    }
    RangeAttestation::Attested {
        lo: req.lo,
        hi: req.hi,
        genesis_root: publics.genesis_root,
        final_root: publics.final_root,
        num_turns: publics.num_turns,
    }
}

/// Build the [`AttestedTurn`] rows for an [`RangeAttestation::Attested`] verdict,
/// reading the per-ordinal roots from the caller-supplied `turns` slice (which the
/// SRF populates by querying `dregg.turns` for the attested window — the proof
/// attests the WINDOW; the roots are the recorded ones, re-tagged `proof_attested`).
/// Returns empty for a refused verdict (fail-closed) or if the recorded turns do
/// not cover the attested window (a defensive guard: the proof says these ordinals
/// are attested, but if the table lacks them, attest nothing rather than fabricate).
pub fn attested_rows(verdict: &RangeAttestation, recorded: &[AttestedTurn]) -> Vec<AttestedTurn> {
    let RangeAttestation::Attested { lo, hi, .. } = verdict else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for ord in *lo..=*hi {
        match recorded.iter().find(|t| t.ordinal == ord) {
            Some(t) => out.push(AttestedTurn {
                ordinal: t.ordinal,
                prev_root: t.prev_root,
                ledger_root: t.ledger_root,
                proof_attested: true,
            }),
            // Defensive: the attested window references an ordinal the store does
            // not have. Do NOT fabricate a row — attest nothing for the gap.
            None => return Vec::new(),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn req<'a>(bytes: &'a [u8], lo: u64, hi: u64) -> AttestRequest<'a> {
        AttestRequest {
            proof_bytes: bytes,
            vk_anchor: [7u8; 32],
            lo,
            hi,
        }
    }

    #[test]
    fn empty_window_is_refused() {
        let r = attest_range(&req(&[1, 2, 3], 5, 4));
        assert!(!r.attested());
        assert!(r.reason().contains("inverted"));
    }

    #[test]
    fn empty_proof_bytes_fail_closed() {
        // No proof ⇒ never attested, regardless of window.
        let r = attest_range(&req(&[], 0, 0));
        assert!(!r.attested());
        assert!(r.reason().to_lowercase().contains("empty"));
    }

    #[test]
    fn stub_attests_nothing_fail_closed() {
        // THE LOAD-BEARING SAFETY PROPERTY: with the circuit link unwired (the
        // default build), a well-formed-looking request still attests NOTHING —
        // the stub returns the SAFE direction (refusal), never a false attest.
        // This is the §10.3 discipline: a labeled proof gate that does not verify
        // must say "unattested", never "attested".
        let r = attest_range(&req(&[0xde, 0xad, 0xbe, 0xef], 0, 10));
        assert!(!r.attested(), "the unwired stub must NEVER attest (fail-closed)");
        assert!(
            r.reason().contains("not yet wired") || r.reason().contains("settle item"),
            "the refusal names the circuit-link settle item: {}",
            r.reason()
        );
        // And it emits zero rows.
        assert!(attested_rows(&r, &recorded(0, 10)).is_empty());
    }

    #[test]
    fn window_overclaim_is_refused() {
        // The anti-overclaim tooth, exercised directly on the verdict logic: a
        // claimed window wider than the proof covers is refused. (We drive
        // check_window directly since the stub never reaches it; the wired build
        // reaches it after a real verify.)
        assert!(RangeAttestation::check_window(0, 9, 10).is_ok(), "10 turns covers [0,9]");
        assert!(RangeAttestation::check_window(0, 10, 10).is_err(), "[0,10] is 11 turns > 10");
        assert!(
            RangeAttestation::check_window(0, 1000, 100).is_err(),
            "a proof for 100 turns cannot attest a 1001-turn window"
        );
        let err = RangeAttestation::check_window(5, 4, 10).unwrap_err();
        assert!(err.contains("inverted"));
    }

    #[test]
    fn attested_rows_are_tagged_and_gap_fails_closed() {
        // A (hand-built) Attested verdict explodes into per-ordinal rows, all
        // tagged proof_attested=true — and a missing recorded ordinal yields NO
        // rows (never a fabricated one).
        let verdict = RangeAttestation::Attested {
            lo: 0,
            hi: 2,
            genesis_root: [0u8; 32],
            final_root: [9u8; 32],
            num_turns: 3,
        };
        let rows = attested_rows(&verdict, &recorded(0, 2));
        assert_eq!(rows.len(), 3);
        assert!(rows.iter().all(|t| t.proof_attested));
        assert_eq!(rows[0].ordinal, 0);
        assert_eq!(rows[2].ordinal, 2);

        // A gap in the recorded turns (ordinal 1 missing) ⇒ attest nothing.
        let recorded_with_gap = vec![recorded_one(0), recorded_one(2)];
        assert!(
            attested_rows(&verdict, &recorded_with_gap).is_empty(),
            "a recorded gap must fail closed, not fabricate the missing row"
        );
    }

    #[test]
    fn refused_verdict_emits_no_rows() {
        let verdict = RangeAttestation::Refused("nope".to_string());
        assert!(attested_rows(&verdict, &recorded(0, 5)).is_empty());
    }

    fn recorded_one(ord: u64) -> AttestedTurn {
        AttestedTurn {
            ordinal: ord,
            prev_root: [ord as u8; 32],
            ledger_root: [(ord + 1) as u8; 32],
            proof_attested: false, // the recorded row's tag is irrelevant; attested_rows re-tags
        }
    }

    fn recorded(lo: u64, hi: u64) -> Vec<AttestedTurn> {
        (lo..=hi).map(recorded_one).collect()
    }
}
