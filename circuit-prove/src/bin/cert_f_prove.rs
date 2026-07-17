//! # `cert_f_prove` — the reveal-nothing STARK, as a thin JSON CLI (the DrEX shielded wire)
//!
//! ```text
//! echo '<solver-cert-json>' | cert_f_prove
//! ```
//!
//! This is the STAGE-1 → TIER-1 wire the fhEgg engine names but does not run: it takes a
//! fhegg-solver Cert-F certificate (`fhegg-solver/src/cert.rs`'s `(n_nodes, edges, w, c, f, π, s, ε)`
//! wire shape — exactly what `fhegg_clear` now emits under `solverCert`) and PROVES it in a REAL
//! dregg STARK:
//!
//!   1. [`from_solution_json`] — fixed-point-scale the solver's f64 certificate into the integer
//!      `CertFWitness` the STARK proves over (`s` re-derived nonneg, `ε` absorbs quantization);
//!   2. `cert.check()` — the native Cert-F predicate (`Market.Certified`) must hold before proving;
//!   3. [`prove_cert_f`] — the production IR-v2 STARK (BabyBear + FRI, `prove_vm_descriptor2`): the
//!      witness `(f, π, s)` lives ONLY in the trace (hidden under the PCS), the sole public value is
//!      the cleared volume `wᵀf`;
//!   4. [`verify_cert_f`] — verify the minted proof against the descriptor + public inputs.
//!
//! ## What this binary EMITS (the reveal-nothing boundary, in code)
//!
//! stdout is a single JSON object carrying ONLY what the WORLD is allowed to see:
//!   * `verify` — did the real STARK proof verify (true/false);
//!   * `proofBytes` — the serialized proof size (postcard);
//!   * `clearedVolume` — the public input `wᵀf` (the ONLY witness-derived scalar the STARK exposes);
//!   * `nNodes`, `mEdges`, `epsilon`, `scale`, `traceWidth`, `valueBits` — the public program shape;
//!   * `proveMs`, `verifyMs` — honest latency (proving costs seconds, not a click);
//!   * `hidden` — the names of what was WITHHELD (`f`, `π`, `s`).
//!
//! It NEVER prints `f`, `π`, or `s`. The per-order flows, the dual prices, and the slacks are read
//! from stdin (the SOLVER's plaintext view) and consumed into the trace, but they do not appear in the
//! output — the world sees the proof + the public inputs, nothing more. That is the OUTPUT-side
//! reveal-nothing this wire delivers; full input-privacy (hidden bids end-to-end over note
//! commitments) is the shielded-pool lane, named in the DrEX UI and in `Market/RevealNothing.lean`.

use std::io::Read;
use std::time::Instant;

use dregg_circuit_prove::cert_f_air::{
    CertFWitness, VALUE_BITS, from_solution_json, from_solution_json_with_epsilon, prove_cert_f,
    verify_cert_f,
};

/// The trace width the descriptor commits (public — a function of the program shape only).
fn trace_width(cert: &CertFWitness) -> usize {
    // width = bit_base + (4m+1)·VALUE_BITS ; bit_base is private, so recover width from the
    // base trace the prover builds (its row length is the committed width).
    cert.base_trace().first().map(|r| r.len()).unwrap_or(0)
}

fn emit_err(msg: &str) -> ! {
    // A structured error the web wire can render, still on stdout so the proxy reads one line.
    println!("{{\"ok\":false,\"error\":{}}}", json_str(msg));
    std::process::exit(1);
}

/// Minimal JSON string escaper (avoids pulling serde_json just for the output object).
fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn main() {
    let mut buf = String::new();
    if std::io::stdin().read_to_string(&mut buf).is_err() {
        emit_err("cert_f_prove: failed to read stdin");
    }
    // The fixed-point scale for the f64→integer bridge. The DrEX demo batch clears at integer
    // flows, so scale=1 is exact; override with CERT_F_SCALE for finer grids.
    let scale: i64 = std::env::var("CERT_F_SCALE")
        .ok()
        .and_then(|s| s.parse().ok())
        .filter(|&s: &i64| s >= 1)
        .unwrap_or(1);

    // The PRESCRIPTIVE accuracy budget (the registered program's ε, in the scaled integer
    // grid). When set, the bridged certificate carries this ε — matching an ε-budget
    // registration — and the bridge refuses a solve whose achieved gap exceeds it. Unset,
    // the descriptive form is used (ε := achieved gap; only matches a registration when
    // exactly tight).
    let epsilon: Option<i64> = std::env::var("CERT_F_EPSILON")
        .ok()
        .and_then(|s| s.parse().ok());

    // [1] bridge the solver's f64 certificate into the integer STARK witness.
    let bridged = match epsilon {
        Some(eps) => from_solution_json_with_epsilon(&buf, scale, eps),
        None => from_solution_json(&buf, scale),
    };
    let cert = match bridged {
        Ok(c) => c,
        Err(e) => emit_err(&format!("cert bridge failed: {e}")),
    };

    // [2] the native Cert-F predicate must hold before we prove (the bridge asserts nothing it
    // does not verify). If the fixed-point rounding broke conservation/box, say so honestly.
    let chk = cert.check();
    if !chk.valid {
        emit_err(&format!(
            "bridged certificate is NOT Cert-F-valid at scale={scale} (conserves={} box={} slackSign={} dualFeasible={} gapOk={}); raise CERT_F_SCALE",
            chk.conserves, chk.box_ok, chk.slack_sign_ok, chk.dual_feasible, chk.gap_ok
        ));
    }

    let cleared_volume = cert.objective();
    let n_nodes = cert.n_nodes;
    let m_edges = cert.m();
    let width = trace_width(&cert);

    // [3] prove the certificate in the REAL dregg STARK (witness f/π/s hidden in the trace).
    let t_prove = Instant::now();
    let (desc, proof, pis) = match prove_cert_f(&cert) {
        Ok(p) => p,
        Err(e) => emit_err(&format!("prove_cert_f failed: {e}")),
    };
    let prove_ms = t_prove.elapsed().as_millis();

    // The serialized proof size — a real byte count the world receives, not a handle to a secret.
    let proof_bytes = postcard::to_allocvec(&proof).map(|v| v.len()).unwrap_or(0);

    // [4] verify the minted proof against the descriptor + public inputs.
    let t_verify = Instant::now();
    let verified = verify_cert_f(&desc, &proof, &pis).is_ok();
    let verify_ms = t_verify.elapsed().as_millis();

    // The public inputs, as decimals (the STARK exposes exactly `[wᵀf]`).
    let pis_dec: Vec<String> = pis.iter().map(|b| b.as_u32().to_string()).collect();

    // Emit ONLY the world-visible object. f, π, s are consumed but NEVER printed.
    println!(
        "{{\
\"ok\":true,\
\"verify\":{verify},\
\"proofBytes\":{proof_bytes},\
\"clearedVolume\":{cleared_volume},\
\"publicInputs\":[{pis}],\
\"nNodes\":{n_nodes},\
\"mEdges\":{m_edges},\
\"epsilon\":{epsilon},\
\"scale\":{scale},\
\"traceWidth\":{width},\
\"valueBits\":{vbits},\
\"proveMs\":{prove_ms},\
\"verifyMs\":{verify_ms},\
\"descriptor\":{desc_name},\
\"hides\":[{hides}],\
\"note\":{note}\
}}",
        verify = verified,
        proof_bytes = proof_bytes,
        cleared_volume = cleared_volume,
        pis = pis_dec.join(","),
        n_nodes = n_nodes,
        m_edges = m_edges,
        epsilon = cert.epsilon,
        scale = scale,
        width = width,
        vbits = VALUE_BITS,
        prove_ms = prove_ms,
        verify_ms = verify_ms,
        desc_name = json_str(&desc.name),
        hides = [
            "f (per-order flow)",
            "π (node potentials / dual prices)",
            "s (dual slacks)"
        ]
        .iter()
        .map(|s| json_str(s))
        .collect::<Vec<_>>()
        .join(","),
        note = json_str(
            "the witness (f, π, s) was consumed into the STARK trace and is NOT in this output — the world sees only the proof + public inputs (wᵀf, the program shape)"
        ),
    );
}
