//! Verified 2PC COORDINATOR-DECISION GATE — make the Lean-exported `evaluate_votes` the
//! AUTHORITATIVE Commit/Abort/Pending verdict, with the Rust `Coordinator::evaluate_votes` demoted
//! to the DIFFERENTIAL sibling.
//!
//! # What this is
//!
//! `api.rs::atomic_vote` feeds each vote to `dregg_coord::Coordinator::receive_vote`, which internally
//! calls `evaluate_votes` (`coord/src/atomic.rs`) and returns a `Decision`. That decision gates the
//! whole atomic turn: `Commit` runs the forest against the ledger, `Abort` tears the proposal down,
//! `Pending` waits. It is exactly the 2PC SAFETY content — and `Dregg2.Coord.TwoPhaseCommit` proves
//! the verified `evaluate` never yields a conflicting Commit+Abort (`evaluate_not_commit_and_abort`),
//! that Commit implies the threshold was met, and that Abort is sound/irreversible.
//!
//! This module makes the node CALL the verified rule at the live decision point. The coordinator
//! exposes its tally as a wire (`Coordinator::decision_wire`); we feed that to the VERIFIED Lean
//! `dregg_coord_2pc_decide` export (`Dregg2.Exec.DistributedExports`), whose
//! `coord_2pc_decide_eq` theorem proves the verdict IS `TwoPhaseCommit.evaluate`. So the
//! commit/abort/pending the node acts on is decided BY THE VERIFIED RULE.
//!
//! The Rust `Coordinator`'s own `Decision` (already computed by `receive_vote`) is kept as the
//! DIFFERENTIAL sibling: on every gated decision we compare the two and log LOUDLY on divergence (a
//! Lean-vs-Rust drift is a real bug in one of them). The template is the consensus tau-order swap
//! (`node::finality_gate` makes `dregg_tau_order` authoritative, Rust `tau` differential).
//!
//! # Flag + fail-safety
//!
//! Gated by [`coord_decision_gate_enabled`] (`DREGG_COORD_DECISION_GATE`, **default ON**). When the
//! Lean archive lacks the export (stale/marshal-only build), or the wire fails to round-trip, the gate
//! FALLS BACK to the Rust `Decision` so the coordinator is never broken — only un-verified — with a
//! once-warning. The verified gate is fail-SAFE: a malformed tally decodes to `Pending` (never a
//! terminal Commit/Abort on garbage), matching `twoPCGate`'s fail-safe sentinel.

use std::sync::Once;

use dregg_coord::Decision;

/// One-shot guard so the verified/fallback diagnostic is logged at most once per process.
static GATE_BACKEND_ANNOUNCED: Once = Once::new();

/// Whether the live 2PC-decision gate is enabled. **Default ON**. `DREGG_COORD_DECISION_GATE=0`/
/// `false`/`off` opts OUT (keeps the raw Rust `Decision`).
pub fn coord_decision_gate_enabled() -> bool {
    !matches!(
        std::env::var("DREGG_COORD_DECISION_GATE").ok().as_deref(),
        Some("0") | Some("false") | Some("FALSE") | Some("off") | Some("OFF")
    )
}

/// Whether the verified Lean distributed exports are linked (so the gate decides via the VERIFIED
/// `dregg_coord_2pc_decide` rather than the Rust fallback).
pub fn lean_backed() -> bool {
    dregg_lean_ffi::distributed_exports_available()
}

/// Map the verified Lean verdict to a `dregg_coord::Decision`.
fn decision_of(verdict: dregg_lean_ffi::Decision2pc) -> Decision {
    match verdict {
        dregg_lean_ffi::Decision2pc::Commit => Decision::Commit,
        dregg_lean_ffi::Decision2pc::Abort => Decision::Abort,
        dregg_lean_ffi::Decision2pc::Pending => Decision::Pending,
    }
}

/// The AUTHORITATIVE 2PC decision for the current coordinator tally.
///
/// `rust_decision` is the verdict the Rust `Coordinator::receive_vote` just produced (the DIFFERENTIAL
/// sibling); `wire` is the coordinator's `decision_wire()` (the tally encoded for the Lean gate), or
/// `None` when not Proposing (terminal/idle — then the Rust decision stands).
///
/// When the gate is enabled AND the Lean export is linked, this runs the VERIFIED
/// `dregg_coord_2pc_decide` over `wire`, COMPARES it to `rust_decision` (logging on drift), and
/// returns the VERIFIED verdict — the node acts on the proved rule. Otherwise it returns
/// `rust_decision` unchanged (fall back to the Rust coordinator, with a once-warning when un-verified).
pub fn authoritative_decision(rust_decision: Decision, wire: Option<&str>) -> Decision {
    if !coord_decision_gate_enabled() {
        return rust_decision;
    }
    let Some(wire) = wire else {
        // Terminal/idle coordinator: the Rust decision (Pending by construction off the Proposing
        // path) stands; there is no tally to verify.
        return rust_decision;
    };

    GATE_BACKEND_ANNOUNCED.call_once(|| {
        if lean_backed() {
            tracing::info!(
                "2PC coordinator decision is LEAN-BACKED: commit/abort/pending is decided by the \
                 VERIFIED dregg_coord_2pc_decide (TwoPhaseCommit.evaluate); the Rust \
                 Coordinator::evaluate_votes is the differential sibling."
            );
        } else {
            tracing::warn!(
                "2PC coordinator decision is running on the Rust FALLBACK (Lean distributed \
                 exports not linked). Rebuild the closure-complete archive \
                 (scripts/seed-dregg2-closure.sh) to gate the decision on the VERIFIED rule."
            );
        }
    });

    match dregg_lean_ffi::verified_2pc_decide(wire) {
        Ok(verdict) => {
            let lean_decision = decision_of(verdict);
            if lean_decision != rust_decision {
                // A Lean-vs-Rust drift on the SAME tally is a real bug in one of the two engines.
                // We trust the VERIFIED Lean rule (it carries the proved no-conflicting-decision
                // safety) and log the divergence LOUDLY for investigation.
                tracing::error!(
                    wire = %wire,
                    rust = ?rust_decision,
                    lean = ?lean_decision,
                    "2PC DECISION DIVERGENCE: Rust Coordinator and verified Lean gate disagree on \
                     the same tally — acting on the VERIFIED verdict. Investigate the Rust path."
                );
            }
            lean_decision
        }
        Err(e) => {
            // The export is unavailable / wire error: fall back to the Rust decision (never break
            // the coordinator). Logged at debug to avoid spamming a fallback build.
            tracing::debug!(error = %e, "2PC gate fell back to the Rust decision");
            rust_decision
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// THE HONEST POLE — when the Lean export is linked, the verified verdict for each well-formed
    /// tally is the one the Rust coordinator also reaches. Asserted FIRST, because without it the
    /// override tooth below could pass against a gate that returns a constant.
    ///
    /// This pole is deliberately weak ON ITS OWN, and saying so is the point: it is exactly the shape
    /// that made the old `lean_gate_decides_unanimous_scenarios` vacuous. `authoritative_decision`'s
    /// `Err` branch returns `rust_decision`, and here every `rust_decision` IS the expected answer — so
    /// this test is green whether `verified_2pc_decide` works, is broken, returns garbage, or is absent.
    /// It carries no assurance alone. `lean_verdict_overrides_a_wrong_rust_decision` is the tooth; this
    /// is only its non-vacuity companion.
    #[test]
    fn lean_gate_agrees_with_rust_on_wellformed_tallies() {
        if !dregg_lean_ffi::demand_lean(
            lean_backed(),
            "the Lean distributed exports (lean_backed()==false)",
        ) {
            return;
        }
        // 3-of-3 all yes ⇒ Commit; 2 yes 1 no ⇒ Abort (threshold unreachable); 2 yes 0 no ⇒ Pending.
        for (wire, expected) in [
            ("y=3;n=0;N=3;t=3", Decision::Commit),
            ("y=2;n=1;N=3;t=3", Decision::Abort),
            ("y=2;n=0;N=3;t=3", Decision::Pending),
        ] {
            assert_eq!(
                authoritative_decision(expected.clone(), Some(wire)),
                expected,
                "the verified 2PC gate must agree with the Rust coordinator on the well-formed tally \
                 {wire} — a disagreement is a real bug in one of the two engines"
            );
        }
    }

    /// **THE TOOTH — the VERIFIED verdict OVERRIDES the Rust one.** This module's whole claim is that
    /// `dregg_coord_2pc_decide`, not `Coordinator::evaluate_votes`, decides commit/abort/pending. The
    /// only way to witness that is to hand the gate a `rust_decision` that is DELIBERATELY WRONG for
    /// the tally and require the Lean verdict to win. Every expected value below is one the fallback
    /// path CANNOT produce, because the fallback returns `rust_decision` verbatim — so a fallback,
    /// a stuck export, or a deleted `verified_2pc_decide` all turn this test RED.
    ///
    /// That is precisely what the deleted `lean_gate_decides_unanimous_scenarios` could not do, and
    /// what the deleted `falls_back_to_rust_when_no_wire` was not even trying to do: the latter
    /// asserted `f(x, None) == x` against a body whose second statement is
    /// `let Some(wire) = wire else { return rust_decision; }` — literally P → P.
    ///
    /// On a FALLBACK build this test does not run: `demand_lean` skips it honestly, or PANICS under
    /// `DREGG_TEST_REQUIRE_LEAN=1`. That the verified gate is unassertable without the archive is the
    /// finding, not a defect of the test.
    #[test]
    fn lean_verdict_overrides_a_wrong_rust_decision() {
        if !dregg_lean_ffi::demand_lean(
            lean_backed(),
            "the Lean distributed exports (lean_backed()==false)",
        ) {
            return;
        }
        // (tally wire, a WRONG rust_decision, the verified verdict that must override it).
        for (wire, wrong_rust, verified) in [
            // Unanimous yes: Lean says Commit though Rust handed us Abort.
            ("y=3;n=0;N=3;t=3", Decision::Abort, Decision::Commit),
            ("y=3;n=0;N=3;t=3", Decision::Pending, Decision::Commit),
            // Threshold unreachable: Lean says Abort though Rust handed us Commit.
            ("y=2;n=1;N=3;t=3", Decision::Commit, Decision::Abort),
            // Undecided: Lean says Pending though Rust handed us a TERMINAL verdict — the
            // safety-relevant direction (a premature Commit must not survive the gate).
            ("y=2;n=0;N=3;t=3", Decision::Commit, Decision::Pending),
            ("y=2;n=0;N=3;t=3", Decision::Abort, Decision::Pending),
        ] {
            let got = authoritative_decision(wrong_rust.clone(), Some(wire));
            assert_eq!(
                got, verified,
                "the VERIFIED 2PC gate must OVERRIDE the Rust coordinator: on tally {wire} the Rust \
                 sibling said {wrong_rust:?} and the verified rule says {verified:?}, but the gate \
                 returned {got:?}. Returning {wrong_rust:?} means the gate FELL BACK — the verified \
                 rule is not deciding and this module's central claim is false on this build."
            );
        }
    }
}
