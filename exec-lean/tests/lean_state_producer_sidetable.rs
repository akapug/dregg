//! lean_state_producer_sidetable.rs — DISSOLVED-VERB WIRE REFUSAL: the factory-dissolved
//! holding-store verbs (`cesc`/`cobl` — the old escrow/obligation kernel ops) are gone from the
//! verified kernel (F1b deleted `RecordKernelState.escrows`; their semantics live in factory-born
//! cells, `Dregg2/Apps/{EscrowFactory,ObligationFactory}`). The kernel no longer PARSES those wire
//! actions — so a STALE OR MALICIOUS PEER whose bytes still carry one must be refused LOUDLY at
//! the wire (`committed == false` or the FFI error sentinel), NEVER silently skipped-and-committed
//! (a silent accept would install a post-state the sender never authorized — parse-confusion).
//!
//! HISTORY (2026-07-16 QA census): this file was a ZERO-TEST HUSK — its old round-trip pins were
//! deleted with the verb lockstep, leaving 173 lines of helpers, a docstring claiming an assertion
//! that did not exist, and a test target that reported `ok. 0 passed` forever. Two comments in
//! `rust_lean_divergence_finder.rs` cite a replacement tooth
//! (`lean_state_producer_coverage::queue_falls_back_factory_dissolved`) that was NEVER WRITTEN.
//! This file now holds the real tooth those comments promised, for the escrow/obligation family
//! plus the general unknown-verb pole.
//!
//! Mechanism: take a conformance-corpus case whose baseline wire COMMITS through
//! `shadow_exec_full_forest_auth` (so the mutation below is the only difference), swap its
//! `{"bal":[...]}` action tag for a dissolved (`cesc`/`cobl`) or unknown (`zzzz`) tag, and assert
//! the verified kernel refuses the mutant. If the kernel ever silently DROPPED the unknown action
//! and committed the rest of the turn, `committed` would be `true` and this suite goes RED.
//!
//! Requires the linked Lean archive; self-skips unarmed and PANICS under
//! `DREGG_TEST_REQUIRE_LEAN=1` (`demand_lean`) when the archive is absent.

use dregg_lean_ffi::marshal::{conformance_input_corpus, marshal_turn_hosted};
use dregg_lean_ffi::{
    decode_shadow_verdict, demand_lean, lean_available, shadow_exec_full_forest_auth,
};

fn skip_no_lean() -> bool {
    // Routed through the DREGG_TEST_REQUIRE_LEAN hard mode (dregg-lean-ffi::demand_lean):
    // unarmed, an archive-less build prints the honest SKIP and returns; ARMED, it PANICS —
    // so this suite can never report `ok` having asserted nothing on the hard-mode lane.
    !demand_lean(lean_available(), "Lean archive (lean_available)")
}

/// Run a raw wire string through the verified kernel; `Ok(committed)` on a decodable reply,
/// `Err` when the FFI itself refuses (also a LOUD outcome).
fn kernel_commit_bit(wire: &str) -> Result<bool, String> {
    let out = shadow_exec_full_forest_auth(wire)?;
    Ok(decode_shadow_verdict(&out)?.committed)
}

/// Find a corpus case whose marshalled wire (a) contains a `{"bal":[...]}` action to mutate and
/// (b) COMMITS at baseline — so the dissolved-verb swap is the ONLY difference the kernel sees.
fn committing_bal_wire() -> String {
    for (name, host, state, turn) in &conformance_input_corpus() {
        let wire = match marshal_turn_hosted(host, state, turn) {
            Ok(w) => w,
            Err(_) => continue,
        };
        if !wire.contains("{\"bal\":[") {
            continue;
        }
        if kernel_commit_bit(&wire) == Ok(true) {
            eprintln!("baseline corpus case `{name}` commits and carries a bal action");
            return wire;
        }
    }
    panic!(
        "no conformance-corpus case both commits and carries a {{\"bal\":[...]}} action — \
         the corpus lost its committing Balance case (fix the corpus, not this test)"
    );
}

/// The tooth: swapping the committing wire's `bal` tag for `verb` must flip the kernel from
/// COMMIT to a loud refusal — never a silent skip-and-commit.
fn dissolved_verb_refuses(verb: &str) {
    if skip_no_lean() {
        return;
    }
    let wire = committing_bal_wire();
    let mutant = wire.replacen("{\"bal\":[", &format!("{{\"{verb}\":["), 1);
    assert_ne!(wire, mutant, "mutation must change the wire");
    match kernel_commit_bit(&mutant) {
        Ok(committed) => assert!(
            !committed,
            "SILENT STATE INSTALL: the verified kernel COMMITTED a turn whose action carried the \
             dissolved/unknown wire verb `{verb}` — stale-peer bytes must refuse loudly, not be \
             skipped-and-committed (parse-confusion)"
        ),
        Err(e) => eprintln!("loud FFI refusal on `{verb}` (also acceptable): {e}"),
    }
}

/// `cesc` — the dissolved CreateEscrow kernel verb (F1b): stale peer bytes must refuse.
#[test]
fn dissolved_escrow_wire_verb_refuses_loudly() {
    dissolved_verb_refuses("cesc");
}

/// `cobl` — the dissolved CreateObligation kernel verb (F1b): stale peer bytes must refuse.
#[test]
fn dissolved_obligation_wire_verb_refuses_loudly() {
    dissolved_verb_refuses("cobl");
}

/// The general pole: a verb the kernel NEVER knew must refuse the same way (pins unknown-tag
/// handling as fail-closed, so a future "skip unknown actions" convenience can't slip in).
#[test]
fn unknown_wire_verb_never_silently_commits() {
    dissolved_verb_refuses("zzzz");
}

/// Baseline sanity pole (the tooth's non-vacuity floor): the UNMUTATED wire really commits, so
/// the three refusal tests above cannot pass vacuously off an already-rejecting baseline.
#[test]
fn baseline_bal_wire_commits() {
    if skip_no_lean() {
        return;
    }
    let wire = committing_bal_wire();
    assert_eq!(
        kernel_commit_bit(&wire),
        Ok(true),
        "the baseline committing corpus wire stopped committing — the refusal teeth above are \
         now vacuous; restore a committing Balance corpus case"
    );
}
