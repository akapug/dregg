//! # The parse-as-derivation FIRST SLICE — the Dyck stack spike + tamper canary.
//!
//! Mirrors `circuit-prove/tests/derivation_emit_audit_extra.rs`: an HONEST witness
//! ACCEPTS and every single-tooth TAMPER REJECTS, so the acceptance is non-vacuous.
//!
//! The circuit is `dregg_circuit::dsl::dyck_stack` (`docs/DESIGN-parse-as-derivation.md`
//! §5 "smallest first slice"): the `D = 3` bounded pushdown stack routing the 3-rule
//! Dyck grammar `S → [ S ] | ε` (`metatheory/Dregg2/Crypto/CfgCompact.lean` `Reference`),
//! proving acceptance of `"[]"` — the exact word `CfgCompact.Reference.brackets_replays`
//! accepts via the compact certificate `[rBracket, rEmpty]`.
//!
//! Acceptance here is the descriptor-satisfaction predicate `dyck_satisfied` (the Rust
//! `Satisfied2` analogue), which DRIVES the deployed `ConstraintExpr::evaluate_with_tables`
//! over the whole trace domain + boundaries. Each canary mutates ONE load-bearing tooth:
//!
//!   * a **stack cell** — breaks the `term` top-match and the `rBracket` push threading;
//!   * the **`RULE_ID`** — breaks the rule sub-selector pin (`SEL_BRACKET·(RULE_ID−1)==0`);
//!   * the **input token** — breaks the `term` top-match against the tape;
//!   * the **first-row stack depth** — breaks the `[initial]` boundary pin;
//!   * the **`route_commitment` public input** — breaks the last-row commitment binding.

use dregg_circuit::dsl::dyck_stack::{
    RULE_EMPTY, SYM_CL, build_brackets_witness, col, dyck_parse_descriptor, dyck_satisfied, pi,
};
use dregg_circuit::field::BabyBear;

const NAME: &str = "dregg-dyck-parse-v1";

/// The trace rows, for readability of the tamper sites (the honest `"[]"` replay):
/// `0 = rule rBracket`, `1 = term '['`, `2 = rule rEmpty`, `3 = term ']'`, `4.. = done`.
const ROW_RULE_BRACKET: usize = 0;
const ROW_TERM_OPEN: usize = 1;

/// The honest `"[]"` parse satisfies the descriptor.
#[test]
fn brackets_parse_accepts() {
    let desc = dyck_parse_descriptor(NAME);
    let (trace, public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "the honest '[]' pushdown replay must ACCEPT"
    );
}

/// Canary — mutate a **stack cell**: flip the `term '['` row's stack top from `op` to
/// `cl`. The `term` top-match (`STACK0 == INPUT_TOKEN`) and the `rBracket` push
/// (`next.STACK0 == op`) both break.
#[test]
fn tamper_stack_cell_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (mut trace, public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    trace[ROW_TERM_OPEN][col::STACK0] = BabyBear::new(SYM_CL);
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a mutated stack cell must REJECT"
    );
}

/// Canary — mutate the **`RULE_ID`**: claim the first row fires `rEmpty` while its
/// `SEL_BRACKET` selector is still 1. The rule sub-selector pin
/// `SEL_BRACKET·(RULE_ID − rBracket) == 0` breaks.
#[test]
fn tamper_rule_id_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (mut trace, public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    trace[ROW_RULE_BRACKET][col::RULE_ID] = BabyBear::new(RULE_EMPTY);
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a forged RULE_ID (selector/rule mismatch) must REJECT"
    );
}

/// Canary — mutate the **input token**: the `term '['` row reads `']'` off the tape
/// instead of `'['`. The `term` top-match (`STACK0 == INPUT_TOKEN`) breaks.
#[test]
fn tamper_input_token_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (mut trace, public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    trace[ROW_TERM_OPEN][col::INPUT_TOKEN] = BabyBear::new(SYM_CL);
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a forged input token must REJECT"
    );
}

/// Canary — mutate the **first-row stack depth**: start at depth 2 instead of 1. The
/// `[initial]`-stack boundary pin (`STACK_DEPTH first == 1`) breaks.
#[test]
fn tamper_initial_depth_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (mut trace, public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    trace[0][col::STACK_DEPTH] = BabyBear::new(2);
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a forged initial stack depth must REJECT"
    );
}

/// Canary — mutate the **`route_commitment` public input**: claim a different parse
/// commitment than the trace's last-row `RUNNING_HASH`. The last-row PI boundary
/// binding breaks (the parse cannot claim a commitment it did not compute).
#[test]
fn tamper_route_commitment_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (trace, mut public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    public_inputs[pi::ROUTE_COMMITMENT] += BabyBear::ONE;
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a forged route_commitment must REJECT"
    );
}
