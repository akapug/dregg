//! Track C rung 2a falsifier: **the protocol-native run accept-path references no
//! custody types.**
//!
//! `docs/deos/PROTOCOL-NATIVE-ECONOMY.md` §4/§6 states the load-bearing falsifier
//! for rung 2a: "grep the run-execution path for the custody types and find
//! nothing." The protocol-native accept path is `dregg-pay/src/protocol_native.rs`
//! (`RunBudgetLedger::charge_run` → `dregg_payable::resolve_pay` → one
//! `Effect::Transfer`). This test greps that module's own source at compile time
//! and fails if any custody type — the HD "B"-model key material or the sweeper —
//! is reachable from it.
//!
//! It is a *structural* falsifier: if a future edit imports `crate::hd`,
//! `crate::sweeper`, or names the custody-key / sweeper types on this path, the
//! substring reappears and this test goes red. The token strings below are built
//! from fragments so this test file itself does not contain the literal tokens it
//! forbids (which would make the grep self-defeating).

/// The exact source of the protocol-native accept path.
const ACCEPT_PATH_SRC: &str = include_str!("../src/protocol_native.rs");

/// Build a forbidden token from fragments, so THIS test's source does not itself
/// contain the literal token (otherwise a grep over the repo would flag the test).
fn forbidden_tokens() -> Vec<String> {
    vec![
        // the HD custody key type
        format!("{}{}", "Se", "ed"),
        // the sweeper type / module
        format!("{}{}", "Sweep", "er"),
        format!("{}{}", "sweep", "er::"),
        // the custody-key env var
        format!("{}{}", "DREGG_PAY_", "SEED"),
        // direct imports of the custodial modules
        format!("crate::{}", "hd"),
        format!("crate::{}", "sweeper"),
    ]
}

#[test]
fn protocol_native_accept_path_names_no_custody_type() {
    for tok in forbidden_tokens() {
        assert!(
            !ACCEPT_PATH_SRC.contains(&tok),
            "rung 2a falsifier: the protocol-native run accept path \
             (dregg-pay/src/protocol_native.rs) must not reference custody type `{tok}` — \
             if it is reachable, the run is custodial in fact and the rung is not done"
        );
    }
}

/// Sanity: the falsifier is not vacuous — the token set is non-empty and the
/// module source we scan is real and non-trivial.
#[test]
fn falsifier_scans_a_real_nonempty_accept_path() {
    assert!(!forbidden_tokens().is_empty());
    assert!(
        ACCEPT_PATH_SRC.contains("charge_run") && ACCEPT_PATH_SRC.contains("resolve_pay"),
        "we must be scanning the actual accept path (charge_run → resolve_pay)"
    );
    // Prove the check can fire: the token set genuinely matches its target strings
    // (so a real custody reference would be caught, not silently missed).
    let sample = format!("{}{}", "Sweep", "er");
    assert!(
        forbidden_tokens().iter().any(|t| *t == sample),
        "the sweeper token must be among those forbidden"
    );
}
