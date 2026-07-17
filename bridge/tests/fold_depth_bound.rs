//! RIG (assumption-rigging / depth-shape-params) — the LIVE presentation fold-chain
//! depth bound.
//!
//! ASSUMPTION (bridge/src/present.rs:660-671):
//!   `BridgePresentationBuilder::add_attenuation` is the SOLE remaining enforcer of the
//!   fold-chain depth bound. The retired `prove_ivc` path (circuit/src/ivc.rs) carried
//!   its own `MAX_FOLD_DEPTH` guard and the ONLY boundary test that ever exercised it
//!   (ivc.rs:1754 `ivc_rejects_chain_exceeding_max_depth`) — but that path is no longer
//!   called by the live `present()`/`prove()` STARK flow (present.rs:961). The guard at
//!   present.rs:670 is:
//!       if self.chain.len() as u32 >= dregg_circuit::MAX_FOLD_DEPTH { return false; }
//!   Its own comment (present.rs:666) calls this SOUNDNESS. Nothing else stops a caller
//!   from building — and then proving through the real STARK — a delegation chain deeper
//!   than MAX_FOLD_DEPTH.
//!
//! WHY IT WAS UNRIGGED: the present.rs unit tests stop at chain_length 3
//! (`test_builder_state_transitions`) and bridge/tests/integration_present_credential.rs
//! calls `add_attenuation` only 6 times — none anywhere near depth 16. An off-by-one
//! (`>=` -> `>`) or a constant drift in this one guard would silently admit a
//! deeper-than-MAX chain with nothing catching it.
//!
//! THE TOOTH (proven to bite by mutation, see TESTQALOG entry):
//!   - `>=` -> `>` in present.rs:670 makes the cap 17 -> `depth_bound_caps_the_live_chain`
//!     RED (final chain_length 17 != 16).
//!   - Removing the guard entirely -> `add_attenuation` keeps succeeding past 15 ->
//!     both the success-count and the final-length asserts go RED.
//!   - Bumping `MAX_FOLD_DEPTH` (circuit) without intent -> the literal `== 16`
//!     depth-shape pin goes RED, forcing a conscious change.

use dregg_bridge::BridgePresentationBuilder;
use dregg_circuit::MAX_FOLD_DEPTH;
use dregg_token::{Attenuation, MacaroonToken};

fn test_key() -> [u8; 32] {
    let mut k = [0u8; 32];
    k[0] = 0x42;
    k[1] = 0x13;
    k[31] = 0xFF;
    k
}

fn test_federation_root() -> [u8; 32] {
    let mut r = [0u8; 32];
    r[0] = 0xFE;
    r[1] = 0xDE;
    r[31] = 0x01;
    r
}

/// A genuine, distinct attenuation for step `i`. Cycles through several caveat
/// TYPES so the first steps deepen the chain with genuinely distinct checks; once
/// the types repeat the delta is an idempotent narrowing, which still pushes a
/// chain step (FoldDelta::compute accepts a no-op narrowing) and therefore still
/// exercises the depth guard — exactly what we are probing.
fn attenuation_for_step(i: usize) -> Attenuation {
    match i % 8 {
        0 => Attenuation {
            apps: vec![(format!("app-{i}"), "rw".into())],
            ..Default::default()
        },
        1 => Attenuation {
            services: vec![(format!("svc-{i}"), "rw".into())],
            ..Default::default()
        },
        2 => Attenuation {
            features: vec![format!("feat-{i}")],
            ..Default::default()
        },
        3 => Attenuation {
            confine_user: Some(format!("user-{i}")),
            ..Default::default()
        },
        4 => Attenuation {
            not_after: Some(1_000_000 + i as i64),
            ..Default::default()
        },
        5 => Attenuation {
            not_before: Some(500_000 + i as i64),
            ..Default::default()
        },
        6 => Attenuation {
            oauth_providers: vec![format!("prov-{i}")],
            ..Default::default()
        },
        _ => Attenuation {
            oauth_scopes: vec![format!("scope-{i}")],
            ..Default::default()
        },
    }
}

/// DEPTH-SHAPE PIN: the deployed maximum fold depth is exactly 16. This is the
/// concrete param the live guard reads; pin it so a silent bump forces a conscious
/// review (VK / circuit-row / prover-cost implications ride on it).
#[test]
fn deployed_max_fold_depth_is_sixteen() {
    assert_eq!(
        MAX_FOLD_DEPTH, 16,
        "MAX_FOLD_DEPTH drifted from the deployed depth-shape param (16); \
         the live present.rs:670 guard and every downstream cost bound assume 16"
    );
}

/// THE TOOTH: the live presentation fold path caps the chain at exactly
/// MAX_FOLD_DEPTH, and add_attenuation is what enforces it.
///
/// Non-vacuity is self-contained: we assert EXACTLY (MAX_FOLD_DEPTH - 1) attenuations
/// succeed and then the next is refused. If the guard were removed or loosened, MORE
/// would succeed (RED). If an attenuation failed EARLY for an unrelated reason, FEWER
/// would succeed (RED) — so the count also proves the chain genuinely reached the guard
/// rather than stopping short.
#[test]
fn depth_bound_caps_the_live_chain() {
    let key = test_key();
    let mut builder = BridgePresentationBuilder::new(key, test_federation_root());
    builder.set_root_token(MacaroonToken::mint(key, b"kid-1", "dregg.fg-goose.online"));
    assert_eq!(builder.chain_length(), 1, "root step present");

    let mut successes = 0usize;
    // Try well past the bound; the guard must stop us.
    let attempts = MAX_FOLD_DEPTH as usize + 8;
    let mut first_refusal_at = None;
    for i in 0..attempts {
        if builder.add_attenuation(&attenuation_for_step(i)) {
            successes += 1;
        } else {
            first_refusal_at = Some(i);
            break;
        }
    }

    // The guard rejects once chain.len() (which starts at 1 for the root) reaches
    // MAX_FOLD_DEPTH, so exactly MAX_FOLD_DEPTH-1 attenuations are admitted.
    assert_eq!(
        successes,
        MAX_FOLD_DEPTH as usize - 1,
        "add_attenuation admitted {successes} steps; the depth guard should admit exactly \
         MAX_FOLD_DEPTH-1 = {} before refusing (loosened guard => more; broken attenuation => fewer)",
        MAX_FOLD_DEPTH as usize - 1
    );
    assert!(
        first_refusal_at.is_some(),
        "add_attenuation NEVER refused within {attempts} attempts — the depth guard is not enforcing"
    );

    // The enforced cap equals the declared param: the chain tops out at MAX_FOLD_DEPTH
    // states (root + MAX_FOLD_DEPTH-1 folds).
    assert_eq!(
        builder.chain_length(),
        MAX_FOLD_DEPTH as usize,
        "final chain_length {} != MAX_FOLD_DEPTH {}; an off-by-one (>= vs >) or a guard \
         reading the wrong constant lands here",
        builder.chain_length(),
        MAX_FOLD_DEPTH
    );

    // The refusal is stable: once at the cap, further attempts stay refused and do not
    // grow the chain (a fail-closed guard, not a one-shot).
    assert!(
        !builder.add_attenuation(&attenuation_for_step(999)),
        "guard must keep refusing at the cap"
    );
    assert_eq!(
        builder.chain_length(),
        MAX_FOLD_DEPTH as usize,
        "a refused attenuation must not grow the chain"
    );
}

/// Independent literal cross-check on the enforced cap: reaching the cap yields a chain
/// of exactly 16 states regardless of how the guard is spelled. Reads the OBSERVED cap,
/// not the constant, so a guard that stopped reading MAX_FOLD_DEPTH (hardcoded a larger
/// number) still lands here.
#[test]
fn enforced_cap_is_exactly_sixteen_states() {
    let key = test_key();
    let mut builder = BridgePresentationBuilder::new(key, test_federation_root());
    builder.set_root_token(MacaroonToken::mint(key, b"kid-1", "dregg.fg-goose.online"));
    for i in 0..(MAX_FOLD_DEPTH as usize + 8) {
        if !builder.add_attenuation(&attenuation_for_step(i)) {
            break;
        }
    }
    assert_eq!(
        builder.chain_length(),
        16,
        "the LIVE fold chain must cap at 16 states; a looser enforced depth lands here \
         even if MAX_FOLD_DEPTH itself was also changed"
    );
}
