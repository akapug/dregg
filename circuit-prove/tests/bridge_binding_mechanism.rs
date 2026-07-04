//! # THE BRIDGE-BINDING FOLD-MECHANISM TOOTH.
//!
//! The bridge analog of the in-lib custom fold-wire teeth: it exercises the bridge-binding MECHANISM
//! end-to-end over REAL recursion leaves, WITHOUT the deployed bridge-mint leg's tuple-emit (the
//! named big-bang piece). Two `prove_bridge_leaf_tuple_claim` leaves — each a genuine bridge-action
//! sub-proof re-exposing its bound 26-slot `(nullifier, recipient, dest_federation, amount)` tuple as
//! an `expose_claim` — are folded through `prove_bridge_binding_node`, which `connect`s the two
//! tuples lane-by-lane.
//!
//! * HONEST — both leaves attest the SAME action: the per-lane `connect` is consistent, the node
//!   folds, the bound tuple is re-exposed.
//! * FORGED — the "leg" leaf claims a DIFFERENT action than the bound sub-proof attests: the
//!   per-lane `connect` is a conflict ⇒ the aggregation is UNSAT ⇒ no node proof. This is the bite
//!   that makes the bridge binding REAL for a pure light client: a leg cannot claim a foreign-spend
//!   tuple no verifying bridge-action sub-proof backs.
//!
//! The deployed wiring (a DUAL-EXPOSE bridge-mint leg leaf, segment ++ the 26-limb tuple at fixed PI
//! slots, folded via `prove_bridge_binding_node_segmented`) is READY but gated on the bridge-mint
//! descriptor EMITTING the tuple PIs — that descriptor-emit rides the big-bang VK regen. This tooth
//! proves the fold MECHANISM + the sub-proof leaf are correct today.
//!
//! Real recursion (minutes), so both poles are `#[ignore]`. Run with:
//!   cargo test -p dregg-circuit-prove --test bridge_binding_mechanism -- --ignored --nocapture

use dregg_circuit::bridge_action_air::BridgeActionWitness;
use dregg_circuit_prove::bridge_leaf_adapter::prove_bridge_leaf_tuple_claim;
use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;
use dregg_circuit_prove::joint_turn_recursive::prove_bridge_binding_node;

fn witness(nf: u8) -> BridgeActionWitness {
    BridgeActionWitness {
        nullifier: [nf; 32],
        recipient: [0x20; 32],
        destination_federation: [0x30; 32],
        amount: 0xDEAD_BEEF_CAFE_F00D,
    }
}

/// POSITIVE POLE — the leg leaf and the bridge sub-proof leaf attest the SAME 26-slot tuple: the
/// binding node folds and re-exposes the bound tuple.
#[test]
#[ignore = "SLOW: real bridge-binding recursion fold (~minutes); run with --ignored"]
fn bridge_binding_honest_folds() {
    let config = ir2_leaf_wrap_config();
    let w = witness(0x10);
    let pis = w.public_inputs();

    let leg = prove_bridge_leaf_tuple_claim(&w, &pis, &config)
        .expect("bridge leg tuple-claim leaf mints");
    let sub = prove_bridge_leaf_tuple_claim(&w, &pis, &config)
        .expect("bridge sub-proof tuple-claim leaf mints");

    prove_bridge_binding_node(&leg, &sub, &config)
        .expect("the honest bridge-binding node folds (tuples agree)");
    eprintln!("BRIDGE binding: honest tuple FOLDED + bound in the recursion tree.");
}

/// THE TOOTH — the leg leaf claims a DIFFERENT tuple (a forged foreign-spend) than the bound
/// sub-proof attests: the in-circuit `connect` is a conflict ⇒ UNSAT ⇒ no node proof.
#[test]
#[ignore = "SLOW: real bridge-binding recursion fold (~minutes); run with --ignored"]
fn bridge_binding_forged_rejected() {
    let config = ir2_leaf_wrap_config();
    let leg_w = witness(0x99); // the leg claims a DIFFERENT nullifier
    let sub_w = witness(0x10); // the bound sub-proof attests the honest one
    let leg_pis = leg_w.public_inputs();
    let sub_pis = sub_w.public_inputs();
    assert_ne!(leg_pis, sub_pis);

    let leg = prove_bridge_leaf_tuple_claim(&leg_w, &leg_pis, &config)
        .expect("the forged leg is itself a valid (but DIFFERENT) bridge-action leaf");
    let sub = prove_bridge_leaf_tuple_claim(&sub_w, &sub_pis, &config)
        .expect("the honest sub-proof leaf mints");

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_bridge_binding_node(&leg, &sub, &config)
    }));
    match result {
        Err(_) => {}
        Ok(Err(_)) => {}
        Ok(Ok(_)) => panic!(
            "a leg claiming a tuple NO bound bridge-action sub-proof backs folded into a verifying \
             node — the bridge binding mechanism is OPEN"
        ),
    }
    eprintln!("BRIDGE binding: forged tuple REJECTED by the fold (connect conflict ⇒ no root).");
}
