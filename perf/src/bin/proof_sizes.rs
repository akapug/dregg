//! Proof-SIZE microbench: the wire-byte numbers we already track, made
//! regression-tracked rather than eyeballed.
//!
//! Emits, for the canonical single-Transfer turn, the wire byte size of:
//!   * the hand-AIR EffectVM proof (`prove_effect_vm_p3`),
//!   * the verified descriptor-interpreter proof (`prove_vm_descriptor`),
//!   * the full self-sovereign turn proof (`prove_turn_self_sovereign`).
//!
//! These are the figures the docs cite (the IR-v2 ~120 KiB descriptor proof,
//! the rotated full-turn ~144 KiB). Run it on persvati and compare the JSON to
//! the committed baseline to catch a size regression.
//!
//! Run:   cargo run --release -p dregg-perf --bin proof-sizes
//! JSON:  cargo run --release -p dregg-perf --bin proof-sizes -- --json

use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
use dregg_circuit::effect_vm_p3_full_air::prove_effect_vm_p3;
use dregg_circuit::generate_effect_vm_trace;
use dregg_circuit::lean_descriptor_air::{parse_vm_descriptor, prove_vm_descriptor};
use dregg_perf::{fmt_bytes, single_transfer};

fn p3_bytes<T: serde::Serialize>(p: &T) -> usize {
    postcard::to_allocvec(p).map(|v| v.len()).unwrap_or(0)
}

fn main() {
    let json_mode = std::env::args().any(|a| a == "--json");

    let (st, effs) = single_transfer();
    let (trace, pis) = generate_effect_vm_trace(&st, &effs);

    // 1. hand-AIR EffectVM proof.
    let hand = prove_effect_vm_p3(&trace, &pis).expect("hand-AIR prove");
    let hand_bytes = p3_bytes(&hand);

    // 2. verified descriptor-interpreter proof (selector 1 = TRANSFER).
    let desc_bytes = descriptor_for_selector(1).map(|json| {
        let desc = parse_vm_descriptor(json).expect("parse transfer descriptor");
        let dpis = pis[..desc.public_input_count].to_vec();
        let proof = prove_vm_descriptor(&desc, &trace, &dpis).expect("descriptor prove");
        p3_bytes(&proof)
    });

    // 3. full self-sovereign turn proof (the real node wire size).
    let turn_bytes = {
        use dregg_sdk::prove_turn_self_sovereign;
        let proof = prove_turn_self_sovereign(&st, &effs, [7u8; 32]).expect("full-turn prove");
        proof.proof_bytes.len()
    };

    let _ = pi::OLD_COMMIT; // keep the pi import meaningful / stable across refactors.

    if json_mode {
        let desc_field = match desc_bytes {
            Some(b) => b.to_string(),
            None => "null".to_string(),
        };
        println!(
            "{{\"effect_vm_hand_air_bytes\":{},\"descriptor_interp_bytes\":{},\"full_turn_self_sovereign_bytes\":{}}}",
            hand_bytes, desc_field, turn_bytes
        );
    } else {
        println!("dregg proof-size microbench (canonical single Transfer)");
        println!("  {:<34} {:>12}", "EffectVM hand-AIR proof", fmt_bytes(hand_bytes));
        match desc_bytes {
            Some(b) => println!(
                "  {:<34} {:>12}",
                "descriptor-interp proof (IR-v2)",
                fmt_bytes(b)
            ),
            None => println!("  {:<34} {:>12}", "descriptor-interp proof", "(no descriptor)"),
        }
        println!(
            "  {:<34} {:>12}",
            "full self-sovereign turn proof",
            fmt_bytes(turn_bytes)
        );
        println!();
        println!("  (compare against the committed baseline JSON: --json mode)");
    }
}
