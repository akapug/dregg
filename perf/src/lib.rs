//! Shared turn-proof workload builders for the dregg perf harnesses.
//!
//! These construct honest Effect-VM traces via the SAME
//! `generate_effect_vm_trace` the executor witness path uses, so the timings
//! reflect the real production prover, not a toy.

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::generate_effect_vm_trace;

/// A named turn workload: an initial cell state plus the effect bundle that
/// makes up one turn.
pub struct Workload {
    pub name: &'static str,
    pub initial: CellState,
    pub effects: Vec<Effect>,
}

/// The reference workload set: a 1-effect self-transfer (the smallest real
/// turn), and progressively larger effect bundles, to show how prove time
/// scales with turn size on the fixed-height EffectVM AIR.
pub fn workloads() -> Vec<Workload> {
    vec![
        Workload {
            name: "transfer_1effect",
            initial: CellState::new(1_000_000, 0),
            effects: vec![Effect::Transfer { amount: 100, direction: 1 }],
        },
        Workload {
            name: "transfer_4effect",
            initial: CellState::new(1_000_000, 0),
            effects: (0..4)
                .map(|i| Effect::Transfer { amount: 10, direction: (i % 2) as u32 })
                .collect(),
        },
        Workload {
            name: "transfer_16effect",
            initial: CellState::new(1_000_000, 0),
            effects: (0..16)
                .map(|i| Effect::Transfer { amount: 1, direction: (i % 2) as u32 })
                .collect(),
        },
    ]
}

/// Build the (base_trace, public_inputs) pair for a workload — the exact inputs
/// `prove_effect_vm_p3` consumes.
pub fn build_trace(w: &Workload) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    generate_effect_vm_trace(&w.initial, &w.effects)
}
