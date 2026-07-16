//! **LAW #1 RATCHET** — the systematic enforcement of "zero Rust-authored constraints or AIRs, ever".
//!
//! `metatheory/README.md:15` states architectural law #1: *"Circuits are **emitted from Lean**... Rust only
//! INTERPRETS those artifacts. A coverage gap is closed by emitting from a new proved module, **never** by
//! hand-authoring a constraint."* Until now that law lived only in PROSE — and prose does not fail a build.
//! Four separate audits (two by the author of this file) miscounted the violation surface, because:
//!
//! **There are THREE constraint dialects, and a grep for one sees a third of the truth:**
//!   1. `builder.assert_zero(..)` / `assert_eq` / `when(..)`  — plonky3 symbolic. GREPPABLE.
//!   2. `Constraint { eval: Box::new(|row, _, pi| ..) }`      — CLOSURES. Invisible to (1).
//!   3. `ConstraintExpr::{Binary,Polynomial,Hash,..}` literals — DATA. Invisible to (1) and (2).
//!
//! A `*_air.rs` filename proves nothing (many hold no algebra; much algebra lives outside them). So this
//! gate scans EVERY `.rs` in `circuit/src` + `circuit-prove/src` across ALL THREE dialects and RATCHETS:
//! the baseline below is frozen ground truth as of 2026-07-16. **A new file with constraint algebra, or a
//! listed file growing, FAILS.** Shrinking is always allowed (that is the direction of the law).
//!
//! ## If this test fails
//! You (or an agent) hand-authored a constraint in Rust. That is the violation itself — do NOT add your
//! file to the baseline to make it green. Emit it from Lean instead (`metatheory/Dregg2/Circuit/Emit/*.lean`
//! -> `emitVmJson2` -> `descriptors/by-name/*.json` -> `descriptor_by_name` -> `prove_vm_descriptor2`; see
//! `EffectVmEmitTurnChainBinding.lean` + `metatheory/EmitTurnChain.lean` for the worked end-to-end example).
//! Lower the baseline when you retire algebra; raise it only with a recorded reason in GOAL-STARK-KILL.md.
//!
//! ## Why entries remain (the honest ledger, not an amnesty)
//! * INTERPRETERS (the law WORKING — they evaluate Lean-authored constraints, they do not author):
//!   `descriptor_ir2.rs` (99), `dsl/dsl_p3_air.rs` (86), `lean_lookup_air.rs` (the proven range gadget).
//! * PROVED-FAITHFUL LOWERINGS: `custom_leaf_adapter.rs` (50) — `CustomLeafEncoding.lean::
//!   cell_to_descriptor_faithful` proves the encoding preserves semantics.
//! * DRIFT-DETECTORS, deliberately kept: `dsl/derivation.rs` (59), `dsl/note_spending.rs` (27) — the
//!   EMITTED paths walk these v1 descriptors as their SOURCE, so "a drift in the deployed circuit is a
//!   build-time refusal, never a silent divergence" (`note_spend_witness.rs:225-227`).
//! * THE USER-PROGRAM GRAMMAR: `dsl/predicates/*`, `dsl/descriptors.rs` — the host-trusted smart-contract
//!   surface users deploy programs against; interpreted, fails closed on an unknown vk_hash.
//! * NAMED RESIDUALS (real, tracked in GOAL-STARK-KILL.md): `dsl/revocation.rs` (40) — DEPLOYED via
//!   `sdk/privacy.rs:621`, blocked by `NonRevocationDepthResidual` (emitter depth-2 vs deployed
//!   TREE_DEPTH=4; cutting over would SHRINK the tree). `ivc.rs` (14) + `dsl/fold.rs` (15, `FoldAir`) —
//!   test-only; `ivc`'s emitter is one Lean PROVES insufficient (`ivc_anchor_insufficient`).

use std::path::Path;

/// The three dialects. Miss one and you will miscount — that is the whole point of this gate.
fn count_constraint_sites(src: &str) -> usize {
    let d1 = src.matches("builder.assert_zero").count()
        + src.matches("builder.assert_eq").count()
        + src.matches("builder.when").count();
    let d2 = src.matches("eval: Box::new").count();
    let d3 = src
        .match_indices("ConstraintExpr::")
        .filter(|(i, _)| {
            src[i + "ConstraintExpr::".len()..]
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_uppercase())
        })
        .count();
    d1 + d2 + d3
}

/// Frozen ground truth (2026-07-16). See the module docs before touching this.
#[rustfmt::skip]
const BASELINE: &[(&str, usize)] = &[
        ("circuit-prove/src/custom_leaf_adapter.rs", 50),
        ("circuit-prove/src/dregg_outer_config.rs", 3),
        ("circuit-prove/src/dsl_leaf_adapter.rs", 3),
        ("circuit-prove/src/effect_vm_p3_air.rs", 9),
        ("circuit-prove/src/gpu_backend.rs", 3),
        ("circuit-prove/src/joint_turn_aggregation.rs", 2),
        ("circuit-prove/src/joint_turn_recursive.rs", 2),
        ("circuit-prove/src/lean_lookup_air.rs", 3),
        ("circuit-prove/src/membership_leaf_adapter.rs", 1),
        ("circuit-prove/src/mpt_holding_leaf.rs", 8),
        ("circuit-prove/src/note_spend_leaf_adapter.rs", 13),
        ("circuit-prove/src/shielded_spend_leaf_adapter.rs", 14),
        ("circuit-prove/src/shielded/attest.rs", 11),
        ("circuit-prove/src/shielded/spend_circuit.rs", 11),
        ("circuit/src/bilateral_aggregation_air.rs", 7),
        ("circuit/src/cap_root.rs", 1),
        ("circuit/src/committed_threshold.rs", 7),
        ("circuit/src/constraint_prover.rs", 1),
        ("circuit/src/derivation_air.rs", 1),
        ("circuit/src/descriptor_ir2.rs", 99),
        ("circuit/src/dsl/accumulator.rs", 10),
        ("circuit/src/dsl/cap_membership.rs", 5),
        ("circuit/src/dsl/circuit.rs", 6),
        ("circuit/src/dsl/committed_threshold.rs", 7),
        ("circuit/src/dsl/derivation.rs", 59),
        ("circuit/src/dsl/descriptors.rs", 40),
        ("circuit/src/dsl/dfa_routing.rs", 9),
        ("circuit/src/dsl/dsl_p3_air.rs", 86),
        ("circuit/src/dsl/fold.rs", 15),
        ("circuit/src/dsl/garbled.rs", 14),
        ("circuit/src/dsl/membership.rs", 1),
        ("circuit/src/dsl/note_spending.rs", 27),
        ("circuit/src/dsl/openable_fields_insertion.rs", 6),
        ("circuit/src/dsl/predicates/arithmetic.rs", 42),
        ("circuit/src/dsl/predicates/base.rs", 34),
        ("circuit/src/dsl/predicates/compound.rs", 20),
        ("circuit/src/dsl/predicates/relational.rs", 31),
        ("circuit/src/dsl/revocation.rs", 40),
        ("circuit/src/dsl/temporal_absence.rs", 4),
        ("circuit/src/garbled_air.rs", 1),
        ("circuit/src/ivc.rs", 14),
        ("circuit/src/lean_descriptor_air.rs", 9),
        ("circuit/src/membership_adjacency_air.rs", 1),
        ("circuit/src/merkle_types.rs", 4),
        ("circuit/src/note_spend_witness.rs", 12),
        ("circuit/src/plonky3_prover.rs", 7),
        ("circuit/src/plonky3_recursion.rs", 3),
        ("circuit/src/presentation.rs", 1),
];

#[test]
fn law1_no_new_rust_authored_constraints() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let mut violations = Vec::new();
    let mut stack = vec![root.join("circuit/src"), root.join("circuit-prove/src")];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
                continue;
            }
            if p.extension().and_then(|s| s.to_str()) != Some("rs") {
                continue;
            }
            let Ok(src) = std::fs::read_to_string(&p) else {
                continue;
            };
            let n = count_constraint_sites(&src);
            if n == 0 {
                continue;
            }
            let rel = p
                .strip_prefix(root)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            match BASELINE.iter().find(|(f, _)| *f == rel) {
                None => violations.push(format!(
                    "  NEW Rust-authored constraints: {rel} ({n} sites)\n     -> EMIT IT FROM LEAN. Do not add it to the baseline."
                )),
                Some((_, allowed)) if n > *allowed => violations.push(format!(
                    "  GREW: {rel} ({allowed} -> {n} sites)\n     -> new hand-authored constraints. Emit them from Lean."
                )),
                _ => {}
            }
        }
    }
    assert!(
        violations.is_empty(),
        "\n\nARCHITECTURAL LAW #1 VIOLATED — Rust must author NO constraints.\n\n{}\n\nSee this file's module docs for how to emit from Lean instead.\n",
        violations.join("\n")
    );
}
