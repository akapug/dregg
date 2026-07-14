//! SLOW: the automaton-step (D1) AIR PROVES as a real recursion-foldable custom
//! leaf, its in-circuit commitment byte-matches the host binding, folds into a real
//! turn chain, and the light client `verify_history` ACCEPTS — the HARD GATE.
//!
//! Custom-leaf proving is minutes+; every test here is `#[ignore]`. Run on persvati:
//!   cargo test -p dregg-automatafl --test prove_fold -- --ignored --nocapture

use dregg_automatafl::build_d1_honest;
use dregg_automatafl::reference::{ATT, AUTO, Board, VAC, automaton_step};

use dregg_circuit::field::BabyBear;

fn mk(n: usize, placed: &[((i32, i32), u8)], auto: (i32, i32)) -> Board {
    let mut cells = vec![VAC; n * n];
    for &(c, p) in placed {
        cells[(c.1 as usize) * n + (c.0 as usize)] = p;
    }
    cells[(auto.1 as usize) * n + (auto.0 as usize)] = AUTO;
    Board {
        n,
        cells,
        auto,
        col_rule: true,
    }
}

/// The driven D1 board: attractor two north, automaton steps north (the Lean demoBoard).
fn demo() -> Board {
    mk(5, &[((2, 4), ATT)], (2, 2))
}

// ============================================================================
// The leaf boundary (runnable in THIS tree — no rotated-witness path).
// ============================================================================

#[test]
#[ignore = "SLOW: real leaf prove of the ~989-col automaton-step AIR + in-circuit commitment expose"]
fn d1_leaf_proves_and_binds_commitment() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let old = demo();
    let b = build_d1_honest(&old);
    assert!(
        b.air_accepts(),
        "sanity: honest D1 must self-accept before proving"
    );
    let program = b.cellprogram();
    let rows = 2usize;
    let w = b.trace_witness(rows);
    let pis = b.pis.clone();
    let config = ir2_leaf_wrap_config();

    let out = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
        .expect("the honest automaton-step AIR must prove as a commitment-exposing foldable leaf");
    let exposed = read_exposed_pi_commitment(&out).expect("leaf exposes an 8-felt commitment");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "in-circuit commitment must byte-match the host WideHash binding"
    );
    eprintln!(
        "D1 LEAF: automaton-step AIR (w={}, {} constraints) PROVED as a foldable leaf; \
         in-circuit commitment == host binding {:?}",
        program.descriptor.trace_width,
        program.descriptor.constraints.len(),
        host.map(|f| f.0)
    );
}

#[test]
#[ignore = "SLOW: real leaf prove attempt on a FORGED next board"]
fn d1_forged_next_does_not_prove() {
    use dregg_automatafl::build_d1;
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let old = demo();
    // demo() steps the automaton north; forge next == old (claim it did NOT move).
    let forged_next = old.clone();
    assert_ne!(
        forged_next,
        automaton_step(&old),
        "the forgery must differ from the truth"
    );
    let b = build_d1(&old, &forged_next);
    // The witness self-check already rejects; a real prove must ALSO fail to assemble.
    assert!(!b.air_accepts(), "sanity: forged next must self-reject");
    let program = b.cellprogram();
    let rows = 2usize;
    let w = b.trace_witness(rows);
    let pis = b.pis.clone();
    let config = ir2_leaf_wrap_config();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
    }));
    match res {
        Err(_) | Ok(Err(_)) => {
            eprintln!("D1 LEAF REJECT: a forged automaton-step (no-move) had no satisfying leaf.");
        }
        Ok(Ok(_)) => panic!("a FORGED automaton-step minted a foldable leaf — soundness OPEN"),
    }
}

// ============================================================================
// The full deployed fold — D1 leaf binds to a Custom-effect turn, folds a K=2
// chain via prove_turn_chain_recursive, verify_history ACCEPTS. (Copies the
// audited game-turn-slice scaffolding, swapping the combat program for D1.)
// ============================================================================
mod fold {
    use super::*;
    use dregg_cell::Ledger;
    use dregg_circuit::descriptor_ir2::{UMemBoundaryWitness, prove_vm_descriptor2_for_config};
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, empty_caveat_manifest,
        generate_rotated_effect_vm_descriptor_and_trace_wide,
    };
    use dregg_circuit::effect_vm::{CellState, Effect};
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::{
        FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive,
    };
    use dregg_circuit_prove::joint_turn_aggregation::{
        CustomWitnessBundle, DescriptorParticipant, RotatedParticipantLeg,
    };
    use dregg_lightclient::verify_history;
    use dregg_turn::rotation_witness as rw;

    fn open_permissions() -> dregg_cell::Permissions {
        use dregg_cell::AuthRequired;
        dregg_cell::Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
        cell.permissions = open_permissions();
        for _ in 0..nonce {
            let _ = cell.state.increment_nonce();
        }
        cell
    }

    fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
    }

    fn d1_bundle() -> (super::build_helper::Prog, CustomWitnessBundle) {
        let old = demo();
        let b = build_d1_honest(&old);
        let program = b.cellprogram();
        let rows = 2usize;
        let w = b.trace_witness(rows);
        let pis = b.pis.clone();
        (
            super::build_helper::Prog { pis: pis.clone() },
            CustomWitnessBundle {
                program,
                witness_values: w,
                num_rows: rows,
                public_inputs: pis,
            },
        )
    }

    fn mint_custom_leg(
        balance: i64,
        nonce: u64,
        commit: [BabyBear; 8],
        bundle: Option<CustomWitnessBundle>,
    ) -> RotatedParticipantLeg {
        let st = CellState::new(balance as u64, nonce as u32);
        let effects = vec![Effect::Custom {
            program_vk_hash: [BabyBear::new(9); 8],
            proof_commitment: commit,
        }];
        let before_cell = producer_cell(balance, nonce);
        let after_cell = producer_cell(balance, nonce + 1);

        let mut ledger = Ledger::new();
        ledger.insert_cell(after_cell.clone()).expect("ledger seed");
        let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
        let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
        let before_w = bridge(&rw::produce(
            &before_cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        ));
        let after_w = bridge(&rw::produce(
            &after_cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        ));

        let (desc, trace, dpis, map_heaps, mb) =
            generate_rotated_effect_vm_descriptor_and_trace_wide(
                &st,
                &effects,
                &before_w,
                &after_w,
                &empty_caveat_manifest(),
                None,
                None,
                None,
                None,
            )
            .expect("custom wide dispatch");
        assert_eq!(
            &dpis[46..54],
            &commit[..],
            "custom leg publishes the 8-felt commitment"
        );

        let config = ir2_leaf_wrap_config();
        let proof = prove_vm_descriptor2_for_config(
            &desc,
            &trace,
            &dpis,
            &mb,
            &map_heaps,
            &UMemBoundaryWitness::default(),
            &config,
        )
        .expect("custom wide leg proves under the leaf-wrap config");

        let leg = RotatedParticipantLeg {
            proof,
            descriptor: desc,
            public_inputs: dpis,
            carrier_witness: None,
        };
        match bundle {
            Some(b) => leg.with_custom_witness(b),
            None => leg,
        }
    }

    fn plain_custom_turn(balance: i64, nonce: u64) -> FinalizedTurn {
        let commit = core::array::from_fn(|i| BabyBear::new((i + 1) as u32));
        let leg = mint_custom_leg(balance, nonce, commit, None);
        FinalizedTurn::new(DescriptorParticipant::rotated(leg))
    }

    #[test]
    #[ignore = "SLOW: real deployed custom-binding recursion fold (~minutes to tens of minutes)"]
    fn d1_turn_folds_and_lightclient_accepts() {
        let (prog, bundle) = d1_bundle();
        let real = custom_proof_pi_commitment(&prog.pis);
        let balance = 1000i64;
        let t0_leg = mint_custom_leg(balance, 0, real, Some(bundle));
        let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
        let t1 = plain_custom_turn(balance, 1);
        assert_eq!(
            t0.new_root(),
            t1.old_root(),
            "turn 0 post-state links to turn 1"
        );
        let turns = vec![t0, t1];

        let mut whole = prove_turn_chain_recursive(&turns)
            .expect("the honest D1-bearing chain must fold through the deployed prover");
        let vk = whole.root_vk_fingerprint();
        let attested = verify_history(&whole, &vk)
            .expect("the REAL light client must ACCEPT the honest D1 whole-chain artifact");
        assert_eq!(attested.num_turns, 2);
        eprintln!(
            "D1 ACCEPT: automaton-step CellProgram -> custom leaf -> fold(K=2) -> verify_history OK. \
             num_turns={}, final_root[0]={}",
            attested.num_turns, attested.final_root[0].0
        );
        // Non-vacuous bite: a relabeled final_root is REJECTED.
        let honest_final = whole.final_root;
        whole.final_root[0] = honest_final[0] + BabyBear::new(1);
        assert!(
            verify_history(&whole, &vk).is_err(),
            "a spliced final_root must be rejected"
        );
        whole.final_root = honest_final;
        verify_history(&whole, &vk).expect("restored honest artifact verifies again");
    }
}

mod build_helper {
    use dregg_circuit::field::BabyBear;
    pub struct Prog {
        pub pis: Vec<BabyBear>,
    }
}
