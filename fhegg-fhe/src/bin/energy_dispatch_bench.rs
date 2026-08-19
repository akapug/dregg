//! Release benchmark for the bounded encrypted energy candidate validator.

use fhegg_fhe::energy_dispatch::{
    decrypt_energy_diagnostics, encrypt_energy_bundle, evaluate_encrypted_energy_candidate,
    EnergyCandidate, EnergyPlaintextBundle, EnergyProvider, EnergyPublicDomain,
};
use tfhe::{generate_keys, set_server_key, ConfigBuilder};

fn main() {
    let providers = [
        EnergyProvider {
            occupied: 1,
            bus: 0,
            min_output: 1,
            max_output: 2,
            ramp_up: 1,
            ramp_down: 1,
            initial_output: 2,
            available: [1, 1, 1],
            segment_width: [1, 1],
            marginal_cost: [2, 4],
        },
        EnergyProvider {
            occupied: 1,
            bus: 1,
            min_output: 1,
            max_output: 4,
            ramp_up: 2,
            ramp_down: 1,
            initial_output: 2,
            available: [1, 1, 1],
            segment_width: [1, 3],
            marginal_cost: [4, 6],
        },
        EnergyProvider {
            occupied: 1,
            bus: 0,
            min_output: 2,
            max_output: 2,
            ramp_up: 2,
            ramp_down: 2,
            initial_output: 2,
            available: [1, 0, 1],
            segment_width: [2, 0],
            marginal_cost: [2, 2],
        },
    ];
    let domain = EnergyPublicDomain {
        demand: [[4, 1], [3, 2], [4, 2]],
        reserve: [1, 1, 1],
        line_limit: [1, 1, 1],
    };
    let candidate = EnergyCandidate {
        generation: [[2, 2, 2], [1, 3, 2], [2, 0, 2]],
        flow_offset: [12, 11, 12],
        upward_reserve: [2, 1, 2],
        provider_credit: [18, 30, 8],
        load_debit: 56,
        objective_cost: 56,
    };

    let keygen_started = std::time::Instant::now();
    let (client, server) = generate_keys(ConfigBuilder::default().build());
    let keygen = keygen_started.elapsed();
    set_server_key(server);
    let (encrypted, encryption) = encrypt_energy_bundle(
        &EnergyPlaintextBundle {
            providers,
            candidate,
        },
        &client,
    );
    let evaluation =
        evaluate_encrypted_energy_candidate(&domain, &encrypted).expect("valid public domain");
    let diagnostics = decrypt_energy_diagnostics(&evaluation, &client);
    assert!(diagnostics.physical_feasibility);
    assert!(diagnostics.settlement_conserves);
    assert_eq!(diagnostics.derived_objective, 56);

    println!(
        "{}",
        serde_json::json!({
            "relation": fhegg_fhe::energy_dispatch::ENERGY_RELATION_ID,
            "backend": "tfhe-rs-1.6.3-exact-integer-cpu",
            "keygen_ms": keygen.as_millis(),
            "ciphertexts": encryption.ciphertexts,
            "encrypt_ms": encryption.elapsed.as_millis(),
            "evaluate": {
                "witness_checks_ms": evaluation.timing.witness_checks.as_millis(),
                "trajectory_and_cost_ms": evaluation.timing.trajectory_and_cost.as_millis(),
                "system_checks_ms": evaluation.timing.system_checks.as_millis(),
                "settlement_checks_ms": evaluation.timing.settlement_checks.as_millis(),
                "total_ms": evaluation.timing.total.as_millis(),
            },
            "decrypted_diagnostics": {
                "witness_well_formed": diagnostics.witness_well_formed,
                "trajectories_valid": diagnostics.trajectories_valid,
                "demand_satisfied": diagnostics.demand_satisfied,
                "line_satisfied": diagnostics.line_satisfied,
                "reserve_satisfied": diagnostics.reserve_satisfied,
                "physical_feasibility": diagnostics.physical_feasibility,
                "settlement_conserves": diagnostics.settlement_conserves,
                "valid_candidate_only": diagnostics.valid_candidate_only,
                "derived_objective": diagnostics.derived_objective,
            },
            "global_optimality": "NOT_EVALUATED",
            "claim_boundary": "candidate feasibility and exact settlement only; no encrypted search, vFHE, threshold custody, admission binding, or selective output delivery"
        })
    );
}
