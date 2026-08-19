//! Adversarial evidence for the encrypted confidential-energy candidate lane.
//!
//! The test fixture is independently reconstructed from the public semantics
//! and the published 56-vs-60 schedule counterexample. It does not import or
//! copy a degg-research source file, fixture, vector, or constant table.

#![cfg(feature = "tfhe-integer")]

use fhegg_fhe::energy_dispatch::{
    decrypt_energy_diagnostics, encrypt_energy_bundle, evaluate_encrypted_energy_candidate,
    EnergyCandidate, EnergyPlaintextBundle, EnergyProvider, EnergyPublicDomain,
    GlobalOptimalityEvidence, ENERGY_FLOW_OFFSET, ENERGY_PERIODS, ENERGY_PROVIDERS,
};
use tfhe::{generate_keys, set_server_key, ConfigBuilder};

fn providers() -> [EnergyProvider; ENERGY_PROVIDERS] {
    [
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
    ]
}

fn domain() -> EnergyPublicDomain {
    EnergyPublicDomain {
        demand: [[4, 1], [3, 2], [4, 2]],
        reserve: [1, 1, 1],
        line_limit: [1, 1, 1],
    }
}

fn period_cost(provider: &EnergyProvider, quantity: u32) -> u32 {
    let first = quantity.min(provider.segment_width[0]);
    first * provider.marginal_cost[0] + (quantity - first) * provider.marginal_cost[1]
}

fn upward_capability(provider: &EnergyProvider, quantity: u32, period: usize) -> u32 {
    if provider.occupied == 0 || provider.available[period] == 0 {
        return 0;
    }
    let running = (provider.max_output - quantity).min(provider.ramp_up);
    if quantity > 0 || provider.min_output <= provider.ramp_up {
        running
    } else {
        0
    }
}

fn derived_candidate(
    providers: &[EnergyProvider; ENERGY_PROVIDERS],
    domain: &EnergyPublicDomain,
    generation: [[u32; ENERGY_PERIODS]; ENERGY_PROVIDERS],
) -> EnergyCandidate {
    let provider_credit = std::array::from_fn(|provider| {
        (0..ENERGY_PERIODS)
            .map(|period| period_cost(&providers[provider], generation[provider][period]))
            .sum()
    });
    let objective_cost = provider_credit.iter().sum();
    let flow_offset = std::array::from_fn(|period| {
        let bus_zero_generation: u32 = (0..ENERGY_PROVIDERS)
            .filter(|provider| providers[*provider].bus == 0)
            .map(|provider| generation[provider][period])
            .sum();
        bus_zero_generation + ENERGY_FLOW_OFFSET - domain.demand[period][0]
    });
    let upward_reserve = std::array::from_fn(|period| {
        (0..ENERGY_PROVIDERS)
            .map(|provider| {
                upward_capability(&providers[provider], generation[provider][period], period)
            })
            .sum()
    });
    EnergyCandidate {
        generation,
        flow_offset,
        upward_reserve,
        provider_credit,
        load_debit: objective_cost,
        objective_cost,
    }
}

fn trajectory_valid(provider: &EnergyProvider, generation: &[u32; ENERGY_PERIODS]) -> bool {
    for period in 0..ENERGY_PERIODS {
        let quantity = generation[period];
        if provider.available[period] == 0 {
            if quantity != 0 {
                return false;
            }
            continue;
        }
        if quantity != 0 && (quantity < provider.min_output || quantity > provider.max_output) {
            return false;
        }
        let (previous, enforce) = if period == 0 {
            (provider.initial_output, true)
        } else {
            (generation[period - 1], provider.available[period - 1] != 0)
        };
        if enforce
            && (quantity > previous + provider.ramp_up || previous > quantity + provider.ramp_down)
        {
            return false;
        }
    }
    true
}

fn physically_feasible(
    providers: &[EnergyProvider; ENERGY_PROVIDERS],
    domain: &EnergyPublicDomain,
    generation: &[[u32; ENERGY_PERIODS]; ENERGY_PROVIDERS],
) -> bool {
    if !(0..ENERGY_PROVIDERS)
        .all(|provider| trajectory_valid(&providers[provider], &generation[provider]))
    {
        return false;
    }
    for period in 0..ENERGY_PERIODS {
        let total: u32 = generation.iter().map(|row| row[period]).sum();
        if total != domain.demand[period].iter().sum::<u32>() {
            return false;
        }
        let bus_zero: u32 = (0..ENERGY_PROVIDERS)
            .filter(|provider| providers[*provider].bus == 0)
            .map(|provider| generation[provider][period])
            .sum();
        if bus_zero.abs_diff(domain.demand[period][0]) > domain.line_limit[period] {
            return false;
        }
        let reserve: u32 = (0..ENERGY_PROVIDERS)
            .map(|provider| {
                upward_capability(&providers[provider], generation[provider][period], period)
            })
            .sum();
        if reserve < domain.reserve[period] {
            return false;
        }
    }
    true
}

fn exhaustive_optimum(
    providers: &[EnergyProvider; ENERGY_PROVIDERS],
    domain: &EnergyPublicDomain,
) -> ([[u32; ENERGY_PERIODS]; ENERGY_PROVIDERS], u32, u64) {
    let mut best = None;
    let mut feasible = 0u64;
    for packed in 0u32..5u32.pow(9) {
        let mut cursor = packed;
        let mut generation = [[0u32; ENERGY_PERIODS]; ENERGY_PROVIDERS];
        for row in &mut generation {
            for quantity in row {
                *quantity = cursor % 5;
                cursor /= 5;
            }
        }
        if !physically_feasible(providers, domain, &generation) {
            continue;
        }
        feasible += 1;
        let cost: u32 = (0..ENERGY_PROVIDERS)
            .flat_map(|provider| {
                (0..ENERGY_PERIODS).map(move |period| {
                    period_cost(&providers[provider], generation[provider][period])
                })
            })
            .sum();
        let replace = best.as_ref().is_none_or(|(best_generation, best_cost)| {
            cost < *best_cost || (cost == *best_cost && generation > *best_generation)
        });
        if replace {
            best = Some((generation, cost));
        }
    }
    let (generation, cost) = best.expect("reconstructed instance is feasible");
    (generation, cost, feasible)
}

fn evaluate(
    providers: [EnergyProvider; ENERGY_PROVIDERS],
    domain: &EnergyPublicDomain,
    candidate: EnergyCandidate,
    client: &tfhe::ClientKey,
) -> (
    fhegg_fhe::energy_dispatch::EnergyEvaluationDiagnostics,
    fhegg_fhe::energy_dispatch::EnergyEncryptionTiming,
    fhegg_fhe::energy_dispatch::EnergyEvaluationTiming,
) {
    let (encrypted, encryption) = encrypt_energy_bundle(
        &EnergyPlaintextBundle {
            providers,
            candidate,
        },
        client,
    );
    let evaluation = evaluate_encrypted_energy_candidate(domain, &encrypted).expect("valid domain");
    let timing = evaluation.timing;
    let diagnostics = decrypt_energy_diagnostics(&evaluation, client);
    (diagnostics, encryption, timing)
}

#[test]
fn tfhe_validates_feasibility_and_settlement_but_not_global_optimality() {
    let providers = providers();
    let domain = domain();
    let canonical_generation = [[2, 2, 2], [1, 3, 2], [2, 0, 2]];
    let suboptimal_generation = [[1, 2, 1], [2, 3, 3], [2, 0, 2]];

    let (optimum_generation, optimum_cost, feasible_count) =
        exhaustive_optimum(&providers, &domain);
    assert_eq!(optimum_generation, canonical_generation);
    assert_eq!(optimum_cost, 56);
    assert_eq!(feasible_count, 4);

    let config = ConfigBuilder::default().build();
    let (client, server) = generate_keys(config);
    set_server_key(server);

    let canonical = derived_candidate(&providers, &domain, canonical_generation);
    assert_eq!(canonical.provider_credit, [18, 30, 8]);
    assert_eq!(canonical.objective_cost, 56);
    assert_eq!(canonical.flow_offset, [12, 11, 12]);
    assert_eq!(canonical.upward_reserve, [2, 1, 2]);
    let (canonical_result, canonical_encryption, canonical_evaluation) =
        evaluate(providers, &domain, canonical, &client);
    assert!(canonical_result.physical_feasibility);
    assert!(canonical_result.settlement_conserves);
    assert!(canonical_result.valid_candidate_only);
    assert_eq!(canonical_result.derived_objective, 56);
    assert_eq!(
        canonical_result.global_optimality,
        GlobalOptimalityEvidence::NotEvaluated
    );

    let suboptimal = derived_candidate(&providers, &domain, suboptimal_generation);
    assert_eq!(suboptimal.objective_cost, 60);
    assert!(physically_feasible(
        &providers,
        &domain,
        &suboptimal.generation
    ));
    let (suboptimal_result, suboptimal_encryption, suboptimal_evaluation) =
        evaluate(providers, &domain, suboptimal, &client);
    assert!(suboptimal_result.physical_feasibility);
    assert!(suboptimal_result.settlement_conserves);
    assert!(suboptimal_result.valid_candidate_only);
    assert_eq!(suboptimal_result.derived_objective, 60);
    assert_eq!(
        suboptimal_result.global_optimality,
        GlobalOptimalityEvidence::NotEvaluated
    );
    assert_ne!(suboptimal_result.derived_objective, optimum_cost);

    let mut forged_settlement = suboptimal;
    forged_settlement.provider_credit[1] -= 1;
    forged_settlement.load_debit -= 1;
    forged_settlement.objective_cost -= 1;
    let (forged_result, forged_encryption, forged_evaluation) =
        evaluate(providers, &domain, forged_settlement, &client);
    assert!(forged_result.physical_feasibility);
    assert!(!forged_result.settlement_conserves);
    assert!(!forged_result.valid_candidate_only);
    assert_eq!(forged_result.derived_objective, 60);

    println!(
        "ENERGY_TFHE_MEASUREMENT {}",
        serde_json::json!({
            "relation": fhegg_fhe::energy_dispatch::ENERGY_RELATION_ID,
            "independently_reconstructed_feasible_schedules": feasible_count,
            "canonical_objective": optimum_cost,
            "suboptimal_objective": suboptimal_result.derived_objective,
            "global_optimality": "NOT_EVALUATED",
            "canonical": {
                "encrypt_ms": canonical_encryption.elapsed.as_millis(),
                "evaluate_ms": canonical_evaluation.total.as_millis(),
            },
            "suboptimal": {
                "encrypt_ms": suboptimal_encryption.elapsed.as_millis(),
                "evaluate_ms": suboptimal_evaluation.total.as_millis(),
            },
            "forged_settlement": {
                "encrypt_ms": forged_encryption.elapsed.as_millis(),
                "evaluate_ms": forged_evaluation.total.as_millis(),
                "settlement_conserves": forged_result.settlement_conserves,
            },
            "trust_boundary": "one-process measurement; evaluator API has server key only; no custody, admission binding, vFHE, selective delivery, or optimality proof"
        })
    );
}

#[test]
fn public_domain_refuses_before_encrypted_work() {
    let mut invalid = domain();
    invalid.demand[0] = [12, 1];
    assert!(invalid.validate().is_err());
}
