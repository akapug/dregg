//! Encrypted candidate validation for a bounded confidential-energy dispatch.
//!
//! This module is an independent implementation experiment for the published
//! relation identifier `confidential-energy-dispatch/p3-t3-b2-q4/v0`.  It was
//! re-specified from that relation's prose at degg-research commit `08a0fc3`;
//! no source file, fixture, vector, or constant table is imported from or
//! copied out of that repository.
//!
//! The experiment deliberately separates three predicates:
//!
//! 1. `EncryptedEnergyEvaluation::physical_feasibility` checks encrypted
//!    witness shape, candidate trajectories, nodal balance, line capacity, and
//!    reserve capability.
//! 2. `EncryptedEnergyEvaluation::settlement_conserves` checks that encrypted
//!    provider credits equal recomputed encrypted piecewise production costs,
//!    and that their sum equals the encrypted debit and objective claim.
//! 3. `EncryptedEnergyEvaluation::global_optimality` is always
//!    `GlobalOptimalityEvidence::NotEvaluated`. Candidate validation does not
//!    compare against another feasible schedule and therefore cannot establish
//!    the relation's canonical minimum and tie rule.
//!
//! All private numerical inputs, the proposed generation trajectory, and the
//! proposed settlement remain TFHE ciphertexts throughout evaluation.  The
//! evaluator API receives no [`tfhe::ClientKey`].  That API separation is not a
//! distributed custody result: the benchmark runs key generation, encryption,
//! evaluation, and decryption in one process, and tfhe-rs uses an installed
//! process-local server key.  FHE provides input confidentiality against a
//! server holding only that evaluation key; it does not prove that the server
//! evaluated this function, bind ciphertexts to an admitted input commitment,
//! provide threshold/selective output release, hide traffic or timing, or
//! establish global optimality.

use std::time::{Duration, Instant};

use tfhe::prelude::*;
use tfhe::{ClientKey, FheBool, FheUint32};

/// The exact relation identifier whose bounded arithmetic is re-specified.
pub const ENERGY_RELATION_ID: &str = "confidential-energy-dispatch/p3-t3-b2-q4/v0";
/// Number of canonical provider slots.
pub const ENERGY_PROVIDERS: usize = 3;
/// Number of planning periods.
pub const ENERGY_PERIODS: usize = 3;
/// Number of buses in the lossless one-line model.
pub const ENERGY_BUSES: usize = 2;
/// Number of sequential marginal-cost segments per provider.
pub const ENERGY_SEGMENTS: usize = 2;
/// Maximum provider output in exact energy atoms.
pub const ENERGY_MAX_OUTPUT: u32 = 4;
/// Maximum private marginal cost in quote atoms per energy atom.
pub const ENERGY_MAX_MARGINAL_COST: u32 = 1_000_000;
/// Maximum aggregate output at the frozen provider/output dimensions.
pub const ENERGY_MAX_SYSTEM_OUTPUT: u32 = 12;
/// Offset used to encode the signed bus-0 line flow into an unsigned field.
pub const ENERGY_FLOW_OFFSET: u32 = ENERGY_MAX_SYSTEM_OUTPUT;

/// Public demand, reserve, and line policy for one bounded evaluation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EnergyPublicDomain {
    /// Exact demand indexed by period, then bus.
    pub demand: [[u32; ENERGY_BUSES]; ENERGY_PERIODS],
    /// Required system-wide upward capability in each period.
    pub reserve: [u32; ENERGY_PERIODS],
    /// Absolute capacity of the one lossless line in each period.
    pub line_limit: [u32; ENERGY_PERIODS],
}

/// A malformed public-domain field. Public validation happens before FHE work.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EnergyDomainError {
    /// Aggregate demand exceeds the frozen three-provider capacity.
    DemandOutOfRange { period: usize },
    /// Reserve exceeds the frozen three-provider capacity.
    ReserveOutOfRange { period: usize },
    /// Line capacity exceeds the frozen three-provider capacity.
    LineLimitOutOfRange { period: usize },
}

impl std::fmt::Display for EnergyDomainError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DemandOutOfRange { period } => {
                write!(formatter, "period {period} demand is outside 0..=12")
            }
            Self::ReserveOutOfRange { period } => {
                write!(formatter, "period {period} reserve is outside 0..=12")
            }
            Self::LineLimitOutOfRange { period } => {
                write!(formatter, "period {period} line limit is outside 0..=12")
            }
        }
    }
}

impl std::error::Error for EnergyDomainError {}

impl EnergyPublicDomain {
    /// Validate every clear public field before starting encrypted evaluation.
    ///
    /// # Errors
    ///
    /// Returns the first period whose demand, reserve, or line limit exceeds
    /// the frozen bounded domain.
    pub fn validate(&self) -> Result<(), EnergyDomainError> {
        for period in 0..ENERGY_PERIODS {
            let demand = self.demand[period][0]
                .checked_add(self.demand[period][1])
                .ok_or(EnergyDomainError::DemandOutOfRange { period })?;
            if self.demand[period]
                .iter()
                .any(|value| *value > ENERGY_MAX_SYSTEM_OUTPUT)
                || demand > ENERGY_MAX_SYSTEM_OUTPUT
            {
                return Err(EnergyDomainError::DemandOutOfRange { period });
            }
            if self.reserve[period] > ENERGY_MAX_SYSTEM_OUTPUT {
                return Err(EnergyDomainError::ReserveOutOfRange { period });
            }
            if self.line_limit[period] > ENERGY_MAX_SYSTEM_OUTPUT {
                return Err(EnergyDomainError::LineLimitOutOfRange { period });
            }
        }
        Ok(())
    }
}

/// One plaintext provider record before client-side encryption.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EnergyProvider {
    /// Canonical occupancy bit (`0` or `1`).
    pub occupied: u32,
    /// Private bus (`0` or `1`).
    pub bus: u32,
    /// Minimum nonzero generation; zero generation remains off.
    pub min_output: u32,
    /// Maximum generation.
    pub max_output: u32,
    /// Maximum upward movement at an ordinary availability boundary.
    pub ramp_up: u32,
    /// Maximum downward movement at an ordinary availability boundary.
    pub ramp_down: u32,
    /// Generation immediately before the horizon.
    pub initial_output: u32,
    /// Forced-availability bits by period.
    pub available: [u32; ENERGY_PERIODS],
    /// Widths of two sequential cost segments.
    pub segment_width: [u32; ENERGY_SEGMENTS],
    /// Nondecreasing private marginal costs.
    pub marginal_cost: [u32; ENERGY_SEGMENTS],
}

/// A proposed private plan and its proposed exact settlement.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EnergyCandidate {
    /// Provider-major generation trajectory.
    pub generation: [[u32; ENERGY_PERIODS]; ENERGY_PROVIDERS],
    /// Claimed signed line flow encoded as `flow + ENERGY_FLOW_OFFSET`.
    pub flow_offset: [u32; ENERGY_PERIODS],
    /// Claimed system upward capability.
    pub upward_reserve: [u32; ENERGY_PERIODS],
    /// Claimed pay-as-modeled-cost credit for each provider.
    pub provider_credit: [u32; ENERGY_PROVIDERS],
    /// Claimed load-side debit.
    pub load_debit: u32,
    /// Claimed total modeled production cost.
    pub objective_cost: u32,
}

/// The complete fixed-size plaintext client input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EnergyPlaintextBundle {
    /// Three occupied or canonically zero-padded provider slots.
    pub providers: [EnergyProvider; ENERGY_PROVIDERS],
    /// Proposed trajectory and settlement.
    pub candidate: EnergyCandidate,
}

#[derive(Clone)]
struct EncryptedEnergyProvider {
    occupied: FheUint32,
    bus: FheUint32,
    min_output: FheUint32,
    max_output: FheUint32,
    ramp_up: FheUint32,
    ramp_down: FheUint32,
    initial_output: FheUint32,
    available: [FheUint32; ENERGY_PERIODS],
    segment_width: [FheUint32; ENERGY_SEGMENTS],
    marginal_cost: [FheUint32; ENERGY_SEGMENTS],
}

#[derive(Clone)]
struct EncryptedEnergyCandidate {
    generation: [[FheUint32; ENERGY_PERIODS]; ENERGY_PROVIDERS],
    flow_offset: [FheUint32; ENERGY_PERIODS],
    upward_reserve: [FheUint32; ENERGY_PERIODS],
    provider_credit: [FheUint32; ENERGY_PROVIDERS],
    load_debit: FheUint32,
    objective_cost: FheUint32,
}

/// Fixed-shape TFHE ciphertext bundle accepted by the evaluator.
///
/// Fields are private so callers cannot accidentally construct a partially
/// encrypted bundle. Use [`encrypt_energy_bundle`] at the client boundary.
pub struct EncryptedEnergyBundle {
    providers: [EncryptedEnergyProvider; ENERGY_PROVIDERS],
    candidate: EncryptedEnergyCandidate,
    zero: FheUint32,
}

/// Client-side encryption measurement.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EnergyEncryptionTiming {
    /// Exactly 63 encrypted 32-bit integer fields, including one retained zero.
    pub ciphertexts: usize,
    /// Wall time for all client-side encryptions.
    pub elapsed: Duration,
}

/// Evaluator-side wall-clock decomposition.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EnergyEvaluationTiming {
    /// Encrypted provider-shape validation.
    pub witness_checks: Duration,
    /// Encrypted trajectory constraints and piecewise production cost.
    pub trajectory_and_cost: Duration,
    /// Encrypted balance, line, reserve, and claimed-derived-field checks.
    pub system_checks: Duration,
    /// Encrypted credit/debit/objective equality and final conjunction.
    pub settlement_checks: Duration,
    /// Whole evaluator call.
    pub total: Duration,
}

/// The exact status of the global-optimality predicate in this experiment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GlobalOptimalityEvidence {
    /// No encrypted search, primal/dual certificate, branch-and-bound log, or
    /// proof compares this candidate with all admissible alternatives.
    NotEvaluated,
}

/// Ciphertext outputs from one candidate evaluation.
///
/// Detailed fields are for local experiment diagnostics. A public protocol
/// should decrypt only its separately frozen leakage projection.
pub struct EncryptedEnergyEvaluation {
    /// All encrypted provider fields form occupied records or canonical zero padding.
    pub witness_well_formed: FheBool,
    /// Trajectories satisfy output/ramp/outage rules and exact production costs were derived.
    pub trajectories_valid: FheBool,
    /// Generation exactly serves public demand.
    pub demand_satisfied: FheBool,
    /// Derived and claimed flow agree and obey public line limits.
    pub line_satisfied: FheBool,
    /// Derived and claimed reserve agree and meet public requirements.
    pub reserve_satisfied: FheBool,
    /// Conjunction of witness, trajectory, demand, line, and reserve predicates.
    pub physical_feasibility: FheBool,
    /// Exact credits equal derived costs and sum to the debit/objective claim.
    pub settlement_conserves: FheBool,
    /// Feasibility and settlement, deliberately without an optimality claim.
    pub valid_candidate_only: FheBool,
    /// Encrypted recomputed production cost; not part of the proposed public leakage.
    pub derived_objective: FheUint32,
    /// Explicitly absent global-optimality evidence.
    pub global_optimality: GlobalOptimalityEvidence,
    /// Measured evaluator timings.
    pub timing: EnergyEvaluationTiming,
}

/// Decrypted local diagnostics for tests and benchmarking.
///
/// A production public surface must not automatically expose this structure:
/// per-predicate failures and the exact objective can leak private information.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EnergyEvaluationDiagnostics {
    /// Decrypted witness-shape result.
    pub witness_well_formed: bool,
    /// Decrypted trajectory result.
    pub trajectories_valid: bool,
    /// Decrypted demand result.
    pub demand_satisfied: bool,
    /// Decrypted line result.
    pub line_satisfied: bool,
    /// Decrypted reserve result.
    pub reserve_satisfied: bool,
    /// Decrypted physical-feasibility conjunction.
    pub physical_feasibility: bool,
    /// Decrypted exact-settlement conjunction.
    pub settlement_conserves: bool,
    /// Decrypted candidate-only acceptance.
    pub valid_candidate_only: bool,
    /// Decrypted recomputed objective, exposed only to this diagnostic API.
    pub derived_objective: u32,
    /// Always `NotEvaluated` in this backend.
    pub global_optimality: GlobalOptimalityEvidence,
}

fn encrypt_provider(provider: &EnergyProvider, key: &ClientKey) -> EncryptedEnergyProvider {
    EncryptedEnergyProvider {
        occupied: FheUint32::encrypt(provider.occupied, key),
        bus: FheUint32::encrypt(provider.bus, key),
        min_output: FheUint32::encrypt(provider.min_output, key),
        max_output: FheUint32::encrypt(provider.max_output, key),
        ramp_up: FheUint32::encrypt(provider.ramp_up, key),
        ramp_down: FheUint32::encrypt(provider.ramp_down, key),
        initial_output: FheUint32::encrypt(provider.initial_output, key),
        available: std::array::from_fn(|period| {
            FheUint32::encrypt(provider.available[period], key)
        }),
        segment_width: std::array::from_fn(|segment| {
            FheUint32::encrypt(provider.segment_width[segment], key)
        }),
        marginal_cost: std::array::from_fn(|segment| {
            FheUint32::encrypt(provider.marginal_cost[segment], key)
        }),
    }
}

/// Encrypt every private field at the client boundary.
#[must_use]
pub fn encrypt_energy_bundle(
    clear: &EnergyPlaintextBundle,
    key: &ClientKey,
) -> (EncryptedEnergyBundle, EnergyEncryptionTiming) {
    let started = Instant::now();
    let providers =
        std::array::from_fn(|provider| encrypt_provider(&clear.providers[provider], key));
    let candidate = EncryptedEnergyCandidate {
        generation: std::array::from_fn(|provider| {
            std::array::from_fn(|period| {
                FheUint32::encrypt(clear.candidate.generation[provider][period], key)
            })
        }),
        flow_offset: std::array::from_fn(|period| {
            FheUint32::encrypt(clear.candidate.flow_offset[period], key)
        }),
        upward_reserve: std::array::from_fn(|period| {
            FheUint32::encrypt(clear.candidate.upward_reserve[period], key)
        }),
        provider_credit: std::array::from_fn(|provider| {
            FheUint32::encrypt(clear.candidate.provider_credit[provider], key)
        }),
        load_debit: FheUint32::encrypt(clear.candidate.load_debit, key),
        objective_cost: FheUint32::encrypt(clear.candidate.objective_cost, key),
    };
    let zero = FheUint32::encrypt(0u32, key);
    (
        EncryptedEnergyBundle {
            providers,
            candidate,
            zero,
        },
        EnergyEncryptionTiming {
            ciphertexts: 63,
            elapsed: started.elapsed(),
        },
    )
}

fn and_all(predicates: Vec<FheBool>) -> FheBool {
    predicates
        .into_iter()
        .reduce(|left, right| &left & &right)
        .expect("every fixed relation predicate set is nonempty")
}

fn or(left: &FheBool, right: &FheBool) -> FheBool {
    left | right
}

fn min_encrypted(left: &FheUint32, right: &FheUint32) -> FheUint32 {
    left.le(right).if_then_else(left, right)
}

fn provider_shape(provider: &EncryptedEnergyProvider) -> FheBool {
    let occupied_is_bit = provider.occupied.le(1u32);
    let occupied = provider.occupied.eq(1u32);

    let mut padding_fields = vec![
        provider.bus.eq(0u32),
        provider.min_output.eq(0u32),
        provider.max_output.eq(0u32),
        provider.ramp_up.eq(0u32),
        provider.ramp_down.eq(0u32),
        provider.initial_output.eq(0u32),
    ];
    padding_fields.extend(provider.available.iter().map(|value| value.eq(0u32)));
    padding_fields.extend(provider.segment_width.iter().map(|value| value.eq(0u32)));
    padding_fields.extend(provider.marginal_cost.iter().map(|value| value.eq(0u32)));
    let canonical_padding = and_all(padding_fields);

    let initial_zero_or_at_least_min = or(
        &provider.initial_output.eq(0u32),
        &provider.initial_output.ge(&provider.min_output),
    );
    let width_sum = &provider.segment_width[0] + &provider.segment_width[1];
    let mut occupied_fields = vec![
        provider.bus.lt(ENERGY_BUSES as u32),
        provider.max_output.ge(1u32),
        provider.max_output.le(ENERGY_MAX_OUTPUT),
        provider.min_output.le(&provider.max_output),
        provider.initial_output.le(&provider.max_output),
        initial_zero_or_at_least_min,
        provider.ramp_up.le(ENERGY_MAX_OUTPUT),
        provider.ramp_down.le(ENERGY_MAX_OUTPUT),
        provider.segment_width[0].le(ENERGY_MAX_OUTPUT),
        provider.segment_width[1].le(ENERGY_MAX_OUTPUT),
        width_sum.eq(&provider.max_output),
        provider.marginal_cost[0].le(&provider.marginal_cost[1]),
        provider.marginal_cost[0].le(ENERGY_MAX_MARGINAL_COST),
        provider.marginal_cost[1].le(ENERGY_MAX_MARGINAL_COST),
    ];
    occupied_fields.extend(provider.available.iter().map(|value| value.le(1u32)));
    let occupied_shape = and_all(occupied_fields);
    let selected_shape = occupied.if_then_else(&occupied_shape, &canonical_padding);
    &occupied_is_bit & &selected_shape
}

fn period_trajectory(
    provider: &EncryptedEnergyProvider,
    generation: &FheUint32,
    period: usize,
) -> FheBool {
    let occupied = provider.occupied.eq(1u32);
    let available = provider.available[period].eq(1u32);
    let active = &occupied & &available;
    let zero = generation.eq(0u32);
    let bounded_nonzero = and_all(vec![
        generation.ge(&provider.min_output),
        generation.le(&provider.max_output),
    ]);
    let online_value = or(&zero, &bounded_nonzero);
    active.if_then_else(&online_value, &zero)
}

fn ramp_boundary(
    provider: &EncryptedEnergyProvider,
    previous: &FheUint32,
    current: &FheUint32,
    previous_available: Option<&FheUint32>,
    current_available: &FheUint32,
) -> FheBool {
    let occupied = provider.occupied.eq(1u32);
    let current_is_available = current_available.eq(1u32);
    let enforce = if let Some(previous_available) = previous_available {
        let previous_is_available = previous_available.eq(1u32);
        &(&occupied & &previous_is_available) & &current_is_available
    } else {
        &occupied & &current_is_available
    };
    let upward_ceiling = previous + &provider.ramp_up;
    let downward_ceiling = current + &provider.ramp_down;
    let ramp_holds = &current.le(&upward_ceiling) & &previous.le(&downward_ceiling);
    let true_ciphertext = current.eq(current);
    enforce.if_then_else(&ramp_holds, &true_ciphertext)
}

fn provider_period_cost(provider: &EncryptedEnergyProvider, generation: &FheUint32) -> FheUint32 {
    let first_quantity = min_encrypted(generation, &provider.segment_width[0]);
    let second_quantity = generation - &first_quantity;
    let first_cost = &first_quantity * &provider.marginal_cost[0];
    let second_cost = &second_quantity * &provider.marginal_cost[1];
    &first_cost + &second_cost
}

fn upward_capability(
    provider: &EncryptedEnergyProvider,
    generation: &FheUint32,
    period: usize,
    zero: &FheUint32,
) -> FheUint32 {
    let raw_headroom = &provider.max_output - generation;
    let headroom = provider
        .max_output
        .ge(generation)
        .if_then_else(&raw_headroom, zero);
    let running_capability = min_encrypted(&headroom, &provider.ramp_up);
    let off_can_start = provider.min_output.le(&provider.ramp_up);
    let off_capability = off_can_start.if_then_else(&running_capability, zero);
    let capability = generation
        .gt(0u32)
        .if_then_else(&running_capability, &off_capability);
    let active = &provider.occupied.eq(1u32) & &provider.available[period].eq(1u32);
    active.if_then_else(&capability, zero)
}

/// Evaluate encrypted witness validity, physical feasibility, and exact
/// settlement consistency without decrypting an intermediate value.
///
/// # Errors
///
/// Refuses a malformed clear public domain before starting FHE evaluation.
pub fn evaluate_encrypted_energy_candidate(
    domain: &EnergyPublicDomain,
    bundle: &EncryptedEnergyBundle,
) -> Result<EncryptedEnergyEvaluation, EnergyDomainError> {
    domain.validate()?;
    let total_started = Instant::now();

    let started = Instant::now();
    let witness_well_formed = and_all(
        bundle
            .providers
            .iter()
            .map(provider_shape)
            .collect::<Vec<_>>(),
    );
    let witness_checks = started.elapsed();

    let started = Instant::now();
    let mut trajectory_predicates = Vec::new();
    let mut provider_costs = Vec::with_capacity(ENERGY_PROVIDERS);
    for provider_index in 0..ENERGY_PROVIDERS {
        let provider = &bundle.providers[provider_index];
        let generation = &bundle.candidate.generation[provider_index];
        for period in 0..ENERGY_PERIODS {
            trajectory_predicates.push(period_trajectory(provider, &generation[period], period));
            let (previous, previous_available) = if period == 0 {
                (&provider.initial_output, None)
            } else {
                (
                    &generation[period - 1],
                    Some(&provider.available[period - 1]),
                )
            };
            trajectory_predicates.push(ramp_boundary(
                provider,
                previous,
                &generation[period],
                previous_available,
                &provider.available[period],
            ));
        }
        let period_costs = generation
            .iter()
            .map(|quantity| provider_period_cost(provider, quantity))
            .collect::<Vec<_>>();
        let period_cost_refs = period_costs.iter().collect::<Vec<_>>();
        provider_costs.push(FheUint32::sum(&period_cost_refs));
    }
    let trajectories_valid = and_all(trajectory_predicates);
    let provider_cost_refs = provider_costs.iter().collect::<Vec<_>>();
    let derived_objective = FheUint32::sum(&provider_cost_refs);
    let trajectory_and_cost = started.elapsed();

    let started = Instant::now();
    let mut demand_predicates = Vec::new();
    let mut line_predicates = Vec::new();
    let mut reserve_predicates = Vec::new();
    for period in 0..ENERGY_PERIODS {
        let generation_column = (0..ENERGY_PROVIDERS)
            .map(|provider| &bundle.candidate.generation[provider][period])
            .collect::<Vec<_>>();
        let total_generation = FheUint32::sum(&generation_column);
        let demand = domain.demand[period][0] + domain.demand[period][1];
        demand_predicates.push(total_generation.eq(demand));

        let bus_zero_generation = (0..ENERGY_PROVIDERS)
            .map(|provider| {
                bundle.providers[provider]
                    .bus
                    .eq(0u32)
                    .if_then_else(&bundle.candidate.generation[provider][period], &bundle.zero)
            })
            .collect::<Vec<_>>();
        let bus_zero_refs = bus_zero_generation.iter().collect::<Vec<_>>();
        let bus_zero_total = FheUint32::sum(&bus_zero_refs);
        let derived_flow_offset = &bus_zero_total + ENERGY_FLOW_OFFSET - domain.demand[period][0];
        let line_floor = ENERGY_FLOW_OFFSET - domain.line_limit[period];
        let line_ceiling = ENERGY_FLOW_OFFSET + domain.line_limit[period];
        line_predicates.push(and_all(vec![
            derived_flow_offset.ge(line_floor),
            derived_flow_offset.le(line_ceiling),
            derived_flow_offset.eq(&bundle.candidate.flow_offset[period]),
        ]));

        let capabilities = (0..ENERGY_PROVIDERS)
            .map(|provider| {
                upward_capability(
                    &bundle.providers[provider],
                    &bundle.candidate.generation[provider][period],
                    period,
                    &bundle.zero,
                )
            })
            .collect::<Vec<_>>();
        let capability_refs = capabilities.iter().collect::<Vec<_>>();
        let derived_reserve = FheUint32::sum(&capability_refs);
        reserve_predicates.push(and_all(vec![
            derived_reserve.ge(domain.reserve[period]),
            derived_reserve.eq(&bundle.candidate.upward_reserve[period]),
        ]));
    }
    let demand_satisfied = and_all(demand_predicates);
    let line_satisfied = and_all(line_predicates);
    let reserve_satisfied = and_all(reserve_predicates);
    let system_checks = started.elapsed();

    let started = Instant::now();
    let credit_matches = and_all(
        provider_costs
            .iter()
            .zip(bundle.candidate.provider_credit.iter())
            .map(|(derived, claimed)| derived.eq(claimed))
            .collect::<Vec<_>>(),
    );
    let claimed_credit_refs = bundle.candidate.provider_credit.iter().collect::<Vec<_>>();
    let credit_sum = FheUint32::sum(&claimed_credit_refs);
    let settlement_conserves = and_all(vec![
        credit_matches,
        credit_sum.eq(&bundle.candidate.load_debit),
        credit_sum.eq(&bundle.candidate.objective_cost),
        derived_objective.eq(&bundle.candidate.objective_cost),
    ]);
    let physical_feasibility = and_all(vec![
        witness_well_formed.clone(),
        trajectories_valid.clone(),
        demand_satisfied.clone(),
        line_satisfied.clone(),
        reserve_satisfied.clone(),
    ]);
    let valid_candidate_only = &physical_feasibility & &settlement_conserves;
    let settlement_checks = started.elapsed();

    Ok(EncryptedEnergyEvaluation {
        witness_well_formed,
        trajectories_valid,
        demand_satisfied,
        line_satisfied,
        reserve_satisfied,
        physical_feasibility,
        settlement_conserves,
        valid_candidate_only,
        derived_objective,
        global_optimality: GlobalOptimalityEvidence::NotEvaluated,
        timing: EnergyEvaluationTiming {
            witness_checks,
            trajectory_and_cost,
            system_checks,
            settlement_checks,
            total: total_started.elapsed(),
        },
    })
}

/// Decrypt detailed local diagnostics after an evaluation.
///
/// This is intentionally a client-key API and therefore outside the evaluator
/// boundary. It is suitable for tests and measurements, not the default public
/// leakage projection.
#[must_use]
pub fn decrypt_energy_diagnostics(
    evaluation: &EncryptedEnergyEvaluation,
    key: &ClientKey,
) -> EnergyEvaluationDiagnostics {
    EnergyEvaluationDiagnostics {
        witness_well_formed: evaluation.witness_well_formed.decrypt(key),
        trajectories_valid: evaluation.trajectories_valid.decrypt(key),
        demand_satisfied: evaluation.demand_satisfied.decrypt(key),
        line_satisfied: evaluation.line_satisfied.decrypt(key),
        reserve_satisfied: evaluation.reserve_satisfied.decrypt(key),
        physical_feasibility: evaluation.physical_feasibility.decrypt(key),
        settlement_conserves: evaluation.settlement_conserves.decrypt(key),
        valid_candidate_only: evaluation.valid_candidate_only.decrypt(key),
        derived_objective: evaluation.derived_objective.decrypt(key),
        global_optimality: evaluation.global_optimality,
    }
}
