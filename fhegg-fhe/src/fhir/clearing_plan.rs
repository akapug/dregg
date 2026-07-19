//! Canonical decoder/dispatcher for the Lean-authored fhIR clearing plan.
//!
//! Plan inference does not live here. `Market.FhIRClearingPlan.compileRebalance` owns the matrix,
//! tier, leakage/resource manifests, and exact no-wrap/noise certificate; its emitted bytes are
//! checked in under `plans/`. Rust strictly decodes those bytes, independently rechecks that the
//! certificate agrees with the current engine's public gates, and constructs `ClearingSpec`.

use super::{
    ClearingSpec, LeakageManifest, Tier, MAX_DIM, MAX_ITERATIONS, MAX_NNZ, MAX_SOC_BLOCK,
    MAX_TRIGGER_DEPTH,
};
use crate::convex_engine::max_iterations_for_params;
use crate::convex_step::{centered_window, PublicLinearStep};
use serde::{Deserialize, Serialize};
use std::fmt;

pub const PLAN_SCHEMA_VERSION: u32 = 1;
pub const EXACT_LINEAR_KERNEL_ID: &str = "fhir-exact-linear-v1";

/// The exact checked-in cache of `Market.FhIRClearingPlan.emitCanonical rebalanceV1`.
pub const LEAN_REBALANCE_V1_JSON: &str = include_str!("../../plans/rebalance-v1.json");

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClearingPlanError(pub String);

impl fmt::Display for ClearingPlanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for ClearingPlanError {}

fn reject(detail: impl fmt::Display) -> ClearingPlanError {
    ClearingPlanError(format!("invalid Lean fhIR clearing plan: {detail}"))
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct MatrixWire {
    rows: usize,
    cols: usize,
    data: Vec<Vec<i64>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct LeakageWire {
    dims: usize,
    nnz_a: usize,
    iterations: u32,
    precision_bits: u32,
    public_facts: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct StepWire {
    tau_num: u64,
    tau_den: u64,
    prox_lo: i64,
    prox_hi: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ResourceCertificate {
    pub max_dim: usize,
    pub max_nnz: usize,
    pub max_iterations: u32,
    pub max_trigger_depth: u32,
    pub max_soc_block: usize,
    pub trigger_depth: u32,
    pub soc_block: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NoWrapCertificate {
    pub input_lo: Vec<i64>,
    pub input_hi: Vec<i64>,
    pub centered_window: u64,
    pub max_abs_intermediate: u128,
    pub final_scale: u128,
    pub growth_factor: u128,
    pub fresh_noise_bound: u128,
    pub noise_ceiling: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ClearingPlanWire {
    version: u32,
    kernel_id: String,
    matrix: MatrixWire,
    tier: String,
    leakage: LeakageWire,
    step: StepWire,
    iterations: u32,
    plaintext_modulus: u64,
    resource: ResourceCertificate,
    no_wrap: NoWrapCertificate,
}

/// A validated Lean plan ready for the current exact-integer convex engine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClearingPlan {
    pub version: u32,
    pub kernel_id: String,
    pub spec: ClearingSpec,
    pub resource: ResourceCertificate,
    pub no_wrap: NoWrapCertificate,
}

impl ClearingPlan {
    pub fn engine_step(&self) -> PublicLinearStep {
        PublicLinearStep {
            a: self.spec.a.clone(),
            tau_num: self.spec.tau_num,
            tau_den: self.spec.tau_den,
        }
    }

    pub fn into_spec(self) -> ClearingSpec {
        self.spec
    }
}

fn abs_max(lo: i128, hi: i128) -> u128 {
    lo.unsigned_abs().max(hi.unsigned_abs())
}

/// Re-run the current engine's exact public interval arithmetic. This validates a certificate;
/// it does not choose or infer a matrix, tier, step, or resource plan.
fn validate_interval_certificate(
    wire: &ClearingPlanWire,
    step: &PublicLinearStep,
) -> Result<(), ClearingPlanError> {
    let d = wire.matrix.rows;
    if wire.no_wrap.input_lo.len() != d || wire.no_wrap.input_hi.len() != d {
        return Err(reject("input interval dimension mismatch"));
    }
    let half = centered_window(wire.plaintext_modulus);
    if wire.no_wrap.centered_window != half {
        return Err(reject("centered-window certificate drift"));
    }

    let mut x: Vec<(i128, i128)> = wire
        .no_wrap
        .input_lo
        .iter()
        .zip(&wire.no_wrap.input_hi)
        .map(|(&lo, &hi)| (i128::from(lo), i128::from(hi)))
        .collect();
    let mut max_abs = x.iter().map(|&(lo, hi)| abs_max(lo, hi)).max().unwrap_or(0);
    if x.iter()
        .any(|&(lo, hi)| lo > hi || abs_max(lo, hi) > u128::from(half))
    {
        return Err(reject(
            "initial interval is noncanonical or outside the centered window",
        ));
    }

    let fused = |i: usize, j: usize| -> Result<i128, ClearingPlanError> {
        let diag = if i == j { i128::from(step.tau_den) } else { 0 };
        diag.checked_sub(
            i128::from(step.tau_num)
                .checked_mul(i128::from(step.a[i][j]))
                .ok_or_else(|| reject("fused coefficient overflow"))?,
        )
        .ok_or_else(|| reject("fused coefficient overflow"))
    };
    let scale_interval = |(lo, hi): (i128, i128), c: i128| {
        let (a, b) = (lo * c, hi * c);
        (a.min(b), a.max(b))
    };

    let mut growth = 0u128;
    for i in 0..d {
        let mut row = 0u128;
        for j in 0..d {
            row = row
                .checked_add(fused(i, j)?.unsigned_abs())
                .ok_or_else(|| reject("growth-factor overflow"))?;
        }
        growth = growth.max(row);
    }
    if wire.no_wrap.growth_factor != growth {
        return Err(reject("fused growth-factor certificate drift"));
    }

    let mut scale = 1i128;
    for _ in 0..wire.iterations {
        let mut next = Vec::with_capacity(d);
        for i in 0..d {
            let mut acc = scale_interval(x[i], fused(i, i)?);
            max_abs = max_abs.max(abs_max(acc.0, acc.1));
            if abs_max(acc.0, acc.1) > u128::from(half) {
                return Err(reject("diagonal term leaves the centered window"));
            }
            for (j, &xj) in x.iter().enumerate() {
                if j == i {
                    continue;
                }
                let c = fused(i, j)?;
                if c == 0 {
                    continue;
                }
                let term = scale_interval(xj, c);
                max_abs = max_abs.max(abs_max(term.0, term.1));
                acc = (
                    acc.0
                        .checked_add(term.0)
                        .ok_or_else(|| reject("interval sum overflow"))?,
                    acc.1
                        .checked_add(term.1)
                        .ok_or_else(|| reject("interval sum overflow"))?,
                );
                max_abs = max_abs.max(abs_max(acc.0, acc.1));
                if abs_max(acc.0, acc.1) > u128::from(half) {
                    return Err(reject("partial sum leaves the centered window"));
                }
            }
            next.push(acc);
        }
        scale = scale
            .checked_mul(i128::from(step.tau_den))
            .ok_or_else(|| reject("scale overflow"))?;
        let box_lo = i128::from(wire.step.prox_lo)
            .checked_mul(scale)
            .ok_or_else(|| reject("prox scale overflow"))?;
        let box_hi = i128::from(wire.step.prox_hi)
            .checked_mul(scale)
            .ok_or_else(|| reject("prox scale overflow"))?;
        if next.iter().any(|&(lo, hi)| lo < box_lo || hi > box_hi) {
            return Err(reject("prox is not certified identity"));
        }
        x = next;
    }

    if wire.no_wrap.max_abs_intermediate != max_abs {
        return Err(reject("max-absolute-intermediate certificate drift"));
    }
    if wire.no_wrap.final_scale != scale.unsigned_abs() {
        return Err(reject("final-scale certificate drift"));
    }
    if wire.no_wrap.max_abs_intermediate > u128::from(half) {
        return Err(reject("no-wrap certificate exceeds the centered window"));
    }
    Ok(())
}

fn validate_and_lower(wire: ClearingPlanWire) -> Result<ClearingPlan, ClearingPlanError> {
    if wire.version != PLAN_SCHEMA_VERSION || wire.kernel_id != EXACT_LINEAR_KERNEL_ID {
        return Err(reject("unsupported schema version or kernel id"));
    }
    if wire.matrix.rows != 2
        || wire.matrix.cols != 2
        || wire.matrix.data != vec![vec![2, 1], vec![1, 2]]
    {
        return Err(reject(
            "kernel matrix is not the Lean-supported rebalance family",
        ));
    }
    if wire.tier != "tier0-dark" {
        return Err(reject("kernel must carry the Tier0-dark type"));
    }
    if wire.iterations == 0 || wire.leakage.iterations != wire.iterations {
        return Err(reject("iteration manifest mismatch"));
    }
    let nnz = wire
        .matrix
        .data
        .iter()
        .flatten()
        .filter(|&&x| x != 0)
        .count();
    let precision_bits = 63 - (wire.plaintext_modulus.max(2) - 1).leading_zeros();
    if wire.leakage.dims != 2
        || wire.leakage.nnz_a != nnz
        || wire.leakage.precision_bits != precision_bits
        || !wire.leakage.public_facts.is_empty()
    {
        return Err(reject("leakage manifest drift"));
    }
    if wire.step.tau_num != 1 || wire.step.tau_den != 3 || wire.step.prox_lo >= wire.step.prox_hi {
        return Err(reject("unsupported or invalid step fraction/prox box"));
    }
    if wire.no_wrap.input_lo != vec![wire.step.prox_lo; 2]
        || wire.no_wrap.input_hi != vec![wire.step.prox_hi; 2]
        || wire.step.prox_lo != -wire.step.prox_hi
    {
        return Err(reject(
            "input intervals do not match the symmetric prox family",
        ));
    }
    if wire.resource.max_dim != MAX_DIM
        || wire.resource.max_nnz != MAX_NNZ
        || wire.resource.max_iterations != MAX_ITERATIONS
        || wire.resource.max_trigger_depth != MAX_TRIGGER_DEPTH
        || wire.resource.max_soc_block != MAX_SOC_BLOCK
        || wire.resource.trigger_depth != 0
        || wire.resource.soc_block != 0
        || wire.matrix.rows > wire.resource.max_dim
        || nnz > wire.resource.max_nnz
        || wire.iterations > wire.resource.max_iterations
    {
        return Err(reject("resource certificate drift or budget overrun"));
    }

    // Bind the plan's t to the parameter set the current FHE consumer actually instantiates.
    let deployed_t = crate::additive::pick_params(20).plaintext();
    if wire.plaintext_modulus != deployed_t {
        return Err(reject(
            "plaintext modulus does not match the deployed BFV parameters",
        ));
    }

    let step = PublicLinearStep {
        a: wire.matrix.data.clone(),
        tau_num: wire.step.tau_num,
        tau_den: wire.step.tau_den,
    };
    validate_interval_certificate(&wire, &step)?;
    let noise_ceiling = max_iterations_for_params(&step, wire.plaintext_modulus);
    if wire.no_wrap.fresh_noise_bound != crate::convex_engine::B_FRESH
        || wire.no_wrap.noise_ceiling != noise_ceiling
        || wire.iterations > noise_ceiling
    {
        return Err(reject("deployed noise certificate drift or depth overrun"));
    }

    let spec = ClearingSpec {
        a: wire.matrix.data,
        tier: Tier::Tier0Dark,
        leakage_manifest: LeakageManifest {
            dims: wire.leakage.dims,
            nnz_a: wire.leakage.nnz_a,
            iterations: wire.leakage.iterations,
            precision_bits: wire.leakage.precision_bits,
            public_facts: wire.leakage.public_facts,
        },
        tau_num: wire.step.tau_num,
        tau_den: wire.step.tau_den,
        prox_lo: wire.step.prox_lo,
        prox_hi: wire.step.prox_hi,
        iterations: wire.iterations,
        plaintext_modulus: wire.plaintext_modulus,
    };
    Ok(ClearingPlan {
        version: wire.version,
        kernel_id: wire.kernel_id,
        spec,
        resource: wire.resource,
        no_wrap: wire.no_wrap,
    })
}

/// Decode only canonical bytes: unknown/duplicate fields, alternate whitespace/order, certificate
/// drift, and unsupported kernels all refuse.
pub fn decode_canonical_clearing_plan(bytes: &str) -> Result<ClearingPlan, ClearingPlanError> {
    let wire: ClearingPlanWire =
        serde_json::from_str(bytes).map_err(|e| reject(format!("wire decode: {e}")))?;
    let canonical = serde_json::to_string(&wire)
        .map_err(|e| reject(format!("canonical re-encode: {e}")))?
        + "\n";
    if canonical != bytes {
        return Err(reject("noncanonical bytes"));
    }
    validate_and_lower(wire)
}

/// Decode the deployed Lean-authored rebalance plan cache.
pub fn lean_rebalance_plan_v1() -> Result<ClearingPlan, ClearingPlanError> {
    decode_canonical_clearing_plan(LEAN_REBALANCE_V1_JSON)
}
