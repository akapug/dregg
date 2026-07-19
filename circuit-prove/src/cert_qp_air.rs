//! Lean-authored exact-integer CertQp proof for the fixed fhIR portfolio family.
//!
//! The public program is exactly `portfolio_qp_public()` after entrywise
//! round-to-nearest at `10^-3`: `n=6`, `mc=7`, budget + six position-cap rows,
//! and the fixed `(P,q,A,l,u,epsilon)` below.  `(x,y)` remain in the trace and
//! are proven through `HidingFriPcs`; the sole public result is the fixed-point
//! expected-return numerator `-q^T x` (scale `S^2`).
//!
//! Rust authors no constraints.  It parses the committed output of
//! `Market.CertQpDescriptor.portfolioDescriptor`, fills its columns, and refuses
//! any public-program or shape drift before proving.  The AIR recomputes all
//! three exact checker clauses: primal interval, stationarity, and projection /
//! normal-cone residual.  PSD remains the separate fhIR compile gate.  The
//! certified object is the rounded `10^-3` problem; extending the deployed
//! runner's `10^-9` registration requires multi-limb products/carries.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::{DreggZkStarkConfig, create_zk_config};

pub const N: usize = 6;
pub const MC: usize = 7;
pub const SCALE_DIGITS: u32 = 3;
pub const SCALE: i128 = 1_000;
pub const EPSILON: i128 = 1;
pub const TOL: i128 = EPSILON * SCALE;
pub const Y_SHIFT: i128 = 2_048;
pub const RANGE_LIMIT: i128 = 1 << 24;
pub const X_LIMIT: i128 = 1 << 10;
pub const Y_SHIFTED_LIMIT: i128 = 1 << 12;
const TRACE_HEIGHT: usize = 8;
const TRACE_WIDTH: usize = 123;

pub const P: [i128; N * N] = [
    1000, 100, 67, 50, 40, 33, 100, 1100, 100, 67, 50, 40, 67, 100, 1200, 100, 67, 50, 50, 67, 100,
    1300, 100, 67, 40, 50, 67, 100, 1400, 100, 33, 40, 50, 67, 100, 1500,
];
pub const Q: [i128; N] = [-250, -350, -450, -550, -650, -750];
pub const A: [i128; MC * N] = [
    1000, 1000, 1000, 1000, 1000, 1000, 1000, 0, 0, 0, 0, 0, 0, 1000, 0, 0, 0, 0, 0, 0, 1000, 0, 0,
    0, 0, 0, 0, 1000, 0, 0, 0, 0, 0, 0, 1000, 0, 0, 0, 0, 0, 0, 1000,
];
pub const L: [i128; MC] = [1000, 0, 0, 0, 0, 0, 0];
pub const U: [i128; MC] = [1000, 400, 400, 400, 400, 400, 400];

/// Byte-pinned output of the Lean descriptor emitter.
pub const CERT_QP_PORTFOLIO6_S3_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/dregg-cert-qp-portfolio6-s3-ir2.json");

/// Exact fixed-point certificate carrier.  Public program entries are included
/// deliberately: proving fails closed unless every one matches the Lean artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertQpWitness {
    pub n: usize,
    pub mc: usize,
    pub scale: u32,
    pub p: Vec<i128>,
    pub q: Vec<i128>,
    pub a: Vec<i128>,
    pub l: Vec<i128>,
    pub u: Vec<i128>,
    pub x: Vec<i128>,
    pub y: Vec<i128>,
    pub epsilon: i128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertQpCheck {
    pub primal_residual: i128,
    pub stationarity_residual: i128,
    pub normal_cone_residual: i128,
    pub tolerance: i128,
    pub primal: bool,
    pub stationarity: bool,
    pub normal_cone: bool,
    pub valid: bool,
}

fn row_dot(row: &[i128], v: &[i128]) -> i128 {
    row.iter().zip(v).map(|(a, b)| a * b).sum()
}

impl CertQpWitness {
    fn registered(&self) -> bool {
        self.n == N
            && self.mc == MC
            && self.scale == SCALE_DIGITS
            && self.epsilon == EPSILON
            && self.p == P
            && self.q == Q
            && self.a == A
            && self.l == L
            && self.u == U
            && self.x.len() == N
            && self.y.len() == MC
    }

    fn ax(&self) -> Vec<i128> {
        (0..MC)
            .map(|i| row_dot(&self.a[i * N..(i + 1) * N], &self.x))
            .collect()
    }

    fn stationarity_at(&self, j: usize) -> i128 {
        let px = row_dot(&self.p[j * N..(j + 1) * N], &self.x);
        let aty: i128 = (0..MC).map(|i| self.a[i * N + j] * self.y[i]).sum();
        px + self.q[j] * SCALE + aty
    }

    /// Exact recomputation of `CertQpExact::check` for the registered family.
    pub fn check(&self) -> Result<CertQpCheck, String> {
        if !self.registered() {
            return Err(
                "CertQp public program/shape is not the Lean-registered portfolio6-s3 descriptor"
                    .into(),
            );
        }
        let ax = self.ax();
        let primal_residual = (0..MC)
            .map(|i| {
                let ls = self.l[i] * SCALE;
                let us = self.u[i] * SCALE;
                (ax[i] - us).max(0) + (ls - ax[i]).max(0)
            })
            .max()
            .unwrap_or(0);
        let stationarity_residual = (0..N)
            .map(|j| self.stationarity_at(j).abs())
            .max()
            .unwrap_or(0);
        let normal_cone_residual = (0..MC)
            .map(|i| {
                let ls = self.l[i] * SCALE;
                let us = self.u[i] * SCALE;
                let projected = (ax[i] + self.y[i] * SCALE).clamp(ls, us);
                (ax[i] - projected).abs()
            })
            .max()
            .unwrap_or(0);
        let tolerance = self.epsilon * SCALE;
        let primal = primal_residual <= tolerance;
        let stationarity = stationarity_residual <= tolerance;
        let normal_cone = normal_cone_residual <= tolerance;
        Ok(CertQpCheck {
            primal_residual,
            stationarity_residual,
            normal_cone_residual,
            tolerance,
            primal,
            stationarity,
            normal_cone,
            valid: primal && stationarity && normal_cone,
        })
    }

    /// Public expected-return numerator `-q^T x`, at scale `S^2`.
    pub fn public_return(&self) -> i128 {
        self.q.iter().zip(&self.x).map(|(q, x)| -q * x).sum()
    }

    pub fn public_inputs(&self) -> Result<Vec<BabyBear>, String> {
        if !self.registered() {
            return Err("unregistered CertQp public program".into());
        }
        Ok(vec![fe(self.public_return())])
    }

    /// Fill exactly the columns named by the Lean descriptor.  Invalid residuals
    /// become negative field representatives; their declared range lookups then
    /// make the AIR unsatisfiable rather than trusting this producer's report.
    pub fn base_trace(&self) -> Result<Vec<Vec<BabyBear>>, String> {
        if !self.registered() {
            return Err("unregistered CertQp public program".into());
        }
        let ax = self.ax();
        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        for j in 0..N {
            row[x_col(j)] = fe(self.x[j]);
            row[x_upper_col(j)] = fe(X_LIMIT - 1 - self.x[j]);
        }
        for i in 0..MC {
            let shifted_y = self.y[i] + Y_SHIFT;
            row[y_col(i)] = fe(shifted_y);
            row[y_upper_col(i)] = fe(Y_SHIFTED_LIMIT - 1 - shifted_y);

            let ls = self.l[i] * SCALE;
            let us = self.u[i] * SCALE;
            row[primal_lo_col(i)] = fe(ax[i] - (ls - TOL));
            row[primal_hi_col(i)] = fe((us + TOL) - ax[i]);

            let shifted = ax[i] + self.y[i] * SCALE;
            let (low, mid, high) = if shifted <= ls {
                (1, 0, 0)
            } else if shifted <= us {
                (0, 1, 0)
            } else {
                (0, 0, 1)
            };
            row[low_sel_col(i)] = fe(low);
            row[mid_sel_col(i)] = fe(mid);
            row[high_sel_col(i)] = fe(high);
            row[low_region_col(i)] = fe(if low == 1 { ls - shifted } else { 0 });
            row[mid_lo_region_col(i)] = fe(if mid == 1 { shifted - ls } else { 0 });
            row[mid_hi_region_col(i)] = fe(if mid == 1 { us - shifted } else { 0 });
            row[high_region_col(i)] = fe(if high == 1 { shifted - us } else { 0 });
            let projected = shifted.clamp(ls, us);
            row[proj_col(i)] = fe(projected);
            row[normal_lo_col(i)] = fe(TOL + ax[i] - projected);
            row[normal_hi_col(i)] = fe(TOL - (ax[i] - projected));
        }
        for j in 0..N {
            let s = self.stationarity_at(j);
            row[stat_lo_col(j)] = fe(TOL + s);
            row[stat_hi_col(j)] = fe(TOL - s);
        }
        row[RETURN_COL] = fe(self.public_return());
        Ok(vec![row; TRACE_HEIGHT])
    }
}

/// Parse the Lean artifact after checking that the witness names its exact public program.
pub fn try_cert_qp_descriptor(cert: &CertQpWitness) -> Result<EffectVmDescriptor2, String> {
    if !cert.registered() {
        return Err(
            "CertQp public program is not the Lean-registered portfolio6-s3 program; refuse shape/program drift"
                .into(),
        );
    }
    parse_vm_descriptor2(CERT_QP_PORTFOLIO6_S3_DESCRIPTOR_JSON)
        .map_err(|e| format!("Lean CertQp descriptor failed to parse: {e}"))
}

/// Mint a witness-hiding proof of the three exact KKT checker clauses.
pub fn prove_cert_qp_zk(
    cert: &CertQpWitness,
) -> Result<
    (
        EffectVmDescriptor2,
        Ir2BatchProof<DreggZkStarkConfig>,
        Vec<BabyBear>,
    ),
    String,
> {
    let desc = try_cert_qp_descriptor(cert)?;
    let pis = cert.public_inputs()?;
    let trace = cert.base_trace()?;
    let config = create_zk_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )?;
    Ok((desc, proof, pis))
}

pub fn verify_cert_qp_zk(
    desc: &EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggZkStarkConfig>,
    pis: &[BabyBear],
) -> Result<(), String> {
    let registered = parse_vm_descriptor2(CERT_QP_PORTFOLIO6_S3_DESCRIPTOR_JSON)
        .map_err(|e| format!("registered Lean CertQp descriptor failed to parse: {e}"))?;
    if desc != &registered {
        return Err(
            "CertQp verifier descriptor differs from the byte-pinned portfolio6-s3 program".into(),
        );
    }
    let config = create_zk_config();
    verify_vm_descriptor2_with_config(desc, proof, pis, &config)
}

fn fe(x: i128) -> BabyBear {
    let p = BABYBEAR_P as i128;
    BabyBear::new(x.rem_euclid(p) as u32)
}

const QP_N: usize = N;
const QP_MC: usize = MC;
fn x_col(j: usize) -> usize {
    j
}
fn y_col(i: usize) -> usize {
    QP_N + i
}
fn primal_lo_col(i: usize) -> usize {
    QP_N + QP_MC + 2 * i
}
fn primal_hi_col(i: usize) -> usize {
    primal_lo_col(i) + 1
}
fn stat_lo_col(j: usize) -> usize {
    QP_N + QP_MC + 2 * QP_MC + 2 * j
}
fn stat_hi_col(j: usize) -> usize {
    stat_lo_col(j) + 1
}
const NORMAL_BASE: usize = QP_N + QP_MC + 2 * QP_MC + 2 * QP_N;
const NORMAL_STRIDE: usize = 10;
fn low_sel_col(i: usize) -> usize {
    NORMAL_BASE + NORMAL_STRIDE * i
}
fn mid_sel_col(i: usize) -> usize {
    low_sel_col(i) + 1
}
fn high_sel_col(i: usize) -> usize {
    low_sel_col(i) + 2
}
fn low_region_col(i: usize) -> usize {
    low_sel_col(i) + 3
}
fn mid_lo_region_col(i: usize) -> usize {
    low_sel_col(i) + 4
}
fn mid_hi_region_col(i: usize) -> usize {
    low_sel_col(i) + 5
}
fn high_region_col(i: usize) -> usize {
    low_sel_col(i) + 6
}
fn proj_col(i: usize) -> usize {
    low_sel_col(i) + 7
}
fn normal_lo_col(i: usize) -> usize {
    low_sel_col(i) + 8
}
fn normal_hi_col(i: usize) -> usize {
    low_sel_col(i) + 9
}
const RETURN_COL: usize = NORMAL_BASE + NORMAL_STRIDE * QP_MC;
fn x_upper_col(j: usize) -> usize {
    RETURN_COL + 1 + j
}
fn y_upper_col(i: usize) -> usize {
    RETURN_COL + 1 + QP_N + i
}
