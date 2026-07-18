//! `fhIR` — the typed product/order DSL (the factory). FULLY DISJOINT from the crypto.
//!
//! Interface fixed in `docs/deos/FHEGG-PROTOTYPE-INTERFACES.md` §4, grammar from
//! `docs/deos/FHEGG-PRODUCT-ORDER-FRONTIER.md`. OWNED by the `fhir` lane. Three type axes; the reject-list;
//! `admissible`/`compile`. No crypto dependency — it emits a `ClearingSpec` the engine consumes.
//!
//! # The three type axes
//!
//! Every program is typed along three orthogonal axes (frontier doc, R2.3 headline):
//!
//! * **visibility** ∈ {`Public`, `Committed`, `Opened`} — who can see a datum. `Committed` is
//!   hidden forever (only aggregates leave); `Opened` is hidden during clearing, revealed at
//!   settle; `Public` is cleartext.
//! * **curvature** ∈ {`Affine`, `Convex`, `Concave`, `Discrete`} — inferred bottom-up over the
//!   expression grammar by the standard convexity calculus.
//! * **phase** ∈ {`Payoff`, `Price`, `Clear`, `Settle`} — where the program runs. The optimizer
//!   phases (`Price`, `Clear`) forbid `Discrete` curvature (the reject-list); the boundary phases
//!   (`Payoff`, `Settle`) admit bounded discrete circuits (one ReLU at settlement is Core).
//!
//! # The reject-list (explicit, from the frontier doc)
//!
//! private-matrix × secret-variable; secret × secret (except certificate atoms); binary decision
//! inside the optimizer; complementarity `x·y=0`; arbitrary disjunction; secret-indexed memory;
//! unbounded trigger recursion (incl. unlagged reflexive triggers — encoding #1: lag every
//! mark-dependent activation by ≥ 1 finalized epoch); PSD / exp-cone without an approved prox
//! (both excluded from v0 per R2.3). Each rejection is NAMED (`RejectKind`), never a bare `false`.
//!
//! # The six-part admissibility judgement
//!
//! `admissible(P)` holds **iff `compile(P)` succeeds** — the judgement is literally implemented as
//! compilation (the "admissible iff it compiles / passes the resource manifest" theorem shape).
//! The six parts, each a named check inside [`compile`]:
//!
//! 1. **semantic form** — grammar well-typed on all three axes; the reject-list walk.
//! 2. **certificate soundness** — certificate atoms (`CertGap`) well-formed: primal/dual over
//!    declared variables, dimensions consistent (soundness must not depend on the finder).
//! 3. **cost bound** — the resource manifest: dims, nnz, `T`, trigger depth, SOC block size all
//!    within the public budget; certificate cost is `T`-independent by construction.
//! 4. **conditional completeness** — every variable carries finite public bounds (the public
//!    radius); `T ≥ 1`; the step size is well-defined.
//! 5. **exact-arithmetic / no-wrap** — static interval analysis over the τ-scaled step
//!    `w = τ_den·x − τ_num·A·x` proves every intermediate fits the centered plaintext window.
//! 6. **leakage refinement** — the manifest lists ONLY dimensions, public topology (nnz), `T`,
//!    precision, and deliberately-public facts; publishing a `Committed` variable, or an `Opened`
//!    variable outside `Settle`, is a named rejection.
//!
//! # What compiles to what
//!
//! The cheap class is the budgeted conic-QP family with **public sparse operators** and
//! private-or-public vector data. `compile` assembles the public step matrix
//! `A = P + Eᵀ·E` (quadratic objective terms + equality-penalty normal form), picks
//! `τ = 1/‖A‖∞`, hulls the box constraints into the prox clamp, and emits a [`ClearingSpec`]
//! whose fields feed `convex_engine::convex_solve(x0, PublicLinearStep{a,τ}, prox_lo, prox_hi, T, t)`
//! directly (same d×d shape `convex_linear_step` demands).
//!
//! Tier typing: all-public → `Tier2Open`; secret data + FHE-tractable ops (affine steps with
//! public coefficients, public-coefficient squares, box prox, ≤ k_max private trigger layers)
//! → `Tier0Dark`; secret data needing certificate-side cones (SOC) or opened results
//! → `Tier1Shielded`.
#![allow(dead_code)]

use std::fmt;

// ---------------------------------------------------------------------------
// The three axes
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Committed,
    Opened,
}

impl Visibility {
    /// Secrecy rank for joins: Public < Opened < Committed.
    fn secrecy(self) -> u8 {
        match self {
            Visibility::Public => 0,
            Visibility::Opened => 1,
            Visibility::Committed => 2,
        }
    }
    fn join(self, other: Visibility) -> Visibility {
        if self.secrecy() >= other.secrecy() {
            self
        } else {
            other
        }
    }
    fn is_secret(self) -> bool {
        self != Visibility::Public
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Curvature {
    Affine,
    Convex,
    Concave,
    Discrete,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    Payoff,
    Price,
    Clear,
    Settle,
}

impl Phase {
    /// The optimizer phases: a finder runs here, so discrete/bilinear structure is rejected.
    pub fn is_optimizer(self) -> bool {
        matches!(self, Phase::Price | Phase::Clear)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tier {
    Tier0Dark,
    Tier1Shielded,
    Tier2Open,
}

// ---------------------------------------------------------------------------
// The reject-list — every rejection is NAMED
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RejectKind {
    /// Private (committed/opened) coefficient multiplying a secret variable — a hidden operator.
    /// "The matrices must be public" is THE efficiency boundary (R2.3 precision-correction #4).
    PrivateMatrixTimesSecretVariable,
    /// secret × secret product outside a certificate atom.
    SecretTimesSecret,
    /// A 0/1 decision variable inside the optimizer (Price/Clear). Fine at Payoff/Settle.
    BinaryDecisionInOptimizer,
    /// Complementarity `x·y = 0` — breaks the continuous regime.
    Complementarity,
    /// Arbitrary disjunction of constraints — integer wall; compile linkage through receipts instead.
    ArbitraryDisjunction,
    /// Memory indexed by a secret value — no secret-indexed RAM (oblivious discipline).
    SecretIndexedMemory,
    /// Trigger chain with a cycle, unbounded depth, or an unlagged (same-batch reflexive) guard.
    UnboundedTriggerRecursion,
    /// PSD / exp-cone (exp, log-sum-exp/LMSR) — no approved prox in v0.
    UnapprovedCone,
    /// Nonconvex composition (e.g. convex + concave, max of concaves) in an optimizer phase.
    NonConvexComposition,
    /// Part 2: a certificate atom that is not well-formed (dangling variable, empty).
    MalformedCertificateAtom,
    /// Part 3: the resource manifest budget is exceeded (dims / nnz / T / trigger depth / SOC size).
    ResourceBudgetExceeded,
    /// Part 4: a variable without finite public bounds, or T = 0 (no public radius ⇒ no completeness).
    MissingPublicBounds,
    /// Part 5: static interval analysis overflows the centered plaintext window (or i64 assembly).
    WindowOverflow,
    /// Part 6: publishing a Committed variable, or an Opened variable outside Settle.
    LeakageViolation,
    /// Structural: undeclared variable / trigger, empty program, inconsistent dimensions.
    IllFormed,
}

impl RejectKind {
    pub fn as_str(self) -> &'static str {
        match self {
            RejectKind::PrivateMatrixTimesSecretVariable => "PrivateMatrixTimesSecretVariable",
            RejectKind::SecretTimesSecret => "SecretTimesSecret",
            RejectKind::BinaryDecisionInOptimizer => "BinaryDecisionInOptimizer",
            RejectKind::Complementarity => "Complementarity",
            RejectKind::ArbitraryDisjunction => "ArbitraryDisjunction",
            RejectKind::SecretIndexedMemory => "SecretIndexedMemory",
            RejectKind::UnboundedTriggerRecursion => "UnboundedTriggerRecursion",
            RejectKind::UnapprovedCone => "UnapprovedCone",
            RejectKind::NonConvexComposition => "NonConvexComposition",
            RejectKind::MalformedCertificateAtom => "MalformedCertificateAtom",
            RejectKind::ResourceBudgetExceeded => "ResourceBudgetExceeded",
            RejectKind::MissingPublicBounds => "MissingPublicBounds",
            RejectKind::WindowOverflow => "WindowOverflow",
            RejectKind::LeakageViolation => "LeakageViolation",
            RejectKind::IllFormed => "IllFormed",
        }
    }
}

impl fmt::Display for RejectKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A NAMED rejection from the reject-list (e.g. private-matrix × secret-variable).
///
/// The payload is `"<RejectKind>: <detail>"`; [`Rejection::kind`] recovers the kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rejection(pub String);

impl Rejection {
    fn new(kind: RejectKind, detail: impl fmt::Display) -> Self {
        Rejection(format!("{kind}: {detail}"))
    }
    /// The named reject-list entry this rejection came from.
    pub fn kind(&self) -> Option<RejectKind> {
        let name = self.0.split(':').next()?;
        [
            RejectKind::PrivateMatrixTimesSecretVariable,
            RejectKind::SecretTimesSecret,
            RejectKind::BinaryDecisionInOptimizer,
            RejectKind::Complementarity,
            RejectKind::ArbitraryDisjunction,
            RejectKind::SecretIndexedMemory,
            RejectKind::UnboundedTriggerRecursion,
            RejectKind::UnapprovedCone,
            RejectKind::NonConvexComposition,
            RejectKind::MalformedCertificateAtom,
            RejectKind::ResourceBudgetExceeded,
            RejectKind::MissingPublicBounds,
            RejectKind::WindowOverflow,
            RejectKind::LeakageViolation,
            RejectKind::IllFormed,
        ]
        .into_iter()
        .find(|k| k.as_str() == name)
    }
}

impl fmt::Display for Rejection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

// ---------------------------------------------------------------------------
// The grammar: coefficients, affine, convex, constraints, triggers, orders
// ---------------------------------------------------------------------------

pub type VarId = usize;
pub type TriggerId = usize;

/// A coefficient in an affine form. Committed/Opened coefficients carry only a PUBLIC magnitude
/// bound (the compiler never sees the value — that is the point); the bound feeds the no-wrap
/// interval analysis (part 5) and the "matrices must be public" check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Coeff {
    Public(i64),
    Committed { abs_bound: i64 },
    Opened { abs_bound: i64 },
}

impl Coeff {
    fn visibility(self) -> Visibility {
        match self {
            Coeff::Public(_) => Visibility::Public,
            Coeff::Committed { .. } => Visibility::Committed,
            Coeff::Opened { .. } => Visibility::Opened,
        }
    }
}

/// `Σ cᵢ·xᵢ + k` — the affine fragment. The workhorse of the cheap regime.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct AffineExpr {
    pub terms: Vec<(Coeff, VarId)>,
    pub constant: i64,
}

impl AffineExpr {
    pub fn constant(k: i64) -> Self {
        AffineExpr {
            terms: vec![],
            constant: k,
        }
    }
    pub fn var(v: VarId) -> Self {
        AffineExpr {
            terms: vec![(Coeff::Public(1), v)],
            constant: 0,
        }
    }
    pub fn term(mut self, c: Coeff, v: VarId) -> Self {
        self.terms.push((c, v));
        self
    }
    pub fn scaled(v: VarId, c: i64) -> Self {
        AffineExpr {
            terms: vec![(Coeff::Public(c), v)],
            constant: 0,
        }
    }
}

/// The expression grammar (frontier §R2.3: affine / convex / constraint / trigger / order / program).
/// Curvature is INFERRED, not declared — the convexity calculus is the type checker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Affine(AffineExpr),
    /// `(aᵀx + b)²` — convex. Coefficients must be Public (a committed square is a hidden Hessian).
    Square(AffineExpr),
    /// `|aᵀx + b|` — convex PWL.
    Abs(AffineExpr),
    /// `max(e₁, e₂)` — convex if both convex/affine (the settlement ReLU is `Max(payoff, 0)`).
    Max(Box<Expr>, Box<Expr>),
    /// `min(e₁, e₂)` — concave if both concave/affine.
    Min(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
    Sum(Vec<Expr>),
    /// General product — the dangerous node. Public-constant scaling is fine; secret×secret and
    /// bilinear-in-the-optimizer are reject-list entries.
    Mul(Box<Expr>, Box<Expr>),
    /// `‖(a₁ᵀx, …, a_kᵀx)‖₂` — a small approved SOC block (variance/vol/Squeeth lane). Tier1.
    SocNorm(Vec<AffineExpr>),
    /// exp-cone — NOT in the v0 cone library. Always a named rejection.
    Exp(AffineExpr),
    /// `log Σ exp` (LMSR) — exp-cone. Always a named rejection (use quadratic/PWL cost instead).
    LogSumExp(Vec<AffineExpr>),
    /// A hidden-eigendecomposition PSD quadratic form — excluded from v0. Always rejected.
    PsdQuadForm {
        dim: usize,
    },
    /// A 0/1 decision on a variable — Discrete curvature. Admissible ONLY at Payoff/Settle.
    BinaryDecision(VarId),
    /// `table[index]` — public table lookup. A SECRET index is secret-indexed memory: rejected.
    IndexBy {
        table: Vec<i64>,
        index: VarId,
    },
    /// A certificate atom: the primal·dual gap pairing. The ONE place secret×secret is admitted
    /// (it is verified, never solved — soundness is trace-independent).
    CertGap {
        primal: AffineExpr,
        dual: AffineExpr,
    },
}

impl Expr {
    pub fn affine(a: AffineExpr) -> Self {
        Expr::Affine(a)
    }
    pub fn var(v: VarId) -> Self {
        Expr::Affine(AffineExpr::var(v))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint {
    /// `aᵀx + b = 0` (affine equality — conservation, balance).
    EqZero(AffineExpr),
    /// `g(x) ≤ 0`, `g` convex.
    LeZero(Expr),
    /// `lo ≤ x_v ≤ hi` — the box; hulls into the prox clamp.
    Box { var: VarId, lo: i64, hi: i64 },
    /// `x·y = 0` — reject-list.
    Complementarity(VarId, VarId),
    /// `C₁ ∨ C₂ ∨ …` — reject-list (compile through receipts/nullifiers, not LP binaries).
    Disjunction(Vec<Constraint>),
}

/// A mark-dependent activation. Encoding #1 (frontier): every guard references a mark lagged by
/// ≥ 1 FINALIZED epoch — `lag_epochs == 0` on a non-constant guard is a reflexive book, rejected.
/// Chains (`parent`) model if-then/bracket linkage; depth is budgeted, cycles rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trigger {
    pub guard: AffineExpr,
    pub lag_epochs: u32,
    pub activates: VarId,
    pub parent: Option<TriggerId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
    Buy,
    Sell,
}

/// An order: a quantity variable in a static padded slot, optionally activation-masked
/// (`q' = a·q`, cap-zero masking — encoding #3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Order {
    pub side: Side,
    pub qty: VarId,
    pub limit_price: Option<i64>,
    pub activation: Option<TriggerId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sense {
    Minimize,
    Maximize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Objective {
    pub sense: Sense,
    pub expr: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarDecl {
    pub name: String,
    pub visibility: Visibility,
    /// Finite public bounds are MANDATORY for admissibility (parts 4 & 5).
    pub lo: i64,
    pub hi: i64,
}

// ---------------------------------------------------------------------------
// The resource budget (part 3) — public, fixed, resource-relative maximality
// ---------------------------------------------------------------------------

pub const MAX_DIM: usize = 4096;
pub const MAX_NNZ: usize = 1 << 20;
pub const MAX_ITERATIONS: u32 = 256;
/// `k_max` layers of affine private triggers (the cheap class allows a bounded stack).
pub const MAX_TRIGGER_DEPTH: u32 = 8;
/// Approved SOC blocks are SMALL (variance/vol epigraphs), per R2.3's cone library 𝔎₀.
pub const MAX_SOC_BLOCK: usize = 16;
/// Static-analysis default plaintext modulus (~2^20, matching the deployed BFV params).
pub const DEFAULT_PLAINTEXT_MODULUS: u64 = 1 << 20;

// ---------------------------------------------------------------------------
// Program — the typed AST, with a builder the e2e lane constructs against
// ---------------------------------------------------------------------------

/// The typed AST (affine/convex/constraint/trigger/order/program).
///
/// Build with the fluent API:
/// ```ignore
/// let mut p = Program::new(Phase::Clear);
/// let x = p.var("x", Visibility::Committed, -100, 100);
/// let y = p.var("y", Visibility::Committed, -100, 100);
/// p.minimize(Expr::Sum(vec![
///     Expr::Square(AffineExpr::var(x)),
///     Expr::Square(AffineExpr::var(y)),
/// ]));
/// p.subject_to(Constraint::EqZero(
///     AffineExpr::var(x).term(Coeff::Public(1), y),  // x + y = 0 (balance)
/// ));
/// let spec = compile(&p)?; // Tier0Dark
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub phase: Phase,
    pub vars: Vec<VarDecl>,
    pub objective: Option<Objective>,
    pub constraints: Vec<Constraint>,
    pub triggers: Vec<Trigger>,
    pub orders: Vec<Order>,
    /// Requested finder depth `T` (public, fixed — data-independent iteration count).
    pub iterations: u32,
    /// Plaintext modulus the static no-wrap analysis certifies against.
    pub plaintext_modulus: u64,
    /// Deliberately-public outputs (part 6): only Public vars, or Opened vars at Settle.
    pub publish: Vec<VarId>,
}

impl Program {
    pub fn new(phase: Phase) -> Self {
        Program {
            phase,
            vars: vec![],
            objective: None,
            constraints: vec![],
            triggers: vec![],
            orders: vec![],
            iterations: 1,
            plaintext_modulus: DEFAULT_PLAINTEXT_MODULUS,
            publish: vec![],
        }
    }
    pub fn var(&mut self, name: &str, visibility: Visibility, lo: i64, hi: i64) -> VarId {
        self.vars.push(VarDecl {
            name: name.to_string(),
            visibility,
            lo,
            hi,
        });
        self.vars.len() - 1
    }
    pub fn minimize(&mut self, expr: Expr) -> &mut Self {
        self.objective = Some(Objective {
            sense: Sense::Minimize,
            expr,
        });
        self
    }
    pub fn maximize(&mut self, expr: Expr) -> &mut Self {
        self.objective = Some(Objective {
            sense: Sense::Maximize,
            expr,
        });
        self
    }
    pub fn subject_to(&mut self, c: Constraint) -> &mut Self {
        self.constraints.push(c);
        self
    }
    pub fn trigger(&mut self, t: Trigger) -> TriggerId {
        self.triggers.push(t);
        self.triggers.len() - 1
    }
    pub fn order(&mut self, o: Order) -> &mut Self {
        self.orders.push(o);
        self
    }
    pub fn with_iterations(&mut self, t: u32) -> &mut Self {
        self.iterations = t;
        self
    }
    pub fn with_plaintext_modulus(&mut self, t: u64) -> &mut Self {
        self.plaintext_modulus = t;
        self
    }
    pub fn publish_var(&mut self, v: VarId) -> &mut Self {
        self.publish.push(v);
        self
    }

    fn visibility_of(&self, v: VarId) -> Result<Visibility, Rejection> {
        self.vars.get(v).map(|d| d.visibility).ok_or_else(|| {
            Rejection::new(RejectKind::IllFormed, format!("undeclared variable #{v}"))
        })
    }
}

// ---------------------------------------------------------------------------
// Leakage manifest (part 6) & ClearingSpec — what the engine consumes
// ---------------------------------------------------------------------------

/// Part 6: the manifest lists ONLY dimensions, public topology, `T`, precision, and
/// deliberately-public facts. Nothing about private data beyond its declared bounds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeakageManifest {
    pub dims: usize,
    pub nnz_a: usize,
    pub iterations: u32,
    /// Precision: bits of the plaintext window the values are certified to fit.
    pub precision_bits: u32,
    /// Names of deliberately-public outputs (Public vars; Opened vars at Settle).
    pub public_facts: Vec<String>,
}

/// What the engine consumes: the public matrix, tier, and a leakage manifest — plus everything
/// `convex_engine::convex_solve` needs (`PublicLinearStep{a, tau}` + prox clamp + `T`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClearingSpec {
    /// The PUBLIC d×d step operator (P + EᵀE): square, matching the state dimension.
    pub a: Vec<Vec<i64>>,
    pub tier: Tier,
    pub leakage_manifest: LeakageManifest,
    /// Step size τ = tau_num/tau_den, chosen τ ≤ 1/‖A‖∞.
    pub tau_num: u64,
    pub tau_den: u64,
    /// The prox clamp (hull of the box constraints / variable bounds).
    pub prox_lo: i64,
    pub prox_hi: i64,
    pub iterations: u32,
    /// The plaintext modulus the no-wrap analysis certified against.
    pub plaintext_modulus: u64,
}

// ---------------------------------------------------------------------------
// Curvature & visibility inference (the typing walk) + the reject-list
// ---------------------------------------------------------------------------

/// What one expression walk learns: its two inferred axes plus tier-relevant structure.
#[derive(Debug, Clone, Copy)]
struct ExprType {
    curvature: Curvature,
    visibility: Visibility,
    /// True iff every op on the secret path is FHE-tractable (affine w/ public coeffs,
    /// public-coefficient squares, sums/negs thereof). SOC/Abs/Max/cert atoms are cert-side.
    fhe_tractable: bool,
    /// True iff the node tree contains a certificate atom (forces Tier1: the certificate
    /// relation is checked in the proof layer, not under FHE).
    has_cert_atom: bool,
    /// Largest SOC block seen (0 if none) — resource-budget input.
    max_soc: usize,
}

fn affine_type(p: &Program, a: &AffineExpr, ctx: &str) -> Result<ExprType, Rejection> {
    let mut vis = Visibility::Public;
    for &(c, v) in &a.terms {
        let vv = p.visibility_of(v)?;
        // THE efficiency boundary: a private coefficient on a secret variable is a hidden
        // operator entry — private-matrix × secret-variable.
        if c.visibility().is_secret() && vv.is_secret() {
            return Err(Rejection::new(
                RejectKind::PrivateMatrixTimesSecretVariable,
                format!(
                    "{ctx}: private coefficient on secret variable '{}'",
                    p.vars[v].name
                ),
            ));
        }
        vis = vis.join(vv).join(c.visibility());
    }
    Ok(ExprType {
        curvature: Curvature::Affine,
        visibility: vis,
        fhe_tractable: true,
        has_cert_atom: false,
        max_soc: 0,
    })
}

/// Is this affine expression a compile-time constant (no variable terms)?
fn affine_const(a: &AffineExpr) -> Option<i64> {
    if a.terms.is_empty() {
        Some(a.constant)
    } else {
        None
    }
}

fn flip(c: Curvature) -> Curvature {
    match c {
        Curvature::Affine => Curvature::Affine,
        Curvature::Convex => Curvature::Concave,
        Curvature::Concave => Curvature::Convex,
        Curvature::Discrete => Curvature::Discrete,
    }
}

/// The convexity-calculus join for `+`: affine absorbs; convex+concave is DC — not typable.
fn sum_curv(a: Curvature, b: Curvature, ctx: &str) -> Result<Curvature, Rejection> {
    use Curvature::*;
    Ok(match (a, b) {
        (Affine, x) | (x, Affine) => x,
        (Convex, Convex) => Convex,
        (Concave, Concave) => Concave,
        (Discrete, _) | (_, Discrete) => Discrete,
        (Convex, Concave) | (Concave, Convex) => {
            return Err(Rejection::new(
                RejectKind::NonConvexComposition,
                format!("{ctx}: convex + concave (difference-of-convex) is not in the cheap class"),
            ))
        }
    })
}

fn expr_type(p: &Program, e: &Expr, ctx: &str) -> Result<ExprType, Rejection> {
    use Curvature::*;
    match e {
        Expr::Affine(a) => affine_type(p, a, ctx),
        Expr::Square(a) => {
            let t = affine_type(p, a, ctx)?;
            // A committed coefficient inside a square lands in the quadratic operator P —
            // a hidden Hessian. The matrices must be public.
            if a.terms.iter().any(|(c, _)| c.visibility().is_secret()) {
                return Err(Rejection::new(
                    RejectKind::PrivateMatrixTimesSecretVariable,
                    format!("{ctx}: committed coefficient inside a square is a hidden Hessian"),
                ));
            }
            Ok(ExprType {
                curvature: Convex,
                ..t
            })
        }
        Expr::Abs(a) => {
            let t = affine_type(p, a, ctx)?;
            // |·| needs a PWL/prox treatment — certificate-side, not the FHE affine step.
            Ok(ExprType {
                curvature: Convex,
                fhe_tractable: false,
                ..t
            })
        }
        Expr::Max(l, r) => {
            let lt = expr_type(p, l, ctx)?;
            let rt = expr_type(p, r, ctx)?;
            let curv = match (lt.curvature, rt.curvature) {
                (Affine | Convex, Affine | Convex) => Convex,
                (Discrete, _) | (_, Discrete) => Discrete,
                _ => {
                    return Err(Rejection::new(
                        RejectKind::NonConvexComposition,
                        format!("{ctx}: max of a concave argument is not convex"),
                    ))
                }
            };
            Ok(merge(lt, rt, curv, false))
        }
        Expr::Min(l, r) => {
            let lt = expr_type(p, l, ctx)?;
            let rt = expr_type(p, r, ctx)?;
            let curv = match (lt.curvature, rt.curvature) {
                (Affine | Concave, Affine | Concave) => Concave,
                (Discrete, _) | (_, Discrete) => Discrete,
                _ => {
                    return Err(Rejection::new(
                        RejectKind::NonConvexComposition,
                        format!("{ctx}: min of a convex argument is not concave"),
                    ))
                }
            };
            Ok(merge(lt, rt, curv, false))
        }
        Expr::Neg(inner) => {
            let t = expr_type(p, inner, ctx)?;
            Ok(ExprType {
                curvature: flip(t.curvature),
                ..t
            })
        }
        Expr::Sum(es) => {
            if es.is_empty() {
                return Err(Rejection::new(
                    RejectKind::IllFormed,
                    format!("{ctx}: empty sum"),
                ));
            }
            let mut acc = expr_type(p, &es[0], ctx)?;
            for e in &es[1..] {
                let t = expr_type(p, e, ctx)?;
                let curv = sum_curv(acc.curvature, t.curvature, ctx)?;
                let fhe = acc.fhe_tractable && t.fhe_tractable;
                acc = merge(acc, t, curv, fhe);
            }
            Ok(acc)
        }
        Expr::Mul(l, r) => {
            let lt = expr_type(p, l, ctx)?;
            let rt = expr_type(p, r, ctx)?;
            // Public-constant scaling preserves the calculus (sign known at compile time).
            let const_of = |e: &Expr| match e {
                Expr::Affine(a) => affine_const(a),
                _ => None,
            };
            if let Some(k) = const_of(l) {
                let curv = if k >= 0 {
                    rt.curvature
                } else {
                    flip(rt.curvature)
                };
                return Ok(merge(lt, rt, curv, rt.fhe_tractable));
            }
            if let Some(k) = const_of(r) {
                let curv = if k >= 0 {
                    lt.curvature
                } else {
                    flip(lt.curvature)
                };
                return Ok(merge(lt, rt, curv, lt.fhe_tractable));
            }
            // Non-constant × non-constant.
            if lt.visibility.is_secret() && rt.visibility.is_secret() {
                return Err(Rejection::new(
                    RejectKind::SecretTimesSecret,
                    format!("{ctx}: secret × secret product outside a certificate atom"),
                ));
            }
            if p.phase.is_optimizer() {
                // Bilinear market impact / hidden couplings inside the finder.
                return Err(Rejection::new(
                    RejectKind::NonConvexComposition,
                    format!("{ctx}: bilinear product inside the optimizer"),
                ));
            }
            Ok(merge(lt, rt, Discrete, false))
        }
        Expr::SocNorm(rows) => {
            if rows.is_empty() {
                return Err(Rejection::new(
                    RejectKind::IllFormed,
                    format!("{ctx}: empty SOC block"),
                ));
            }
            let mut acc: Option<ExprType> = None;
            for a in rows {
                let t = affine_type(p, a, ctx)?;
                acc = Some(match acc {
                    None => t,
                    Some(prev) => merge(prev, t, Convex, false),
                });
            }
            let mut t = acc.unwrap();
            t.curvature = Convex;
            t.fhe_tractable = false; // SOC prox is certificate-side, not an FHE affine step
            t.max_soc = t.max_soc.max(rows.len());
            Ok(t)
        }
        Expr::Exp(_) => Err(Rejection::new(
            RejectKind::UnapprovedCone,
            format!("{ctx}: exp-cone has no approved prox in v0"),
        )),
        Expr::LogSumExp(_) => Err(Rejection::new(
            RejectKind::UnapprovedCone,
            format!("{ctx}: log-sum-exp (LMSR) is exp-cone; use a quadratic/PWL cost function"),
        )),
        Expr::PsdQuadForm { dim } => Err(Rejection::new(
            RejectKind::UnapprovedCone,
            format!(
                "{ctx}: PSD cone (dim {dim}) needs a hidden eigendecomposition; excluded from v0"
            ),
        )),
        Expr::BinaryDecision(v) => {
            let vis = p.visibility_of(*v)?;
            if p.phase.is_optimizer() {
                return Err(Rejection::new(
                    RejectKind::BinaryDecisionInOptimizer,
                    format!(
                        "{ctx}: 0/1 decision on '{}' inside the optimizer (phase {:?}); compile \
                         linkage through receipts, or move it to Payoff/Settle",
                        p.vars[*v].name, p.phase
                    ),
                ));
            }
            Ok(ExprType {
                curvature: Discrete,
                visibility: vis,
                fhe_tractable: false,
                has_cert_atom: false,
                max_soc: 0,
            })
        }
        Expr::IndexBy { table, index } => {
            let vis = p.visibility_of(*index)?;
            if vis.is_secret() {
                return Err(Rejection::new(
                    RejectKind::SecretIndexedMemory,
                    format!(
                        "{ctx}: memory indexed by secret '{}'; use fixed padded slots + cap-zero masking",
                        p.vars[*index].name
                    ),
                ));
            }
            if table.is_empty() {
                return Err(Rejection::new(
                    RejectKind::IllFormed,
                    format!("{ctx}: empty lookup table"),
                ));
            }
            Ok(ExprType {
                curvature: Discrete,
                visibility: vis,
                fhe_tractable: false,
                has_cert_atom: false,
                max_soc: 0,
            })
        }
        Expr::CertGap { primal, dual } => {
            // The exception in the reject-list: secret×secret is admitted HERE, because the
            // certificate is verified, never solved. Well-formedness is part 2.
            if primal.terms.is_empty() || dual.terms.is_empty() {
                return Err(Rejection::new(
                    RejectKind::MalformedCertificateAtom,
                    format!("{ctx}: certificate atom with an empty primal or dual side"),
                ));
            }
            let mut vis = Visibility::Public;
            for &(_, v) in primal.terms.iter().chain(dual.terms.iter()) {
                vis = vis.join(p.visibility_of(v)?);
            }
            Ok(ExprType {
                curvature: Curvature::Affine,
                visibility: vis,
                fhe_tractable: false,
                has_cert_atom: true,
                max_soc: 0,
            })
        }
    }
}

fn merge(a: ExprType, b: ExprType, curvature: Curvature, fhe: bool) -> ExprType {
    ExprType {
        curvature,
        visibility: a.visibility.join(b.visibility),
        fhe_tractable: fhe,
        has_cert_atom: a.has_cert_atom || b.has_cert_atom,
        max_soc: a.max_soc.max(b.max_soc),
    }
}

// ---------------------------------------------------------------------------
// Triggers: lag discipline + bounded recursion (reject-list)
// ---------------------------------------------------------------------------

fn check_triggers(p: &Program) -> Result<u32, Rejection> {
    let mut max_depth = 0u32;
    for (i, tr) in p.triggers.iter().enumerate() {
        p.visibility_of(tr.activates)?;
        affine_type(p, &tr.guard, &format!("trigger #{i} guard"))?;
        // Encoding #1: lag ALL mark-dependent activation by ≥ 1 finalized epoch. A same-batch
        // guard over any variable is a reflexive book (fixed-point hazard) — rejected.
        if tr.lag_epochs == 0 && !tr.guard.terms.is_empty() {
            return Err(Rejection::new(
                RejectKind::UnboundedTriggerRecursion,
                format!(
                    "trigger #{i}: unlagged (same-batch) mark-dependent guard — reflexive book"
                ),
            ));
        }
        // Walk the parent chain: cycles or depth > k_max are unbounded recursion.
        let mut depth = 1u32;
        let mut seen = vec![false; p.triggers.len()];
        seen[i] = true;
        let mut cur = tr.parent;
        while let Some(pid) = cur {
            if pid >= p.triggers.len() {
                return Err(Rejection::new(
                    RejectKind::IllFormed,
                    format!("trigger #{i}: dangling parent #{pid}"),
                ));
            }
            if seen[pid] {
                return Err(Rejection::new(
                    RejectKind::UnboundedTriggerRecursion,
                    format!("trigger #{i}: cyclic trigger chain through #{pid}"),
                ));
            }
            seen[pid] = true;
            depth += 1;
            if depth > MAX_TRIGGER_DEPTH {
                return Err(Rejection::new(
                    RejectKind::UnboundedTriggerRecursion,
                    format!(
                        "trigger #{i}: chain depth {depth} exceeds k_max = {MAX_TRIGGER_DEPTH}"
                    ),
                ));
            }
            cur = p.triggers[pid].parent;
        }
        max_depth = max_depth.max(depth);
    }
    for (i, o) in p.orders.iter().enumerate() {
        p.visibility_of(o.qty)?;
        if let Some(t) = o.activation {
            if t >= p.triggers.len() {
                return Err(Rejection::new(
                    RejectKind::IllFormed,
                    format!("order #{i}: dangling activation trigger #{t}"),
                ));
            }
        }
    }
    Ok(max_depth)
}

// ---------------------------------------------------------------------------
// compile — the six-part judgement, then the spec assembly
// ---------------------------------------------------------------------------

struct Analysis {
    /// Join of all types on the walk (objective + constraints).
    visibility: Visibility,
    fhe_tractable: bool,
    has_cert_atom: bool,
    max_soc: usize,
    has_opened: bool,
}

/// Parts 1 & 2: the typing walk over objective + constraints (grammar, three axes, reject-list,
/// certificate well-formedness).
fn analyze(p: &Program) -> Result<Analysis, Rejection> {
    if p.vars.is_empty() {
        return Err(Rejection::new(
            RejectKind::IllFormed,
            "program declares no variables",
        ));
    }
    let mut vis = Visibility::Public;
    let mut fhe = true;
    let mut cert = false;
    let mut soc = 0usize;

    if let Some(obj) = &p.objective {
        let t = expr_type(p, &obj.expr, "objective")?;
        // Curvature × phase: the optimizer minimizes convex / maximizes concave, only.
        if p.phase.is_optimizer() {
            let ok = match obj.sense {
                Sense::Minimize => matches!(t.curvature, Curvature::Affine | Curvature::Convex),
                Sense::Maximize => matches!(t.curvature, Curvature::Affine | Curvature::Concave),
            };
            if !ok {
                return Err(Rejection::new(
                    RejectKind::NonConvexComposition,
                    format!(
                        "objective: {:?} of a {:?} expression in an optimizer phase",
                        obj.sense, t.curvature
                    ),
                ));
            }
        }
        vis = vis.join(t.visibility);
        fhe &= t.fhe_tractable;
        cert |= t.has_cert_atom;
        soc = soc.max(t.max_soc);
    }

    for (i, c) in p.constraints.iter().enumerate() {
        match c {
            Constraint::EqZero(a) => {
                let t = affine_type(p, a, &format!("constraint #{i} (eq)"))?;
                if a.terms.is_empty() {
                    return Err(Rejection::new(
                        RejectKind::IllFormed,
                        format!("constraint #{i}: equality with no variables"),
                    ));
                }
                // Equality rows enter the public operator: coefficients must be public when any
                // secret variable participates (matrix publicity).
                if t.visibility.is_secret()
                    && a.terms.iter().any(|(cf, _)| cf.visibility().is_secret())
                {
                    return Err(Rejection::new(
                        RejectKind::PrivateMatrixTimesSecretVariable,
                        format!("constraint #{i}: private coefficient in a coupling row"),
                    ));
                }
                vis = vis.join(t.visibility);
            }
            Constraint::LeZero(e) => {
                let t = expr_type(p, e, &format!("constraint #{i} (le)"))?;
                if p.phase.is_optimizer()
                    && !matches!(t.curvature, Curvature::Affine | Curvature::Convex)
                {
                    return Err(Rejection::new(
                        RejectKind::NonConvexComposition,
                        format!(
                            "constraint #{i}: g ≤ 0 with {:?} g in an optimizer phase",
                            t.curvature
                        ),
                    ));
                }
                vis = vis.join(t.visibility);
                fhe &= t.fhe_tractable;
                cert |= t.has_cert_atom;
                soc = soc.max(t.max_soc);
            }
            Constraint::Box { var, lo, hi } => {
                p.visibility_of(*var)?;
                if lo > hi {
                    return Err(Rejection::new(
                        RejectKind::IllFormed,
                        format!("constraint #{i}: box lo > hi"),
                    ));
                }
            }
            Constraint::Complementarity(x, y) => {
                return Err(Rejection::new(
                    RejectKind::Complementarity,
                    format!(
                        "constraint #{i}: x·y = 0 on ('{}','{}') breaks the continuous regime",
                        p.vars.get(*x).map(|d| d.name.as_str()).unwrap_or("?"),
                        p.vars.get(*y).map(|d| d.name.as_str()).unwrap_or("?"),
                    ),
                ));
            }
            Constraint::Disjunction(cs) => {
                return Err(Rejection::new(
                    RejectKind::ArbitraryDisjunction,
                    format!(
                        "constraint #{i}: {}-way disjunction; compile linkage through fill \
                         receipts / shared nullifiers, not LP binaries",
                        cs.len()
                    ),
                ));
            }
        }
    }

    let has_opened = p.vars.iter().any(|d| d.visibility == Visibility::Opened);
    Ok(Analysis {
        visibility: vis,
        fhe_tractable: fhe,
        has_cert_atom: cert,
        max_soc: soc,
        has_opened,
    })
}

/// Part 4: every variable has finite public bounds; T ≥ 1.
fn check_completeness(p: &Program) -> Result<(), Rejection> {
    for d in &p.vars {
        if d.lo > d.hi {
            return Err(Rejection::new(
                RejectKind::MissingPublicBounds,
                format!("variable '{}': lo > hi", d.name),
            ));
        }
        if d.lo == i64::MIN || d.hi == i64::MAX {
            return Err(Rejection::new(
                RejectKind::MissingPublicBounds,
                format!(
                    "variable '{}': unbounded (no public radius, no completeness bound)",
                    d.name
                ),
            ));
        }
    }
    if p.iterations == 0 {
        return Err(Rejection::new(
            RejectKind::MissingPublicBounds,
            "T = 0 iterations",
        ));
    }
    Ok(())
}

/// Part 6: build the manifest; reject leaks.
fn check_leakage(p: &Program, dims: usize, nnz: usize) -> Result<LeakageManifest, Rejection> {
    let mut facts = Vec::new();
    for &v in &p.publish {
        let d = p.vars.get(v).ok_or_else(|| {
            Rejection::new(RejectKind::IllFormed, format!("publish of undeclared #{v}"))
        })?;
        match d.visibility {
            Visibility::Public => facts.push(d.name.clone()),
            Visibility::Opened => {
                if p.phase == Phase::Settle {
                    facts.push(d.name.clone());
                } else {
                    return Err(Rejection::new(
                        RejectKind::LeakageViolation,
                        format!("'{}' is Opened; it may be published only at Settle", d.name),
                    ));
                }
            }
            Visibility::Committed => {
                return Err(Rejection::new(
                    RejectKind::LeakageViolation,
                    format!("'{}' is Committed; publishing it voids the tier", d.name),
                ));
            }
        }
    }
    let precision_bits = 63 - (p.plaintext_modulus.max(2) - 1).leading_zeros();
    Ok(LeakageManifest {
        dims,
        nnz_a: nnz,
        iterations: p.iterations,
        precision_bits,
        public_facts: facts,
    })
}

/// Assemble the PUBLIC d×d step operator `A = P + EᵀE`:
/// * `P` from public-coefficient `Square` terms in the objective (Gram of each row),
/// * `EᵀE` from affine equality rows (the penalty / normal form of the coupling).
/// All arithmetic checked — assembly overflow is a part-5 rejection.
fn assemble_matrix(p: &Program) -> Result<Vec<Vec<i64>>, Rejection> {
    let d = p.vars.len();
    let mut a = vec![vec![0i64; d]; d];
    let overflow = || {
        Rejection::new(
            RejectKind::WindowOverflow,
            "i64 overflow assembling the step operator",
        )
    };

    let mut rows: Vec<Vec<(i64, VarId)>> = Vec::new();
    fn square_rows(e: &Expr, out: &mut Vec<Vec<(i64, VarId)>>) {
        match e {
            Expr::Square(af) => out.push(
                af.terms
                    .iter()
                    .filter_map(|(c, v)| match c {
                        Coeff::Public(k) => Some((*k, *v)),
                        _ => None, // secret coeffs already rejected by the walk
                    })
                    .collect(),
            ),
            Expr::Sum(es) => es.iter().for_each(|e| square_rows(e, out)),
            Expr::Neg(inner) => square_rows(inner, out),
            Expr::Mul(l, r) => {
                // Only public-constant scaling survives the walk here; scaling does not change
                // the SUPPORT of the operator, and magnitudes re-enter via the window analysis.
                square_rows(l, out);
                square_rows(r, out);
            }
            _ => {}
        }
    }
    if let Some(obj) = &p.objective {
        square_rows(&obj.expr, &mut rows);
    }
    for c in &p.constraints {
        if let Constraint::EqZero(af) = c {
            rows.push(
                af.terms
                    .iter()
                    .filter_map(|(c, v)| match c {
                        Coeff::Public(k) => Some((*k, *v)),
                        _ => None,
                    })
                    .collect(),
            );
        }
    }

    for row in &rows {
        for &(ci, vi) in row {
            for &(cj, vj) in row {
                let prod = ci.checked_mul(cj).ok_or_else(overflow)?;
                a[vi][vj] = a[vi][vj].checked_add(prod).ok_or_else(overflow)?;
            }
        }
    }
    Ok(a)
}

/// The six-part admissibility judgement: admissible IFF it compiles + passes the resource
/// manifest. Returns the tier the program is well-typed at (Tier0 iff FHE-tractable, ...), or a
/// NAMED rejection (the reject-list).
pub fn admissible(p: &Program) -> Result<Tier, Rejection> {
    // The theorem shape, literally: admissible(P) ⟺ compile(P) succeeds.
    compile(p).map(|spec| spec.tier)
}

pub fn compile(p: &Program) -> Result<ClearingSpec, Rejection> {
    // Part 1 & 2 — semantic form, three-axis typing, reject-list, certificate atoms.
    let analysis = analyze(p)?;
    let trigger_depth = check_triggers(p)?;

    // Part 4 — conditional completeness (public radius, T ≥ 1).
    check_completeness(p)?;

    // Part 3 — the resource manifest.
    let d = p.vars.len();
    if d > MAX_DIM {
        return Err(Rejection::new(
            RejectKind::ResourceBudgetExceeded,
            format!("{d} variables > MAX_DIM = {MAX_DIM}"),
        ));
    }
    if p.iterations > MAX_ITERATIONS {
        return Err(Rejection::new(
            RejectKind::ResourceBudgetExceeded,
            format!("T = {} > MAX_ITERATIONS = {MAX_ITERATIONS}", p.iterations),
        ));
    }
    if trigger_depth > MAX_TRIGGER_DEPTH {
        return Err(Rejection::new(
            RejectKind::ResourceBudgetExceeded,
            format!("trigger depth {trigger_depth} > k_max = {MAX_TRIGGER_DEPTH}"),
        ));
    }
    if analysis.max_soc > MAX_SOC_BLOCK {
        return Err(Rejection::new(
            RejectKind::ResourceBudgetExceeded,
            format!(
                "SOC block of {} > MAX_SOC_BLOCK = {MAX_SOC_BLOCK}",
                analysis.max_soc
            ),
        ));
    }

    // Assemble the public operator.
    let a = assemble_matrix(p)?;
    let nnz = a.iter().flatten().filter(|&&x| x != 0).count();
    if nnz > MAX_NNZ {
        return Err(Rejection::new(
            RejectKind::ResourceBudgetExceeded,
            format!("nnz(A) = {nnz} > MAX_NNZ = {MAX_NNZ}"),
        ));
    }

    // Step size: τ = 1/‖A‖∞ (τ_num = 1), so ‖τA‖∞ ≤ 1 and the scaled step contracts.
    let inf_norm: u128 = a
        .iter()
        .map(|row| {
            row.iter()
                .map(|&x| i128::from(x).unsigned_abs())
                .sum::<u128>()
        })
        .max()
        .unwrap_or(0);
    let tau_den = u64::try_from(inf_norm.max(1)).map_err(|_| {
        Rejection::new(
            RejectKind::WindowOverflow,
            "‖A‖∞ exceeds u64 (step size undefined)",
        )
    })?;
    let tau_num = 1u64;

    // Prox clamp: the hull of explicit boxes, else of the variable bounds.
    let boxes: Vec<(i64, i64)> = p
        .constraints
        .iter()
        .filter_map(|c| match c {
            Constraint::Box { lo, hi, .. } => Some((*lo, *hi)),
            _ => None,
        })
        .collect();
    let (prox_lo, prox_hi) = if boxes.is_empty() {
        (
            p.vars.iter().map(|v| v.lo).min().unwrap_or(0),
            p.vars.iter().map(|v| v.hi).max().unwrap_or(0),
        )
    } else {
        (
            boxes.iter().map(|b| b.0).min().unwrap(),
            boxes.iter().map(|b| b.1).max().unwrap(),
        )
    };

    // Part 5 — static no-wrap: the engine computes w_i = τ_den·x_i − τ_num·Σ_j A_ij·x_j on the
    // τ_den-scaled lattice. Worst case |w_i| ≤ τ_den·X + ‖A‖∞·X ≤ 2·τ_den·X where X is the
    // largest bound magnitude. Certify it fits the centered window (t−1)/2.
    let x_mag: u128 = p
        .vars
        .iter()
        .map(|v| {
            i128::from(v.lo)
                .unsigned_abs()
                .max(i128::from(v.hi).unsigned_abs())
        })
        .max()
        .unwrap_or(0)
        .max(i128::from(prox_lo).unsigned_abs())
        .max(i128::from(prox_hi).unsigned_abs());
    let worst = 2u128 * u128::from(tau_den) * x_mag;
    let half_window = u128::from((p.plaintext_modulus.max(3) - 1) / 2);
    if worst > half_window {
        return Err(Rejection::new(
            RejectKind::WindowOverflow,
            format!(
                "scaled step worst case {worst} exceeds the centered window {half_window} \
                 (t = {}); shrink bounds or the operator",
                p.plaintext_modulus
            ),
        ));
    }

    // Part 6 — the leakage manifest.
    let leakage_manifest = check_leakage(p, d, nnz)?;

    // Tier typing (visibility × tractability):
    //   all-public                → Tier2Open
    //   secret + FHE-tractable    → Tier0Dark  (affine steps w/ public operator + box prox +
    //                               ≤ k_max private trigger layers: the cheap FHE class)
    //   secret + cert-side cones,
    //   cert atoms, or Opened     → Tier1Shielded
    let any_secret =
        analysis.visibility.is_secret() || p.vars.iter().any(|v| v.visibility.is_secret());
    let tier = if !any_secret {
        Tier::Tier2Open
    } else if analysis.fhe_tractable && !analysis.has_cert_atom && !analysis.has_opened {
        Tier::Tier0Dark
    } else {
        Tier::Tier1Shielded
    };

    Ok(ClearingSpec {
        a,
        tier,
        leakage_manifest,
        tau_num,
        tau_den,
        prox_lo,
        prox_hi,
        iterations: p.iterations,
        plaintext_modulus: p.plaintext_modulus,
    })
}

// ---------------------------------------------------------------------------
// Tests — the reject-list BITES (each named), and admissible programs emit
// engine-consumable specs.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// A 2-asset committed portfolio rebalance: min x² + y² s.t. x + y = 0, boxed. The canonical
    /// Tier0 program (public operator, committed data, box prox).
    fn rebalance(vis: Visibility) -> Program {
        let mut p = Program::new(Phase::Clear);
        let x = p.var("x", vis, -100, 100);
        let y = p.var("y", vis, -100, 100);
        p.minimize(Expr::Sum(vec![
            Expr::Square(AffineExpr::var(x)),
            Expr::Square(AffineExpr::var(y)),
        ]));
        p.subject_to(Constraint::EqZero(
            AffineExpr::var(x).term(Coeff::Public(1), y),
        ));
        p.subject_to(Constraint::Box {
            var: x,
            lo: -100,
            hi: 100,
        });
        p.subject_to(Constraint::Box {
            var: y,
            lo: -100,
            hi: 100,
        });
        p.with_iterations(4);
        p
    }

    fn kind(r: &Result<Tier, Rejection>) -> RejectKind {
        r.as_ref()
            .unwrap_err()
            .kind()
            .expect("rejection carries a named kind")
    }

    // ---- (a) private-matrix × secret-variable REJECTS, with the NAMED rejection ----
    #[test]
    fn private_matrix_times_secret_variable_rejects() {
        let mut p = Program::new(Phase::Clear);
        let x = p.var("x", Visibility::Committed, -10, 10);
        // A committed coefficient multiplying a committed variable: a hidden operator entry.
        p.minimize(Expr::Affine(
            AffineExpr::default().term(Coeff::Committed { abs_bound: 5 }, x),
        ));
        let r = admissible(&p);
        assert_eq!(kind(&r), RejectKind::PrivateMatrixTimesSecretVariable);
        // And compile rejects identically (admissible iff compiles).
        assert_eq!(
            compile(&p).unwrap_err().kind().unwrap(),
            RejectKind::PrivateMatrixTimesSecretVariable
        );
    }

    #[test]
    fn hidden_hessian_rejects() {
        // The committed coefficient INSIDE a square lands in P — also private-matrix.
        let mut p = Program::new(Phase::Clear);
        let x = p.var("x", Visibility::Public, -10, 10);
        p.minimize(Expr::Square(
            AffineExpr::default().term(Coeff::Committed { abs_bound: 3 }, x),
        ));
        assert_eq!(
            kind(&admissible(&p)),
            RejectKind::PrivateMatrixTimesSecretVariable
        );
    }

    // ---- (b) a binary decision inside the optimizer REJECTS; the SAME node at Settle types ----
    #[test]
    fn binary_decision_inside_optimizer_rejects() {
        let mut p = Program::new(Phase::Clear); // optimizer phase
        let x = p.var("fill", Visibility::Committed, 0, 1);
        p.minimize(Expr::BinaryDecision(x));
        assert_eq!(kind(&admissible(&p)), RejectKind::BinaryDecisionInOptimizer);
    }

    #[test]
    fn binary_decision_at_settle_is_admissible() {
        // The phase axis does real work: the SAME discrete node is fine at settlement
        // (one comparison at settle is Core).
        let mut p = Program::new(Phase::Settle);
        let x = p.var("fill", Visibility::Public, 0, 1);
        p.minimize(Expr::BinaryDecision(x));
        assert!(admissible(&p).is_ok(), "{:?}", admissible(&p));
    }

    // ---- (c) an affine public program COMPILES to a ClearingSpec at Tier2 ----
    #[test]
    fn affine_public_program_compiles_tier2() {
        let mut p = Program::new(Phase::Clear);
        let x = p.var("x", Visibility::Public, -50, 50);
        let y = p.var("y", Visibility::Public, -50, 50);
        p.minimize(Expr::Affine(AffineExpr::var(x).term(Coeff::Public(2), y)));
        p.subject_to(Constraint::EqZero(
            AffineExpr::var(x).term(Coeff::Public(1), y),
        ));
        p.publish_var(x);
        let spec = compile(&p).expect("affine public program must compile");
        assert_eq!(spec.tier, Tier::Tier2Open);
        // Well-formed for the engine: square d×d, valid τ, sane clamp, manifest dims.
        let d = 2;
        assert_eq!(spec.a.len(), d);
        assert!(spec.a.iter().all(|row| row.len() == d));
        assert!(spec.tau_den >= 1 && spec.tau_num == 1);
        assert!(spec.prox_lo <= spec.prox_hi);
        assert_eq!(spec.leakage_manifest.dims, d);
        assert_eq!(spec.leakage_manifest.iterations, spec.iterations);
        assert_eq!(spec.leakage_manifest.public_facts, vec!["x".to_string()]);
        // The equality row x + y = 0 contributes EᵀE = [[1,1],[1,1]].
        assert_eq!(spec.a, vec![vec![1, 1], vec![1, 1]]);
    }

    // ---- (d) a convex committed program compiles at Tier0/1 with the RIGHT tier ----
    #[test]
    fn convex_committed_box_prox_is_tier0() {
        let spec = compile(&rebalance(Visibility::Committed)).expect("rebalance must compile");
        assert_eq!(spec.tier, Tier::Tier0Dark);
        // P = 2I (two unit squares) + EᵀE = [[1,1],[1,1]] ⇒ A = [[2,1],[1,2]].
        assert_eq!(spec.a, vec![vec![2, 1], vec![1, 2]]);
        assert_eq!(spec.tau_den, 3); // ‖A‖∞ = 3
        assert_eq!((spec.prox_lo, spec.prox_hi), (-100, 100));
        assert_eq!(spec.iterations, 4);
    }

    #[test]
    fn convex_committed_soc_is_tier1() {
        let mut p = Program::new(Phase::Clear);
        let x = p.var("x", Visibility::Committed, -100, 100);
        let y = p.var("y", Visibility::Committed, -100, 100);
        // Variance-swap-shaped: minimize x²+y² with a small SOC epigraph constraint.
        p.minimize(Expr::Sum(vec![
            Expr::Square(AffineExpr::var(x)),
            Expr::Square(AffineExpr::var(y)),
        ]));
        p.subject_to(Constraint::LeZero(Expr::Sum(vec![
            Expr::SocNorm(vec![AffineExpr::var(x), AffineExpr::var(y)]),
            Expr::Affine(AffineExpr::constant(-50)),
        ])));
        let spec = compile(&p).expect("SOC committed program must compile");
        assert_eq!(spec.tier, Tier::Tier1Shielded);
    }

    #[test]
    fn opened_visibility_forces_tier1() {
        let spec = compile(&rebalance(Visibility::Opened)).unwrap();
        assert_eq!(spec.tier, Tier::Tier1Shielded);
    }

    // ---- the rest of the reject-list, each NAMED ----
    #[test]
    fn secret_times_secret_rejects_but_cert_atom_is_the_exception() {
        let mut p = Program::new(Phase::Settle); // NOT an optimizer phase: isolate the secrecy rule
        let x = p.var("x", Visibility::Committed, -10, 10);
        let y = p.var("y", Visibility::Committed, -10, 10);
        p.minimize(Expr::Mul(Box::new(Expr::var(x)), Box::new(Expr::var(y))));
        assert_eq!(kind(&admissible(&p)), RejectKind::SecretTimesSecret);

        // The exception: the same pairing as a certificate atom is admissible.
        let mut q = Program::new(Phase::Settle);
        let x = q.var("x", Visibility::Committed, -10, 10);
        let y = q.var("y", Visibility::Committed, -10, 10);
        q.minimize(Expr::CertGap {
            primal: AffineExpr::var(x),
            dual: AffineExpr::var(y),
        });
        let r = admissible(&q).expect("certificate atom is the admitted exception");
        assert_eq!(r, Tier::Tier1Shielded); // cert atoms are proof-layer, never Tier0-FHE
    }

    #[test]
    fn complementarity_rejects() {
        let mut p = rebalance(Visibility::Committed);
        p.subject_to(Constraint::Complementarity(0, 1));
        assert_eq!(kind(&admissible(&p)), RejectKind::Complementarity);
    }

    #[test]
    fn arbitrary_disjunction_rejects() {
        let mut p = rebalance(Visibility::Committed);
        p.subject_to(Constraint::Disjunction(vec![
            Constraint::Box {
                var: 0,
                lo: 0,
                hi: 0,
            },
            Constraint::Box {
                var: 1,
                lo: 0,
                hi: 0,
            },
        ]));
        assert_eq!(kind(&admissible(&p)), RejectKind::ArbitraryDisjunction);
    }

    #[test]
    fn secret_indexed_memory_rejects_public_index_fine() {
        let mut p = Program::new(Phase::Settle);
        let i = p.var("i", Visibility::Committed, 0, 3);
        p.minimize(Expr::IndexBy {
            table: vec![1, 2, 3, 4],
            index: i,
        });
        assert_eq!(kind(&admissible(&p)), RejectKind::SecretIndexedMemory);

        let mut q = Program::new(Phase::Settle);
        let i = q.var("i", Visibility::Public, 0, 3);
        q.minimize(Expr::IndexBy {
            table: vec![1, 2, 3, 4],
            index: i,
        });
        assert!(admissible(&q).is_ok());
    }

    #[test]
    fn unlagged_reflexive_trigger_rejects() {
        let mut p = rebalance(Visibility::Committed);
        let mark = p.var("mark", Visibility::Public, 0, 1000);
        p.trigger(Trigger {
            guard: AffineExpr::var(mark), // references a mark with lag 0: reflexive book
            lag_epochs: 0,
            activates: 0,
            parent: None,
        });
        assert_eq!(kind(&admissible(&p)), RejectKind::UnboundedTriggerRecursion);
    }

    #[test]
    fn cyclic_trigger_chain_rejects_and_lagged_chain_admits() {
        let mut p = rebalance(Visibility::Committed);
        let mark = p.var("mark", Visibility::Public, 0, 1000);
        let t0 = p.trigger(Trigger {
            guard: AffineExpr::var(mark),
            lag_epochs: 1,
            activates: 0,
            parent: None,
        });
        // A lagged single trigger is FINE (the cheap class allows k_max private trigger layers).
        assert!(admissible(&p).is_ok(), "{:?}", admissible(&p));

        // Now close the cycle: t0 and t1 become each other's parent.
        let t1 = p.trigger(Trigger {
            guard: AffineExpr::var(mark),
            lag_epochs: 1,
            activates: 1,
            parent: Some(t0),
        });
        p.triggers[t0].parent = Some(t1);
        assert_eq!(kind(&admissible(&p)), RejectKind::UnboundedTriggerRecursion);
    }

    #[test]
    fn exp_cone_and_psd_reject_as_unapproved() {
        let mut p = Program::new(Phase::Clear);
        let x = p.var("x", Visibility::Public, -10, 10);
        p.minimize(Expr::Exp(AffineExpr::var(x)));
        assert_eq!(kind(&admissible(&p)), RejectKind::UnapprovedCone);

        let mut q = Program::new(Phase::Clear);
        let y = q.var("q", Visibility::Public, -10, 10);
        q.minimize(Expr::LogSumExp(vec![AffineExpr::var(y)]));
        assert_eq!(kind(&admissible(&q)), RejectKind::UnapprovedCone);

        let mut r = Program::new(Phase::Clear);
        r.var("z", Visibility::Public, -10, 10);
        r.minimize(Expr::PsdQuadForm { dim: 64 });
        assert_eq!(kind(&admissible(&r)), RejectKind::UnapprovedCone);
    }

    #[test]
    fn nonconvex_composition_rejects_in_optimizer() {
        let mut p = Program::new(Phase::Clear);
        let x = p.var("x", Visibility::Public, -10, 10);
        // Maximize a convex square in an optimizer phase: not typable.
        p.maximize(Expr::Square(AffineExpr::var(x)));
        assert_eq!(kind(&admissible(&p)), RejectKind::NonConvexComposition);
    }

    #[test]
    fn missing_bounds_reject() {
        let mut p = Program::new(Phase::Clear);
        let x = p.var("x", Visibility::Committed, i64::MIN, i64::MAX);
        p.minimize(Expr::Square(AffineExpr::var(x)));
        assert_eq!(kind(&admissible(&p)), RejectKind::MissingPublicBounds);
    }

    #[test]
    fn window_overflow_rejects_statically() {
        // Bounds so large the τ-scaled step cannot fit the ~2^20 window: part 5 fails CLOSED
        // at compile time, before any ciphertext exists.
        let mut p = Program::new(Phase::Clear);
        let x = p.var("x", Visibility::Committed, -(1 << 40), 1 << 40);
        p.minimize(Expr::Square(AffineExpr::var(x)));
        assert_eq!(kind(&admissible(&p)), RejectKind::WindowOverflow);
    }

    #[test]
    fn leakage_violation_rejects_committed_publish() {
        let mut p = rebalance(Visibility::Committed);
        p.publish_var(0); // publishing a Committed var voids the tier
        assert_eq!(kind(&admissible(&p)), RejectKind::LeakageViolation);

        // Opened publish outside Settle also rejects…
        let mut q = rebalance(Visibility::Opened);
        q.publish_var(0);
        assert_eq!(kind(&admissible(&q)), RejectKind::LeakageViolation);
        // …but at Settle it is the deliberate reveal.
        q.phase = Phase::Settle;
        assert!(admissible(&q).is_ok(), "{:?}", admissible(&q));
    }

    #[test]
    fn resource_budget_bites() {
        let mut p = rebalance(Visibility::Committed);
        p.with_iterations(MAX_ITERATIONS + 1);
        assert_eq!(kind(&admissible(&p)), RejectKind::ResourceBudgetExceeded);
    }

    // ---- non-vacuity: admissible ⟺ compiles, and the spec is engine-consumable ----
    #[test]
    fn admissible_iff_compiles_on_a_sample_family() {
        let mut samples: Vec<Program> = vec![
            rebalance(Visibility::Committed),
            rebalance(Visibility::Public),
            rebalance(Visibility::Opened),
        ];
        let mut bad = rebalance(Visibility::Committed);
        bad.subject_to(Constraint::Complementarity(0, 1));
        samples.push(bad);
        for p in &samples {
            let a = admissible(p);
            let c = compile(p);
            assert_eq!(a.is_ok(), c.is_ok());
            if let (Ok(t), Ok(spec)) = (&a, &c) {
                assert_eq!(*t, spec.tier);
            }
        }
    }

    #[test]
    fn spec_feeds_the_convex_engine_shape() {
        // The emitted spec must be DIRECTLY consumable by convex_engine::convex_solve:
        // PublicLinearStep wants a square d×d matrix and a nonzero τ_den; the runtime window
        // check must accept what part 5 certified (same centered-window formula).
        use crate::convex_step::{centered_window, PublicLinearStep};
        let spec = compile(&rebalance(Visibility::Committed)).unwrap();
        let step = PublicLinearStep {
            a: spec.a.clone(),
            tau_num: spec.tau_num,
            tau_den: spec.tau_den,
        };
        let d = spec.leakage_manifest.dims;
        assert_eq!(step.a.len(), d);
        assert!(step.a.iter().all(|row| row.len() == d));
        assert!(step.tau_den > 0);
        // Part-5 static certificate uses exactly the engine's window.
        let worst = 2u128 * u128::from(spec.tau_den) * 100;
        assert!(worst <= u128::from(centered_window(spec.plaintext_modulus)));
    }
}
