//! `fhIR` — the typed product/order DSL (the factory). FULLY DISJOINT from the crypto.
//!
//! Interface fixed in `docs/deos/FHEGG-PROTOTYPE-INTERFACES.md` §4, grammar from
//! `docs/deos/FHEGG-PRODUCT-ORDER-FRONTIER.md`. OWNED by the `fhir` lane. Three type axes; the reject-list;
//! `admissible`/`compile`. No crypto dependency — it emits a `ClearingSpec` the engine consumes.
#![allow(dead_code, unused_variables)]

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Committed,
    Opened,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Curvature {
    Affine,
    Convex,
    Concave,
    Discrete,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tier {
    Tier0Dark,
    Tier1Shielded,
    Tier2Open,
}

/// The typed AST (affine/convex/constraint/trigger/order/program) — the `fhir` lane defines the full shape.
pub struct Program;
/// What the engine consumes: the public matrix, tier, and a leakage manifest.
pub struct ClearingSpec {
    pub a: Vec<Vec<i64>>,
    pub tier: Tier,
}
/// A NAMED rejection from the reject-list (e.g. private-matrix × secret-variable).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rejection(pub String);

/// The six-part admissibility judgement: admissible IFF it compiles + passes the resource manifest.
pub fn admissible(p: &Program) -> Result<Tier, Rejection> {
    todo!("fhir lane: the typed admissibility judgement + reject-list")
}
pub fn compile(p: &Program) -> Result<ClearingSpec, Rejection> {
    todo!("fhir lane: compile to a ClearingSpec")
}
