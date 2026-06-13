//! The CALM coordination classifier — the query planner of
//! docs/EPISTEMIC-DATALOG.md, graded from day one.
//!
//! CALM (Hellerstein/Ameloot): a distributed computation is coordination-free
//! iff it is expressible in monotone Datalog. The proved instance on dregg's
//! side is `DreggCalculus.modality_price_monotone` ("grow-only ⇒
//! coordination-free"); this module is the per-query application of that
//! grading to the Q1 surface:
//!
//! - The EDB is append-only and height-stamped (monotone by construction).
//! - Positive atoms, joins, and filters are MONOTONE operators: once an
//!   answer row appears it never retracts as more receipts arrive. Such a
//!   query is answerable from ANY node's partial view and is cacheable —
//!   coordination-free.
//! - A NEGATED atom is the one non-monotone operator on this surface:
//!   "not revoked(Cap, _)" can flip an answer row from present to absent
//!   when a later receipt arrives. Its answer is correct only relative to a
//!   FINALIZED prefix — "this answer is only as fresh as height H" — the
//!   canonical case being negation-over-revocation.
//!
//! There is no third class: the Q1 surface has no aggregation and no
//! recursion, so monotone-vs-negation exhausts it.

use serde::{Deserialize, Serialize};

use crate::query::Query;

/// The coordination tier of a query under CALM.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CoordinationClass {
    /// Monotone: coordination-free, answerable from a partial view, every
    /// row final once produced. (CALM forward direction.)
    Monotone,
    /// Finalized-dependent: the answer is correct only as of a finalized
    /// height; rows may retract as later receipts arrive.
    FinalizedDependent,
}

/// The classifier verdict: the tier plus human-auditable reasons.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Classification {
    pub class: CoordinationClass,
    /// Why (one entry per non-monotone construct found; empty ⇒ monotone).
    pub reasons: Vec<String>,
}

impl Classification {
    pub fn is_monotone(&self) -> bool {
        self.class == CoordinationClass::Monotone
    }
}

/// Classify a query. Sound and complete FOR THIS SURFACE: negated atoms are
/// the only non-monotone operator a [`Query`] can contain (selections,
/// constants, joins, and comparisons over an append-only EDB all preserve
/// monotonicity), so the verdict is exact, not a heuristic.
pub fn classify(q: &Query) -> Classification {
    let mut reasons = Vec::new();
    for a in &q.negated {
        reasons.push(format!(
            "negated atom over {}: absence is not stable under append \
             (answer is only correct for a finalized prefix)",
            a.pred.name()
        ));
    }
    let class = if reasons.is_empty() {
        CoordinationClass::Monotone
    } else {
        CoordinationClass::FinalizedDependent
    };
    Classification { class, reasons }
}
