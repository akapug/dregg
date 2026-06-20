//! The two-regime classifier — which conflicts are real, which are illusory.
//!
//! dregg's refinement of Pijul (DOCUMENT-LANGUAGE.md §2.4) is the **two-regime
//! split**, already proved on the value side (`Confluence.lean`):
//!
//! - **The I-confluent / monotone fragment.** Grow-only content, append-only
//!   spans, monotone tombstones. Two branches *always* glue by union; no
//!   conflict can arise (the union is unconditionally a valid state). This is
//!   the prose fragment, and the common case — most concurrent edits touch
//!   disjoint spans and merge silently.
//!
//! - **The conservation / authority fragment.** A single-valued field (a
//!   canonical title, a pinned authority, a conserved quantity) is *not*
//!   grow-only; two branches' union may carry clashing values, which is a
//!   **real** conflict that a resolution patch (possibly a joint-turn) must
//!   collapse.
//!
//! A *prose antichain* (two concurrent inserts) is a [`Regime::Prose`] conflict:
//! legible, resolvable by either author, never blocking the rest of the doc. A
//! *field clash* is a [`Regime::Field`] conflict: it sits at the non-monotone
//! boundary and is the document-language reading of the same wall that forces
//! consensus in the value layer. The classifier is the static gate that answers
//! "is this a real conflict or an illusory one" per region.

/// The regime a conflict belongs to — the answer to "is this real?".
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Regime {
    /// A prose antichain (two concurrent inserts at one position). Resolvable by
    /// ordering or choosing; legible; never blocks the rest of the document.
    /// In the I-confluent fragment this is the *only* kind that arises, and even
    /// it is a benign state rather than a failure.
    Prose,
    /// A single-valued field clash (conservation / authority). The non-monotone
    /// boundary: two branches assigned different values to one canonical field.
    /// A resolution must *choose* (or escalate to a joint-turn / settlement).
    Field,
}

impl Regime {
    /// Whether resolving this conflict may require consensus / a joint decision
    /// (true for a [`Regime::Field`] authority/conservation clash) versus being
    /// resolvable unilaterally by a region author (a [`Regime::Prose`] antichain).
    pub fn needs_consensus(self) -> bool {
        matches!(self, Regime::Field)
    }

    /// A short human label for the conflict view.
    pub fn label(self) -> &'static str {
        match self {
            Regime::Prose => "prose",
            Regime::Field => "field",
        }
    }
}
