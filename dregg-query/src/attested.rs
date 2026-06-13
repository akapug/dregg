//! Q2 — the certificate-carrying answer: query results that PROVE they
//! omitted nothing.
//!
//! The shape of the guarantee (the model: `Dregg2.Lightclient.MMR`
//! `server_cannot_omit_position`): the node commits its receipt log under an
//! MMR root; a query answer ships with a [`RangeCertificate`] — the range
//! opening of the receipt positions it was computed FROM. The verifier:
//!
//! 1. checks the opening against a TRUSTED root (obtained out-of-band today;
//!    pinned by `recStateCommit` once the `CommitBindsMMR` weld lands with
//!    THE ROTATION — at which point one light-client check pins it for the
//!    whole history, `light_client_position_non_omission`);
//! 2. concludes the receipt slice is EXACTLY positions `[lo, hi]` of the
//!    genuine log — no receipt hidden, none forged, none reordered;
//! 3. RE-DERIVES the answer: extracts the facts and re-runs the query
//!    locally. The server is not trusted for evaluation at all — the
//!    certificate makes the INPUT complete, recomputation makes the OUTPUT
//!    honest.
//!
//! What completeness means then splits on the CALM grade
//! ([`crate::classify`]):
//! - **Monotone** query: every returned row is FINAL — more receipts can only
//!   add rows, so "provably omitted nothing" holds unconditionally over the
//!   certified range.
//! - **FinalizedDependent** query: the rows are exact FOR THE CERTIFIED
//!   PREFIX — "fresh as of height `fresh_as_of`"; a later receipt (e.g. a
//!   revocation) may retract a row. The annotation travels with the answer.

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::classify::{classify, Classification};
use crate::fact::Height;
use crate::hexutil::serde_hex32;
use crate::mmr::{verify_range, MmrError, MmrHasher, RangeOpening};
use crate::query::{eval, Bindings, Query, QueryError};
use crate::receipt::{extract_facts, ReceiptError, ReceiptRecord};

/// The non-omission certificate for a receipt slice: the committed root the
/// server claims, the dense position range, and the range opening.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RangeCertificate {
    /// The MMR root of the receipt log this opening is against. The verifier
    /// compares it to a root it trusts — it is a CLAIM, not a proof, until
    /// matched.
    #[serde(with = "serde_hex32")]
    pub root: [u8; 32],
    /// First certified position (inclusive, dense `chain_index`).
    pub lo: u64,
    /// Last certified position (inclusive; clipped to the committed length).
    pub hi: u64,
    /// The positional range opening (peak frontier + per-slot paths).
    pub opening: RangeOpening,
}

/// A receipt slice with its non-omission certificate — the certified EDB.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestedSlice {
    pub receipts: Vec<ReceiptRecord>,
    pub cert: RangeCertificate,
}

#[derive(Debug, Error)]
pub enum AttestError {
    #[error("certificate root does not match the trusted root")]
    UntrustedRoot,
    #[error(transparent)]
    Mmr(#[from] MmrError),
    #[error(transparent)]
    Receipt(#[from] ReceiptError),
    #[error("slot {slot}: receipt chain_index {got} != certified dense position {want}")]
    DenseIndex { slot: usize, got: u64, want: u64 },
    #[error(transparent)]
    Query(#[from] QueryError),
    #[error("answer rows do not match local re-evaluation over the certified slice")]
    RowsMismatch,
    #[error("carried classification does not match the classifier's verdict")]
    ClassificationMismatch,
    #[error("carried fresh_as_of {got} != certified slice's height frontier {want}")]
    Freshness { got: Height, want: Height },
}

impl AttestedSlice {
    /// Verify the slice against a trusted root: the opening verifies
    /// (`RVerifies` — count + per-slot positional openings) with the
    /// receipts' own `receipt_hash` values as the opened leaves, and each
    /// receipt's `chain_index` IS its certified dense position. On success
    /// the slice is exactly positions `[lo, min(hi, len-1)]` of the genuine
    /// log. Returns the root-pinned log length.
    pub fn verify<H: MmrHasher>(&self, hasher: &H, trusted_root: &[u8; 32]) -> Result<u64, AttestError> {
        if &self.cert.root != trusted_root {
            return Err(AttestError::UntrustedRoot);
        }
        let mut values = Vec::with_capacity(self.receipts.len());
        for (slot, r) in self.receipts.iter().enumerate() {
            let want = self.cert.lo + slot as u64;
            if r.chain_index != want {
                return Err(AttestError::DenseIndex {
                    slot,
                    got: r.chain_index,
                    want,
                });
            }
            values.push(r.receipt_hash_bytes()?);
        }
        let len = verify_range(
            hasher,
            trusted_root,
            self.cert.lo,
            self.cert.hi,
            &values,
            &self.cert.opening,
        )?;
        Ok(len)
    }

    /// The height frontier of the slice — what a finalized-dependent answer
    /// is fresh as of.
    pub fn height_frontier(&self) -> Height {
        self.receipts.iter().map(|r| r.height).max().unwrap_or(0)
    }
}

/// **The certificate-carrying answer** — rows + the CALM annotation + the
/// freshness frontier + the certified EDB slice they were derived from.
/// Self-contained: [`AttestedAnswer::verify`] needs only a trusted root.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestedAnswer {
    /// The query the rows answer.
    pub query: Query,
    /// The answer rows (variable bindings, set semantics).
    pub rows: Vec<Bindings>,
    /// The CALM grade: monotone (rows final) vs finalized-dependent (rows
    /// correct as of `fresh_as_of` only).
    pub classification: Classification,
    /// The certified slice's height frontier.
    pub fresh_as_of: Height,
    /// The certified EDB: receipts + their non-omission certificate.
    pub slice: AttestedSlice,
}

/// Evaluate `query` over a certified slice, producing the attested answer.
/// (The producer side — the CLI / SDK / node all assemble answers through
/// this so the carried annotation can never drift from the classifier.)
pub fn answer(slice: AttestedSlice, query: Query) -> Result<AttestedAnswer, QueryError> {
    let base = extract_facts(&slice.receipts);
    let rows = eval(&base, &query)?;
    let classification = classify(&query);
    let fresh_as_of = slice.height_frontier();
    Ok(AttestedAnswer {
        query,
        rows,
        classification,
        fresh_as_of,
        slice,
    })
}

impl AttestedAnswer {
    /// Full verification against a trusted root:
    ///
    /// 1. the slice's non-omission certificate verifies (the input was the
    ///    EXACT receipt range — `server_cannot_omit_position`);
    /// 2. the rows equal a local re-evaluation over that certified input
    ///    (evaluation is recomputed, never trusted);
    /// 3. the carried classification and freshness frontier match recomputation.
    pub fn verify<H: MmrHasher>(
        &self,
        hasher: &H,
        trusted_root: &[u8; 32],
    ) -> Result<(), AttestError> {
        self.slice.verify(hasher, trusted_root)?;
        let base = extract_facts(&self.slice.receipts);
        let rows = eval(&base, &self.query)?;
        if rows != self.rows {
            return Err(AttestError::RowsMismatch);
        }
        if classify(&self.query) != self.classification {
            return Err(AttestError::ClassificationMismatch);
        }
        let want = self.slice.height_frontier();
        if self.fresh_as_of != want {
            return Err(AttestError::Freshness {
                got: self.fresh_as_of,
                want,
            });
        }
        Ok(())
    }
}
