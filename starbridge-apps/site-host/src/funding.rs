//! The funding gate — a publish is admitted only against a resident, non-lapsed
//! hosting lease, never synthesized from the request.
//!
//! This is the IMPROVEMENT over a bare "does the chain fund this?" shim: the gate is
//! backed by the resident [`hosted_lease::HostedLease`] — a real durable-execution
//! lease whose rent is metered by a [`StandingObligation`](dregg_cell) (or the fused
//! prepaid meter) and which LAPSES on non-payment. A publish for an owner with no
//! lease, or a lapsed lease, fails closed with a `402` — but instead of a dead end,
//! the refusal carries an **x402-style topup hint** ([`TopupHint`]) naming the lease,
//! the rent asset, a suggested amount, and the retry endpoint, so an agent client can
//! auto-fund the lease and re-POST the publish. No free hosting; a self-healing pay
//! loop.

use std::collections::BTreeMap;
use std::sync::Mutex;

use hosted_lease::HostedLease;
use serde::{Deserialize, Serialize};

/// The suggested budget (in the lease's rent asset) a single publish top-up should
/// cover — a small fixed control-plane cost (write the content cell + seal the
/// receipt), not a per-byte charge (serving bandwidth is metered on the read path).
pub const PUBLISH_TOPUP_UNITS: u64 = 1;

/// Why the funding gate refused — the two x402 topup shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TopupReason {
    /// A hosting lease exists for the owner but has LAPSED (rent unpaid) — top it up
    /// to reinstate and retry.
    Lapsed,
    /// No hosting lease covers the owner — open/fund one and retry.
    Unfunded,
}

/// An x402-style payment requirement returned on a `402`: everything an agent client
/// needs to auto-fund the owner's hosting lease and retry the publish.
///
/// Rendered into the `402` response as a JSON body plus an `X-Payment-Required`
/// header, so a machine client reads the requirement, tops up, and re-POSTs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TopupHint {
    /// The payment scheme identifier (`site-host-lease-topup`).
    pub scheme: String,
    /// Why funding was refused.
    pub reason: TopupReason,
    /// The lease cell to top up (hex), when a lease exists for the owner.
    pub lease: Option<String>,
    /// The rent asset the top-up is denominated in (hex), when known.
    pub asset: Option<String>,
    /// A suggested top-up amount (>= one rent period) in the rent asset.
    pub amount: u64,
    /// Where a client funds the lease (a hint the host advertises).
    pub topup_endpoint: String,
    /// The publish endpoint to retry once funded.
    pub retry: String,
    /// A human-readable explanation.
    pub detail: String,
}

impl TopupHint {
    /// The scheme identifier used by this crate's topup hints.
    pub const SCHEME: &'static str = "site-host-lease-topup";
}

/// The funding gate's decision for a publish.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FundingDecision {
    /// A resident, non-lapsed lease covers the publish — admit it.
    Covered,
    /// Refused; carries the x402 topup hint the `402` returns.
    Denied(TopupHint),
}

/// The funding gate a [`crate::publish::SitePublishHandler`] consults: given the
/// authenticated owner subject, decide whether a publish is funded.
///
/// The `retry` and `topup_endpoint` are passed in by the handler (it knows the
/// concrete request path + the host's funding endpoint) so an implementation stays
/// decoupled from routing.
pub trait PublishFunding: Send + Sync {
    /// Decide whether `owner`'s publish is funded. `retry` is the publish path to
    /// echo into a topup hint; `topup_endpoint` is where the client funds a lease.
    fn authorize_publish(&self, owner: &str, retry: &str, topup_endpoint: &str) -> FundingDecision;
}

/// The resident lease-backed funding gate: a book of hosting leases keyed by owner
/// subject, each a real [`hosted_lease::HostedLease`]. A publish is covered iff the
/// owner has a lease in the book that has not lapsed; otherwise the refusal carries a
/// topup hint built from the lease's own terms.
#[derive(Default)]
pub struct LeaseBook {
    leases: Mutex<BTreeMap<String, HostedLease>>,
}

impl LeaseBook {
    /// An empty book (every owner is unfunded until a lease is bound).
    pub fn new() -> LeaseBook {
        LeaseBook::default()
    }

    /// Bind `owner`'s hosting lease into the book (replacing any prior one).
    pub fn bind(&self, owner: impl Into<String>, lease: HostedLease) {
        self.leases
            .lock()
            .expect("lease book poisoned")
            .insert(owner.into(), lease);
    }

    /// Whether `owner` has a bound lease (lapsed or not).
    pub fn has_lease(&self, owner: &str) -> bool {
        self.leases
            .lock()
            .expect("lease book poisoned")
            .contains_key(owner)
    }

    /// Whether `owner`'s bound lease has lapsed (`false` if no lease / not lapsed).
    pub fn is_lapsed(&self, owner: &str) -> bool {
        self.leases
            .lock()
            .expect("lease book poisoned")
            .get(owner)
            .map(|l| l.is_lapsed())
            .unwrap_or(false)
    }
}

impl PublishFunding for LeaseBook {
    fn authorize_publish(&self, owner: &str, retry: &str, topup_endpoint: &str) -> FundingDecision {
        let book = self.leases.lock().expect("lease book poisoned");
        match book.get(owner) {
            None => FundingDecision::Denied(TopupHint {
                scheme: TopupHint::SCHEME.to_string(),
                reason: TopupReason::Unfunded,
                lease: None,
                asset: None,
                amount: PUBLISH_TOPUP_UNITS,
                topup_endpoint: topup_endpoint.to_string(),
                retry: retry.to_string(),
                detail: format!("no hosting lease covers `{owner}`: open and fund one, then retry"),
            }),
            Some(lease) if lease.is_lapsed() => {
                let terms = lease.terms();
                let rent = terms.rent_per_period.max(PUBLISH_TOPUP_UNITS);
                FundingDecision::Denied(TopupHint {
                    scheme: TopupHint::SCHEME.to_string(),
                    reason: TopupReason::Lapsed,
                    lease: Some(hex32(terms.lease.as_bytes())),
                    asset: Some(hex32(terms.asset.as_bytes())),
                    amount: rent,
                    topup_endpoint: topup_endpoint.to_string(),
                    retry: retry.to_string(),
                    detail: format!(
                        "the hosting lease for `{owner}` has lapsed (rent unpaid): top up ~{rent} and retry"
                    ),
                })
            }
            Some(_) => FundingDecision::Covered,
        }
    }
}

/// Lower-hex a 32-byte id.
fn hex32(b: &[u8; 32]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(64);
    for x in b {
        let _ = write!(s, "{x:02x}");
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::Cell;
    use dregg_types::CellId;
    use hosted_lease::{LeaseTerms, field_from_u64};

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    fn lease_cell() -> Cell {
        Cell::with_balance([7u8; 32], [9u8; 32], 10_000)
    }

    // provider=2, lease=7, asset=9; rent 100 every 50 blocks from block 1000.
    fn terms() -> LeaseTerms {
        LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0)
    }

    #[test]
    fn a_bound_non_lapsed_lease_covers_the_publish() {
        let book = LeaseBook::new();
        let lease = HostedLease::open(lease_cell(), terms(), field_from_u64(0)).unwrap();
        book.bind("agent:alice", lease);
        assert_eq!(
            book.authorize_publish("agent:alice", "/v1/sites/blog/publish", "/v1/fund"),
            FundingDecision::Covered
        );
    }

    #[test]
    fn an_unfunded_owner_gets_an_unfunded_topup_hint() {
        let book = LeaseBook::new();
        let d = book.authorize_publish("agent:nobody", "/v1/sites/blog/publish", "/v1/fund");
        match d {
            FundingDecision::Denied(hint) => {
                assert_eq!(hint.reason, TopupReason::Unfunded);
                assert!(hint.lease.is_none());
                assert_eq!(hint.retry, "/v1/sites/blog/publish");
                assert_eq!(hint.topup_endpoint, "/v1/fund");
                assert_eq!(hint.scheme, TopupHint::SCHEME);
            }
            other => panic!("expected Denied, got {other:?}"),
        }
    }

    #[test]
    fn a_lapsed_lease_gets_a_lapsed_topup_hint_naming_the_lease() {
        let book = LeaseBook::new();
        let mut lease = HostedLease::open(lease_cell(), terms(), field_from_u64(0)).unwrap();
        // Run the clock past the next due block with no payment -> lapse.
        assert!(lease.lapse_if_behind(1100).unwrap());
        assert!(lease.is_lapsed());
        book.bind("agent:alice", lease);

        let d = book.authorize_publish("agent:alice", "/v1/sites/blog/publish", "/v1/fund");
        match d {
            FundingDecision::Denied(hint) => {
                assert_eq!(hint.reason, TopupReason::Lapsed);
                assert_eq!(hint.lease.as_deref(), Some(&*hex32(&[7u8; 32])));
                assert_eq!(hint.asset.as_deref(), Some(&*hex32(&[9u8; 32])));
                assert_eq!(hint.amount, 100, "the lease's own rent");
            }
            other => panic!("expected Denied, got {other:?}"),
        }
    }
}
