//! The funding gate: where a create proves its lease is **funded on-chain** — the
//! LEASE-1a fix.
//!
//! ## Why this exists (red-team LEASE-1a)
//!
//! The public create API used to *synthesize* a `funded: true` lease from the
//! caller's requested guest size (`Lease::funded(app, …, budget_derived_from_the_
//! request)`). The gateway then ran that self-asserted lease through the bridge's
//! shape gate — which only checks the `funded` bool + the terms, never real
//! funding. So `POST /v1/apps/x/machines` with a fabricated `memory_mb` minted a
//! big funded lease and ran free compute, no payment.
//!
//! A lease may only be treated as `funded` after a **verified on-chain read**
//! confirms the funding is real. This module is that gate: the gateway holds a
//! [`FundingSource`] — the chain's attestation of which leases are funded — and a
//! create is admitted only against a real funded lease the source attests, whose
//! on-chain reserve covers the request. Self-asserted funding is never trusted.
//!
//! - [`AttestedFunding`] — an in-memory snapshot of the funded leases a verified
//!   on-chain read attested (the leases MUST come from such a read, never from the
//!   request). Under `dregg-verify`,
//!   [`from_verified_source`](AttestedFunding::from_verified_source) builds it
//!   directly from the control plane's light-client-VERIFIED on-chain read
//!   (`VerifiedNodeLeaseSource`), so funded leases provably come from the chain.
//! - [`NodeFunding`] — reads funded leases live from a dregg node on each lookup:
//!   light-client-VERIFIED under `dregg-verify`, the node cell-API read (real, but
//!   node-trusted) otherwise. Either way the funding is read from the chain, never
//!   synthesized from the caller's request.

use dreggnet_bridge::{CapGrade, Lease};

/// Why a funding lookup could not authorize a create.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FundingError {
    /// No verified funding source is configured. The gateway fails **closed** — it
    /// will not admit work without a way to confirm real on-chain funding.
    NoSource,
    /// The verified on-chain read failed (transport / verification / decode). The
    /// gateway fails closed: a chain it cannot verify funds nothing.
    Read(String),
}

impl std::fmt::Display for FundingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FundingError::NoSource => write!(
                f,
                "no verified funding source configured: refusing to admit work without confirming real on-chain funding"
            ),
            FundingError::Read(why) => write!(f, "verified on-chain funding read failed: {why}"),
        }
    }
}

impl std::error::Error for FundingError {}

/// The chain's attestation of which leases are funded — the ONLY source of a
/// `funded` lease the gateway trusts.
///
/// An implementation MUST return only leases whose funding was confirmed by a real
/// on-chain read (a light-client-verified receipt-log read, or at minimum a live
/// node cell read). It must NEVER fabricate a funded lease from the caller's
/// request — that is exactly the LEASE-1a hole this trait closes.
pub trait FundingSource: Send + Sync {
    /// The funded, active leases the chain attests for `app` (the lessee boundary).
    /// Each carries its REAL on-chain reserve as `budget_units`.
    fn funded_leases(&self, app: &str) -> Result<Vec<Lease>, FundingError>;

    /// Authorize a create: find a funded lease this source attests for `app` whose
    /// on-chain reserve covers `need_budget` and whose granted cap-grade meets the
    /// requested isolation `floor`. Returns the REAL on-chain lease (with its real
    /// budget), or `None` if the chain funds no lease covering the request — in
    /// which case the create must be refused (no free compute).
    fn authorize(
        &self,
        app: &str,
        floor: CapGrade,
        need_budget: i64,
    ) -> Result<Option<Lease>, FundingError> {
        let leases = self.funded_leases(app)?;
        Ok(leases.into_iter().find(|l| {
            l.funded && l.is_active() && l.cap_grade >= floor && l.budget_units >= need_budget
        }))
    }
}

/// An in-memory snapshot of the funded leases a **verified on-chain read** attested.
///
/// The leases held here MUST have come from such a read (e.g.
/// [`from_verified_source`](Self::from_verified_source) under `dregg-verify`, or a
/// node cell read) — this type never invents funding. It is the gateway-side cache
/// of "what the chain currently funds", refreshed from the verified read.
#[derive(Debug, Clone, Default)]
pub struct AttestedFunding {
    leases: Vec<Lease>,
}

impl AttestedFunding {
    /// An empty attestation — the chain funds nothing (every create fails closed).
    pub fn empty() -> AttestedFunding {
        AttestedFunding { leases: Vec::new() }
    }

    /// Snapshot funded leases that a verified on-chain read attested. The caller is
    /// responsible for these having come from such a read; only `funded`, active
    /// leases are retained.
    pub fn from_leases(leases: impl IntoIterator<Item = Lease>) -> AttestedFunding {
        AttestedFunding {
            leases: leases
                .into_iter()
                .filter(|l| l.funded && l.is_active())
                .collect(),
        }
    }

    /// How many funded leases the snapshot holds.
    pub fn len(&self) -> usize {
        self.leases.len()
    }

    /// Whether the snapshot attests no funded leases.
    pub fn is_empty(&self) -> bool {
        self.leases.is_empty()
    }

    /// Build the snapshot directly from the control plane's light-client-VERIFIED
    /// on-chain lease read (`VerifiedNodeLeaseSource`) — the LEASE-1a wire: funded
    /// leases come from the cryptographically verified receipt log, NOT the request.
    ///
    /// A verification failure (a forged / truncated / unreachable chain) surfaces as
    /// [`FundingError::Read`]; the caller must fail closed (admit nothing).
    #[cfg(feature = "dregg-verify")]
    pub fn from_verified_source(
        source: &mut dreggnet_control::VerifiedNodeLeaseSource,
    ) -> Result<AttestedFunding, FundingError> {
        let leases = source
            .read_verified_leases()
            .map_err(|e| FundingError::Read(e.to_string()))?;
        Ok(AttestedFunding::from_leases(
            leases.into_iter().map(|o| o.lease),
        ))
    }
}

impl FundingSource for AttestedFunding {
    fn funded_leases(&self, app: &str) -> Result<Vec<Lease>, FundingError> {
        Ok(self
            .leases
            .iter()
            .filter(|l| l.lessee == app)
            .cloned()
            .collect())
    }
}

/// Reads funded leases live from a dregg node on each lookup — the deployable
/// funding source for the serving binary.
///
/// Under `dregg-verify` each lookup performs a **light-client-verified** read of
/// the node's receipt log (`VerifiedNodeLeaseSource`); otherwise it reads the
/// node's lease cells over the cell API (`NodeApiLeaseSource`) — real on-chain
/// state, node-trusted. Either way the `funded` leases come from the chain, never
/// from the caller's request, so the LEASE-1a hole is closed on both builds.
#[derive(Debug, Clone)]
pub struct NodeFunding {
    node_url: String,
}

impl NodeFunding {
    /// A funding source reading funded leases from the dregg node at `node_url`.
    pub fn new(node_url: impl Into<String>) -> NodeFunding {
        NodeFunding {
            node_url: node_url.into(),
        }
    }
}

impl FundingSource for NodeFunding {
    fn funded_leases(&self, app: &str) -> Result<Vec<Lease>, FundingError> {
        // A fresh read each lookup so funding reflects current chain state (and so a
        // create is never admitted against a stale or self-asserted lease).
        #[cfg(feature = "dregg-verify")]
        let leases = {
            let mut src = dreggnet_control::VerifiedNodeLeaseSource::new(&self.node_url);
            src.read_verified_leases()
                .map_err(|e| FundingError::Read(e.to_string()))?
        };
        #[cfg(not(feature = "dregg-verify"))]
        let leases = {
            let mut src = dreggnet_control::NodeApiLeaseSource::new(&self.node_url);
            src.read_active_leases()
                .map_err(|e| FundingError::Read(e.to_string()))?
        };
        Ok(leases
            .into_iter()
            .map(|o| o.lease)
            .filter(|l| l.lessee == app && l.funded && l.is_active())
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn funded(app: &str, grade: CapGrade, budget: i64) -> Lease {
        Lease::funded(app, grade, "computrons", budget, 1)
    }

    #[test]
    fn attested_funding_authorizes_only_a_covered_request() {
        let funding = AttestedFunding::from_leases([funded("app-a", CapGrade::Caged, 500)]);

        // A request within the on-chain reserve at a met floor is authorized.
        let lease = funding
            .authorize("app-a", CapGrade::Sandboxed, 100)
            .unwrap()
            .expect("covered request authorized");
        assert_eq!(lease.lessee, "app-a");
        assert_eq!(
            lease.budget_units, 500,
            "the REAL on-chain reserve, not the request"
        );

        // A request demanding more than the on-chain reserve is NOT funded.
        assert!(
            funding
                .authorize("app-a", CapGrade::Sandboxed, 9999)
                .unwrap()
                .is_none()
        );

        // A request for an app the chain does not fund is NOT funded.
        assert!(
            funding
                .authorize("other-app", CapGrade::Sandboxed, 1)
                .unwrap()
                .is_none()
        );

        // A request demanding a stronger isolation floor than the grant is NOT funded.
        assert!(
            funding
                .authorize("app-a", CapGrade::MicroVm, 100)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn empty_attestation_funds_nothing() {
        let funding = AttestedFunding::empty();
        assert!(
            funding
                .authorize("app-a", CapGrade::Sandboxed, 1)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn from_leases_drops_unfunded() {
        let mut unfunded = funded("app-a", CapGrade::Sandboxed, 100);
        unfunded.funded = false;
        let funding = AttestedFunding::from_leases([unfunded]);
        assert!(funding.is_empty());
    }
}
