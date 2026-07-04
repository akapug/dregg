//! `governance` — account **standing** and the **receipted governance log**.
//!
//! Every moderation action on the permissionless cloud — flagging an account,
//! suspending a resource, reinstating one, recording an abuse report — is a
//! **turn**: it is sealed into a prev-hash-chained, ed25519-signed governance
//! stream (`dreggnet_receipt`), so what was done / why / by whom is an auditable,
//! re-witnessable record rather than an arbitrary, deniable host action. A
//! third party holding the governance signer's public key can `verify_chain`
//! the whole stream and detect any reorder, splice, or forgery.
//!
//! The standing of an account (`Good` / `Flagged` / `Suspended`) is the gate on
//! resource creation: a suspended account creates nothing, a flagged account
//! runs under tighter quotas. Standing only ever moves through a sealed
//! [`GovernanceEvent`], so the *reason* an owner sees is exactly the reason on
//! the signed record.

use dreggnet_receipt::{BodyHasher, ReceiptAttestation, ReceiptBody, ReceiptChain};
use serde::{Deserialize, Serialize};

/// The standing of a cap-account, the gate on what it may create.
///
/// Ordered weakest-privilege → strongest-privilege so a `<` comparison answers
/// "is at least as restricted as".
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum AccountStanding {
    /// Suspended: creates nothing, existing resources may be taken down. The
    /// floor a confirmed-abusive account sits at.
    Suspended,
    /// Flagged: still serves, but runs under the tighter flagged quota tier
    /// (a throttle short of a full takedown — the "under review" state).
    Flagged,
    /// Good standing: the conservative default every new anonymous account gets.
    Good,
}

impl AccountStanding {
    /// The wire/log label.
    pub fn as_str(self) -> &'static str {
        match self {
            AccountStanding::Suspended => "suspended",
            AccountStanding::Flagged => "flagged",
            AccountStanding::Good => "good",
        }
    }

    /// Whether an account in this standing may create new resources at all.
    /// Suspended cannot; flagged can (under a tighter ceiling); good can.
    pub fn may_create(self) -> bool {
        !matches!(self, AccountStanding::Suspended)
    }
}

/// Default standing for a never-before-seen anonymous account: good, but the
/// conservative quota tier (see [`crate::quota::QuotaPolicy`]) does the real
/// bounding. A KYC-free account is admitted, not trusted.
impl Default for AccountStanding {
    fn default() -> Self {
        AccountStanding::Good
    }
}

/// What a governance event did.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GovAction {
    /// An abuse report was filed against a resource (intake only — no state
    /// change; review is the operator's call). Recorded for the audit trail.
    Report,
    /// A resource was suspended (stops serving/running) and/or the owning
    /// account moved to a tighter standing.
    Suspend,
    /// An account was flagged (tighter quotas, still serving).
    Flag,
    /// A resource/account was reinstated to good standing.
    Reinstate,
}

impl GovAction {
    /// The log label.
    pub fn as_str(self) -> &'static str {
        match self {
            GovAction::Report => "report",
            GovAction::Suspend => "suspend",
            GovAction::Flag => "flag",
            GovAction::Reinstate => "reinstate",
        }
    }
}

/// A single, signed governance turn — the takedown/standing receipt.
///
/// It is a [`ReceiptBody`]: its typed fields hash canonically, and once sealed
/// into the [`GovernanceLog`]'s chain it carries an [`ReceiptAttestation`]
/// (prev-hash link + ed25519 signature) so the moderation stream is append-only
/// and tamper-evident. `resource_id` is `None` for an account-wide action
/// (e.g. flagging the whole account) and `Some` for a specific resource
/// takedown.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GovernanceEvent {
    /// Producer-monotonic sequence (the chain position).
    pub seq: u64,
    /// What this event did.
    pub action: GovAction,
    /// The cap-account subject the action concerns (the `dga1_`-derived id).
    pub subject: String,
    /// The specific resource acted on, if any (a site/server/agent/bucket id).
    pub resource_id: Option<String>,
    /// The account standing AFTER this event (when it changed standing).
    pub standing_after: Option<AccountStanding>,
    /// The human-readable reason — the field the owner's console shows.
    pub reason: String,
    /// Who took the action: an operator's `dga1_` subject, or an
    /// `automated:<signal>` label for an automated-signal takedown.
    pub actor: String,
    /// When the action was taken (unix seconds).
    pub at: i64,
    /// The chain attestation, present once sealed.
    pub attestation: Option<ReceiptAttestation>,
}

impl ReceiptBody for GovernanceEvent {
    fn body_hash(&self) -> [u8; 32] {
        let mut h = BodyHasher::new(b"dreggnet-governance-event-v1");
        h.u64(self.seq)
            .field(self.action.as_str().as_bytes())
            .field(self.subject.as_bytes())
            .field(self.resource_id.as_deref().unwrap_or("").as_bytes())
            .field(
                self.standing_after
                    .map(|s| s.as_str())
                    .unwrap_or("")
                    .as_bytes(),
            )
            .field(self.reason.as_bytes())
            .field(self.actor.as_bytes())
            .u64(self.at as u64);
        h.finalize()
    }

    fn seq(&self) -> u64 {
        self.seq
    }

    fn attestation(&self) -> Option<&ReceiptAttestation> {
        self.attestation.as_ref()
    }
}

/// The append-only governance log: a [`ReceiptChain`] plus the materialized,
/// verifiable list of sealed [`GovernanceEvent`]s. The producer (the operator
/// authority / the automated-signal service) holds the signer; anyone holding
/// its public key re-witnesses the whole moderation history.
pub struct GovernanceLog {
    chain: ReceiptChain,
    events: Vec<GovernanceEvent>,
}

impl GovernanceLog {
    /// A fresh governance log signing under a secret seed (a real deployment
    /// configures a persistent operator-authority secret).
    pub fn from_seed(seed: [u8; 32]) -> GovernanceLog {
        GovernanceLog {
            chain: ReceiptChain::from_seed(seed),
            events: Vec::new(),
        }
    }

    /// The public key non-witnesses verify the governance stream under.
    pub fn signer_public(&self) -> [u8; 32] {
        self.chain.signer_public()
    }

    /// Seal a governance turn into the chain: assign the next sequence, link it
    /// to the head, sign it, and append it to the materialized log. Returns the
    /// sealed event (now carrying its attestation).
    pub fn record(
        &mut self,
        action: GovAction,
        subject: impl Into<String>,
        resource_id: Option<String>,
        standing_after: Option<AccountStanding>,
        reason: impl Into<String>,
        actor: impl Into<String>,
        at: i64,
    ) -> GovernanceEvent {
        let seq = self.events.len() as u64;
        let mut ev = GovernanceEvent {
            seq,
            action,
            subject: subject.into(),
            resource_id,
            standing_after,
            reason: reason.into(),
            actor: actor.into(),
            at,
            attestation: None,
        };
        // A governance event is a root owned-state transition of the operator
        // authority (not a view of a kernel turn), so `turn_receipt_hash` is None;
        // the operator's signature carries it.
        let att = self.chain.seal(ev.body_hash(), seq, None);
        ev.attestation = Some(att);
        self.events.push(ev.clone());
        ev
    }

    /// The full sealed governance stream (for an audit export / a console view).
    pub fn events(&self) -> &[GovernanceEvent] {
        &self.events
    }

    /// How many governance turns have been sealed.
    pub fn len(&self) -> usize {
        self.events.len()
    }

    /// Whether the log is empty.
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_receipt::verify_chain;

    #[test]
    fn standing_gates_creation() {
        assert!(AccountStanding::Good.may_create());
        assert!(AccountStanding::Flagged.may_create());
        assert!(!AccountStanding::Suspended.may_create());
    }

    #[test]
    fn a_sealed_governance_stream_verifies_and_is_auditable() {
        let mut log = GovernanceLog::from_seed([5u8; 32]);
        log.record(
            GovAction::Report,
            "dregg:abc",
            Some("site_x".into()),
            None,
            "phishing report from user",
            "automated:spamhaus",
            1000,
        );
        log.record(
            GovAction::Suspend,
            "dregg:abc",
            Some("site_x".into()),
            Some(AccountStanding::Suspended),
            "confirmed phishing kit",
            "dregg:operator1",
            1100,
        );
        // The whole moderation stream re-witnesses under the operator key.
        assert_eq!(verify_chain(log.events()), Ok(()));
        assert_eq!(log.len(), 2);
        assert_eq!(log.events()[1].action, GovAction::Suspend);
        assert_eq!(
            log.events()[1].standing_after,
            Some(AccountStanding::Suspended)
        );
    }

    #[test]
    fn tampering_a_takedown_reason_breaks_the_signature() {
        let mut log = GovernanceLog::from_seed([6u8; 32]);
        log.record(
            GovAction::Suspend,
            "dregg:bad",
            Some("srv_1".into()),
            Some(AccountStanding::Suspended),
            "malware C2",
            "dregg:operator1",
            1000,
        );
        // Forge the reason after sealing — the audit verification catches it.
        let mut forged = log.events().to_vec();
        forged[0].reason = "totally legit, reinstate".into();
        assert!(verify_chain(&forged).is_err());
    }
}
