//! The receipted secret-access audit — a verifiable, re-witnessable access log.
//!
//! Every secret ACCESS (a cap-gated read, granted OR denied) emits one
//! [`SecretAccessReceipt`] sealed into a [`dreggnet_receipt::ReceiptChain`]: a
//! prev-hash-chained, ed25519-signed record a non-witness can verify. It answers
//! *who* (the credential subject), *what* (the secret name + version), *when*
//! (the clock), and the *outcome* (granted/denied + reason).
//!
//! Crucially the receipt carries the secret NAME but NEVER the secret VALUE — the
//! audit log is itself part of the operator-visible surface, so plaintext must
//! not appear in it. That is a load-bearing confinement tooth (see the
//! `no_plaintext_anywhere` store test).

use dreggnet_receipt::{BodyHasher, ReceiptAttestation, ReceiptBody};
use serde::{Deserialize, Serialize};

/// Domain separator for the access-receipt body hash.
const ACCESS_BODY_DOMAIN: &[u8] = b"dreggnet-secret-access-receipt-v1";

/// Granted or denied — the outcome of a cap-gated read.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AccessOutcome {
    /// The cap was satisfied; the value was decrypted and injected/returned.
    Granted,
    /// The cap was refused (wrong/insufficient/expired cap, wrong account, or a
    /// missing secret). No plaintext was produced.
    Denied,
}

impl AccessOutcome {
    fn tag(self) -> &'static str {
        match self {
            AccessOutcome::Granted => "granted",
            AccessOutcome::Denied => "denied",
        }
    }
}

/// One receipted access event. A typed [`ReceiptBody`] sealed into the audit
/// chain. Serializable so a verifier (or the no-leak scan) can inspect it; it
/// carries NO plaintext, only the secret name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SecretAccessReceipt {
    /// Producer-monotonic position in the audit chain.
    pub seq: u64,
    /// The account that owns the secret.
    pub account: String,
    /// WHO — the credential subject (`dregg:…`), or `<none>` if undecodable.
    pub subject: String,
    /// WHAT — the secret name (NEVER the value).
    pub secret_name: String,
    /// Which version was read (0 when denied / not applicable).
    pub version: u32,
    /// WHEN — the verifier clock (unix seconds).
    pub at: u64,
    /// The outcome.
    pub outcome: AccessOutcome,
    /// Human reason (empty for a clean grant; the refusal text when denied).
    pub reason: String,
    /// The chain attestation, present once sealed.
    pub attest: Option<ReceiptAttestation>,
}

impl ReceiptBody for SecretAccessReceipt {
    fn body_hash(&self) -> [u8; 32] {
        let mut h = BodyHasher::new(ACCESS_BODY_DOMAIN);
        h.field(self.account.as_bytes())
            .field(self.subject.as_bytes())
            .field(self.secret_name.as_bytes())
            .u64(self.version as u64)
            .u64(self.at)
            .field(self.outcome.tag().as_bytes())
            .field(self.reason.as_bytes());
        h.finalize()
    }

    fn seq(&self) -> u64 {
        self.seq
    }

    fn attestation(&self) -> Option<&ReceiptAttestation> {
        self.attest.as_ref()
    }
}
