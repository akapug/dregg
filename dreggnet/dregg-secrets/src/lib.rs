//! `dreggnet-secrets` — managed secrets / KMS for DreggNet workloads.
//!
//! Cloud table-stakes (`docs/CLOUD-PROVIDER-READINESS.md`: "no secrets/KMS").
//! A permissionless cloud runs arbitrary tenant workloads that need managed
//! secrets — API keys, DB creds, the BYO-LLM keys — that the OPERATOR cannot
//! read, that reach ONLY the sandbox that needs them, and whose every access is
//! auditable. This crate is that layer, built from the existing dregg pieces:
//!
//! * **[`kms`]** — the key hierarchy + envelope encryption. A KMS root derives a
//!   per-account KEK ([`blake3`] KDF) that wraps a per-secret-version DEK; the
//!   value is sealed under the DEK with a vetted AEAD (XChaCha20-Poly1305). At
//!   rest, everything is ciphertext. THE HONEST LIMIT: an operator-held root can
//!   still derive+decrypt — true operator-blindness needs a tenant-held root
//!   ([`kms::KmsRoot::operator_can_read`]).
//! * **[`cap`]** — the `secret:<name>` capability over the [`dreggnet_webauth`]
//!   credential. A secret is readable only by a cap that grants it, verified
//!   under the owning account's root (cap-scoping AND account-scoping teeth).
//! * **[`store`]** — the per-account [`store::SecretStore`]: store, versioned
//!   rotation, and the ONE cap-gated, audited read.
//! * **[`audit`]** — every access (granted/denied) is a receipted, re-witnessable
//!   event over the [`dreggnet_receipt`] chain. Carries the secret NAME, never
//!   the value.
//! * **[`inject`]** — THE EXEC-SECRET-INJECTION SEAM: a workload declares the
//!   secrets it needs; [`inject::inject_for_workload`] resolves them (cap-gated)
//!   into confined sandbox env/files that never reach a log/receipt/operator
//!   view (the BYO-LLM-key confinement pattern generalized).
//! * **[`console`]** — THE CONSOLE-SECRETS-PANEL SEAM: the plaintext-free
//!   metadata view the signed-in customer sees.

pub mod audit;
pub mod cap;
pub mod console;
pub mod inject;
pub mod kms;
pub mod store;

pub use cap::CapDenied;
pub use kms::{Envelope, KmsRoot, RootHolder};
pub use store::{SecretMeta, SecretStore};

/// The unified error for the secrets layer.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum SecretError {
    /// No secret by this name exists (or it is fully retired).
    #[error("no secret named `{name}`")]
    NotFound { name: String },
    /// A `put` of a name that already exists (use `rotate`).
    #[error("a secret named `{name}` already exists (rotate it instead)")]
    AlreadyExists { name: String },
    /// The presented credential does not grant read of this secret (cap, account,
    /// or expiry teeth). No plaintext was produced.
    #[error("read of secret `{name}` refused: {reason}")]
    CapDenied { name: String, reason: String },
    /// An AEAD open failed — a tamper, a wrong root, or a cross-account move.
    /// Fail-closed: no plaintext is ever returned on a crypto error.
    #[error("cryptographic failure: {0}")]
    Crypto(String),
}

#[cfg(test)]
mod integration {
    //! End-to-end proof of the four claims, including the cross-module
    //! no-plaintext-anywhere scan (the load-bearing confinement tooth).

    use crate::audit::AccessOutcome;
    use crate::cap::mint_secret_caps;
    use crate::console::panel_for;
    use crate::inject::{SecretBinding, SecretRequest, inject_for_workload};
    use crate::kms::KmsRoot;
    use crate::store::SecretStore;
    use dreggnet_receipt::ReceiptBody;
    use dreggnet_webauth::cred::RootKey;

    const PLAINTEXT: &[u8] = b"postgres://user:HUNTER2-the-secret@db.internal/prod";

    fn contains(haystack: &[u8], needle: &[u8]) -> bool {
        !needle.is_empty() && haystack.windows(needle.len()).any(|w| w == needle)
    }

    #[test]
    fn end_to_end_secrets_lifecycle_and_no_leak() {
        let acct = RootKey::from_seed([100u8; 32]);
        let store = SecretStore::new(
            "tenant-prod",
            acct.public(),
            KmsRoot::operator_held([101u8; 32]),
            [102u8; 32],
        );

        // 1. Store a secret.
        store.put("my-app/DB_URL", PLAINTEXT, 1_000).unwrap();

        // 2. A workload WITH the cap gets it injected and reads the value.
        let cred = mint_secret_caps(&acct, ["my-app/DB_URL"], None).encode();
        let req = SecretRequest::new().with(SecretBinding::env("my-app/DB_URL", "DATABASE_URL"));
        let injected = inject_for_workload(&store, &cred, &req, 2_000).unwrap();
        let got: Vec<u8> = injected
            .env_vars()
            .find(|(k, _)| *k == "DATABASE_URL")
            .map(|(_, v)| v.to_vec())
            .unwrap();
        assert_eq!(got, PLAINTEXT, "the workload reads the real value");

        // 3. A workload WITHOUT the cap is refused.
        let nocap = mint_secret_caps(&acct, ["my-app/OTHER"], None).encode();
        assert!(inject_for_workload(&store, &nocap, &req, 2_100).is_err());

        // 4. Another account cannot read it.
        let attacker = RootKey::from_seed([200u8; 32]);
        let forged = mint_secret_caps(&attacker, ["my-app/DB_URL"], None).encode();
        assert!(store.read(&forged, "my-app/DB_URL", 2_200).is_err());

        // 5. Rotation: new version, old retired; the read yields the new value.
        let v2 = store
            .rotate("my-app/DB_URL", b"postgres://rotated/prod", 3_000)
            .unwrap();
        assert_eq!(v2, 2);
        let after = store.read(&cred, "my-app/DB_URL", 3_100).unwrap();
        assert_eq!(&after[..], b"postgres://rotated/prod");

        // 6. The access is audited and re-witnessable.
        assert!(store.verify_audit());
        let log = store.audit_receipts();
        // grants: inject(2000) + read(3100); denials: inject-nocap(2100) + cross-acct(2200).
        let grants = log
            .iter()
            .filter(|r| r.outcome == AccessOutcome::Granted)
            .count();
        let denials = log
            .iter()
            .filter(|r| r.outcome == AccessOutcome::Denied)
            .count();
        assert_eq!(grants, 2);
        assert_eq!(denials, 2);

        // 7. THE NO-PLAINTEXT-ANYWHERE SCAN — every operator/log/receipt-visible
        //    surface must be free of the original plaintext.
        // 7a. The store at rest (the envelopes the operator's DB holds).
        let panel = panel_for(&store);
        assert!(
            !contains(format!("{panel:?}").as_bytes(), PLAINTEXT),
            "console panel leaked"
        );
        // 7b. The audit receipts (signed, operator-visible).
        for r in &log {
            assert!(
                !contains(format!("{r:?}").as_bytes(), PLAINTEXT),
                "audit receipt leaked"
            );
            // The receipt body hash binds the name, not the value.
            assert!(!contains(&r.body_hash(), PLAINTEXT));
        }
        // 7c. The injected material's Debug (a stray debug print).
        assert!(
            !contains(format!("{injected:?}").as_bytes(), PLAINTEXT),
            "InjectedSecrets Debug leaked"
        );
        // 7d. The scrub helper strips it from any text a surface might emit.
        let line = format!("connecting with {}", String::from_utf8_lossy(PLAINTEXT));
        assert!(!injected.scrub(&line).contains("HUNTER2-the-secret"));

        // 8. The honest KMS limit is surfaced (operator-held here).
        assert!(store.operator_can_read());
        assert!(panel.operator_can_read);
    }
}
