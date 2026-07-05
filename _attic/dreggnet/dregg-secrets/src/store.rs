//! The cap-account-owned, encrypted, versioned, audited secret store.
//!
//! A [`SecretStore`] belongs to ONE cap-account/org. A tenant:
//! * **stores** a named secret (`my-app/DB_URL` = value) — sealed at rest under
//!   the account's KMS material ([`crate::kms::Envelope`]); the operator's
//!   storage layer only ever holds ciphertext;
//! * **rotates** it — a new version becomes current and the prior is retired;
//! * **reads** it — ONLY by presenting a credential that grants `secret:<name>`
//!   under the account root ([`crate::cap`]); every read (granted or denied) is a
//!   receipted audit event ([`crate::audit`]).
//!
//! The store never logs or returns the plaintext anywhere but the
//! [`Zeroizing`] value handed back to the caller for injection.

use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use dreggnet_receipt::{ReceiptBody, ReceiptChain, verify_chain};
use dreggnet_webauth::cred::PublicKey;
use zeroize::Zeroizing;

use crate::SecretError;
use crate::audit::{AccessOutcome, SecretAccessReceipt};
use crate::cap::grants_secret;
use crate::kms::{Envelope, KmsRoot};

/// One stored version of a secret. Carries only ciphertext.
#[derive(Clone, Debug)]
struct SecretVersion {
    version: u32,
    envelope: Envelope,
    created_at: u64,
    retired: bool,
}

/// The per-account secret store.
pub struct SecretStore {
    account: String,
    /// The account's root public key — presented caps are verified under this
    /// (the account-scoping tooth).
    account_root: PublicKey,
    /// The KMS material that seals/opens this account's secrets.
    kms: KmsRoot,
    /// name → versions (ascending; the last non-retired is current).
    secrets: Mutex<BTreeMap<String, Vec<SecretVersion>>>,
    /// The receipted access-audit chain.
    audit: ReceiptChain,
    /// The retained audit receipts (for re-witness, the console last-access view,
    /// and the no-leak scan).
    audit_log: Mutex<Vec<SecretAccessReceipt>>,
    audit_seq: AtomicU64,
}

impl SecretStore {
    /// A fresh store for `account`, verifying presented caps under `account_root`,
    /// sealing under `kms`, and signing audit receipts with `audit_signer_seed`.
    pub fn new(
        account: impl Into<String>,
        account_root: PublicKey,
        kms: KmsRoot,
        audit_signer_seed: [u8; 32],
    ) -> SecretStore {
        SecretStore {
            account: account.into(),
            account_root,
            kms,
            secrets: Mutex::new(BTreeMap::new()),
            audit: ReceiptChain::from_seed(audit_signer_seed),
            audit_log: Mutex::new(Vec::new()),
            audit_seq: AtomicU64::new(0),
        }
    }

    /// The account this store owns secrets for.
    pub fn account(&self) -> &str {
        &self.account
    }

    /// Whether the operator can (technically) read this account's plaintext — the
    /// honest KMS limit, surfaced through to the store level.
    pub fn operator_can_read(&self) -> bool {
        self.kms.operator_can_read()
    }

    /// The public key non-witnesses verify the audit chain under.
    pub fn audit_signer_public(&self) -> [u8; 32] {
        self.audit.signer_public()
    }

    // ─────────────────────────────── writes ────────────────────────────────

    /// Store a NEW named secret at version 1. Errors if it already exists (use
    /// [`rotate`](Self::rotate) to add a version). Writes are an owner action,
    /// not a cap-gated read, so they are not audited as accesses.
    pub fn put(&self, name: &str, value: &[u8], now: u64) -> Result<u32, SecretError> {
        let mut map = self.secrets.lock().expect("secrets poisoned");
        if map.contains_key(name) {
            return Err(SecretError::AlreadyExists {
                name: name.to_string(),
            });
        }
        let envelope = Envelope::seal(&self.kms, &self.account, value);
        map.insert(
            name.to_string(),
            vec![SecretVersion {
                version: 1,
                envelope,
                created_at: now,
                retired: false,
            }],
        );
        Ok(1)
    }

    /// Rotate a secret: seal `new_value` as the next version (current) and retire
    /// every prior version. Returns the new version number. The old plaintext is
    /// no longer reachable — a read returns the new current version.
    pub fn rotate(&self, name: &str, new_value: &[u8], now: u64) -> Result<u32, SecretError> {
        let mut map = self.secrets.lock().expect("secrets poisoned");
        let versions = map.get_mut(name).ok_or_else(|| SecretError::NotFound {
            name: name.to_string(),
        })?;
        let next = versions.iter().map(|v| v.version).max().unwrap_or(0) + 1;
        for v in versions.iter_mut() {
            v.retired = true;
        }
        let envelope = Envelope::seal(&self.kms, &self.account, new_value);
        versions.push(SecretVersion {
            version: next,
            envelope,
            created_at: now,
            retired: false,
        });
        Ok(next)
    }

    // ─────────────────────────── the cap-gated read ────────────────────────

    /// Read a secret's CURRENT value — the one cap-gated, audited entry point.
    ///
    /// 1. verify the presented credential grants `secret:<name>` under the
    ///    account root (cap-scoping + account-scoping teeth);
    /// 2. on refusal: audit a `Denied` event and return [`SecretError::CapDenied`]
    ///    — NO plaintext;
    /// 3. on grant: decrypt the current version, audit a `Granted` event (who/
    ///    what/when), and return the [`Zeroizing`] plaintext.
    ///
    /// The returned value is the ONLY place plaintext leaves the store; it never
    /// enters a log, the audit receipt, or the operator view.
    pub fn read(
        &self,
        cred_enc: &str,
        name: &str,
        now: u64,
    ) -> Result<Zeroizing<Vec<u8>>, SecretError> {
        let subject =
            dreggnet_webauth::subject_of(cred_enc).unwrap_or_else(|| "<none>".to_string());

        // 1. cap-gate.
        if let Err(denied) = grants_secret(cred_enc, &self.account_root, name, now) {
            self.audit_event(
                &subject,
                name,
                0,
                now,
                AccessOutcome::Denied,
                denied.to_string(),
            );
            return Err(SecretError::CapDenied {
                name: name.to_string(),
                reason: denied.to_string(),
            });
        }

        // 2. locate the current version (cap satisfied but secret may be absent).
        let (version, envelope) = {
            let map = self.secrets.lock().expect("secrets poisoned");
            match map
                .get(name)
                .and_then(|vs| vs.iter().rev().find(|v| !v.retired))
            {
                Some(v) => (v.version, v.envelope.clone()),
                None => {
                    self.audit_event(
                        &subject,
                        name,
                        0,
                        now,
                        AccessOutcome::Denied,
                        "no current version (secret absent or fully retired)".to_string(),
                    );
                    return Err(SecretError::NotFound {
                        name: name.to_string(),
                    });
                }
            }
        };

        // 3. decrypt + audit the grant.
        let plaintext = envelope.open(&self.kms, &self.account)?;
        self.audit_event(
            &subject,
            name,
            version,
            now,
            AccessOutcome::Granted,
            String::new(),
        );
        Ok(plaintext)
    }

    // ─────────────────────────── read-model / audit ────────────────────────

    /// The current version number of `name`, if it exists.
    pub fn current_version(&self, name: &str) -> Option<u32> {
        let map = self.secrets.lock().expect("secrets poisoned");
        map.get(name)
            .and_then(|vs| vs.iter().rev().find(|v| !v.retired))
            .map(|v| v.version)
    }

    /// The secret names this store holds (no values).
    pub fn names(&self) -> Vec<String> {
        let map = self.secrets.lock().expect("secrets poisoned");
        map.keys().cloned().collect()
    }

    /// A cap-scoped, plaintext-free metadata view of a secret (for the console).
    pub fn metadata(&self, name: &str) -> Option<SecretMeta> {
        let map = self.secrets.lock().expect("secrets poisoned");
        let vs = map.get(name)?;
        let current = vs.iter().rev().find(|v| !v.retired);
        Some(SecretMeta {
            name: name.to_string(),
            current_version: current.map(|v| v.version).unwrap_or(0),
            total_versions: vs.len() as u32,
            created_at: vs.first().map(|v| v.created_at).unwrap_or(0),
            last_rotated_at: current.map(|v| v.created_at).unwrap_or(0),
        })
    }

    /// A snapshot of the audit log (the receipted access events).
    pub fn audit_receipts(&self) -> Vec<SecretAccessReceipt> {
        self.audit_log.lock().expect("audit poisoned").clone()
    }

    /// Re-witness the whole audit chain — every event signed by this store's
    /// audit key, prev-hash-linked, strictly sequenced. The non-witness check.
    pub fn verify_audit(&self) -> bool {
        verify_chain(&self.audit_receipts()).is_ok()
    }

    /// The timestamp of the most recent access (granted or denied) of `name`.
    pub fn last_access(&self, name: &str) -> Option<u64> {
        self.audit_log
            .lock()
            .expect("audit poisoned")
            .iter()
            .filter(|r| r.secret_name == name)
            .map(|r| r.at)
            .max()
    }

    /// Seal one access event into the audit chain.
    fn audit_event(
        &self,
        subject: &str,
        name: &str,
        version: u32,
        at: u64,
        outcome: AccessOutcome,
        reason: String,
    ) {
        let seq = self.audit_seq.fetch_add(1, Ordering::SeqCst);
        let mut rec = SecretAccessReceipt {
            seq,
            account: self.account.clone(),
            subject: subject.to_string(),
            secret_name: name.to_string(),
            version,
            at,
            outcome,
            reason,
            attest: None,
        };
        let att = self.audit.seal(rec.body_hash(), seq, None);
        rec.attest = Some(att);
        self.audit_log.lock().expect("audit poisoned").push(rec);
    }
}

/// A plaintext-free metadata view of a secret (the console read model element).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecretMeta {
    pub name: String,
    pub current_version: u32,
    pub total_versions: u32,
    pub created_at: u64,
    pub last_rotated_at: u64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cap::mint_secret_caps;
    use dreggnet_webauth::cred::RootKey;

    fn store_with_root(root: &RootKey) -> SecretStore {
        SecretStore::new(
            "acct-A",
            root.public(),
            KmsRoot::operator_held([77u8; 32]),
            [88u8; 32],
        )
    }

    #[test]
    fn store_then_cap_gated_read() {
        let root = RootKey::from_seed([30u8; 32]);
        let store = store_with_root(&root);
        store
            .put("my-app/DB_URL", b"postgres://u:p@h/db", 100)
            .unwrap();

        let cred = mint_secret_caps(&root, ["my-app/DB_URL"], None).encode();
        let got = store.read(&cred, "my-app/DB_URL", 200).unwrap();
        assert_eq!(&got[..], b"postgres://u:p@h/db");
    }

    #[test]
    fn read_without_cap_is_refused() {
        let root = RootKey::from_seed([31u8; 32]);
        let store = store_with_root(&root);
        store.put("my-app/DB_URL", b"value", 100).unwrap();

        // A cap for a DIFFERENT secret.
        let cred = mint_secret_caps(&root, ["my-app/OTHER"], None).encode();
        let err = store.read(&cred, "my-app/DB_URL", 200).unwrap_err();
        assert!(matches!(err, SecretError::CapDenied { .. }));
    }

    #[test]
    fn rotation_makes_a_new_version_and_retires_the_old() {
        let root = RootKey::from_seed([32u8; 32]);
        let store = store_with_root(&root);
        store.put("s/A", b"v1-value", 100).unwrap();
        assert_eq!(store.current_version("s/A"), Some(1));

        let v2 = store.rotate("s/A", b"v2-value", 150).unwrap();
        assert_eq!(v2, 2);
        assert_eq!(store.current_version("s/A"), Some(2));

        // A read now yields the new value; the old plaintext is unreachable.
        let cred = mint_secret_caps(&root, ["s/A"], None).encode();
        let got = store.read(&cred, "s/A", 200).unwrap();
        assert_eq!(&got[..], b"v2-value");
    }

    #[test]
    fn access_is_audited_and_re_witnessable() {
        let root = RootKey::from_seed([33u8; 32]);
        let store = store_with_root(&root);
        store.put("s/A", b"value", 100).unwrap();
        let cred = mint_secret_caps(&root, ["s/A"], None).encode();
        let _ = store.read(&cred, "s/A", 200).unwrap();
        // A denied read too.
        let bad = mint_secret_caps(&root, ["s/OTHER"], None).encode();
        let _ = store.read(&bad, "s/A", 250);

        let log = store.audit_receipts();
        assert_eq!(log.len(), 2);
        assert_eq!(log[0].outcome, AccessOutcome::Granted);
        assert_eq!(log[0].at, 200);
        assert_eq!(log[1].outcome, AccessOutcome::Denied);
        assert!(store.verify_audit(), "the audit chain must re-witness");
        assert_eq!(store.last_access("s/A"), Some(250));
    }

    #[test]
    fn cross_account_cannot_read() {
        let acct_a = RootKey::from_seed([34u8; 32]);
        let acct_b = RootKey::from_seed([35u8; 32]);
        let store = store_with_root(&acct_a);
        store.put("s/A", b"value", 100).unwrap();
        // B mints a cap for the same name under B's root — refused (wrong root).
        let bs_cred = mint_secret_caps(&acct_b, ["s/A"], None).encode();
        assert!(store.read(&bs_cred, "s/A", 200).is_err());
    }

    #[test]
    fn duplicate_put_is_refused() {
        let root = RootKey::from_seed([36u8; 32]);
        let store = store_with_root(&root);
        store.put("s/A", b"v1", 100).unwrap();
        assert!(matches!(
            store.put("s/A", b"v2", 100),
            Err(SecretError::AlreadyExists { .. })
        ));
    }
}
