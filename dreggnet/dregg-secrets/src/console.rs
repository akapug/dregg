//! THE CONSOLE-SECRETS-PANEL SEAM — the signed-in customer's secrets view.
//!
//! The console ([`dreggnet-console`]) renders a per-account panel of the secrets
//! the customer owns: each secret's NAME, current version, total versions, when
//! it was created / last rotated, and when it was last accessed (from the
//! receipted audit log). It NEVER renders a plaintext value — the panel is a
//! metadata-only, plaintext-free read model, exactly the operator-visible-surface
//! discipline the audit receipts keep.
//!
//! ## The live wire (console side, not edited here — swarm-safe)
//! `console`'s render layer calls [`panel_for`] with the signed-in subject's
//! account [`SecretStore`] and renders [`SecretsPanel`] into the dashboard. A
//! "reveal" affordance would itself be a cap-gated [`SecretStore::read`] (audited
//! like any other access), never a panel field — so even the customer's own
//! reveal is on the receipted path.

use crate::store::{SecretMeta, SecretStore};

/// One row in the secrets panel — metadata only, never a value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecretPanelEntry {
    pub name: String,
    pub current_version: u32,
    pub total_versions: u32,
    pub created_at: u64,
    pub last_rotated_at: u64,
    /// When the secret was last accessed (granted or denied), from the audit log.
    pub last_access: Option<u64>,
}

/// The whole cap-scoped panel for one account. Plaintext-free by construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecretsPanel {
    pub account: String,
    /// Whether the operator can technically read this account's plaintext — the
    /// honest KMS limit, surfaced to the customer (operator-held vs tenant-held).
    pub operator_can_read: bool,
    pub entries: Vec<SecretPanelEntry>,
}

/// Build the console panel for `store`'s account — names, versions, timestamps,
/// last-access. No value ever enters this model.
pub fn panel_for(store: &SecretStore) -> SecretsPanel {
    let entries = store
        .names()
        .into_iter()
        .filter_map(|name| {
            let SecretMeta {
                name,
                current_version,
                total_versions,
                created_at,
                last_rotated_at,
            } = store.metadata(&name)?;
            let last_access = store.last_access(&name);
            Some(SecretPanelEntry {
                name,
                current_version,
                total_versions,
                created_at,
                last_rotated_at,
                last_access,
            })
        })
        .collect();
    SecretsPanel {
        account: store.account().to_string(),
        operator_can_read: store.operator_can_read(),
        entries,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cap::mint_secret_caps;
    use crate::kms::KmsRoot;
    use dreggnet_webauth::cred::RootKey;

    #[test]
    fn panel_lists_metadata_only() {
        let root = RootKey::from_seed([50u8; 32]);
        let store = SecretStore::new(
            "acct-A",
            root.public(),
            KmsRoot::operator_held([9u8; 32]),
            [10u8; 32],
        );
        store
            .put("my-app/DB_URL", b"postgres://super-secret-value", 100)
            .unwrap();
        store
            .rotate("my-app/DB_URL", b"postgres://rotated-secret", 150)
            .unwrap();
        let cred = mint_secret_caps(&root, ["my-app/DB_URL"], None).encode();
        let _ = store.read(&cred, "my-app/DB_URL", 200).unwrap();

        let panel = panel_for(&store);
        assert_eq!(panel.account, "acct-A");
        assert!(panel.operator_can_read); // operator-held root
        assert_eq!(panel.entries.len(), 1);
        let e = &panel.entries[0];
        assert_eq!(e.name, "my-app/DB_URL");
        assert_eq!(e.current_version, 2);
        assert_eq!(e.total_versions, 2);
        assert_eq!(e.last_rotated_at, 150);
        assert_eq!(e.last_access, Some(200));

        // The whole rendered panel contains no plaintext.
        let rendered = format!("{panel:?}");
        assert!(!rendered.contains("super-secret-value"));
        assert!(!rendered.contains("rotated-secret"));
    }
}
