//! The `secret:<name>` capability vocabulary over the dregg credential core.
//!
//! A secret is OWNED by a cap-account/org (it is sealed under that account's KMS
//! material) and is READABLE only by a presented credential that (a) verifies
//! under the account's root public key and (b) grants the capability
//! `secret:<name>`. Both halves are teeth:
//!
//! * **cap-scoping (b)** — a credential narrowed (attenuated) to `secret:A` can
//!   never reach `secret:B` (the no-amplify property, `cred::attenuation_only_narrows`).
//!   A sub-agent gets exactly the secrets its caps name, nothing wider.
//! * **account-scoping (a)** — a credential minted under account B's root fails
//!   the signature chain against account A's root, so account B cannot read
//!   account A's secrets even with a `secret:<name>` cap (cross-account teeth).
//!
//! This rides the webauth credential exactly as the web-surface `cap` vocabulary
//! does ([`dreggnet_webauth::grant`]): a single first-party `AnyOf([AttrEq{cap,
//! "secret:<name>"} …])` caveat, verified against a context binding
//! `cap = secret:<name>` and `clock = now`.

use dreggnet_webauth::cred::{Caveat, Context, Credential, Pred, PublicKey, RootKey};

/// The request-attribute key a capability is matched on (shared with webauth).
pub const CAP_KEY: &str = "cap";

/// The capability-string prefix that names read access to a secret.
pub const SECRET_CAP_PREFIX: &str = "secret:";

/// The capability string that grants read of secret `name`.
pub fn secret_cap_name(name: &str) -> String {
    format!("{SECRET_CAP_PREFIX}{name}")
}

/// Build the single caveat granting exactly read of `names`.
fn secret_caveat(names: &[String]) -> Caveat {
    Caveat::FirstParty(Pred::AnyOf(
        names
            .iter()
            .map(|n| Pred::AttrEq {
                key: CAP_KEY.to_string(),
                value: secret_cap_name(n),
            })
            .collect(),
    ))
}

/// Mint a credential (under the account's root) granting read of `names`,
/// optionally expiring at `until` (a unix-second clock reading).
pub fn mint_secret_caps(
    root: &RootKey,
    names: impl IntoIterator<Item = impl Into<String>>,
    until: Option<u64>,
) -> Credential {
    let names: Vec<String> = names.into_iter().map(Into::into).collect();
    let mut caveats = vec![secret_caveat(&names)];
    if let Some(at) = until {
        caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
    }
    root.mint(caveats)
}

/// Narrow an existing credential to a subset of secret names (sub-agent
/// confinement). Appends a confining `AnyOf` — can only ever remove reach.
pub fn attenuate_secret_caps(
    cred: Credential,
    names: impl IntoIterator<Item = impl Into<String>>,
    until: Option<u64>,
) -> Credential {
    let names: Vec<String> = names.into_iter().map(Into::into).collect();
    let mut caveats = vec![secret_caveat(&names)];
    if let Some(at) = until {
        caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
    }
    cred.attenuate(caveats)
}

/// The verification context for a read of secret `name` at clock `now`.
pub fn secret_cap_context(name: &str, now: u64) -> Context {
    Context::new().at(now).attr(CAP_KEY, secret_cap_name(name))
}

/// Why a presented credential was refused read of a secret.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum CapDenied {
    /// The credential string did not decode.
    #[error("credential did not decode: {0}")]
    Decode(String),
    /// The credential verified, but does not grant `secret:<name>` (or is
    /// expired / fails under this account's root — the cap-scoping/account-scoping
    /// teeth). Carries the human refusal reason.
    #[error("credential does not grant read of secret `{name}`: {reason}")]
    NotGranted { name: String, reason: String },
}

/// Decide whether the presented (encoded) credential grants read of secret
/// `name`, verifying under `account_root` at clock `now`. Pure, offline,
/// fail-closed — the cap-gate the store consults before decrypting anything.
pub fn grants_secret(
    cred_enc: &str,
    account_root: &PublicKey,
    name: &str,
    now: u64,
) -> Result<(), CapDenied> {
    let cred = Credential::decode(cred_enc).map_err(|e| CapDenied::Decode(e.to_string()))?;
    let ctx = secret_cap_context(name, now);
    cred.verify(account_root, &ctx)
        .map_err(|r| CapDenied::NotGranted {
            name: name.to_string(),
            reason: r.to_string(),
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_granting_cap_admits_its_secret() {
        let root = RootKey::from_seed([21u8; 32]);
        let cred = mint_secret_caps(&root, ["my-app/DB_URL"], None).encode();
        assert!(grants_secret(&cred, &root.public(), "my-app/DB_URL", 1000).is_ok());
    }

    #[test]
    fn a_cap_does_not_admit_a_different_secret() {
        let root = RootKey::from_seed([22u8; 32]);
        let cred = mint_secret_caps(&root, ["my-app/DB_URL"], None).encode();
        assert!(grants_secret(&cred, &root.public(), "my-app/API_KEY", 1000).is_err());
    }

    #[test]
    fn attenuation_confines_to_a_subset() {
        let root = RootKey::from_seed([23u8; 32]);
        let wide = mint_secret_caps(&root, ["s/A", "s/B"], None);
        let narrow = attenuate_secret_caps(wide, ["s/A"], None).encode();
        assert!(grants_secret(&narrow, &root.public(), "s/A", 1000).is_ok());
        assert!(grants_secret(&narrow, &root.public(), "s/B", 1000).is_err());
    }

    #[test]
    fn another_accounts_root_cannot_admit() {
        let acct_a = RootKey::from_seed([24u8; 32]);
        let acct_b = RootKey::from_seed([25u8; 32]);
        // B mints a cap for the SAME secret name, but A's store verifies under A's root.
        let bs_cred = mint_secret_caps(&acct_b, ["s/A"], None).encode();
        assert!(grants_secret(&bs_cred, &acct_a.public(), "s/A", 1000).is_err());
    }

    #[test]
    fn expiry_is_enforced() {
        let root = RootKey::from_seed([26u8; 32]);
        let cred = mint_secret_caps(&root, ["s/A"], Some(1_000)).encode();
        assert!(grants_secret(&cred, &root.public(), "s/A", 999).is_ok());
        assert!(grants_secret(&cred, &root.public(), "s/A", 1_001).is_err());
    }
}
