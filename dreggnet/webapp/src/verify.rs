//! `verify` — the trustless read of a published site: re-witness, with **no trust
//! in the serving host**, that the bytes a visitor was served ARE the bytes the
//! owner published.
//!
//! Hosting already commits a site to a [`content_root`](crate::hosting::content_root)
//! and seals each publish into a prev-hash-chained, ed25519-signed receipt stream
//! ([`SiteRegistry::signed`](crate::hosting::SiteRegistry::signed)). This module
//! closes the loop on the *read* side: it turns those two facts into a single
//! self-contained artifact a non-witness downloads and checks.
//!
//! ```text
//!   the host serves                          a client re-witnesses (no trust)
//!   ───────────────                          ────────────────────────────────
//!   GET /.well-known/dregg-receipt.json      verify_site_bundle(bundle, owner_key)
//!     └─ SiteReceiptBundle {                    1. signer == the pinned owner key?
//!          signer,        (the owner key)       2. verify_chain(receipt)  ← signed + intact
//!          receipt,       (signed publish)      3. content_root(content) == receipt.content_root
//!          content,       (the served bytes)       └─ a flipped byte moves the root → REFUSED
//!        }                                      4. manifest commit (the source commitment)
//! ```
//!
//! The trust anchor is the **owner's public key**, known out-of-band (recorded at
//! deploy time, or pinned by a reader). A lying host that flips a served byte moves
//! the recomputed `content_root` away from the signed one (caught at 3); a host that
//! forges a receipt either signs under the wrong key (caught at 1) or breaks the
//! signature over the claimed root (caught at 2). This is the literal "you verify,
//! you don't trust" read — the live caller of [`dreggnet_receipt::verify_chain`].

use std::slice;

use serde::{Deserialize, Serialize};

use dreggnet_receipt::{ChainError, ReceiptBody, verify_chain};

use crate::hosting::{PublishReceipt, SiteContent, content_root};

/// The well-known path a host serves a site's [`SiteReceiptBundle`] at, so a
/// non-witness can fetch the receipt + the served bytes and re-verify them.
pub const SITE_RECEIPT_PATH: &str = "/.well-known/dregg-receipt.json";

/// Where the deploy's source-commitment manifest lives within a published site
/// (the `dregg-deploy` `DeployManifestAsset`). Defined here — rather than depended
/// on from `dregg-deploy` (which sits *above* this crate) — so the verifier can read
/// the committed commit hash out of the served content. The two constants are the
/// same wire path by contract.
pub const DEPLOY_MANIFEST_PATH: &str = "/.well-known/dregg-deploy.json";

/// The complete, self-verifying read artifact for a published site: the owner's
/// signing key, the signed publish receipt, and the served content. A client
/// re-witnesses it with [`verify_site_bundle`] holding only the owner's public key
/// (the trust anchor) — never trusting the host that served it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SiteReceiptBundle {
    /// The producing authority's ed25519 public key — the owner key a reader pins.
    pub signer: [u8; 32],
    /// The signed, prev-hash-chained publish receipt (the turn receipt of the
    /// publish). Its `content_root` is what the served bytes must reproduce.
    pub receipt: PublishReceipt,
    /// The served site content (path → asset). Re-hashed to `content_root` and
    /// checked against the receipt's committed root.
    pub content: SiteContent,
}

/// Why a [`SiteReceiptBundle`] failed to re-witness — each variant a way a host
/// could have lied (and been caught).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SiteVerifyError {
    /// The receipt carried no attestation — a bare projection, not a signed
    /// receipt (the registry that produced it was not a signed one).
    Unsigned,
    /// The receipt was signed by a key other than the one the reader pinned (or
    /// the bundle's declared `signer` disagrees with the receipt's). A forged
    /// receipt re-signed by the host is caught here.
    UnexpectedSigner { expected: [u8; 32], found: [u8; 32] },
    /// The receipt chain did not verify (broken link, bad signature, …) — the
    /// signed commitment over `(name, owner, content_root, …)` is not intact.
    ChainInvalid(ChainError),
    /// The bytes served do not re-hash to the receipt's committed `content_root` —
    /// the host tampered (or substituted) the content. The headline tooth.
    ContentRootMismatch {
        committed: String,
        recomputed: String,
    },
    /// The number of assets served disagrees with what the receipt committed to.
    AssetCountMismatch { committed: usize, served: usize },
    /// The bundle carried no content — nothing to re-witness.
    EmptyContent,
}

impl std::fmt::Display for SiteVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SiteVerifyError::Unsigned => {
                write!(
                    f,
                    "the publish receipt is unsigned (not a re-witnessable receipt)"
                )
            }
            SiteVerifyError::UnexpectedSigner { expected, found } => write!(
                f,
                "receipt signed by an unexpected key: pinned {}, found {}",
                hex32(expected),
                hex32(found)
            ),
            SiteVerifyError::ChainInvalid(e) => write!(f, "receipt chain invalid: {e:?}"),
            SiteVerifyError::ContentRootMismatch {
                committed,
                recomputed,
            } => write!(
                f,
                "served bytes do not match the committed content root \
                 (committed {committed}, served bytes hash to {recomputed})"
            ),
            SiteVerifyError::AssetCountMismatch { committed, served } => write!(
                f,
                "served asset count {served} != the receipt's committed count {committed}"
            ),
            SiteVerifyError::EmptyContent => write!(f, "the bundle carried no content"),
        }
    }
}

impl std::error::Error for SiteVerifyError {}

/// What a successful re-witness establishes about a site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedSite {
    /// The verified site name.
    pub name: String,
    /// The verified owner (the cap holder that published it).
    pub owner: String,
    /// The committed content root the served bytes reproduced.
    pub content_root: String,
    /// The number of assets served (== the receipt's committed count).
    pub asset_count: usize,
    /// The source commitment — the commit the site was built from — read from the
    /// committed deploy manifest, when present.
    pub commit: Option<String>,
}

/// **The trustless read.** Re-witness, with no trust in the source, that a
/// [`SiteReceiptBundle`]'s served bytes are the bytes the owner published.
///
/// When `expected_signer` is `Some`, the receipt must be signed by exactly that key
/// (the pinned owner identity — the trust anchor that makes a *forged* receipt
/// detectable). `None` skips the pin (verifying only internal consistency: signed +
/// intact + bytes-bind-to-root), which a caller uses when it learns the key from the
/// bundle itself.
///
/// On success returns the [`VerifiedSite`]; otherwise the specific [`SiteVerifyError`]
/// that a lying/forged source was caught by.
pub fn verify_site_bundle(
    bundle: &SiteReceiptBundle,
    expected_signer: Option<[u8; 32]>,
) -> Result<VerifiedSite, SiteVerifyError> {
    let receipt = &bundle.receipt;
    let att = receipt.attestation().ok_or(SiteVerifyError::Unsigned)?;

    // (1) the receipt is signed by the pinned owner key, and the bundle's declared
    //     signer agrees with the receipt's own signer.
    if let Some(expected) = expected_signer {
        if att.signer != expected {
            return Err(SiteVerifyError::UnexpectedSigner {
                expected,
                found: att.signer,
            });
        }
    }
    if bundle.signer != att.signer {
        return Err(SiteVerifyError::UnexpectedSigner {
            expected: bundle.signer,
            found: att.signer,
        });
    }

    // (2) the receipt chain verifies — signed, unbroken, tamper-evident. A publish
    //     into a fresh signed registry is a genesis receipt (prev = None), so the
    //     single-receipt chain verifies on its own. THE LIVE verify_chain CALLER.
    verify_chain(slice::from_ref(receipt)).map_err(SiteVerifyError::ChainInvalid)?;

    // (3) the served bytes re-hash to the receipt's committed content root — a host
    //     that flipped a single byte moves the root and is caught here.
    if bundle.content.is_empty() {
        return Err(SiteVerifyError::EmptyContent);
    }
    let recomputed = content_root(&bundle.content);
    if recomputed != receipt.content_root {
        return Err(SiteVerifyError::ContentRootMismatch {
            committed: receipt.content_root.clone(),
            recomputed,
        });
    }
    if receipt.asset_count != bundle.content.len() {
        return Err(SiteVerifyError::AssetCountMismatch {
            committed: receipt.asset_count,
            served: bundle.content.len(),
        });
    }

    Ok(VerifiedSite {
        name: receipt.name.clone(),
        owner: receipt.owner.clone(),
        content_root: receipt.content_root.clone(),
        asset_count: bundle.content.len(),
        commit: manifest_commit(&bundle.content),
    })
}

/// Read the source-commitment commit hash out of a site's committed deploy
/// manifest, if it carries one. The commit is bound into `content_root` (the
/// manifest is a committed asset), so a verified bundle's commit is itself proven.
pub fn manifest_commit(content: &SiteContent) -> Option<String> {
    let asset = content.resolve(DEPLOY_MANIFEST_PATH)?;
    let v: serde_json::Value = serde_json::from_slice(&asset.body).ok()?;
    v.get("commit")?.as_str().map(|s| s.to_string())
}

/// Lower-hex encode a 32-byte key (for display / pinning).
pub fn hex32(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for byte in b {
        s.push(char::from_digit((byte >> 4) as u32, 16).unwrap());
        s.push(char::from_digit((byte & 0xf) as u32, 16).unwrap());
    }
    s
}

/// Parse a 64-char lower/upper-hex string back into a 32-byte key. `None` on a
/// wrong length or a non-hex character.
pub fn parse_hex32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    let bytes = s.as_bytes();
    for (i, slot) in out.iter_mut().enumerate() {
        let hi = (bytes[2 * i] as char).to_digit(16)?;
        let lo = (bytes[2 * i + 1] as char).to_digit(16)?;
        *slot = (hi * 16 + lo) as u8;
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hosting::{PublishCap, SiteContent, SiteRegistry};

    fn signed_blog() -> (SiteRegistry, SiteReceiptBundle) {
        let reg = SiteRegistry::signed([7u8; 32]);
        let content = SiteContent::new()
            .with("/index.html", "<h1>hello from a dregg cell</h1>")
            .with("/style.css", "body{}");
        reg.publish(
            &PublishCap::for_site("agent:ember", "blog"),
            "blog",
            content,
        )
        .expect("publish");
        let bundle = reg
            .site_bundle("blog")
            .expect("a signed registry yields a bundle");
        (reg, bundle)
    }

    #[test]
    fn a_genuine_bundle_verifies() {
        let (reg, bundle) = signed_blog();
        let owner_key = reg.receipt_signer().unwrap();
        let v = verify_site_bundle(&bundle, Some(owner_key)).expect("verifies");
        assert_eq!(v.name, "blog");
        assert_eq!(v.owner, "agent:ember");
        assert_eq!(v.asset_count, 2);
        // No deploy manifest in this hand-built content.
        assert!(v.commit.is_none());
    }

    #[test]
    fn a_flipped_served_byte_is_refused() {
        let (_reg, mut bundle) = signed_blog();
        // The host serves a tampered index.html — the recomputed root moves.
        let asset = bundle.content.assets.get_mut("/index.html").unwrap();
        asset.body = b"<h1>OWNED BY THE HOST</h1>".to_vec();
        let err = verify_site_bundle(&bundle, None).unwrap_err();
        assert!(
            matches!(err, SiteVerifyError::ContentRootMismatch { .. }),
            "got {err:?}"
        );
    }

    #[test]
    fn a_receipt_resigned_by_the_host_is_caught_by_the_pin() {
        // A lying host keeps the served bytes but re-seals the receipt under ITS OWN
        // key (so the chain verifies internally). The owner-key pin catches it.
        let (reg, _) = signed_blog();
        let owner_key = reg.receipt_signer().unwrap();

        let host = SiteRegistry::signed([99u8; 32]); // the host's own key
        let content = SiteContent::new()
            .with("/index.html", "<h1>hello from a dregg cell</h1>")
            .with("/style.css", "body{}");
        host.publish(
            &PublishCap::for_site("agent:ember", "blog"),
            "blog",
            content,
        )
        .unwrap();
        let forged = host.site_bundle("blog").unwrap();

        // Internally consistent (signed under the host key) — but NOT the owner.
        assert!(verify_site_bundle(&forged, None).is_ok());
        let err = verify_site_bundle(&forged, Some(owner_key)).unwrap_err();
        assert!(
            matches!(err, SiteVerifyError::UnexpectedSigner { .. }),
            "got {err:?}"
        );
    }

    #[test]
    fn tampering_the_claimed_root_breaks_the_signature() {
        let (_reg, mut bundle) = signed_blog();
        // Forge the receipt's claimed root while keeping the owner's signature.
        bundle.receipt.content_root = "deadbeefdeadbeef".to_string();
        let err = verify_site_bundle(&bundle, None).unwrap_err();
        assert!(
            matches!(err, SiteVerifyError::ChainInvalid(_)),
            "got {err:?}"
        );
    }

    #[test]
    fn an_unsigned_registry_yields_no_bundle() {
        let reg = SiteRegistry::new();
        reg.publish(
            &PublishCap::for_site("a", "x"),
            "x",
            SiteContent::new().with("/index.html", "hi"),
        )
        .unwrap();
        // The free/local (unsigned) default cannot produce a re-witnessable bundle.
        assert!(reg.site_bundle("x").is_none());
    }

    /// The signed publish receipt commits the REAL Poseidon2 content root, and
    /// `verify_site_bundle` re-witnesses the served bytes against THAT root — the real
    /// verifiable hosting. The committed root is the wide (64-hex) collision-resistant
    /// Poseidon2 commitment (FNV is gone from the path).
    #[test]
    fn verify_re_witnesses_against_the_real_poseidon2_root() {
        let (reg, bundle) = signed_blog();
        let owner_key = reg.receipt_signer().unwrap();
        // The receipt commits the real wide Poseidon2 root.
        assert_eq!(bundle.receipt.content_root.len(), 64);
        // A genuine bundle re-witnesses against it.
        let v =
            verify_site_bundle(&bundle, Some(owner_key)).expect("verifies against the real root");
        assert_eq!(v.content_root, bundle.receipt.content_root);
        // A flipped served byte moves the recomputed Poseidon2 root → refused.
        let mut tampered = bundle.clone();
        tampered.content.assets.get_mut("/index.html").unwrap().body = b"<h1>OWNED</h1>".to_vec();
        assert!(matches!(
            verify_site_bundle(&tampered, Some(owner_key)),
            Err(SiteVerifyError::ContentRootMismatch { .. })
        ));
    }

    /// The anti-aliasing tooth. A lying host substitutes a served asset's bytes for a
    /// SAME-LENGTH `+p` alias — the exact collision class the old 4-byte `% p` packing
    /// accepted. With the injective packing the recomputed `content_root` moves, so
    /// `verify_site_bundle` REJECTS it with `ContentRootMismatch`. Before the fix the
    /// substituted bytes re-hashed to the identical root and verified as genuine.
    #[test]
    fn same_length_alias_substitution_is_refused() {
        use dregg_circuit::field::BabyBear;

        // A `+p` alias pair over one 4-byte chunk (both length 4).
        let honest = vec![0x01u8, 0x00, 0x00, 0x00];
        let forged = vec![0x02u8, 0x00, 0x00, 0x78];
        assert_eq!(honest.len(), forged.len(), "same-length substitution");
        // Witness the OLD shared primitive aliased them (the pre-fix hole).
        assert_eq!(
            BabyBear::from_bytes_packed(&honest),
            BabyBear::from_bytes_packed(&forged),
            "the old 4-byte %p packing aliases this pair"
        );

        let reg = SiteRegistry::signed([7u8; 32]);
        let content = SiteContent::new()
            .with("/index.html", "<h1>hi</h1>")
            .with("/blob.bin", honest);
        reg.publish(
            &PublishCap::for_site("agent:ember", "blog"),
            "blog",
            content,
        )
        .expect("publish");
        let bundle = reg.site_bundle("blog").expect("signed bundle");
        let owner_key = reg.receipt_signer().unwrap();

        // The honest bundle verifies against the committed root.
        assert!(verify_site_bundle(&bundle, Some(owner_key)).is_ok());

        // The host swaps in the same-length aliasing bytes — now REFUSED.
        let mut tampered = bundle.clone();
        tampered.content.assets.get_mut("/blob.bin").unwrap().body = forged;
        let err = verify_site_bundle(&tampered, Some(owner_key)).unwrap_err();
        assert!(
            matches!(err, SiteVerifyError::ContentRootMismatch { .. }),
            "the +p alias substitution must move the injective content_root; got {err:?}"
        );
    }

    #[test]
    fn hex32_round_trips() {
        let k = [
            0u8, 1, 2, 250, 255, 16, 32, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
            19, 20, 21, 22, 23, 24, 25, 26, 27,
        ];
        assert_eq!(parse_hex32(&hex32(&k)), Some(k));
        assert_eq!(parse_hex32("nothex"), None);
    }
}
