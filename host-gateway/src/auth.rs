//! Cap-scope subject resolution — who a request is, for the `/api/*` reads.
//!
//! The cap-scoped reads return exactly the records owned by the authenticated
//! subject, so the gateway must know that subject **soundly**. Two postures:
//!
//! * [`SubjectAuth::Verified`] — the gateway verifies a presented `dga1_` credential
//!   itself, under a configured root, through [`webauth_core::decide`], and derives the
//!   subject from the admitted credential ([`webauth_core::subject_of`]). It trusts no
//!   upstream — a forged / wrong-root / expired / revoked / under-capped credential is
//!   refused. This is the default and the improvement over the retired gateway, which
//!   trusted a proxy-set subject header.
//!
//! * [`SubjectAuth::TrustedHeader`] — trust a pre-verified forward-auth header set by a
//!   reverse proxy that already ran the credential check (the retired posture). Sound
//!   ONLY when the listener is bound to an internal interface so the header cannot be
//!   forged by a direct caller. Offered for that deployment, documented as such.
//!
//! Either way, a missing / unresolved subject yields `None`, and the read spine fails
//! **closed** (`401`) — the unscoped, cloud-wide catalog is never returned.

use http_serve::ServeRequest;
use webauth_core::config::WebAuthConfig;
use webauth_core::{AuthInput, decide, subject_of};

/// How the gateway establishes the cap-scope subject for a request.
pub enum SubjectAuth {
    /// Verify the presented `dga1_` credential under `config` for `required_cap`, and
    /// derive the subject from the admitted credential. The gateway is the verifier.
    Verified {
        /// The forward-auth decision config (root pubkey, revocation set, break-glass).
        config: WebAuthConfig,
        /// The capability the console-read surface requires.
        required_cap: String,
    },
    /// Trust a pre-verified subject header (name lower-cased), e.g. `x-dregg-subject`.
    /// Sound only behind an internal-only bind. See the module docs.
    TrustedHeader {
        /// The header the upstream proxy sets to the verified subject.
        header: String,
    },
}

impl SubjectAuth {
    /// The verifying posture (the default): verify a credential under `config` for
    /// `required_cap`.
    pub fn verified(config: WebAuthConfig, required_cap: impl Into<String>) -> SubjectAuth {
        SubjectAuth::Verified {
            config,
            required_cap: required_cap.into(),
        }
    }

    /// The trusted-header posture: trust `header` set by an internal-only proxy.
    pub fn trusted_header(header: impl Into<String>) -> SubjectAuth {
        SubjectAuth::TrustedHeader {
            header: header.into(),
        }
    }

    /// Resolve the verified subject for `req`, or `None` (fail-closed) if there is no
    /// sound subject.
    pub fn resolve(&self, req: &ServeRequest) -> Option<String> {
        match self {
            SubjectAuth::TrustedHeader { header } => req
                .header(header)
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .map(str::to_string),
            SubjectAuth::Verified {
                config,
                required_cap,
            } => {
                let credential = presented_credential(req)?;
                let input = AuthInput {
                    credential: Some(credential.clone()),
                    break_glass: req.header("x-dregg-break-glass").map(str::to_string),
                    required_cap: Some(required_cap.clone()),
                    now: unix_now(),
                };
                if !decide(config, &input).admitted() {
                    return None;
                }
                // The credential verified + is capped; its subject is the scope key.
                subject_of(&credential)
            }
        }
    }
}

/// Pull a presented `dga1_` credential off a request: an `Authorization: Bearer <tok>`
/// header, else an `X-Dregg-Credential` header. Duplicate-safe (a smuggled duplicate
/// reads back `None`, per [`ServeRequest::header`]).
pub fn presented_credential(req: &ServeRequest) -> Option<String> {
    if let Some(auth) = req.header("authorization") {
        let auth = auth.trim();
        if let Some(bearer) = auth
            .strip_prefix("Bearer ")
            .or_else(|| auth.strip_prefix("bearer "))
        {
            let tok = bearer.trim();
            if !tok.is_empty() {
                return Some(tok.to_string());
            }
        }
    }
    req.header("x-dregg-credential")
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_string)
}

/// The verifier's wall clock (unix seconds) for a credential's temporal caveats.
pub fn unix_now() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use http_serve::HttpMethod;

    fn req_with(headers: Vec<(&str, &str)>) -> ServeRequest {
        ServeRequest {
            method: HttpMethod::Get,
            host: "h".into(),
            target: "/api/sites".into(),
            body: Vec::new(),
            headers: headers
                .into_iter()
                .map(|(n, v)| (n.to_ascii_lowercase(), v.to_string()))
                .collect(),
        }
    }

    #[test]
    fn trusted_header_reads_the_subject_and_is_duplicate_safe() {
        let auth = SubjectAuth::trusted_header("x-dregg-subject");
        assert_eq!(
            auth.resolve(&req_with(vec![("x-dregg-subject", "dregg:alice")]))
                .as_deref(),
            Some("dregg:alice")
        );
        // Empty / missing -> None (fail-closed).
        assert_eq!(
            auth.resolve(&req_with(vec![("x-dregg-subject", "  ")])),
            None
        );
        assert_eq!(auth.resolve(&req_with(vec![])), None);
        // A smuggled duplicate reads back None.
        assert_eq!(
            auth.resolve(&req_with(vec![
                ("x-dregg-subject", "dregg:alice"),
                ("x-dregg-subject", "dregg:mallory"),
            ])),
            None
        );
    }

    #[test]
    fn presented_credential_prefers_bearer_then_header() {
        assert_eq!(
            presented_credential(&req_with(vec![("authorization", "Bearer dga1_tok")])).as_deref(),
            Some("dga1_tok")
        );
        assert_eq!(
            presented_credential(&req_with(vec![("x-dregg-credential", "dga1_hdr")])).as_deref(),
            Some("dga1_hdr")
        );
        assert_eq!(presented_credential(&req_with(vec![])), None);
    }

    // THE VERIFY-DONT-TRUST TOOTH: the gateway verifies a presented credential ITSELF
    // and derives the subject from it — a genuine capped credential resolves to its
    // subject; a credential lacking the required cap (or none at all) resolves to None.
    #[test]
    fn verified_path_derives_the_subject_from_a_genuine_capped_credential() {
        use dregg_agent::cred::RootKey;
        use webauth_core::grant::mint_caps;

        let root = RootKey::from_seed([7u8; 32]);
        let cfg = WebAuthConfig {
            root_pubkey_hex: Some(root.public().to_hex()),
            ..WebAuthConfig::default()
        };
        let token = mint_caps(&root, ["console-read"], None).encode();
        let auth = SubjectAuth::verified(cfg, "console-read");

        // A genuine credential carrying the required cap → its subject.
        let resolved = auth.resolve(&req_with(vec![(
            "authorization",
            &format!("Bearer {token}"),
        )]));
        assert_eq!(
            resolved,
            subject_of(&token),
            "the derived subject is the credential's"
        );
        assert!(resolved.is_some());

        // No credential → None (fail-closed).
        assert_eq!(auth.resolve(&req_with(vec![])), None);

        // A genuine credential LACKING the required cap → None (not authorized).
        let uncapped = mint_caps(&root, ["something-else"], None).encode();
        assert_eq!(
            auth.resolve(&req_with(vec![("x-dregg-credential", &uncapped)])),
            None,
            "a credential without the console-read cap does not resolve a subject"
        );
    }
}
