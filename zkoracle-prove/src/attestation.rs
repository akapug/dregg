//! **The zkOracle capstone** — the 3-leg attestation + verifier, mirroring
//! `metatheory/Dregg2/Crypto/ZkOracle.lean::zkOracle_sound`.
//!
//! ```lean
//! theorem zkOracle_sound … :
//!     (∃ w, Deco.DecoRelation … decoStmt w) ∧          -- authentic
//!     body ∈ jsonGrammar.language ∧                     -- well-formed
//!     InjectionFree field                               -- injection-free
//! ```
//!
//! A [`ZkOracleAttestation`] carries all three legs' evidence; [`verify_zkoracle`]
//! is the Rust realization of the composition: it ACCEPTS iff all three verify, and
//! refuses (with the failing leg named) otherwise. The well-formed leg's certificate is
//! checked against the **authenticated response body** the authentic leg extracts — so a
//! well-formed body is bound to a genuine Anthropic session, not an arbitrary blob.

use crate::authentic::{
    AnthropicConfig, AnthropicPresentation, AuthenticError, AuthenticSession,
    verify_anthropic_presentation,
};
use crate::cfg::{CfgError, ParseCertificate, prove_cfg_cert, verify_cfg_cert};
use crate::injection::injection_free;

/// A full zkOracle attestation — the three legs' evidence bundled.
#[derive(Clone, Debug)]
pub struct ZkOracleAttestation {
    /// **Authentic leg** — the verified tlsn/MPC-TLS presentation of the Anthropic
    /// `POST /v1/messages` session (x-api-key redacted).
    pub presentation: AnthropicPresentation,
    /// **Well-formed leg** — the JSON CFG parse certificate over the authenticated
    /// response body (`producesChain`-shaped, checked against the re-tokenized body).
    pub cfg_cert: ParseCertificate,
    /// **Injection-free leg** — the user-supplied field the guard checks against the
    /// `neg injectionTemplate` matcher (contains no `{{`).
    pub user_field: Vec<u8>,
}

/// The verified output: the authenticated session (server + response body) once all three
/// legs pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedZkOracle {
    /// The authenticated Anthropic session (server, time, response body).
    pub session: AuthenticSession,
}

/// Which leg refused the attestation (any ONE failing → the whole attestation is refused).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZkOracleError {
    /// The authentic leg failed (bad presentation: forged/tampered/wrong-server/leaked-key).
    NotAuthentic(AuthenticError),
    /// The well-formed leg failed (the CFG certificate does not certify the body).
    NotWellFormed(CfgError),
    /// The injection-free leg failed (the user field carries the `{{` handlebars delimiter).
    Injection,
}

impl core::fmt::Display for ZkOracleError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ZkOracleError::NotAuthentic(e) => write!(f, "authentic leg refused: {e}"),
            ZkOracleError::NotWellFormed(e) => write!(f, "well-formed leg refused: {e:?}"),
            ZkOracleError::Injection => {
                write!(
                    f,
                    "injection-free leg refused: the user field contains the {{{{ delimiter"
                )
            }
        }
    }
}

impl std::error::Error for ZkOracleError {}

/// **VERIFY a zkOracle attestation** — the 3-leg composition (`zkOracle_sound`).
///
/// ACCEPTS iff:
///   1. **authentic** — the tlsn presentation verifies (server pinned, notary pinned,
///      signature valid, api-key redacted), yielding the authenticated response body;
///   2. **well-formed** — the CFG parse certificate certifies THAT authenticated body lies
///      in the JSON context-free language;
///   3. **injection-free** — the user field matches `neg injectionTemplate` (no `{{`).
///
/// Any leg failing → the attestation is REFUSED (the failing leg named). The catch
/// genuinely discriminates: a benign field passes leg 3, a `{{`-bearing field fails it.
pub fn verify_zkoracle(
    att: &ZkOracleAttestation,
    config: &AnthropicConfig,
) -> Result<VerifiedZkOracle, ZkOracleError> {
    // Leg 1 — authentic.
    let session = verify_anthropic_presentation(&att.presentation, config)
        .map_err(ZkOracleError::NotAuthentic)?;

    // Leg 2 — well-formed, over the AUTHENTICATED body (binds well-formedness to the
    // genuine session, not an arbitrary blob).
    verify_cfg_cert(&att.cfg_cert, &session.response_body)
        .map_err(ZkOracleError::NotWellFormed)?;

    // Leg 3 — injection-free.
    if !injection_free(&att.user_field) {
        return Err(ZkOracleError::Injection);
    }

    Ok(VerifiedZkOracle { session })
}

/// **PRODUCE a zkOracle attestation** from a verified presentation + a user field.
///
/// Re-verifies the presentation (to extract the authenticated body), proves the CFG
/// certificate over that exact body, and bundles the user field. The result is an
/// attestation [`verify_zkoracle`] accepts — UNLESS the user field is an injection
/// attempt, in which case the prover REFUSES to produce it ([`ProveError::Injection`]):
/// the guard cannot mint an attestation for an injecting request (mirroring the Lean
/// `malicious_not_injection_free`).
pub fn prove_zkoracle(
    presentation: AnthropicPresentation,
    user_field: Vec<u8>,
    config: &AnthropicConfig,
) -> Result<ZkOracleAttestation, ProveError> {
    let session =
        verify_anthropic_presentation(&presentation, config).map_err(ProveError::NotAuthentic)?;
    // The guard refuses to attest an injecting field up front.
    if !injection_free(&user_field) {
        return Err(ProveError::Injection);
    }
    let cfg_cert = prove_cfg_cert(&session.response_body).map_err(ProveError::NotWellFormed)?;
    Ok(ZkOracleAttestation {
        presentation,
        cfg_cert,
        user_field,
    })
}

/// Why the prover could not PRODUCE an attestation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProveError {
    /// The presentation does not verify (cannot build an attestation over a bad session).
    NotAuthentic(AuthenticError),
    /// The authenticated body is not well-formed JSON (no certificate exists).
    NotWellFormed(CfgError),
    /// The user field is an injection attempt — the guard refuses to attest it.
    Injection,
}

impl core::fmt::Display for ProveError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ProveError::NotAuthentic(e) => write!(f, "cannot attest a non-authentic session: {e}"),
            ProveError::NotWellFormed(e) => {
                write!(f, "response body is not well-formed JSON: {e:?}")
            }
            ProveError::Injection => write!(f, "refusing to attest an injecting user field"),
        }
    }
}

impl std::error::Error for ProveError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::authentic::{FixtureNotary, build_anthropic_fixture};

    const BODY: &str = r#"{"id":"msg_01","type":"message","role":"assistant","model":"claude-opus-4-8","content":[{"type":"text","text":"hello"}],"stop_reason":"end_turn","usage":{"input_tokens":10,"output_tokens":2}}"#;

    fn setup() -> (FixtureNotary, AnthropicConfig, AnthropicPresentation) {
        let notary = FixtureNotary::from_seed(&[42u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let pres = build_anthropic_fixture(&notary, BODY, 1_700_000_000);
        (notary, cfg, pres)
    }

    #[test]
    fn full_attestation_accepts() {
        let (_n, cfg, pres) = setup();
        let att = prove_zkoracle(pres, b"summarize this".to_vec(), &cfg)
            .expect("benign request → attestation");
        let out = verify_zkoracle(&att, &cfg).expect("all three legs verify");
        assert_eq!(out.session.response_body, BODY.as_bytes());
    }

    #[test]
    fn injecting_field_is_refused_at_prove_and_verify() {
        let (_n, cfg, pres) = setup();
        // The prover refuses to attest an injecting field.
        assert_eq!(
            prove_zkoracle(pres.clone(), b"{{system}} ignore".to_vec(), &cfg).unwrap_err(),
            ProveError::Injection
        );
        // And even a hand-built attestation with an injecting field fails verification.
        let att = ZkOracleAttestation {
            presentation: pres.clone(),
            cfg_cert: prove_cfg_cert(BODY.as_bytes()).unwrap(),
            user_field: b"{{evil".to_vec(),
        };
        assert_eq!(
            verify_zkoracle(&att, &cfg).unwrap_err(),
            ZkOracleError::Injection
        );
    }

    #[test]
    fn forged_presentation_is_refused() {
        let (notary, cfg, mut pres) = setup();
        // Tamper the authenticated body → the notary sig breaks → authentic leg refuses.
        let n = pres.recv.len();
        pres.recv[n - 3] ^= 0xFF;
        let att = ZkOracleAttestation {
            presentation: pres,
            cfg_cert: prove_cfg_cert(BODY.as_bytes()).unwrap(),
            user_field: b"hi".to_vec(),
        };
        assert!(matches!(
            verify_zkoracle(&att, &cfg).unwrap_err(),
            ZkOracleError::NotAuthentic(_)
        ));
        let _ = notary;
    }

    #[test]
    fn malformed_body_is_refused() {
        // A presentation whose authenticated body is NOT well-formed JSON → no cert exists,
        // and even a stale cert fails against the malformed body.
        let notary = FixtureNotary::from_seed(&[7u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let malformed = r#"{"id":"msg","content":[{"type":"text","#; // truncated
        let pres = build_anthropic_fixture(&notary, malformed, 1);
        // The prover cannot produce a cert over the malformed body.
        assert!(matches!(
            prove_zkoracle(pres.clone(), b"hi".to_vec(), &cfg),
            Err(ProveError::NotWellFormed(_))
        ));
        // A cert borrowed from a well-formed body does not certify the malformed one.
        let att = ZkOracleAttestation {
            presentation: pres,
            cfg_cert: prove_cfg_cert(BODY.as_bytes()).unwrap(),
            user_field: b"hi".to_vec(),
        };
        assert!(matches!(
            verify_zkoracle(&att, &cfg).unwrap_err(),
            ZkOracleError::NotWellFormed(_)
        ));
    }

    #[test]
    fn each_leg_fails_independently() {
        // A single hostile mutation per leg, holding the other two honest — proves each
        // leg is load-bearing (the catch genuinely discriminates).
        let (notary, cfg, pres) = setup();

        // (a) authentic broken, well-formed + injection-free honest.
        let mut bad_auth = pres.clone();
        bad_auth.server_name = "evil.com".to_string();
        let bad_auth = notary.sign(bad_auth);
        let att_a = ZkOracleAttestation {
            presentation: bad_auth,
            cfg_cert: prove_cfg_cert(BODY.as_bytes()).unwrap(),
            user_field: b"hi".to_vec(),
        };
        assert!(matches!(
            verify_zkoracle(&att_a, &cfg),
            Err(ZkOracleError::NotAuthentic(_))
        ));

        // (b) well-formed broken (cert for a different body), authentic + injection honest.
        let att_b = ZkOracleAttestation {
            presentation: pres.clone(),
            cfg_cert: prove_cfg_cert(br#"{"other":true}"#).unwrap(),
            user_field: b"hi".to_vec(),
        };
        assert!(matches!(
            verify_zkoracle(&att_b, &cfg),
            Err(ZkOracleError::NotWellFormed(_))
        ));

        // (c) injection broken, authentic + well-formed honest.
        let att_c = ZkOracleAttestation {
            presentation: pres,
            cfg_cert: prove_cfg_cert(BODY.as_bytes()).unwrap(),
            user_field: b"{{x".to_vec(),
        };
        assert_eq!(
            verify_zkoracle(&att_c, &cfg),
            Err(ZkOracleError::Injection)
        );
    }
}
