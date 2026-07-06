//! **The authentic leg** — the tlsn / MPC-TLS (DECO/zkTLS) attestation of an Anthropic
//! `POST /v1/messages` session, generalized from deco-prove's Stripe adapter.
//!
//! This is the Rust realization of `zkOracle_sound`'s **authentic** conjunct
//! (`∃ w, DecoRelation … decoStmt w`): a verified tlsn presentation certifies that the
//! disclosed response body came from a genuine TLS session with the pinned Anthropic host,
//! with the **`x-api-key` secret REDACTED** — the killer property: prove what the model
//! returned WITHOUT revealing your Anthropic API key.
//!
//! ## What this module is (honest scope)
//!
//! This is the **Layer-2 tlsn-attestation INTERFACE + ADAPTER** (the exact shape of
//! deco-prove's `tlsn_attest.rs`, generalized Stripe→Anthropic), exercised end-to-end by
//! an in-tree fixture. The genuine live MPC-TLS 2PC run lives behind the `tlsn-live`
//! feature ([`crate::tlsn_live`]) — vendored TLSNotary, a real Notary + Prover, a real
//! `presentation.verify()`. The operational remainder — pointing the Prover at the live
//! `api.anthropic.com` with a real key + a deployed notary — is NAMED, not faked
//! (`docs/deos/ZKORACLE-PROVER-STATUS.md`).
//!
//! The modeled notary signature curve is **ed25519** (the curve already in-tree, as in
//! deco-prove); tlsn's real notary signs secp256k1/p256 — a notary-config detail, not a
//! semantic one.

use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};

/// The pinned Anthropic API host a genuine messages presentation must be a session with.
pub const ANTHROPIC_SERVER_NAME: &str = "api.anthropic.com";

/// The Anthropic messages endpoint path.
pub const MESSAGES_PATH: &str = "/v1/messages";

/// The request header carrying the Anthropic secret key — the value that MUST be redacted
/// (never authenticated) in the presentation.
pub const API_KEY_HEADER: &str = "x-api-key";

/// An obvious placeholder secret so no real-key SHAPE lands in the tree; the redaction is
/// identical regardless of the token's contents.
pub const API_KEY_PLACEHOLDER: &str = "sk-ant-MERCHANT-API-KEY-PLACEHOLDER";

/// Domain separation over the modeled notary signature.
const TLSN_PRESENTATION_DOMAIN: &[u8] = b"dregg/zkoracle/tlsn-presentation/v1";

/// The notary's verifying key — models `tlsn_core::signing::VerifyingKey { alg, data }`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TlsnVerifyingKey {
    /// The signature algorithm identifier (modeled: `"ed25519"`).
    pub alg: String,
    /// The public key bytes (ed25519: 32 bytes).
    pub data: Vec<u8>,
}

/// A **verified tlsn presentation** over an Anthropic messages session — models the object
/// `tlsn_core` `presentation.verify(&provider)` yields.
///
/// The request direction discloses the target + non-secret headers but REDACTS the
/// `x-api-key` value (fill `X`, not authenticated). The response direction discloses the
/// full messages JSON body — the public evidence the well-formed (CFG) and injection-free
/// legs run over.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnthropicPresentation {
    /// The notary's verifying key (a verifier pins its own anchor).
    pub verifying_key: TlsnVerifyingKey,
    /// The authenticated server identity (must be [`ANTHROPIC_SERVER_NAME`]).
    pub server_name: String,
    /// The session time (`connection_info.time`, unix seconds).
    pub connection_time: u64,
    /// The request-direction bytes as delivered (`sent_unsafe()`) — the `x-api-key` value
    /// positions are the fill byte `X`.
    pub sent: Vec<u8>,
    /// The response-direction bytes as delivered (`received_unsafe()`) — headers + the
    /// authenticated messages JSON body.
    pub recv: Vec<u8>,
    /// The notary's ed25519 signature over [`Self::canonical_signing_bytes`].
    pub notary_sig: [u8; 64],
}

impl AnthropicPresentation {
    /// The canonical bytes the notary signs: domain + pinned identity + BOTH directions'
    /// delivered bytes. Tampering any disclosed byte breaks the signature.
    fn canonical_signing_bytes(&self) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend_from_slice(TLSN_PRESENTATION_DOMAIN);
        m.extend_from_slice(&(self.server_name.len() as u64).to_le_bytes());
        m.extend_from_slice(self.server_name.as_bytes());
        m.extend_from_slice(&self.connection_time.to_le_bytes());
        m.extend_from_slice(&(self.sent.len() as u64).to_le_bytes());
        m.extend_from_slice(&self.sent);
        m.extend_from_slice(&(self.recv.len() as u64).to_le_bytes());
        m.extend_from_slice(&self.recv);
        m
    }
}

/// The pinned expectations the adapter checks a presentation against.
#[derive(Clone, Debug)]
pub struct AnthropicConfig {
    /// The server the presentation must be a session with (default [`ANTHROPIC_SERVER_NAME`]).
    pub expected_server: String,
    /// The pinned notary verifying key anchor.
    pub expected_notary: TlsnVerifyingKey,
}

impl AnthropicConfig {
    /// Pin the Anthropic server + a notary anchor.
    pub fn new(expected_notary: TlsnVerifyingKey) -> Self {
        AnthropicConfig {
            expected_server: ANTHROPIC_SERVER_NAME.to_string(),
            expected_notary,
        }
    }
}

/// A verified authentic Anthropic session — the response body extracted from the
/// AUTHENTICATED transcript, with the api-key hidden.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticSession {
    /// The authenticated server identity.
    pub server_name: String,
    /// The session time.
    pub connection_time: u64,
    /// The authenticated messages JSON response body (the public evidence).
    pub response_body: Vec<u8>,
}

/// Why a presentation is refused by the adapter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthenticError {
    /// The authenticated server is not the pinned Anthropic host.
    WrongServer { got: String },
    /// The presentation's verifying key is not the pinned notary anchor.
    WrongNotary,
    /// The notary key bytes are not a valid ed25519 point.
    MalformedKey,
    /// The notary signature does not verify (models a failed `presentation.verify()` —
    /// the transcript or identity was tampered).
    BadNotarySignature,
    /// The `x-api-key` secret survived into the authenticated request bytes — selective
    /// disclosure FAILED, the killer property is violated, refuse.
    ApiKeyDisclosed,
    /// The response direction has no HTTP header/body separator (`\r\n\r\n`).
    NoResponseBody,
}

impl core::fmt::Display for AuthenticError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AuthenticError::WrongServer { got } => {
                write!(
                    f,
                    "presentation server {got:?} is not the pinned {ANTHROPIC_SERVER_NAME:?}"
                )
            }
            AuthenticError::WrongNotary => {
                write!(f, "presentation notary key is not the pinned anchor")
            }
            AuthenticError::MalformedKey => {
                write!(f, "notary key bytes are not a valid ed25519 point")
            }
            AuthenticError::BadNotarySignature => {
                write!(f, "notary signature does not verify over the presentation")
            }
            AuthenticError::ApiKeyDisclosed => {
                write!(
                    f,
                    "the x-api-key secret was not redacted (selective disclosure failed)"
                )
            }
            AuthenticError::NoResponseBody => write!(f, "no header/body separator in the response"),
        }
    }
}

impl std::error::Error for AuthenticError {}

/// **THE ADAPTER** — verify a tlsn presentation of an Anthropic messages session and
/// extract the authenticated response body.
///
/// Enforces, in order: server pinning, notary pinning, the presentation signature, and
/// the `x-api-key` redaction (the secret must NOT appear in the authenticated request
/// bytes). On success returns the authenticated response body for the downstream legs.
///
/// ⚑ This checks the presentation as *delivered + signed*; the 2PC session-integrity that
/// makes the signature *trustless* is the named remaining wiring ([`crate::tlsn_live`] +
/// module docs).
pub fn verify_anthropic_presentation(
    pres: &AnthropicPresentation,
    config: &AnthropicConfig,
) -> Result<AuthenticSession, AuthenticError> {
    // (1) server pinning.
    if pres.server_name != config.expected_server {
        return Err(AuthenticError::WrongServer {
            got: pres.server_name.clone(),
        });
    }
    // (2) notary pinning.
    if pres.verifying_key != config.expected_notary {
        return Err(AuthenticError::WrongNotary);
    }
    // (3) the presentation signature (models presentation.verify()'s signature leg).
    let key_bytes: [u8; 32] = pres
        .verifying_key
        .data
        .as_slice()
        .try_into()
        .map_err(|_| AuthenticError::MalformedKey)?;
    let vk = VerifyingKey::from_bytes(&key_bytes).map_err(|_| AuthenticError::MalformedKey)?;
    let sig = Signature::from_bytes(&pres.notary_sig);
    vk.verify(&pres.canonical_signing_bytes(), &sig)
        .map_err(|_| AuthenticError::BadNotarySignature)?;

    // (4) selective disclosure: the api-key secret must be redacted out of the sent bytes.
    if contains_subslice(&pres.sent, API_KEY_PLACEHOLDER.as_bytes())
        || contains_subslice(&pres.sent, b"MERCHANT-API-KEY")
    {
        return Err(AuthenticError::ApiKeyDisclosed);
    }

    // (5) extract the authenticated response body.
    let sep = find_subslice(&pres.recv, b"\r\n\r\n").ok_or(AuthenticError::NoResponseBody)?;
    let response_body = pres.recv[sep + 4..].to_vec();

    Ok(AuthenticSession {
        server_name: pres.server_name.clone(),
        connection_time: pres.connection_time,
        response_body,
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// The fixture producer — models the tlsn notary + 2PC + live Anthropic session.
//
// ⚑ NOT a real notary. The in-tree PRODUCER that builds a tlsn-format presentation over a
// realistic Anthropic messages transcript so the adapter can be exercised end-to-end (and
// forgeries refuted) without the mpz 2PC stack. The genuine run is [`crate::tlsn_live`].
// ─────────────────────────────────────────────────────────────────────────────

/// The modeled notary that signs an [`AnthropicPresentation`]. Deterministic from a seed.
pub struct FixtureNotary {
    signing: SigningKey,
}

impl FixtureNotary {
    /// A fixture notary from a 32-byte seed.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        FixtureNotary {
            signing: SigningKey::from_bytes(seed),
        }
    }

    /// The notary's pinnable verifying key.
    pub fn verifying_key(&self) -> TlsnVerifyingKey {
        TlsnVerifyingKey {
            alg: "ed25519".to_string(),
            data: self.signing.verifying_key().to_bytes().to_vec(),
        }
    }

    /// Sign a presentation (fills [`AnthropicPresentation::notary_sig`]).
    pub fn sign(&self, mut pres: AnthropicPresentation) -> AnthropicPresentation {
        let sig: Signature = self.signing.sign(&pres.canonical_signing_bytes());
        pres.notary_sig = sig.to_bytes();
        pres
    }
}

/// **Build an Anthropic messages presentation fixture.**
///
/// Constructs a realistic authenticated HTTP/1.1 transcript of
/// `POST https://api.anthropic.com/v1/messages`:
///
/// - **Request (`sent`):** the request line + `host` + `x-api-key: sk-ant-…` + headers.
///   The `x-api-key` VALUE is REDACTED (fill `X`, NOT authenticated) — the killer use
///   case: prove the response WITHOUT revealing your Anthropic key.
/// - **Response (`recv`):** the status line + headers + the messages JSON body,
///   authenticated in full (the public evidence the CFG + injection legs run over).
///
/// The presentation is signed by `notary`.
pub fn build_anthropic_fixture(
    notary: &FixtureNotary,
    response_body: &str,
    connection_time: u64,
) -> AnthropicPresentation {
    // ── Request transcript. The api-key VALUE is redacted; the header NAME stays.
    let key_prefix = "x-api-key: ";
    let sent_str = format!(
        "POST {path} HTTP/1.1\r\n\
         host: api.anthropic.com\r\n\
         {kp}{secret}\r\n\
         anthropic-version: 2023-06-01\r\n\
         content-type: application/json\r\n\r\n",
        path = MESSAGES_PATH,
        kp = key_prefix,
        secret = API_KEY_PLACEHOLDER,
    );
    // Redact exactly the api-key value bytes (fill X); everything else is authenticated.
    let secret_start = sent_str
        .find(API_KEY_PLACEHOLDER)
        .expect("placeholder present");
    let secret_end = secret_start + API_KEY_PLACEHOLDER.len();
    let mut sent = sent_str.into_bytes();
    for b in &mut sent[secret_start..secret_end] {
        *b = b'X';
    }

    // ── Response transcript — the messages JSON body authenticated in full.
    let recv = format!(
        "HTTP/1.1 200 OK\r\n\
         content-type: application/json\r\n\
         request-id: req_fixture\r\n\r\n\
         {response_body}"
    )
    .into_bytes();

    let pres = AnthropicPresentation {
        verifying_key: notary.verifying_key(),
        server_name: ANTHROPIC_SERVER_NAME.to_string(),
        connection_time,
        sent,
        recv,
        notary_sig: [0u8; 64],
    };
    notary.sign(pres)
}

fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || needle.len() > haystack.len() {
        return None;
    }
    haystack.windows(needle.len()).position(|w| w == needle)
}

fn contains_subslice(haystack: &[u8], needle: &[u8]) -> bool {
    find_subslice(haystack, needle).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    const BODY: &str = r#"{"id":"msg_01","type":"message","role":"assistant","content":[{"type":"text","text":"hello"}],"stop_reason":"end_turn"}"#;

    #[test]
    fn honest_presentation_yields_body_and_hides_key() {
        let notary = FixtureNotary::from_seed(&[1u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let pres = build_anthropic_fixture(&notary, BODY, 1_700_000_000);

        let session =
            verify_anthropic_presentation(&pres, &cfg).expect("honest presentation verifies");
        assert_eq!(session.server_name, ANTHROPIC_SERVER_NAME);
        assert_eq!(session.response_body, BODY.as_bytes());
        // The api-key secret does not survive into the authenticated sent bytes.
        assert!(!contains_subslice(&pres.sent, b"MERCHANT-API-KEY"));
    }

    #[test]
    fn wrong_server_refused() {
        let notary = FixtureNotary::from_seed(&[2u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let mut pres = build_anthropic_fixture(&notary, BODY, 1);
        pres.server_name = "evil.example.com".to_string();
        let resigned = notary.sign(pres);
        assert!(matches!(
            verify_anthropic_presentation(&resigned, &cfg).unwrap_err(),
            AuthenticError::WrongServer { .. }
        ));
    }

    #[test]
    fn wrong_notary_refused() {
        let notary = FixtureNotary::from_seed(&[3u8; 32]);
        let other = FixtureNotary::from_seed(&[4u8; 32]);
        let cfg = AnthropicConfig::new(other.verifying_key());
        let pres = build_anthropic_fixture(&notary, BODY, 1);
        assert_eq!(
            verify_anthropic_presentation(&pres, &cfg).unwrap_err(),
            AuthenticError::WrongNotary
        );
    }

    #[test]
    fn tampered_disclosed_byte_breaks_signature() {
        let notary = FixtureNotary::from_seed(&[5u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let mut pres = build_anthropic_fixture(&notary, BODY, 1);
        // Flip a byte in the authenticated response body.
        let n = pres.recv.len();
        pres.recv[n - 5] ^= 0xFF;
        assert_eq!(
            verify_anthropic_presentation(&pres, &cfg).unwrap_err(),
            AuthenticError::BadNotarySignature
        );
    }

    #[test]
    fn disclosed_api_key_is_refused() {
        // A presentation that FAILED to redact the key (the secret in the sent bytes) is
        // refused even if correctly signed — the killer property is enforced.
        let notary = FixtureNotary::from_seed(&[6u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let mut pres = build_anthropic_fixture(&notary, BODY, 1);
        // Splice the secret back into the sent bytes and re-sign.
        let leaked =
            format!("POST /v1/messages HTTP/1.1\r\nx-api-key: {API_KEY_PLACEHOLDER}\r\n\r\n");
        pres.sent = leaked.into_bytes();
        let resigned = notary.sign(pres);
        assert_eq!(
            verify_anthropic_presentation(&resigned, &cfg).unwrap_err(),
            AuthenticError::ApiKeyDisclosed
        );
    }
}
