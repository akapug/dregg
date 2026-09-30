//! Discharge Gateway HTTP service.
//!
//! This crate provides an axum-based HTTP server that wraps the core
//! [`dregg_macaroon::DischargeGateway`] logic. It exposes:
//!
//! - `POST /discharge` — request a discharge macaroon (signed by the ticket's
//!   holder key; see [`dregg_macaroon::DischargeRequest`])
//! - `GET /conditions` — the ticket conditions this gateway can discharge
//! - `GET /health` — health check with metrics
//!
//! # Configuration
//!
//! ```toml
//! [gateway]
//! bind = "0.0.0.0:8421"
//! signing_key_file = "/etc/dregg/gateway.key"   # 64 hex chars: the shared KA
//! location = "https://gateway.example.com"
//!
//! # Trusted signers of payment attestations. Without this section, every
//! # ticket that demands payment is refused.
//! [payment]
//! attestor_keys = ["<ed25519 pubkey hex>"]
//!
//! # Proof verifiers, by id. A ticket's proof condition names one of these.
//! [[proof_verifiers]]
//! id = "kyc"
//! kind = "ed25519_attestation"
//! attestor_keys = ["<ed25519 pubkey hex>"]
//!
//! # Operator conditions, applied to every ticket.
//! [[conditions]]
//! type = "rate_limit"
//! max_per_hour = 10
//! ```

use std::collections::HashSet;
use std::sync::Arc;

use axum::{
    Json, Router,
    extract::State,
    http::StatusCode,
    routing::{get, post},
};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;
use zeroize::Zeroizing;

use dregg_macaroon::{
    AllowlistEvaluator, DischargeGateway, PaymentAttestation, PaymentEvaluator, ProofAttestation,
    ProofVerifierFn, RateLimitEvaluator, VerifyingProofEvaluator,
};

// =============================================================================
// Configuration
// =============================================================================

/// Top-level gateway configuration (parsed from TOML).
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GatewayConfig {
    pub gateway: GatewaySettings,
    /// Payment attestation trust. Absent: payment conditions always refuse.
    #[serde(default)]
    pub payment: Option<PaymentConfig>,
    /// Proof verifiers ticket and operator proof conditions can name.
    #[serde(default)]
    pub proof_verifiers: Vec<ProofVerifierConfig>,
    /// Operator conditions applied to every ticket.
    #[serde(default)]
    pub conditions: Vec<ConditionConfig>,
}

/// Core gateway settings.
///
/// The shared key is read only from `signing_key_file`. There is no inline key
/// field, so no `{:?}` of the configuration can print it.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GatewaySettings {
    /// Bind address (e.g., "0.0.0.0:8421").
    pub bind: String,
    /// Path to the 32-byte shared key file (hex-encoded).
    pub signing_key_file: String,
    /// The gateway's public location URL.
    pub location: String,
    /// Discharge TTL in seconds (default: 300).
    #[serde(default = "default_ttl")]
    pub discharge_ttl_secs: i64,
}

fn default_ttl() -> i64 {
    300
}

/// Trusted payment attestors.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PaymentConfig {
    /// Ed25519 public keys (hex) whose [`PaymentAttestation`]s are accepted.
    pub attestor_keys: Vec<String>,
}

/// The proof verifier kinds this binary ships.
#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
pub enum ProofVerifierKind {
    /// A [`ProofAttestation`]: an Ed25519 signature by a trusted attestor over
    /// the statement, the ticket and the holder.
    #[serde(rename = "ed25519_attestation")]
    Ed25519Attestation,
}

/// A named proof verifier.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProofVerifierConfig {
    pub id: String,
    pub kind: ProofVerifierKind,
    pub attestor_keys: Vec<String>,
}

/// An operator condition, applied to every ticket.
#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "type", deny_unknown_fields)]
pub enum ConditionConfig {
    /// At most `max_per_hour` discharges per holder key.
    #[serde(rename = "rate_limit")]
    RateLimit { max_per_hour: u32 },
    /// A verified payment of at least `min_amount` (needs `[payment]`).
    #[serde(rename = "payment")]
    Payment { min_amount: u64 },
    /// The holder key must be one of `holders` (Ed25519 public keys, hex).
    #[serde(rename = "allowlist")]
    Allowlist { holders: Vec<String> },
    /// A proof of `statement` (UTF-8) accepted by the named proof verifier.
    #[serde(rename = "proof")]
    Proof { verifier: String, statement: String },
}

impl ConditionConfig {
    /// Short name, for logs.
    pub fn name(&self) -> &'static str {
        match self {
            Self::RateLimit { .. } => "rate_limit",
            Self::Payment { .. } => "payment",
            Self::Allowlist { .. } => "allowlist",
            Self::Proof { .. } => "proof",
        }
    }
}

// =============================================================================
// HTTP types
// =============================================================================

/// POST /discharge request body. Unknown fields are refused, so a client still
/// sending the retired `client_id` / `payment` / `metadata` fields gets a 4xx
/// rather than having them silently ignored.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HttpDischargeRequest {
    /// Base64 ticket bytes from the 3P caveat.
    pub ticket: String,
    /// Unix seconds at which the holder signed.
    pub issued_at: i64,
    /// Base64 Ed25519 signature by the ticket's holder key over
    /// `DischargeRequest::signing_message`.
    pub holder_signature: String,
    /// Optional base64 proof bytes.
    pub proof: Option<String>,
    /// Optional base64 payment evidence (a MsgPack `PaymentAttestation`).
    pub payment_evidence: Option<String>,
}

/// POST /discharge response body.
#[derive(Serialize)]
pub struct HttpDischargeResponse {
    /// The discharge macaroon (em2_ prefixed).
    pub discharge: String,
    /// Unix timestamp when the discharge expires.
    pub expires_at: i64,
    /// Which conditions were satisfied.
    pub condition_met: String,
}

/// Error response body.
#[derive(Serialize)]
pub struct HttpErrorResponse {
    pub error: String,
    pub condition: String,
}

/// GET /conditions response.
#[derive(Serialize)]
pub struct ConditionsResponse {
    /// Ticket conditions this gateway can discharge.
    pub ticket_conditions: Vec<String>,
    /// Operator conditions applied to every ticket.
    pub operator_conditions: Vec<String>,
}

/// GET /health response.
#[derive(Serialize)]
pub struct HealthResponse {
    pub status: String,
    pub issued_total: u64,
}

// =============================================================================
// Application state
// =============================================================================

/// Shared application state.
pub struct AppState {
    pub gateway: DischargeGateway,
    operator_conditions: Vec<String>,
}

pub type SharedState = Arc<RwLock<AppState>>;

// =============================================================================
// Router builder
// =============================================================================

/// Build the gateway from a config, returning the shared state and router.
///
/// Refuses a config whose conditions cannot be verified: a `payment` condition
/// without `[payment]`, or a `proof` condition naming an unconfigured verifier.
pub fn build_gateway(config: &GatewayConfig) -> Result<(SharedState, Router), String> {
    let key = resolve_key(&config.gateway.signing_key_file)?;
    let mut gateway = DischargeGateway::new(*key, config.gateway.location.clone());
    gateway.set_discharge_ttl(config.gateway.discharge_ttl_secs);

    let payment_verifier = match &config.payment {
        Some(p) => {
            let keys = parse_keys(&p.attestor_keys, "payment.attestor_keys")?;
            if keys.is_empty() {
                return Err("[payment] needs at least one attestor key".into());
            }
            let v = PaymentAttestation::verifier(keys);
            gateway.set_payment_verifier(v.clone());
            Some(v)
        }
        None => None,
    };

    let mut proof_verifiers: std::collections::HashMap<String, ProofVerifierFn> =
        std::collections::HashMap::new();
    for pv in &config.proof_verifiers {
        let keys = parse_keys(&pv.attestor_keys, &format!("proof_verifiers[{}]", pv.id))?;
        if keys.is_empty() {
            return Err(format!(
                "proof verifier '{}' needs at least one attestor key",
                pv.id
            ));
        }
        let f = match pv.kind {
            ProofVerifierKind::Ed25519Attestation => ProofAttestation::verifier(keys),
        };
        if proof_verifiers.insert(pv.id.clone(), f.clone()).is_some() {
            return Err(format!("proof verifier '{}' is configured twice", pv.id));
        }
        gateway.add_proof_verifier(pv.id.clone(), f);
    }

    for cond in &config.conditions {
        match cond {
            ConditionConfig::RateLimit { max_per_hour } => {
                gateway.add_evaluator(Box::new(RateLimitEvaluator::new(*max_per_hour, 3600)));
            }
            ConditionConfig::Payment { min_amount } => {
                let v = payment_verifier.clone().ok_or(
                    "a payment condition needs a [payment] section naming the attestors \
                     whose evidence the gateway verifies",
                )?;
                gateway.add_evaluator(Box::new(PaymentEvaluator::new(*min_amount, v)));
            }
            ConditionConfig::Allowlist { holders } => {
                let allowed = parse_keys(holders, "allowlist.holders")?;
                gateway.add_evaluator(Box::new(AllowlistEvaluator { allowed }));
            }
            ConditionConfig::Proof {
                verifier,
                statement,
            } => {
                let f = proof_verifiers.get(verifier).cloned().ok_or_else(|| {
                    format!("proof condition names verifier '{verifier}', which is not configured")
                })?;
                gateway.add_evaluator(Box::new(VerifyingProofEvaluator::new(
                    f,
                    statement.as_bytes().to_vec(),
                )));
            }
        }
    }

    let operator_conditions = config
        .conditions
        .iter()
        .map(|c| c.name().to_string())
        .collect();
    let state: SharedState = Arc::new(RwLock::new(AppState {
        gateway,
        operator_conditions,
    }));

    let router = Router::new()
        .route("/discharge", post(post_discharge))
        .route("/conditions", get(get_conditions))
        .route("/health", get(get_health))
        .with_state(state.clone());

    Ok((state, router))
}

/// Read the 32-byte shared key from its file. The file contents and the parsed
/// key are zeroized when dropped.
fn resolve_key(path: &str) -> Result<Zeroizing<[u8; 32]>, String> {
    let contents = Zeroizing::new(
        std::fs::read_to_string(path)
            .map_err(|e| format!("failed to read key file '{}': {}", path, e))?,
    );
    let bytes = hex_decode(contents.trim()).map_err(|e| format!("key file '{path}': {e}"))?;
    let bytes = Zeroizing::new(bytes);
    if bytes.len() != 32 {
        return Err(format!(
            "key file '{path}': key must be 32 bytes (64 hex chars), got {}",
            bytes.len()
        ));
    }
    let mut key = Zeroizing::new([0u8; 32]);
    key.copy_from_slice(&bytes);
    Ok(key)
}

fn parse_keys(hexes: &[String], what: &str) -> Result<HashSet<[u8; 32]>, String> {
    hexes
        .iter()
        .map(|h| {
            let b = hex_decode(h).map_err(|e| format!("{what}: {e}"))?;
            let k: [u8; 32] = b
                .as_slice()
                .try_into()
                .map_err(|_| format!("{what}: key must be 32 bytes, got {}", b.len()))?;
            ed25519_dalek::VerifyingKey::from_bytes(&k)
                .map_err(|e| format!("{what}: not an Ed25519 public key: {e}"))?;
            Ok(k)
        })
        .collect()
}

fn hex_decode(hex: &str) -> Result<Vec<u8>, String> {
    if !hex.len().is_multiple_of(2) {
        return Err(format!("odd-length hex ({} chars)", hex.len()));
    }
    hex.as_bytes()
        .chunks(2)
        .enumerate()
        .map(|(i, c)| {
            let hi =
                nibble(c[0]).ok_or_else(|| format!("invalid hex char at position {}", i * 2))?;
            let lo = nibble(c[1])
                .ok_or_else(|| format!("invalid hex char at position {}", i * 2 + 1))?;
            Ok((hi << 4) | lo)
        })
        .collect()
}

fn nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

// =============================================================================
// Handlers
// =============================================================================

type HttpError = (StatusCode, Json<HttpErrorResponse>);

fn bad_request(field: &str, e: impl std::fmt::Display) -> HttpError {
    (
        StatusCode::BAD_REQUEST,
        Json(HttpErrorResponse {
            error: format!("invalid {field} base64: {e}"),
            condition: "request_parse".to_string(),
        }),
    )
}

async fn post_discharge(
    State(state): State<SharedState>,
    Json(req): Json<HttpDischargeRequest>,
) -> Result<Json<HttpDischargeResponse>, HttpError> {
    use base64::Engine;
    let engine = base64::engine::general_purpose::STANDARD;
    let decode_opt = |field: &str, v: &Option<String>| -> Result<Option<Vec<u8>>, HttpError> {
        v.as_ref()
            .map(|s| engine.decode(s).map_err(|e| bad_request(field, e)))
            .transpose()
    };

    let discharge_req = dregg_macaroon::DischargeRequest {
        ticket: engine
            .decode(&req.ticket)
            .map_err(|e| bad_request("ticket", e))?,
        issued_at: req.issued_at,
        holder_signature: engine
            .decode(&req.holder_signature)
            .map_err(|e| bad_request("holder_signature", e))?,
        proof: decode_opt("proof", &req.proof)?,
        payment_evidence: decode_opt("payment_evidence", &req.payment_evidence)?,
    };

    let s = state.read().await;
    match s.gateway.process_request(&discharge_req) {
        Ok(resp) => Ok(Json(HttpDischargeResponse {
            discharge: resp.discharge,
            expires_at: resp.expires_at,
            condition_met: resp.condition_met,
        })),
        Err(e) => Err((
            StatusCode::FORBIDDEN,
            Json(HttpErrorResponse {
                error: e.reason,
                condition: e.condition,
            }),
        )),
    }
}

async fn get_conditions(State(state): State<SharedState>) -> Json<ConditionsResponse> {
    let s = state.read().await;
    let mut ticket_conditions = vec!["holder".to_string()];
    if s.gateway.has_payment_verifier() {
        ticket_conditions.push("payment".to_string());
    }
    let mut proofs: Vec<String> = s
        .gateway
        .proof_verifier_ids()
        .map(|id| format!("proof:{id}"))
        .collect();
    proofs.sort();
    ticket_conditions.extend(proofs);
    Json(ConditionsResponse {
        ticket_conditions,
        operator_conditions: s.operator_conditions.clone(),
    })
}

async fn get_health(State(state): State<SharedState>) -> Json<HealthResponse> {
    let s = state.read().await;
    Json(HealthResponse {
        status: "ok".to_string(),
        issued_total: s.gateway.issued_count(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use base64::Engine;
    use dregg_macaroon::{
        CaveatSet, DischargeRequest, Macaroon, ThirdPartyCaveat, TicketCondition, ticket_caveats,
        ticket_digest,
    };
    use ed25519_dalek::SigningKey;
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    const LOCATION: &str = "https://gateway.test";
    const KA: [u8; 32] = [0x42; 32];

    fn b64(b: &[u8]) -> String {
        base64::engine::general_purpose::STANDARD.encode(b)
    }

    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }

    fn now() -> i64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() as i64
    }

    fn write_key(dir: &tempfile::TempDir) -> String {
        let path = dir.path().join("ka.hex");
        std::fs::write(&path, hex(&KA)).unwrap();
        path.to_string_lossy().into_owned()
    }

    fn config_toml(key_file: &str, extra: &str) -> String {
        format!(
            "[gateway]\nbind = \"127.0.0.1:0\"\nsigning_key_file = \"{key_file}\"\nlocation = \"{LOCATION}\"\n{extra}"
        )
    }

    fn ticket(holder: &SigningKey, conditions: Vec<TicketCondition>) -> Vec<u8> {
        let mut mac = Macaroon::new(&[7u8; 32], b"kid".to_vec(), "https://issuer.test".into());
        mac.add_third_party(
            LOCATION,
            &KA,
            ticket_caveats(&holder.verifying_key(), conditions),
        )
        .unwrap();
        let tp = mac.caveats.third_party_caveats();
        ThirdPartyCaveat::decode_body(&tp[0].body).unwrap().ticket
    }

    fn body_for(req: &DischargeRequest) -> serde_json::Value {
        let mut v = serde_json::json!({
            "ticket": b64(&req.ticket),
            "issued_at": req.issued_at,
            "holder_signature": b64(&req.holder_signature),
        });
        if let Some(p) = &req.proof {
            v["proof"] = b64(p).into();
        }
        if let Some(p) = &req.payment_evidence {
            v["payment_evidence"] = b64(p).into();
        }
        v
    }

    async fn post(router: &Router, body: serde_json::Value) -> (StatusCode, serde_json::Value) {
        let resp = router
            .clone()
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/discharge")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();
        let status = resp.status();
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        (
            status,
            serde_json::from_slice(&bytes).unwrap_or(serde_json::Value::Null),
        )
    }

    #[test]
    fn retired_config_shapes_refuse_to_load() {
        let dir = tempfile::tempdir().unwrap();
        let kf = write_key(&dir);
        for extra in [
            "[[conditions]]\ntype = \"proof_required\"\n",
            "[[conditions]]\ntype = \"always_allow\"\n",
            "[[conditions]]\ntype = \"allowlist\"\nclients = [\"alice\"]\n",
        ] {
            let r: Result<GatewayConfig, _> = toml::from_str(&config_toml(&kf, extra));
            assert!(r.is_err(), "must not load: {extra}");
        }
        // The inline key field is gone.
        let inline = format!(
            "[gateway]\nbind = \"x\"\nsigning_key_file = \"{kf}\"\nsigning_key_hex = \"{}\"\nlocation = \"l\"\n",
            hex(&KA)
        );
        assert!(toml::from_str::<GatewayConfig>(&inline).is_err());
    }

    #[test]
    fn unverifiable_conditions_refuse_to_build() {
        let dir = tempfile::tempdir().unwrap();
        let kf = write_key(&dir);
        let pay: GatewayConfig = toml::from_str(&config_toml(
            &kf,
            "[[conditions]]\ntype = \"payment\"\nmin_amount = 5\n",
        ))
        .unwrap();
        assert!(build_gateway(&pay).is_err(), "payment without attestors");

        let proof: GatewayConfig = toml::from_str(&config_toml(
            &kf,
            "[[conditions]]\ntype = \"proof\"\nverifier = \"kyc\"\nstatement = \"s\"\n",
        ))
        .unwrap();
        assert!(build_gateway(&proof).is_err(), "proof naming no verifier");
    }

    #[test]
    fn config_debug_does_not_print_the_key() {
        let dir = tempfile::tempdir().unwrap();
        let kf = write_key(&dir);
        let cfg: GatewayConfig = toml::from_str(&config_toml(&kf, "")).unwrap();
        let dbg = format!("{cfg:?}");
        assert!(!dbg.contains(&hex(&KA)), "{dbg}");
        assert!(build_gateway(&cfg).is_ok());
    }

    #[tokio::test]
    async fn http_discharge_is_bound_to_the_holder_and_verifies_proofs() {
        let dir = tempfile::tempdir().unwrap();
        let kf = write_key(&dir);
        let kyc = SigningKey::from_bytes(&[9; 32]);
        let cfg: GatewayConfig = toml::from_str(&config_toml(
            &kf,
            &format!(
                "[[proof_verifiers]]\nid = \"kyc\"\nkind = \"ed25519_attestation\"\nattestor_keys = [\"{}\"]\n",
                hex(&kyc.verifying_key().to_bytes())
            ),
        ))
        .unwrap();
        let (_state, router) = build_gateway(&cfg).unwrap();

        let alice = SigningKey::from_bytes(&[1; 32]);
        let mallory = SigningKey::from_bytes(&[2; 32]);
        let t = ticket(
            &alice,
            vec![TicketCondition::Proof {
                verifier: "kyc".into(),
                statement: b"over-18".to_vec(),
            }],
        );

        // The retired self-asserted fields are refused at parse.
        let mut old = body_for(&DischargeRequest::sign(
            t.clone(),
            now(),
            None,
            None,
            LOCATION,
            &alice,
        ));
        old["payment"] = 1_000_000.into();
        let (status, _) = post(&router, old).await;
        assert!(status.is_client_error(), "old field shape: {status}");
        let mut old = body_for(&DischargeRequest::sign(
            t.clone(),
            now(),
            None,
            None,
            LOCATION,
            &alice,
        ));
        old["client_id"] = "alice".into();
        assert!(post(&router, old).await.0.is_client_error());

        // Mallory, with the ticket and arbitrary proof bytes.
        let (status, v) = post(
            &router,
            body_for(&DischargeRequest::sign(
                t.clone(),
                now(),
                Some(vec![0xAB; 96]),
                None,
                LOCATION,
                &mallory,
            )),
        )
        .await;
        assert_eq!(status, StatusCode::FORBIDDEN);
        assert_eq!(v["condition"], "holder_binding");

        // Alice with arbitrary proof bytes: refused by the verifier, not burned.
        let (status, v) = post(
            &router,
            body_for(&DischargeRequest::sign(
                t.clone(),
                now(),
                Some(vec![0xAB; 96]),
                None,
                LOCATION,
                &alice,
            )),
        )
        .await;
        assert_eq!(status, StatusCode::FORBIDDEN);
        assert_eq!(v["condition"], "proof:kyc");

        // Alice with a real attestation: issued.
        let proof = ProofAttestation::sign(
            &kyc,
            LOCATION,
            b"over-18",
            &ticket_digest(&t),
            &alice.verifying_key().to_bytes(),
        );
        let (status, v) = post(
            &router,
            body_for(&DischargeRequest::sign(
                t.clone(),
                now(),
                Some(proof),
                None,
                LOCATION,
                &alice,
            )),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{v}");
        assert!(
            v["discharge"]
                .as_str()
                .is_some_and(|d| d.starts_with("em2_"))
        );

        // Payment tickets are refused: no [payment] section configured.
        let tp = ticket(&alice, vec![TicketCondition::Payment { min_amount: 1 }]);
        let (status, v) = post(
            &router,
            body_for(&DischargeRequest::sign(
                tp,
                now(),
                None,
                Some(vec![1]),
                LOCATION,
                &alice,
            )),
        )
        .await;
        assert_eq!(status, StatusCode::FORBIDDEN);
        assert_eq!(v["condition"], "payment");

        // A ticket with no holder cannot be bound to any request.
        let mut mac = Macaroon::new(&[7u8; 32], b"kid".to_vec(), "i".into());
        mac.add_third_party(LOCATION, &KA, CaveatSet::new())
            .unwrap();
        let bare = ThirdPartyCaveat::decode_body(&mac.caveats.third_party_caveats()[0].body)
            .unwrap()
            .ticket;
        let (status, v) = post(
            &router,
            body_for(&DischargeRequest::sign(
                bare,
                now(),
                None,
                None,
                LOCATION,
                &alice,
            )),
        )
        .await;
        assert_eq!(status, StatusCode::FORBIDDEN);
        assert_eq!(v["condition"], "ticket_caveat");
    }
}
