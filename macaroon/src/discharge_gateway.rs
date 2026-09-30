//! Discharge gateway: evaluates conditions and issues discharge macaroons for
//! third-party caveats.
//!
//! # Overview
//!
//! 1. Service A issues a token with a third-party caveat addressed to the
//!    gateway. The ticket inside it is sealed under the shared key `KA` and
//!    carries the conditions A wants enforced ([`TicketCondition`]), including
//!    exactly one [`TicketCondition::Holder`]: the Ed25519 key of the party
//!    entitled to the discharge.
//! 2. The holder sends the ticket to the gateway in a [`DischargeRequest`]
//!    signed with that key ([`DischargeRequest::sign`]).
//! 3. The gateway decrypts the ticket, verifies the holder signature, and
//!    evaluates every condition the ticket names plus every evaluator the
//!    operator configured. Each condition is discharged only by something the
//!    gateway verifies: a signature under the ticket's holder key, a proof
//!    checked by a registered [`ProofVerifierFn`], a payment attestation checked
//!    by a registered [`PaymentVerifierFn`]. No evaluator reads a value whose
//!    only authority is that the requester typed it.
//! 4. Only after every condition passes is the ticket burned and the discharge
//!    issued. A request that fails leaves the ticket spendable.
//! 5. The client binds the discharge to its token and presents both to A.
//!
//! This module provides the core logic, reusable without any HTTP layer.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use zeroize::Zeroize;

use crate::caveat::{CaveatSet, CaveatType, WireCaveat};
use crate::caveat_3p::ThirdPartyCaveat;
use crate::crypto;
use crate::macaroon::create_discharge;

// =============================================================================
// Ticket conditions
// =============================================================================

/// Ticket caveat: the Ed25519 public key (32 bytes) of the ticket holder. The
/// discharge request must be signed by this key. Every ticket must carry exactly
/// one.
pub const CAV_DISCHARGE_HOLDER: CaveatType = 16;
/// Ticket caveat: a payment of at least `min_amount` must be evidenced by an
/// attestation the gateway's payment verifier accepts. Body: MsgPack `u64`.
pub const CAV_DISCHARGE_PAYMENT: CaveatType = 17;
/// Ticket caveat: a proof of `statement` must be accepted by the gateway's proof
/// verifier registered under `verifier`. Body: MsgPack `(String, Vec<u8>)`.
pub const CAV_DISCHARGE_PROOF: CaveatType = 18;

/// A condition the ticket issuer asks the gateway to enforce.
///
/// Carried as caveats inside the sealed ticket, so the requester cannot add,
/// remove or alter them: they are authenticated by the AEAD under `KA`. A ticket
/// carrying any caveat that is not one of these is refused — the gateway does
/// not discharge a condition it does not understand.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TicketCondition {
    /// The Ed25519 public key entitled to request the discharge.
    Holder([u8; 32]),
    /// A verified payment of at least this amount.
    Payment { min_amount: u64 },
    /// A proof of `statement`, verified by the verifier registered as `verifier`.
    Proof {
        verifier: String,
        statement: Vec<u8>,
    },
}

impl TicketCondition {
    /// Encode as a ticket caveat.
    pub fn to_wire(&self) -> WireCaveat {
        match self {
            Self::Holder(pk) => WireCaveat::new(CAV_DISCHARGE_HOLDER, pk.to_vec()),
            Self::Payment { min_amount } => WireCaveat::new(
                CAV_DISCHARGE_PAYMENT,
                rmp_serde::to_vec(min_amount).expect("u64 encodes"),
            ),
            Self::Proof {
                verifier,
                statement,
            } => WireCaveat::new(
                CAV_DISCHARGE_PROOF,
                rmp_serde::to_vec(&(verifier, statement)).expect("tuple encodes"),
            ),
        }
    }

    /// Decode a ticket caveat. Any caveat type this gateway does not enforce is
    /// an error, never skipped.
    pub fn from_wire(wire: &WireCaveat) -> Result<Self, String> {
        match wire.caveat_type {
            CAV_DISCHARGE_HOLDER => {
                let pk: [u8; 32] = wire.body.as_slice().try_into().map_err(|_| {
                    format!(
                        "holder caveat must be a 32-byte Ed25519 key, got {} bytes",
                        wire.body.len()
                    )
                })?;
                Ok(Self::Holder(pk))
            }
            CAV_DISCHARGE_PAYMENT => rmp_serde::from_slice::<u64>(&wire.body)
                .map(|min_amount| Self::Payment { min_amount })
                .map_err(|e| format!("malformed payment caveat: {e}")),
            CAV_DISCHARGE_PROOF => rmp_serde::from_slice::<(String, Vec<u8>)>(&wire.body)
                .map(|(verifier, statement)| Self::Proof {
                    verifier,
                    statement,
                })
                .map_err(|e| format!("malformed proof caveat: {e}")),
            other => Err(format!(
                "ticket carries caveat type {other}, which this gateway cannot enforce"
            )),
        }
    }
}

/// Build the caveat set to seal into a ticket: the holder key plus the
/// conditions. Pass the result to `Macaroon::add_third_party`.
pub fn ticket_caveats(
    holder: &VerifyingKey,
    conditions: impl IntoIterator<Item = TicketCondition>,
) -> CaveatSet {
    let mut set = CaveatSet::new();
    set.push(TicketCondition::Holder(holder.to_bytes()).to_wire());
    for c in conditions {
        set.push(c.to_wire());
    }
    set
}

// =============================================================================
// Core types
// =============================================================================

/// How far a request's `issued_at` may sit from the gateway clock, in seconds.
pub const REQUEST_MAX_SKEW_SECS: i64 = 300;

/// Domain tag of the message a holder signs to request a discharge.
const REQUEST_DOMAIN: &[u8] = b"dregg-discharge-request-v1";
/// Domain tag of a payment attestation.
const PAYMENT_ATTESTATION_DOMAIN: &[u8] = b"dregg-discharge-payment-attestation-v1";
/// Domain tag of a proof attestation.
const PROOF_ATTESTATION_DOMAIN: &[u8] = b"dregg-discharge-proof-attestation-v1";

fn put_lp(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    out.extend_from_slice(bytes);
}

fn put_opt_digest(out: &mut Vec<u8>, bytes: Option<&[u8]>) {
    match bytes {
        None => out.push(0),
        Some(b) => {
            out.push(1);
            out.extend_from_slice(&Sha256::digest(b));
        }
    }
}

/// SHA-256 of the sealed ticket bytes: the public name of a ticket that
/// signatures and attestations bind to.
pub fn ticket_digest(ticket: &[u8]) -> [u8; 32] {
    Sha256::digest(ticket).into()
}

fn now_unix() -> Result<i64, String> {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .map_err(|e| format!("system clock error: {e}"))
}

fn hex_prefix(key: &[u8; 32]) -> String {
    key[..8].iter().map(|b| format!("{b:02x}")).collect()
}

fn verify_ed25519(pk: &[u8; 32], msg: &[u8], sig: &[u8]) -> Result<(), String> {
    let vk = VerifyingKey::from_bytes(pk).map_err(|e| format!("invalid Ed25519 key: {e}"))?;
    let sig = Signature::from_slice(sig).map_err(|e| format!("malformed signature: {e}"))?;
    vk.verify_strict(msg, &sig)
        .map_err(|_| "signature does not verify".to_string())
}

/// A request to obtain a discharge macaroon from the gateway.
///
/// Every field is covered by `holder_signature`, made with the key the ticket
/// names. There is no client identifier, amount or metadata field: nothing the
/// requester asserts is taken as satisfying a condition.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DischargeRequest {
    /// Encrypted ticket from the 3P caveat.
    pub ticket: Vec<u8>,
    /// Unix seconds at which the holder signed the request.
    pub issued_at: i64,
    /// Ed25519 signature by the ticket's holder key over
    /// [`DischargeRequest::signing_message`].
    pub holder_signature: Vec<u8>,
    /// Proof bytes for a proof condition, checked by a registered verifier.
    pub proof: Option<Vec<u8>>,
    /// Payment evidence for a payment condition, checked by the registered
    /// payment verifier.
    pub payment_evidence: Option<Vec<u8>>,
}

impl DischargeRequest {
    /// The message the holder signs, bound to the gateway `location`, the
    /// ticket, the time, and the exact proof and payment evidence presented.
    pub fn signing_message(&self, location: &str) -> Vec<u8> {
        let mut m = Vec::with_capacity(160);
        m.extend_from_slice(REQUEST_DOMAIN);
        put_lp(&mut m, location.as_bytes());
        m.extend_from_slice(&ticket_digest(&self.ticket));
        m.extend_from_slice(&self.issued_at.to_le_bytes());
        put_opt_digest(&mut m, self.proof.as_deref());
        put_opt_digest(&mut m, self.payment_evidence.as_deref());
        m
    }

    /// Build and sign a request with the holder's key.
    pub fn sign(
        ticket: Vec<u8>,
        issued_at: i64,
        proof: Option<Vec<u8>>,
        payment_evidence: Option<Vec<u8>>,
        location: &str,
        holder: &SigningKey,
    ) -> Self {
        let mut req = Self {
            ticket,
            issued_at,
            holder_signature: Vec::new(),
            proof,
            payment_evidence,
        };
        req.holder_signature = holder
            .sign(&req.signing_message(location))
            .to_bytes()
            .to_vec();
        req
    }
}

/// What an evaluator sees: only facts the gateway has authenticated.
///
/// `holder` is the key the sealed ticket names AND that signed this request.
/// `proof` and `payment_evidence` are the requester's bytes; an evaluator may
/// only accept them through a verifier that checks them cryptographically.
pub struct DischargeContext<'a> {
    /// The gateway's location (what the request signature is bound to).
    pub location: &'a str,
    /// SHA-256 of the ticket.
    pub ticket_digest: [u8; 32],
    /// The authenticated principal: the ticket's holder key.
    pub holder: [u8; 32],
    /// Proof bytes presented, if any (unverified until a verifier checks them).
    pub proof: Option<&'a [u8]>,
    /// Payment evidence presented, if any (unverified until a verifier checks it).
    pub payment_evidence: Option<&'a [u8]>,
}

/// A successful discharge response.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DischargeResponse {
    /// Base64-encoded discharge macaroon (em2_ prefixed).
    pub discharge: String,
    /// Unix timestamp when this discharge expires.
    pub expires_at: i64,
    /// The conditions that were satisfied, comma-separated.
    pub condition_met: String,
}

/// Error returned when a discharge request is denied.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DischargeError {
    /// Human-readable denial reason.
    pub reason: String,
    /// The condition that was not met.
    pub condition: String,
}

impl std::fmt::Display for DischargeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "discharge denied ({}): {}", self.condition, self.reason)
    }
}

impl std::error::Error for DischargeError {}

fn denied(condition: &str, reason: impl Into<String>) -> DischargeError {
    DischargeError {
        reason: reason.into(),
        condition: condition.to_string(),
    }
}

// =============================================================================
// Condition Evaluators
// =============================================================================

/// Trait for evaluating whether a discharge condition is satisfied.
pub trait ConditionEvaluator: Send + Sync {
    /// Evaluate whether the condition is satisfied.
    ///
    /// Returns `Ok(())` if the discharge should be issued, or `Err(reason)` if denied.
    fn evaluate(&self, ctx: &DischargeContext<'_>) -> Result<(), String>;

    /// Human-readable name of this evaluator (for logging/metrics).
    fn name(&self) -> &str;
}

/// Issue only during a time window (e.g., business hours in a given timezone offset).
pub struct TimeWindowEvaluator {
    /// Start hour (0-23, inclusive).
    pub start_hour: u8,
    /// End hour (0-23, inclusive).
    pub end_hour: u8,
    /// UTC offset in hours (e.g., -5 for EST, +1 for CET).
    pub utc_offset_hours: i8,
}

impl ConditionEvaluator for TimeWindowEvaluator {
    fn evaluate(&self, _ctx: &DischargeContext<'_>) -> Result<(), String> {
        let secs = now_unix()? + (self.utc_offset_hours as i64 * 3600);
        let hour_of_day = (secs.rem_euclid(86400) / 3600) as u8;

        let inside = if self.start_hour <= self.end_hour {
            hour_of_day >= self.start_hour && hour_of_day <= self.end_hour
        } else {
            hour_of_day >= self.start_hour || hour_of_day <= self.end_hour
        };
        if inside {
            Ok(())
        } else {
            Err(format!(
                "outside time window: current hour {} not in [{}, {}]",
                hour_of_day, self.start_hour, self.end_hour
            ))
        }
    }

    fn name(&self) -> &str {
        "time_window"
    }
}

/// Per-holder rate limiting: max N discharges per holder key per window.
///
/// Keyed on the authenticated holder key. A holder key is named by the ticket
/// issuer inside the sealed ticket, so a requester cannot mint a fresh key to
/// reset its count.
pub struct RateLimitEvaluator {
    /// Maximum discharges per holder per window.
    pub max_per_window: u32,
    /// Window duration in seconds.
    pub window_secs: u64,
    /// Maximum number of tracked holders.
    max_clients: usize,
    /// State: holder key -> (count, window_start_unix).
    state: Mutex<HashMap<[u8; 32], (u32, u64)>>,
}

impl RateLimitEvaluator {
    /// Create a new rate limit evaluator.
    pub fn new(max_per_window: u32, window_secs: u64) -> Self {
        Self::with_max_clients(max_per_window, window_secs, 10_000)
    }

    /// Create a rate limit evaluator with a custom max tracked-holders limit.
    pub fn with_max_clients(max_per_window: u32, window_secs: u64, max_clients: usize) -> Self {
        Self {
            max_per_window,
            window_secs,
            max_clients,
            state: Mutex::new(HashMap::new()),
        }
    }
}

impl ConditionEvaluator for RateLimitEvaluator {
    fn evaluate(&self, ctx: &DischargeContext<'_>) -> Result<(), String> {
        let now = now_unix()? as u64;

        let mut state = self
            .state
            .lock()
            .map_err(|e| format!("lock poisoned: {e}"))?;

        // Evict expired entries when the state grows too large.
        if state.len() >= self.max_clients {
            state.retain(|_, (_, window_start)| {
                now.saturating_sub(*window_start) < self.window_secs
            });
            if state.len() >= self.max_clients {
                return Err("rate limiter at capacity".to_string());
            }
        }

        let entry = state.entry(ctx.holder).or_insert((0, now));

        if now.saturating_sub(entry.1) >= self.window_secs {
            *entry = (0, now);
        }

        if entry.0 >= self.max_per_window {
            Err(format!(
                "rate limit exceeded: {} discharges in {}s window (max {})",
                entry.0, self.window_secs, self.max_per_window
            ))
        } else {
            entry.0 += 1;
            Ok(())
        }
    }

    fn name(&self) -> &str {
        "rate_limit"
    }
}

/// Verifies payment evidence and returns the amount it proves was paid to this
/// gateway for this ticket and holder. `Err` if the evidence does not verify.
pub type PaymentVerifierFn =
    Arc<dyn Fn(&[u8], &DischargeContext<'_>) -> Result<u64, String> + Send + Sync>;

/// Require a VERIFIED payment of at least `min_amount`.
///
/// The amount compared is the one the verifier returns from checking the
/// evidence — never a number the requester supplies.
pub struct PaymentEvaluator {
    min_amount: u64,
    verifier: PaymentVerifierFn,
}

impl PaymentEvaluator {
    /// A payment condition checked by `verifier`.
    pub fn new(min_amount: u64, verifier: PaymentVerifierFn) -> Self {
        Self {
            min_amount,
            verifier,
        }
    }
}

impl ConditionEvaluator for PaymentEvaluator {
    fn evaluate(&self, ctx: &DischargeContext<'_>) -> Result<(), String> {
        let evidence = ctx.payment_evidence.ok_or_else(|| {
            format!(
                "payment required: evidence of at least {} not provided",
                self.min_amount
            )
        })?;
        let paid = (self.verifier)(evidence, ctx)
            .map_err(|e| format!("payment evidence rejected: {e}"))?;
        if paid >= self.min_amount {
            Ok(())
        } else {
            Err(format!(
                "insufficient payment: verified {}, need at least {}",
                paid, self.min_amount
            ))
        }
    }

    fn name(&self) -> &str {
        "payment"
    }
}

/// A proof verifier: takes the proof bytes, the statement the condition names,
/// and the context, and returns `Ok(())` only if the proof verifies for that
/// statement. Implementations should bind the proof to `ctx.ticket_digest` and
/// `ctx.holder` so one proof cannot discharge another ticket.
pub type ProofVerifierFn =
    Arc<dyn Fn(&[u8], &[u8], &DischargeContext<'_>) -> Result<(), String> + Send + Sync>;

/// Require a proof of `statement` that `verifier` accepts.
///
/// This is the only proof evaluator. A proof condition is discharged by the
/// verifier's check and by nothing else; there is no presence-only variant.
pub struct VerifyingProofEvaluator {
    verifier: ProofVerifierFn,
    statement: Vec<u8>,
}

impl VerifyingProofEvaluator {
    /// A proof condition over `statement`, checked by `verifier`.
    pub fn new(verifier: ProofVerifierFn, statement: Vec<u8>) -> Self {
        Self {
            verifier,
            statement,
        }
    }
}

impl ConditionEvaluator for VerifyingProofEvaluator {
    fn evaluate(&self, ctx: &DischargeContext<'_>) -> Result<(), String> {
        match ctx.proof {
            Some(proof) if !proof.is_empty() => (self.verifier)(proof, &self.statement, ctx),
            Some(_) => Err("proof is empty".to_string()),
            None => Err("proof required but not provided".to_string()),
        }
    }

    fn name(&self) -> &str {
        "verifying_proof"
    }
}

/// Require the authenticated holder key to be in an allowlist.
pub struct AllowlistEvaluator {
    /// Allowed holder Ed25519 public keys.
    pub allowed: HashSet<[u8; 32]>,
}

impl ConditionEvaluator for AllowlistEvaluator {
    fn evaluate(&self, ctx: &DischargeContext<'_>) -> Result<(), String> {
        if self.allowed.contains(&ctx.holder) {
            Ok(())
        } else {
            Err(format!(
                "holder {} not in allowlist",
                hex_prefix(&ctx.holder)
            ))
        }
    }

    fn name(&self) -> &str {
        "allowlist"
    }
}

/// Composite: ALL conditions must be satisfied.
pub struct AllOfEvaluator {
    pub evaluators: Vec<Box<dyn ConditionEvaluator>>,
}

impl ConditionEvaluator for AllOfEvaluator {
    fn evaluate(&self, ctx: &DischargeContext<'_>) -> Result<(), String> {
        for eval in &self.evaluators {
            eval.evaluate(ctx)?;
        }
        Ok(())
    }

    fn name(&self) -> &str {
        "all_of"
    }
}

/// Composite: ANY condition must be satisfied.
pub struct AnyOfEvaluator {
    pub evaluators: Vec<Box<dyn ConditionEvaluator>>,
}

impl ConditionEvaluator for AnyOfEvaluator {
    fn evaluate(&self, ctx: &DischargeContext<'_>) -> Result<(), String> {
        if self.evaluators.is_empty() {
            return Err("no evaluators configured".to_string());
        }
        let mut last_err = String::new();
        for eval in &self.evaluators {
            match eval.evaluate(ctx) {
                Ok(()) => return Ok(()),
                Err(e) => last_err = e,
            }
        }
        Err(format!("no condition satisfied; last: {}", last_err))
    }

    fn name(&self) -> &str {
        "any_of"
    }
}

// =============================================================================
// Signed attestations (the verifiers the gateway ships)
// =============================================================================

/// A payment attestation: an attestor (the party that observed the payment —
/// the payment processor or the node that settled it) signs that `amount` was
/// paid to the gateway at `location` for the ticket `ticket_digest`, requested
/// by `holder`, under payment reference `payment_ref`.
///
/// Binding the ticket digest means one payment discharges one ticket: the
/// attestation is useless for any other ticket, and the ticket burn stops it
/// being used twice for the same one.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PaymentAttestation {
    pub amount: u64,
    pub payment_ref: Vec<u8>,
    pub attestor: [u8; 32],
    pub signature: Vec<u8>,
}

impl PaymentAttestation {
    fn message(
        location: &str,
        ticket_digest: &[u8; 32],
        holder: &[u8; 32],
        amount: u64,
        payment_ref: &[u8],
    ) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend_from_slice(PAYMENT_ATTESTATION_DOMAIN);
        put_lp(&mut m, location.as_bytes());
        m.extend_from_slice(ticket_digest);
        m.extend_from_slice(holder);
        m.extend_from_slice(&amount.to_le_bytes());
        put_lp(&mut m, payment_ref);
        m
    }

    /// Sign an attestation (attestor side). Returns the MsgPack evidence bytes
    /// to put in [`DischargeRequest::payment_evidence`].
    pub fn sign(
        attestor: &SigningKey,
        location: &str,
        ticket_digest: &[u8; 32],
        holder: &[u8; 32],
        amount: u64,
        payment_ref: Vec<u8>,
    ) -> Vec<u8> {
        let msg = Self::message(location, ticket_digest, holder, amount, &payment_ref);
        let att = Self {
            amount,
            payment_ref,
            attestor: attestor.verifying_key().to_bytes(),
            signature: attestor.sign(&msg).to_bytes().to_vec(),
        };
        rmp_serde::to_vec(&att).expect("attestation encodes")
    }

    /// A [`PaymentVerifierFn`] that accepts attestations signed by any of
    /// `attestors` and returns the attested amount.
    pub fn verifier(attestors: HashSet<[u8; 32]>) -> PaymentVerifierFn {
        Arc::new(move |evidence, ctx| {
            let att: PaymentAttestation = rmp_serde::from_slice(evidence)
                .map_err(|e| format!("malformed payment attestation: {e}"))?;
            if !attestors.contains(&att.attestor) {
                return Err("payment attestor is not trusted by this gateway".to_string());
            }
            let msg = Self::message(
                ctx.location,
                &ctx.ticket_digest,
                &ctx.holder,
                att.amount,
                &att.payment_ref,
            );
            verify_ed25519(&att.attestor, &msg, &att.signature)
                .map_err(|e| format!("payment attestation: {e}"))?;
            Ok(att.amount)
        })
    }
}

/// A proof attestation: an attestor signs that `statement` holds for the holder
/// of the ticket `ticket_digest` at the gateway `location`.
///
/// This is the proof verifier the standalone gateway can be configured with. It
/// verifies a signature by a key the operator trusts to vouch for the
/// statement; it is not a zero-knowledge proof system. A STARK or other
/// verifier is registered the same way, as a [`ProofVerifierFn`].
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProofAttestation {
    pub attestor: [u8; 32],
    pub signature: Vec<u8>,
}

impl ProofAttestation {
    fn message(
        location: &str,
        statement: &[u8],
        ticket_digest: &[u8; 32],
        holder: &[u8; 32],
    ) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend_from_slice(PROOF_ATTESTATION_DOMAIN);
        put_lp(&mut m, location.as_bytes());
        put_lp(&mut m, statement);
        m.extend_from_slice(ticket_digest);
        m.extend_from_slice(holder);
        m
    }

    /// Sign an attestation (attestor side). Returns the MsgPack proof bytes.
    pub fn sign(
        attestor: &SigningKey,
        location: &str,
        statement: &[u8],
        ticket_digest: &[u8; 32],
        holder: &[u8; 32],
    ) -> Vec<u8> {
        let msg = Self::message(location, statement, ticket_digest, holder);
        let att = Self {
            attestor: attestor.verifying_key().to_bytes(),
            signature: attestor.sign(&msg).to_bytes().to_vec(),
        };
        rmp_serde::to_vec(&att).expect("attestation encodes")
    }

    /// A [`ProofVerifierFn`] accepting attestations signed by any of `attestors`.
    pub fn verifier(attestors: HashSet<[u8; 32]>) -> ProofVerifierFn {
        Arc::new(move |proof, statement, ctx| {
            let att: ProofAttestation = rmp_serde::from_slice(proof)
                .map_err(|e| format!("malformed proof attestation: {e}"))?;
            if !attestors.contains(&att.attestor) {
                return Err("proof attestor is not trusted by this gateway".to_string());
            }
            let msg = Self::message(ctx.location, statement, &ctx.ticket_digest, &ctx.holder);
            verify_ed25519(&att.attestor, &msg, &att.signature)
                .map_err(|e| format!("proof attestation: {e}"))
        })
    }
}

// =============================================================================
// Discharge Gateway
// =============================================================================

/// Maximum number of entries in the replay prevention set before eviction.
/// When exceeded, the oldest entries are removed to bound memory usage.
const MAX_ISSUED_CACHE: usize = 100_000;

/// Why a persisted replay set could not be loaded.
///
/// [`DischargeGateway::load_issued_set`] used to return `()` and, per its own
/// docstring, "silently ignore" a blob that was not a whole number of 32-byte
/// hashes — leaving the gateway with an EMPTY replay set. An empty replay set is
/// not a degraded one: it admits every ticket ever issued. A caller that cannot
/// load the set must refuse to serve discharges, so the failure is typed and
/// returned rather than swallowed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReplaySetLoadError {
    /// The blob is not a whole number of 32-byte hashes, so at least one entry is
    /// unrecoverable and the set that would be built is strictly weaker than the
    /// one that was persisted.
    Truncated {
        /// Length of the blob that was offered.
        len: usize,
    },
}

impl std::fmt::Display for ReplaySetLoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Truncated { len } => write!(
                f,
                "persisted replay set is {len} bytes, not a whole number of 32-byte ticket hashes"
            ),
        }
    }
}

impl std::error::Error for ReplaySetLoadError {}

/// The discharge gateway: evaluates conditions and issues discharge macaroons.
pub struct DischargeGateway {
    /// The shared key for decrypting third-party tickets.
    /// This is the `KA` shared between the token issuer and this gateway.
    shared_key: [u8; 32],

    /// The gateway's location identifier (must match the 3P caveat location).
    location: String,

    /// Operator-configured conditions, applied to every ticket in addition to
    /// the conditions the ticket itself names.
    evaluators: Vec<Box<dyn ConditionEvaluator>>,

    /// Verifier for [`TicketCondition::Payment`]. `None` refuses every ticket
    /// that demands payment.
    payment_verifier: Option<PaymentVerifierFn>,

    /// Verifiers for [`TicketCondition::Proof`], by name. A ticket naming a
    /// verifier not registered here is refused.
    proof_verifiers: HashMap<String, ProofVerifierFn>,

    /// Burned ticket hashes (for replay prevention). A ticket enters this set
    /// only when a discharge is issued for it.
    issued: Mutex<BoundedReplaySet>,

    /// Discharge validity duration in seconds (default: 300 = 5 minutes).
    discharge_ttl_secs: i64,

    /// Counter of total discharges issued (for metrics).
    issued_count: Mutex<u64>,
}

/// Bounded replay prevention set: O(1) contains + FIFO eviction.
struct BoundedReplaySet {
    set: HashSet<[u8; 32]>,
    order: VecDeque<[u8; 32]>,
}

impl BoundedReplaySet {
    fn new() -> Self {
        Self {
            set: HashSet::new(),
            order: VecDeque::new(),
        }
    }

    fn contains(&self, hash: &[u8; 32]) -> bool {
        self.set.contains(hash)
    }

    /// Insert `hash`; returns `false` if it was already present.
    fn insert(&mut self, hash: [u8; 32]) -> bool {
        // ⚑ `set` and `order` MUST stay in exact correspondence: eviction pops one
        // `order` entry and removes that hash from `set`, so a hash sitting twice
        // in `order` gets removed from `set` while an `order` entry still names
        // it — i.e. a ticket falls out of the replay set early and becomes
        // discharge-able again. `load_issued_set` feeds persisted blobs through
        // here (and a persisted blob is exactly where a duplicate can arrive), so
        // the invariant is enforced HERE rather than relying on every caller.
        if self.set.contains(&hash) {
            return false;
        }
        while self.set.len() >= MAX_ISSUED_CACHE {
            if let Some(oldest) = self.order.pop_front() {
                self.set.remove(&oldest);
            } else {
                break;
            }
        }
        self.set.insert(hash);
        self.order.push_back(hash);
        true
    }

    fn clear(&mut self) {
        self.set.clear();
        self.order.clear();
    }
}

impl DischargeGateway {
    /// Create a new discharge gateway.
    ///
    /// # Arguments
    /// - `shared_key`: The key shared between token issuers and this gateway (`KA`).
    /// - `location`: The gateway's URL/identifier (must match 3P caveat locations).
    pub fn new(shared_key: [u8; 32], location: String) -> Self {
        Self {
            shared_key,
            location,
            evaluators: Vec::new(),
            payment_verifier: None,
            proof_verifiers: HashMap::new(),
            issued: Mutex::new(BoundedReplaySet::new()),
            discharge_ttl_secs: 300,
            issued_count: Mutex::new(0),
        }
    }

    /// Set the discharge TTL (time-to-live) in seconds.
    pub fn set_discharge_ttl(&mut self, ttl_secs: i64) {
        self.discharge_ttl_secs = ttl_secs;
    }

    /// Register an operator condition, applied to every ticket.
    ///
    /// ALL registered evaluators must pass, in addition to the ticket's own
    /// conditions. Use [`AllOfEvaluator`] or [`AnyOfEvaluator`] for composites.
    pub fn add_evaluator(&mut self, evaluator: Box<dyn ConditionEvaluator>) {
        self.evaluators.push(evaluator);
    }

    /// Install the verifier that discharges ticket payment conditions.
    pub fn set_payment_verifier(&mut self, verifier: PaymentVerifierFn) {
        self.payment_verifier = Some(verifier);
    }

    /// Register a proof verifier under `id`, for ticket proof conditions that
    /// name it.
    pub fn add_proof_verifier(&mut self, id: impl Into<String>, verifier: ProofVerifierFn) {
        self.proof_verifiers.insert(id.into(), verifier);
    }

    /// Names of the registered proof verifiers.
    pub fn proof_verifier_ids(&self) -> impl Iterator<Item = &str> {
        self.proof_verifiers.keys().map(String::as_str)
    }

    /// Whether a payment verifier is installed.
    pub fn has_payment_verifier(&self) -> bool {
        self.payment_verifier.is_some()
    }

    /// Get the gateway's location.
    pub fn location(&self) -> &str {
        &self.location
    }

    /// Get the number of discharges issued.
    pub fn issued_count(&self) -> u64 {
        *self.issued_count.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Get the shared key (for use in tests or setup).
    pub fn shared_key(&self) -> &[u8; 32] {
        &self.shared_key
    }

    /// Process a discharge request.
    ///
    /// 1. Decrypt the ticket and read its conditions; refuse any caveat the
    ///    gateway cannot enforce, and any ticket without exactly one holder key.
    /// 2. Check the request is fresh and signed by the ticket's holder key.
    /// 3. Refuse a ticket that is already burned.
    /// 4. Evaluate the ticket's conditions, then the operator's evaluators.
    /// 5. Burn the ticket (atomically; a concurrent winner makes this a replay)
    ///    and issue the discharge.
    ///
    /// A request refused at any step before 5 leaves the ticket unburned.
    pub fn process_request(
        &self,
        request: &DischargeRequest,
    ) -> Result<DischargeResponse, DischargeError> {
        // Step 1: decrypt the ticket and parse the conditions sealed in it.
        let wire_ticket = ThirdPartyCaveat::decrypt_ticket(&request.ticket, &self.shared_key)
            .map_err(|e| {
                denied(
                    "ticket_decryption",
                    format!("failed to decrypt ticket: {e}"),
                )
            })?;

        let mut holder: Option<[u8; 32]> = None;
        let mut conditions = Vec::new();
        for wire in wire_ticket.caveats.iter() {
            match TicketCondition::from_wire(wire).map_err(|e| denied("ticket_caveat", e))? {
                TicketCondition::Holder(pk) => {
                    if holder.replace(pk).is_some() {
                        return Err(denied(
                            "ticket_caveat",
                            "ticket names more than one holder key",
                        ));
                    }
                }
                other => conditions.push(other),
            }
        }
        let holder = holder.ok_or_else(|| {
            denied(
                "ticket_caveat",
                "ticket names no holder key, so no request can be bound to it",
            )
        })?;

        // Step 2: the request must be fresh and signed by the holder key.
        let now = now_unix().map_err(|e| denied("internal", e))?;
        if (now - request.issued_at).abs() > REQUEST_MAX_SKEW_SECS {
            return Err(denied(
                "holder_binding",
                format!(
                    "request issued_at {} is more than {}s from gateway time {}",
                    request.issued_at, REQUEST_MAX_SKEW_SECS, now
                ),
            ));
        }
        verify_ed25519(
            &holder,
            &request.signing_message(&self.location),
            &request.holder_signature,
        )
        .map_err(|e| denied("holder_binding", format!("holder signature: {e}")))?;

        // Step 3: an already-burned ticket is refused before any evaluator runs
        // (stateful evaluators such as the rate limiter must not be charged for it).
        let ticket_hash = crypto::hmac_sha256(&self.shared_key, &request.ticket);
        {
            let issued = self
                .issued
                .lock()
                .map_err(|_| denied("internal", "internal lock error"))?;
            if issued.contains(&ticket_hash) {
                return Err(denied(
                    "replay_prevention",
                    "ticket already discharged (replay detected)",
                ));
            }
        }

        // Step 4: evaluate. The context carries only authenticated facts.
        let ctx = DischargeContext {
            location: &self.location,
            ticket_digest: ticket_digest(&request.ticket),
            holder,
            proof: request.proof.as_deref(),
            payment_evidence: request.payment_evidence.as_deref(),
        };
        let mut met = vec!["holder".to_string()];
        for cond in &conditions {
            match cond {
                TicketCondition::Payment { min_amount } => {
                    let verifier = self.payment_verifier.clone().ok_or_else(|| {
                        denied(
                            "payment",
                            "ticket requires payment but this gateway has no payment verifier",
                        )
                    })?;
                    PaymentEvaluator::new(*min_amount, verifier)
                        .evaluate(&ctx)
                        .map_err(|e| denied("payment", e))?;
                    met.push("payment".to_string());
                }
                TicketCondition::Proof {
                    verifier,
                    statement,
                } => {
                    let label = format!("proof:{verifier}");
                    let f = self.proof_verifiers.get(verifier).cloned().ok_or_else(|| {
                        denied(
                            &label,
                            format!("ticket requires proof verifier '{verifier}', which this gateway does not have"),
                        )
                    })?;
                    VerifyingProofEvaluator::new(f, statement.clone())
                        .evaluate(&ctx)
                        .map_err(|e| denied(&label, e))?;
                    met.push(label);
                }
                TicketCondition::Holder(_) => unreachable!("holder separated above"),
            }
        }
        for evaluator in &self.evaluators {
            evaluator
                .evaluate(&ctx)
                .map_err(|reason| denied(evaluator.name(), reason))?;
            met.push(evaluator.name().to_string());
        }

        // Step 5: burn, then issue. Insert-if-absent under the lock, so of two
        // concurrent requests for one ticket exactly one is issued.
        {
            let mut issued = self
                .issued
                .lock()
                .map_err(|_| denied("internal", "internal lock error"))?;
            if !issued.insert(ticket_hash) {
                return Err(denied(
                    "replay_prevention",
                    "ticket already discharged (replay detected)",
                ));
            }
        }

        let mut discharge_key = [0u8; 32];
        discharge_key.copy_from_slice(&wire_ticket.discharge_key);
        let discharge = create_discharge(
            request.ticket.clone(),
            &discharge_key,
            self.location.clone(),
            &[],
        );
        discharge_key.zeroize();

        let encoded = discharge
            .encode()
            .map_err(|e| denied("encoding", format!("failed to encode discharge: {e}")))?;

        if let Ok(mut count) = self.issued_count.lock() {
            *count += 1;
        }

        Ok(DischargeResponse {
            discharge: encoded,
            expires_at: now + self.discharge_ttl_secs,
            condition_met: met.join(","),
        })
    }

    /// Reset the replay prevention set (for testing only).
    #[cfg(test)]
    pub fn reset_issued(&self) {
        if let Ok(mut issued) = self.issued.lock() {
            issued.clear();
        }
    }

    /// Serialize the replay prevention set for persistence.
    ///
    /// Returns a byte vector containing all ticket hashes in FIFO order.
    /// Each hash is 32 bytes, concatenated sequentially.
    pub fn serialize_issued_set(&self) -> Vec<u8> {
        let issued = match self.issued.lock() {
            Ok(guard) => guard,
            Err(e) => e.into_inner(),
        };
        let mut data = Vec::with_capacity(issued.order.len() * 32);
        for hash in &issued.order {
            data.extend_from_slice(hash);
        }
        data
    }

    /// Number of ticket hashes currently in the replay prevention set.
    ///
    /// Lets a persisting caller tell whether a request changed the set without
    /// writing on every refused request. Only an issued discharge changes it.
    pub fn issued_len(&self) -> usize {
        let issued = match self.issued.lock() {
            Ok(guard) => guard,
            Err(e) => e.into_inner(),
        };
        issued.set.len()
    }

    /// Load a previously persisted replay prevention set.
    ///
    /// The input must be a sequence of 32-byte hashes (as produced by
    /// `serialize_issued_set`). Returns how many hashes were loaded.
    ///
    /// ⚑ A malformed blob is an ERROR and the set is left UNTOUCHED. This used to
    /// `return` silently on a length that was not a multiple of 32, which left the
    /// gateway holding an empty set — i.e. every previously issued ticket became
    /// discharge-able again, with no trace. There is no safe partial load here:
    /// the set's whole job is to be complete.
    pub fn load_issued_set(&self, data: &[u8]) -> Result<usize, ReplaySetLoadError> {
        if !data.len().is_multiple_of(32) {
            return Err(ReplaySetLoadError::Truncated { len: data.len() });
        }
        let mut issued = match self.issued.lock() {
            Ok(guard) => guard,
            Err(e) => e.into_inner(),
        };
        issued.clear();
        for chunk in data.chunks_exact(32) {
            let mut hash = [0u8; 32];
            hash.copy_from_slice(chunk);
            issued.insert(hash);
        }
        Ok(issued.set.len())
    }
}

impl Drop for DischargeGateway {
    fn drop(&mut self) {
        self.shared_key.zeroize();
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Macaroon;

    const LOCATION: &str = "https://gateway.dev";

    fn key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    fn now() -> i64 {
        now_unix().unwrap()
    }

    /// A token with one 3P caveat addressed to the gateway, sealing `holder`
    /// and `conditions` into the ticket. Returns (root_key, token, ticket).
    fn token_for(
        shared_key: &[u8; 32],
        holder: &SigningKey,
        conditions: Vec<TicketCondition>,
    ) -> ([u8; 32], Macaroon, Vec<u8>) {
        let root_key = crypto::random_key();
        let mut mac = Macaroon::new(&root_key, b"test-kid".to_vec(), "https://issuer.dev".into());
        mac.add_third_party(
            LOCATION,
            shared_key,
            ticket_caveats(&holder.verifying_key(), conditions),
        )
        .unwrap();
        let ticket = extract_ticket(&mac);
        (root_key, mac, ticket)
    }

    fn token_with_caveats(shared_key: &[u8; 32], caveats: CaveatSet) -> Vec<u8> {
        let root_key = crypto::random_key();
        let mut mac = Macaroon::new(&root_key, b"test-kid".to_vec(), "https://issuer.dev".into());
        mac.add_third_party(LOCATION, shared_key, caveats).unwrap();
        extract_ticket(&mac)
    }

    fn extract_ticket(mac: &Macaroon) -> Vec<u8> {
        let tp_caveats = mac.caveats.third_party_caveats();
        ThirdPartyCaveat::decode_body(&tp_caveats[0].body)
            .unwrap()
            .ticket
    }

    fn signed(ticket: &[u8], holder: &SigningKey) -> DischargeRequest {
        DischargeRequest::sign(ticket.to_vec(), now(), None, None, LOCATION, holder)
    }

    fn gateway(shared_key: [u8; 32]) -> DischargeGateway {
        DischargeGateway::new(shared_key, LOCATION.to_string())
    }

    fn keyset(keys: &[&SigningKey]) -> HashSet<[u8; 32]> {
        keys.iter().map(|k| k.verifying_key().to_bytes()).collect()
    }

    // ---- holder binding (POST /discharge bound to the ticket) -----------------

    #[test]
    fn honest_holder_gets_a_discharge_that_verifies() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let (root_key, token, ticket) = token_for(&shared_key, &alice, vec![]);
        let gw = gateway(shared_key);

        let resp = gw.process_request(&signed(&ticket, &alice)).unwrap();
        assert_eq!(resp.condition_met, "holder");

        let mut discharge = Macaroon::decode(&resp.discharge).unwrap();
        token.bind_discharge(&mut discharge);
        assert!(token.verify(&root_key, &[discharge]).is_ok());
    }

    #[test]
    fn a_request_not_signed_by_the_ticket_holder_is_refused_and_does_not_burn() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let mallory = key(2);
        let (_, _, ticket) = token_for(&shared_key, &alice, vec![]);
        let gw = gateway(shared_key);

        // Mallory has seen the ticket (it rides in the token) and signs with her key.
        let err = gw.process_request(&signed(&ticket, &mallory)).unwrap_err();
        assert_eq!(err.condition, "holder_binding");
        // An unsigned / garbage signature likewise.
        let mut garbage = signed(&ticket, &alice);
        garbage.holder_signature = vec![0u8; 64];
        assert_eq!(
            gw.process_request(&garbage).unwrap_err().condition,
            "holder_binding"
        );
        assert_eq!(gw.issued_len(), 0, "refused requests burn nothing");

        // Alice still discharges her ticket.
        assert!(gw.process_request(&signed(&ticket, &alice)).is_ok());
    }

    #[test]
    fn a_signature_does_not_transfer_to_other_evidence_or_another_gateway() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let (_, _, ticket) = token_for(&shared_key, &alice, vec![]);
        let gw = gateway(shared_key);

        // Signed for a different location.
        let other = DischargeRequest::sign(
            ticket.clone(),
            now(),
            None,
            None,
            "https://other-gateway.dev",
            &alice,
        );
        assert_eq!(
            gw.process_request(&other).unwrap_err().condition,
            "holder_binding"
        );
        // Evidence swapped in after signing.
        let mut swapped = signed(&ticket, &alice);
        swapped.proof = Some(vec![1, 2, 3]);
        assert_eq!(
            gw.process_request(&swapped).unwrap_err().condition,
            "holder_binding"
        );
    }

    #[test]
    fn a_stale_request_is_refused() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let (_, _, ticket) = token_for(&shared_key, &alice, vec![]);
        let gw = gateway(shared_key);
        let stale = DischargeRequest::sign(
            ticket,
            now() - REQUEST_MAX_SKEW_SECS - 5,
            None,
            None,
            LOCATION,
            &alice,
        );
        assert_eq!(
            gw.process_request(&stale).unwrap_err().condition,
            "holder_binding"
        );
    }

    #[test]
    fn a_ticket_without_exactly_one_holder_or_with_an_unknown_caveat_is_refused() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let gw = gateway(shared_key);

        let none = token_with_caveats(&shared_key, CaveatSet::new());
        assert_eq!(
            gw.process_request(&signed(&none, &alice))
                .unwrap_err()
                .condition,
            "ticket_caveat"
        );

        let mut two = ticket_caveats(&alice.verifying_key(), []);
        two.push(TicketCondition::Holder(key(2).verifying_key().to_bytes()).to_wire());
        let two = token_with_caveats(&shared_key, two);
        assert_eq!(
            gw.process_request(&signed(&two, &alice))
                .unwrap_err()
                .condition,
            "ticket_caveat"
        );

        let mut unknown = ticket_caveats(&alice.verifying_key(), []);
        unknown.push(WireCaveat::new(48, b"whatever".to_vec()));
        let unknown = token_with_caveats(&shared_key, unknown);
        let err = gw.process_request(&signed(&unknown, &alice)).unwrap_err();
        assert_eq!(err.condition, "ticket_caveat");
        assert!(err.reason.contains("48"), "{}", err.reason);
    }

    // ---- replay / burn ordering (F12) -----------------------------------------

    #[test]
    fn test_replay_prevention() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let (_, _, ticket) = token_for(&shared_key, &alice, vec![]);
        let gw = gateway(shared_key);

        assert!(gw.process_request(&signed(&ticket, &alice)).is_ok());
        let err = gw.process_request(&signed(&ticket, &alice)).unwrap_err();
        assert_eq!(err.condition, "replay_prevention");
    }

    #[test]
    fn a_failed_condition_does_not_consume_the_ticket() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let kyc = key(9);
        let statement = b"over-18".to_vec();
        let (_, _, ticket) = token_for(
            &shared_key,
            &alice,
            vec![TicketCondition::Proof {
                verifier: "kyc".into(),
                statement: statement.clone(),
            }],
        );
        let mut gw = gateway(shared_key);
        gw.add_proof_verifier("kyc", ProofAttestation::verifier(keyset(&[&kyc])));

        // No proof: denied, ticket untouched.
        let err = gw.process_request(&signed(&ticket, &alice)).unwrap_err();
        assert_eq!(err.condition, "proof:kyc");
        assert_eq!(
            gw.issued_len(),
            0,
            "a denied request must not burn the ticket"
        );

        // Now with a real attestation: issued, and only now burned.
        let proof = ProofAttestation::sign(
            &kyc,
            LOCATION,
            &statement,
            &ticket_digest(&ticket),
            &alice.verifying_key().to_bytes(),
        );
        let req =
            DischargeRequest::sign(ticket.clone(), now(), Some(proof), None, LOCATION, &alice);
        assert!(gw.process_request(&req).is_ok());
        assert_eq!(gw.issued_len(), 1);
    }

    // ---- proof conditions (F11) -----------------------------------------------

    #[test]
    fn a_proof_condition_is_discharged_only_by_a_verified_proof() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let kyc = key(9);
        let rogue = key(10);
        let statement = b"over-18".to_vec();
        let cond = || {
            vec![TicketCondition::Proof {
                verifier: "kyc".into(),
                statement: statement.clone(),
            }]
        };
        let (_, _, ticket) = token_for(&shared_key, &alice, cond());
        let (_, _, other_ticket) = token_for(&shared_key, &alice, cond());
        let alice_pk = alice.verifying_key().to_bytes();

        // A gateway without the named verifier refuses outright.
        let bare = gateway(shared_key);
        let err = bare
            .process_request(&DischargeRequest::sign(
                ticket.clone(),
                now(),
                Some(vec![0xAB; 96]),
                None,
                LOCATION,
                &alice,
            ))
            .unwrap_err();
        assert_eq!(err.condition, "proof:kyc");

        let mut gw = gateway(shared_key);
        gw.add_proof_verifier("kyc", ProofAttestation::verifier(keyset(&[&kyc])));
        let try_proof = |proof: Vec<u8>| {
            gw.process_request(&DischargeRequest::sign(
                ticket.clone(),
                now(),
                Some(proof),
                None,
                LOCATION,
                &alice,
            ))
        };

        // The bytes the deleted ProofRequiredEvaluator accepted.
        assert!(
            try_proof(vec![0xAB; 96]).is_err(),
            "arbitrary bytes are not a proof"
        );
        // Signed by an attestor the gateway does not trust.
        let t = ticket_digest(&ticket);
        assert!(
            try_proof(ProofAttestation::sign(
                &rogue, LOCATION, &statement, &t, &alice_pk
            ))
            .is_err()
        );
        // A genuine attestation, but of a different statement.
        assert!(
            try_proof(ProofAttestation::sign(
                &kyc, LOCATION, b"over-21", &t, &alice_pk
            ))
            .is_err()
        );
        // A genuine attestation for another ticket.
        let t2 = ticket_digest(&other_ticket);
        assert!(
            try_proof(ProofAttestation::sign(
                &kyc, LOCATION, &statement, &t2, &alice_pk
            ))
            .is_err()
        );
        assert_eq!(gw.issued_len(), 0);

        // The honest proof.
        let resp = try_proof(ProofAttestation::sign(
            &kyc, LOCATION, &statement, &t, &alice_pk,
        ))
        .expect("verified proof discharges");
        assert_eq!(resp.condition_met, "holder,proof:kyc");
    }

    #[test]
    fn an_operator_proof_condition_uses_the_verifying_evaluator() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let kyc = key(9);
        let (_, _, ticket) = token_for(&shared_key, &alice, vec![]);
        let mut gw = gateway(shared_key);
        gw.add_evaluator(Box::new(VerifyingProofEvaluator::new(
            ProofAttestation::verifier(keyset(&[&kyc])),
            b"member".to_vec(),
        )));

        let bogus = DischargeRequest::sign(
            ticket.clone(),
            now(),
            Some(vec![1; 64]),
            None,
            LOCATION,
            &alice,
        );
        assert_eq!(
            gw.process_request(&bogus).unwrap_err().condition,
            "verifying_proof"
        );

        let proof = ProofAttestation::sign(
            &kyc,
            LOCATION,
            b"member",
            &ticket_digest(&ticket),
            &alice.verifying_key().to_bytes(),
        );
        let ok = DischargeRequest::sign(ticket, now(), Some(proof), None, LOCATION, &alice);
        assert!(gw.process_request(&ok).is_ok());
    }

    // ---- payment conditions (F11) ---------------------------------------------

    #[test]
    fn a_payment_condition_is_discharged_only_by_a_verified_attestation() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let processor = key(7);
        let rogue = key(8);
        let (_, _, ticket) = token_for(
            &shared_key,
            &alice,
            vec![TicketCondition::Payment { min_amount: 100 }],
        );
        let (_, _, other_ticket) = token_for(
            &shared_key,
            &alice,
            vec![TicketCondition::Payment { min_amount: 100 }],
        );
        let alice_pk = alice.verifying_key().to_bytes();
        let t = ticket_digest(&ticket);

        // No payment verifier installed: every payment ticket is refused.
        let bare = gateway(shared_key);
        let ev =
            PaymentAttestation::sign(&processor, LOCATION, &t, &alice_pk, 100, b"tx1".to_vec());
        let err = bare
            .process_request(&DischargeRequest::sign(
                ticket.clone(),
                now(),
                None,
                Some(ev),
                LOCATION,
                &alice,
            ))
            .unwrap_err();
        assert_eq!(err.condition, "payment");

        let mut gw = gateway(shared_key);
        gw.set_payment_verifier(PaymentAttestation::verifier(keyset(&[&processor])));
        let try_pay = |ev: Option<Vec<u8>>| {
            gw.process_request(&DischargeRequest::sign(
                ticket.clone(),
                now(),
                None,
                ev,
                LOCATION,
                &alice,
            ))
        };

        assert!(try_pay(None).is_err(), "no evidence");
        // The old self-asserted shape, as bytes: a bare number is not evidence.
        assert!(try_pay(Some(rmp_serde::to_vec(&100u64).unwrap())).is_err());
        // Attested by an untrusted key.
        assert!(
            try_pay(Some(PaymentAttestation::sign(
                &rogue,
                LOCATION,
                &t,
                &alice_pk,
                100,
                b"tx1".to_vec()
            )))
            .is_err()
        );
        // Attested, but too little.
        let short = try_pay(Some(PaymentAttestation::sign(
            &processor,
            LOCATION,
            &t,
            &alice_pk,
            50,
            b"tx1".to_vec(),
        )))
        .unwrap_err();
        assert!(short.reason.contains("insufficient"), "{}", short.reason);
        // Attested for another ticket.
        let t2 = ticket_digest(&other_ticket);
        assert!(
            try_pay(Some(PaymentAttestation::sign(
                &processor,
                LOCATION,
                &t2,
                &alice_pk,
                100,
                b"tx1".to_vec()
            )))
            .is_err()
        );
        // Attested for another holder.
        let bob_pk = key(3).verifying_key().to_bytes();
        assert!(
            try_pay(Some(PaymentAttestation::sign(
                &processor,
                LOCATION,
                &t,
                &bob_pk,
                100,
                b"tx1".to_vec()
            )))
            .is_err()
        );
        // Amount tampered after signing.
        let mut att: PaymentAttestation = rmp_serde::from_slice(&PaymentAttestation::sign(
            &processor,
            LOCATION,
            &t,
            &alice_pk,
            1,
            b"tx1".to_vec(),
        ))
        .unwrap();
        att.amount = 1_000;
        assert!(try_pay(Some(rmp_serde::to_vec(&att).unwrap())).is_err());
        assert_eq!(gw.issued_len(), 0);

        let resp = try_pay(Some(PaymentAttestation::sign(
            &processor,
            LOCATION,
            &t,
            &alice_pk,
            100,
            b"tx1".to_vec(),
        )))
        .expect("verified payment discharges");
        assert_eq!(resp.condition_met, "holder,payment");
    }

    // ---- allowlist / rate limit keyed on the authenticated holder -------------

    #[test]
    fn allowlist_is_keyed_on_the_holder_key() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let eve = key(5);
        let mut gw = gateway(shared_key);
        gw.add_evaluator(Box::new(AllowlistEvaluator {
            allowed: keyset(&[&alice]),
        }));

        let (_, _, t_alice) = token_for(&shared_key, &alice, vec![]);
        assert!(gw.process_request(&signed(&t_alice, &alice)).is_ok());

        // Eve holds a valid ticket of her own; she is not on the list.
        let (_, _, t_eve) = token_for(&shared_key, &eve, vec![]);
        assert_eq!(
            gw.process_request(&signed(&t_eve, &eve))
                .unwrap_err()
                .condition,
            "allowlist"
        );
        // Nor can she present Alice's identity: she cannot sign as Alice, and a
        // ticket naming Alice is Alice's.
        let (_, _, t_alice2) = token_for(&shared_key, &alice, vec![]);
        assert_eq!(
            gw.process_request(&signed(&t_alice2, &eve))
                .unwrap_err()
                .condition,
            "holder_binding"
        );
    }

    #[test]
    fn rate_limit_is_keyed_on_the_holder_key() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let bob = key(2);
        let mut gw = gateway(shared_key);
        gw.add_evaluator(Box::new(RateLimitEvaluator::new(2, 3600)));

        for _ in 0..2 {
            let (_, _, t) = token_for(&shared_key, &alice, vec![]);
            assert!(gw.process_request(&signed(&t, &alice)).is_ok());
        }
        let (_, _, t) = token_for(&shared_key, &alice, vec![]);
        assert_eq!(
            gw.process_request(&signed(&t, &alice))
                .unwrap_err()
                .condition,
            "rate_limit"
        );
        // The refused ticket is still spendable; a different holder is unaffected.
        assert_eq!(gw.issued_len(), 2);
        let (_, _, tb) = token_for(&shared_key, &bob, vec![]);
        assert!(gw.process_request(&signed(&tb, &bob)).is_ok());
    }

    #[test]
    fn test_composite_any_of() {
        let shared_key = crypto::random_key();
        let vip = key(1);
        let normie = key(2);
        let kyc = key(9);
        let mut gw = gateway(shared_key);
        gw.add_evaluator(Box::new(AnyOfEvaluator {
            evaluators: vec![
                Box::new(AllowlistEvaluator {
                    allowed: keyset(&[&vip]),
                }),
                Box::new(VerifyingProofEvaluator::new(
                    ProofAttestation::verifier(keyset(&[&kyc])),
                    b"member".to_vec(),
                )),
            ],
        }));

        let (_, _, t) = token_for(&shared_key, &vip, vec![]);
        assert!(gw.process_request(&signed(&t, &vip)).is_ok());

        let (_, _, t) = token_for(&shared_key, &normie, vec![]);
        assert!(gw.process_request(&signed(&t, &normie)).is_err());
        let proof = ProofAttestation::sign(
            &kyc,
            LOCATION,
            b"member",
            &ticket_digest(&t),
            &normie.verifying_key().to_bytes(),
        );
        let req = DischargeRequest::sign(t, now(), Some(proof), None, LOCATION, &normie);
        assert!(gw.process_request(&req).is_ok());
    }

    #[test]
    fn test_wrong_shared_key_rejects() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let (_, _, ticket) = token_for(&shared_key, &alice, vec![]);
        let gw = gateway(crypto::random_key());
        assert_eq!(
            gw.process_request(&signed(&ticket, &alice))
                .unwrap_err()
                .condition,
            "ticket_decryption"
        );
    }

    #[test]
    fn test_issued_count() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let gw = gateway(shared_key);
        for _ in 0..3 {
            let (_, _, t) = token_for(&shared_key, &alice, vec![]);
            gw.process_request(&signed(&t, &alice)).unwrap();
        }
        assert_eq!(gw.issued_count(), 3);
    }

    // ---- persisted replay set -------------------------------------------------

    /// A gateway holding an EMPTY set re-issues a ticket it has already
    /// discharged, and the re-issued macaroon verifies against the root token
    /// exactly like the first one. This is what `/api/discharge` was one
    /// swallowed `Err` away from doing on every restart-with-an-unreadable-store.
    #[test]
    fn an_empty_replay_set_re_issues_an_already_spent_ticket() {
        let shared_key = crypto::random_key();
        let alice = key(1);
        let (root_key, mac, ticket) = token_for(&shared_key, &alice, vec![]);
        let gw = gateway(shared_key);

        let first = gw
            .process_request(&signed(&ticket, &alice))
            .expect("first discharge");
        assert!(
            gw.process_request(&signed(&ticket, &alice)).is_err(),
            "the burn must refuse the second presentation"
        );

        let restored = gateway(shared_key);
        assert_eq!(restored.issued_len(), 0, "a fresh gateway knows nothing");
        let second = restored
            .process_request(&signed(&ticket, &alice))
            .expect("⚑ THE SPENT TICKET IS DISCHARGED AGAIN");

        assert_ne!(second.discharge, first.discharge);
        let mut discharge = Macaroon::decode(&second.discharge).unwrap();
        mac.bind_discharge(&mut discharge);
        assert!(
            mac.verify(&root_key, &[discharge]).is_ok(),
            "the re-issued discharge verifies — this is the ticket reuse the \
             persisted set exists to prevent"
        );
    }

    /// A malformed persisted blob is an ERROR and leaves the set UNTOUCHED.
    #[test]
    fn a_malformed_persisted_set_is_refused_and_does_not_clear_the_live_one() {
        let shared_key = crypto::random_key();
        let gw = gateway(shared_key);

        let mut seed = [0u8; 64];
        seed[..32].copy_from_slice(&[0x11u8; 32]);
        seed[32..].copy_from_slice(&[0x33u8; 32]);
        assert_eq!(gw.load_issued_set(&seed), Ok(2));
        assert_eq!(gw.issued_len(), 2);

        assert_eq!(
            gw.load_issued_set(&[0x22u8; 65]),
            Err(ReplaySetLoadError::Truncated { len: 65 }),
        );
        assert_eq!(gw.issued_len(), 2);

        let blob = gw.serialize_issued_set();
        let fresh = gateway(shared_key);
        assert_eq!(fresh.load_issued_set(&blob), Ok(2));
        assert_eq!(fresh.serialize_issued_set(), blob, "round-trip is exact");
    }

    /// `set` and `order` must not diverge on a duplicated persisted hash.
    #[test]
    fn a_duplicated_hash_in_a_persisted_blob_does_not_desynchronise_the_eviction_queue() {
        let gw = gateway(crypto::random_key());
        let mut blob = Vec::new();
        blob.extend_from_slice(&[0xAAu8; 32]);
        blob.extend_from_slice(&[0xAAu8; 32]);
        blob.extend_from_slice(&[0xBBu8; 32]);
        assert_eq!(gw.load_issued_set(&blob), Ok(2), "A and B, not A A B");
        assert_eq!(gw.serialize_issued_set().len(), 64);
    }
}
