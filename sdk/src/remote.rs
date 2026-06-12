//! Remote turn submission (#171): build + sign a turn LOCALLY, submit the
//! canonical signed envelope to a node over HTTP.
//!
//! [`RemoteRuntime`] is the remote twin of [`crate::runtime::AgentRuntime`]'s
//! two-nouns surface: `remote.turn().transfer(..).sign().await?.submit().await?`
//! yields a committed receipt from a NODE — the agent's keypair never leaves
//! this process, and the node may never have seen it before.
//!
//! The wire shape is the node's `POST /turns/submit` signed-envelope ingress
//! (postcard-encoded [`SignedTurn`], `Content-Type: application/octet-stream`):
//! the node verifies the envelope signature against the canonical `Turn::hash`,
//! checks the agent cell is the signer's default cell, and executes through the
//! SAME producer-aware executor gate as local turns (no parallel entry).
//!
//! Two bindings are discovered from the node before signing:
//!
//!  * **federation id** — the executor verifies each action's Ed25519
//!    signature over the federation-BOUND signing message; an unconfigured
//!    solo node binds `blake3(operator pubkey)` rather than the placeholder
//!    its `/api/federations` serves.
//!  * **nonce / receipt-chain head** — the turn rides the agent cell's live
//!    replay counter and the node's committed receipt head (causal binding);
//!    a race with another commit is retried once with fresh bindings (the
//!    per-action signature stays valid; only the envelope is re-signed).
//!
//! Every turn is stamped with a `valid_until` horizon BEFORE the envelope is
//! signed. This is load-bearing beyond expiry: the verified Lean producer's
//! wire marshal REQUIRES `valid_until`, so an unstamped remote turn would fall
//! off the verified producer back to the legacy Rust producer on every node
//! (the REORIENT "thin-HTTP turns fall off the Lean producer" failure mode,
//! closed here for the remote path).

use dregg_cell::CellId;
use dregg_turn::{Action, Authorization, CallForest, Effect, Turn, TurnExecutor, action::symbol};
use dregg_types::hex_encode;
use serde::Deserialize;

use crate::cipherclerk::{AgentCipherclerk, SignedTurn};
use crate::error::SdkError;
use crate::raw;

/// Validity horizon stamped on every remote turn: wall-clock now + one hour.
/// A TIMESTAMP deadline (the executor enforces `current_timestamp <= valid_until`),
/// matching the node's own `DEFAULT_TURN_VALIDITY_HORIZON_SECS`.
pub const REMOTE_TURN_VALIDITY_HORIZON_SECS: i64 = 3600;

/// Default fee (computron budget) for remote turns, mirroring the local
/// runtime's agent-turn default.
pub const DEFAULT_REMOTE_FEE: u64 = 10_000;

fn now_secs() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

fn hex_decode_32(s: &str) -> Result<[u8; 32], SdkError> {
    let bytes = hex::decode(s).map_err(|e| SdkError::Wire(format!("bad hex from node: {e}")))?;
    bytes
        .try_into()
        .map_err(|_| SdkError::Wire("expected 32-byte hex value from node".to_string()))
}

// ─── node response shapes (the fields this client consumes) ───

#[derive(Debug, Deserialize)]
struct FederationInfoLite {
    #[serde(default)]
    federation_id: String,
    #[serde(default)]
    is_local: bool,
    #[serde(default)]
    member_count: usize,
    #[serde(default)]
    committee_epoch: u64,
}

#[derive(Debug, Deserialize)]
struct NodeIdentityLite {
    public_key: String,
}

#[derive(Debug, Deserialize)]
struct CellDetailLite {
    #[serde(default)]
    found: bool,
    #[serde(default)]
    nonce: u64,
}

/// One entry of `GET /api/receipts` (the fields the remote client consumes).
#[derive(Debug, Clone, Deserialize)]
pub struct RemoteReceiptInfo {
    /// Hex-encoded turn hash this receipt commits.
    pub turn_hash: String,
    /// Hex-encoded receipt hash (the chain link).
    pub receipt_hash: String,
    /// Position in the node's committed receipt chain.
    #[serde(default)]
    pub chain_index: usize,
    /// Whether this receipt is the chain head.
    #[serde(default)]
    pub chain_head: bool,
    /// Whether an attestation (witness/proof) is attached.
    #[serde(default)]
    pub has_proof: bool,
}

#[derive(Debug, Deserialize)]
struct SubmitSignedTurnResponseLite {
    #[serde(default)]
    accepted: bool,
    #[serde(default)]
    turn_hash: Option<String>,
    #[serde(default)]
    error: Option<String>,
}

#[derive(Debug, Deserialize)]
struct FaucetResponseLite {
    #[serde(default)]
    success: bool,
    #[serde(default)]
    error: Option<String>,
}

/// The committed result of a remote submission.
#[derive(Debug, Clone)]
pub struct RemoteReceipt {
    /// Hex-encoded canonical `Turn::hash` of the committed turn — the key
    /// under which the receipt appears in the node's `/api/receipts`.
    pub turn_hash: String,
}

/// A remote agent runtime: local keys, remote (node-side) execution.
///
/// Holds the agent's [`AgentCipherclerk`] (identity + signing) and a node base
/// URL. All state reads and the authoritative execution happen on the node.
pub struct RemoteRuntime {
    cipherclerk: AgentCipherclerk,
    base: String,
    http: reqwest::Client,
    cell: CellId,
    federation_id: std::sync::OnceLock<[u8; 32]>,
}

impl RemoteRuntime {
    /// Bind a cipherclerk to a node base URL (e.g. `http://127.0.0.1:8080`).
    /// No I/O happens until the first signing/submission (federation binding
    /// is discovered lazily and cached).
    pub fn connect(base_url: impl Into<String>, cipherclerk: AgentCipherclerk) -> Self {
        let cell = cipherclerk.cell_id("default");
        Self {
            cipherclerk,
            base: base_url.into().trim_end_matches('/').to_string(),
            http: reqwest::Client::new(),
            cell,
            federation_id: std::sync::OnceLock::new(),
        }
    }

    /// The agent cell every turn acts as — `derive_raw(pubkey, blake3("default"))`,
    /// the same derivation the node's ingress enforces against the envelope signer.
    pub fn cell_id(&self) -> CellId {
        self.cell
    }

    async fn get_json<T: serde::de::DeserializeOwned>(&self, path: &str) -> Result<T, SdkError> {
        let url = format!("{}{}", self.base, path);
        let resp = self
            .http
            .get(&url)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("GET {path}: {e}")))?;
        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!("GET {path}: HTTP {}", resp.status())));
        }
        resp.json::<T>()
            .await
            .map_err(|e| SdkError::Wire(format!("GET {path}: bad body: {e}")))
    }

    /// The federation id the node's EXECUTOR verifies action signatures
    /// against. A configured federation: the local `/api/federations` entry
    /// with a real committee. An unconfigured solo node (the devnet default)
    /// serves a placeholder there while its executor binds
    /// `blake3(operator pubkey)` — mirrored here.
    pub async fn federation_id(&self) -> Result<[u8; 32], SdkError> {
        if let Some(id) = self.federation_id.get() {
            return Ok(*id);
        }
        let discovered = self.discover_federation_id().await?;
        Ok(*self.federation_id.get_or_init(|| discovered))
    }

    async fn discover_federation_id(&self) -> Result<[u8; 32], SdkError> {
        if let Ok(feds) = self.get_json::<Vec<FederationInfoLite>>("/api/federations").await {
            if let Some(local) = feds
                .iter()
                .find(|f| f.is_local && f.member_count > 0 && f.committee_epoch > 0)
            {
                return hex_decode_32(&local.federation_id);
            }
        }
        // Solo-node derivation: blake3(operator pubkey).
        let identity: NodeIdentityLite = self.get_json("/api/node/identity").await?;
        let pk = hex_decode_32(&identity.public_key)?;
        Ok(*blake3::hash(&pk).as_bytes())
    }

    /// The agent cell's live replay counter on the node's ledger (0 when the
    /// cell does not exist yet).
    pub async fn current_nonce(&self) -> Result<u64, SdkError> {
        let detail: CellDetailLite = self
            .get_json(&format!("/api/cell/{}", hex_encode(&self.cell.0)))
            .await?;
        Ok(if detail.found { detail.nonce } else { 0 })
    }

    /// The node's committed receipt-chain head (causal binding for
    /// `previous_receipt_hash`). `None` when the node has no receipts yet.
    pub async fn receipt_chain_head(&self) -> Result<Option<[u8; 32]>, SdkError> {
        let infos: Vec<RemoteReceiptInfo> = self.get_json("/api/receipts").await?;
        let head = infos
            .iter()
            .find(|r| r.chain_head)
            .or_else(|| infos.iter().max_by_key(|r| r.chain_index));
        match head {
            Some(h) => Ok(Some(hex_decode_32(&h.receipt_hash)?)),
            None => Ok(None),
        }
    }

    /// Fetch the committed receipt for `turn_hash` (hex) from `/api/receipts`.
    pub async fn receipt(&self, turn_hash: &str) -> Result<Option<RemoteReceiptInfo>, SdkError> {
        let infos: Vec<RemoteReceiptInfo> = self.get_json("/api/receipts").await?;
        Ok(infos.into_iter().find(|r| r.turn_hash == turn_hash))
    }

    /// Devnet onboarding: `POST /api/faucet` to materialize this agent's
    /// hosted cell with its REAL owner key (required before the cell can pass
    /// Ed25519 turn authorization) and claim `amount` computrons.
    pub async fn faucet(&self, amount: u64) -> Result<(), SdkError> {
        let body = serde_json::json!({
            "recipient": hex_encode(&self.cell.0),
            "amount": amount,
            "public_key": hex_encode(&self.cipherclerk.public_key().0),
        });
        let url = format!("{}/api/faucet", self.base);
        let resp = self
            .http
            .post(&url)
            .json(&body)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("POST /api/faucet: {e}")))?;
        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "POST /api/faucet: HTTP {}",
                resp.status()
            )));
        }
        let out: FaucetResponseLite = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("faucet: bad body: {e}")))?;
        if !out.success {
            return Err(SdkError::Rejected(
                out.error.unwrap_or_else(|| "faucet refused".to_string()),
            ));
        }
        Ok(())
    }

    /// Begin staging a remote turn (the two-nouns surface):
    /// `remote.turn().transfer(..).sign().await?.submit().await?`.
    pub fn turn(&self) -> RemoteTurnBuilder<'_> {
        RemoteTurnBuilder {
            runtime: self,
            target: None,
            method: "execute".to_string(),
            fee: None,
            effects: Vec::new(),
        }
    }

    /// Sign `unsigned` over the canonical federation-bound signing message
    /// with this identity's key — the remote twin of the local runtime's
    /// `sign_action_for_runtime` (the ONLY way an action leaves this runtime).
    fn sign_action(&self, unsigned: Action, federation_id: &[u8; 32]) -> Action {
        let unsigned = Action {
            authorization: Authorization::Unchecked,
            ..unsigned
        };
        let message = TurnExecutor::compute_signing_message(&unsigned, federation_id);
        let sig = self.cipherclerk.sign_bytes(&message);
        Action {
            authorization: Authorization::from_sig_bytes(sig.0),
            ..unsigned
        }
    }

    /// Envelope-sign `turn` and POST the postcard `SignedTurn` to the node's
    /// `/turns/submit` ingress.
    async fn submit_envelope(&self, turn: &Turn) -> Result<SubmitSignedTurnResponseLite, SdkError> {
        let signed: SignedTurn = self.cipherclerk.sign_turn(turn);
        let bytes = postcard::to_stdvec(&signed)
            .map_err(|e| SdkError::Wire(format!("envelope encode: {e}")))?;
        let url = format!("{}/turns/submit", self.base);
        let resp = self
            .http
            .post(&url)
            .header("Content-Type", "application/octet-stream")
            .body(bytes)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("POST /turns/submit: {e}")))?;
        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "POST /turns/submit: HTTP {}",
                resp.status()
            )));
        }
        resp.json::<SubmitSignedTurnResponseLite>()
            .await
            .map_err(|e| SdkError::Wire(format!("submit response: bad body: {e}")))
    }
}

/// Stages effects for one remote turn. Produced by [`RemoteRuntime::turn`];
/// terminal verb is [`sign`](Self::sign) (async: the federation binding is
/// discovered from the node on first use).
pub struct RemoteTurnBuilder<'rt> {
    runtime: &'rt RemoteRuntime,
    target: Option<CellId>,
    method: String,
    fee: Option<u64>,
    effects: Vec<Effect>,
}

impl<'rt> RemoteTurnBuilder<'rt> {
    /// Address the action at `target` instead of the agent's own cell.
    pub fn on(mut self, target: CellId) -> Self {
        self.target = Some(target);
        self
    }

    /// Set the action method name (default `"execute"`).
    pub fn method(mut self, name: &str) -> Self {
        self.method = name.to_string();
        self
    }

    /// Set the turn fee (computron budget). Default [`DEFAULT_REMOTE_FEE`].
    pub fn fee(mut self, fee: u64) -> Self {
        self.fee = Some(fee);
        self
    }

    /// Stage a transfer from the acting cell to `to`.
    pub fn transfer(mut self, to: CellId, amount: u64) -> Self {
        let from = self.acting_cell();
        self.effects.push(Effect::Transfer { from, to, amount });
        self
    }

    /// Stage a field write on the acting cell (encoded like
    /// [`dregg_cell::field_from_u64`]).
    pub fn write_u64(self, index: usize, value: u64) -> Self {
        let cell = self.acting_cell();
        let value = dregg_cell::field_from_u64(value);
        self.effect(Effect::SetField { cell, index, value })
    }

    /// Stage a nonce increment on the acting cell.
    pub fn increment_nonce(self) -> Self {
        let cell = self.acting_cell();
        self.effect(Effect::IncrementNonce { cell })
    }

    /// Stage a raw [`Effect`].
    pub fn effect(mut self, effect: Effect) -> Self {
        self.effects.push(effect);
        self
    }

    /// Stage several raw [`Effect`]s.
    pub fn effects(mut self, effects: impl IntoIterator<Item = Effect>) -> Self {
        self.effects.extend(effects);
        self
    }

    fn acting_cell(&self) -> CellId {
        self.target.unwrap_or(self.runtime.cell)
    }

    /// Sign the staged action with this identity's key over the canonical
    /// federation-bound signing message, yielding a [`RemoteAuthorizedTurn`]
    /// ready to [`submit`](RemoteAuthorizedTurn::submit). After this point the
    /// act is credentialed; there is no way back to an unauthorized shape.
    pub async fn sign(self) -> Result<RemoteAuthorizedTurn<'rt>, SdkError> {
        if self.effects.is_empty() {
            return Err(SdkError::Rejected(
                "refusing to sign an empty turn (no effects staged)".to_string(),
            ));
        }
        let federation_id = self.runtime.federation_id().await?;
        let target = self.acting_cell();
        let unsigned = raw::unsigned_action_named(target, &self.method, self.effects);
        let action = self.runtime.sign_action(unsigned, &federation_id);
        Ok(RemoteAuthorizedTurn {
            runtime: self.runtime,
            action,
            fee: self.fee.unwrap_or(DEFAULT_REMOTE_FEE),
            submitted: false,
        })
    }
}

/// A signed, ready-to-submit remote turn. Produced by
/// [`RemoteTurnBuilder::sign`]; consumed by [`submit`](Self::submit).
pub struct RemoteAuthorizedTurn<'rt> {
    runtime: &'rt RemoteRuntime,
    action: Action,
    fee: u64,
    submitted: bool,
}

impl RemoteAuthorizedTurn<'_> {
    /// The clerk's faithful, total explanation of exactly what was signed
    /// (the anti-blind-signing reading; see [`crate::explain`]).
    pub fn explain(&self) -> String {
        crate::explain::explain_action(&self.action)
    }

    /// The signed action (inspection only — `submit` consumes the turn).
    pub fn action(&self) -> &Action {
        &self.action
    }

    /// Build the turn envelope with live node bindings (nonce, receipt-chain
    /// head, `valid_until` horizon), envelope-sign it, and submit. A chain-head
    /// race (another commit landing between read and submit) is retried once
    /// with fresh bindings — the per-action signature stays valid; only the
    /// envelope is re-signed. One-shot.
    pub async fn submit(mut self) -> Result<RemoteReceipt, SdkError> {
        if self.submitted {
            return Err(SdkError::Rejected(
                "RemoteAuthorizedTurn already submitted (one-shot)".to_string(),
            ));
        }
        self.submitted = true;

        let mut last_error = String::new();
        for attempt in 0..2 {
            let nonce = self.runtime.current_nonce().await?;
            let previous_receipt_hash = self.runtime.receipt_chain_head().await?;
            let mut forest = CallForest::new();
            forest.add_root(self.action.clone());
            let turn = Turn {
                agent: self.runtime.cell,
                nonce,
                fee: self.fee,
                memo: None,
                // Load-bearing twice over: the executor's expiry gate AND the
                // verified Lean producer's wire marshal (an unstamped turn
                // falls back to the legacy Rust producer on every node).
                valid_until: Some(now_secs() + REMOTE_TURN_VALIDITY_HORIZON_SECS),
                call_forest: forest,
                depends_on: vec![],
                previous_receipt_hash,
                conservation_proof: None,
                sovereign_witnesses: std::collections::HashMap::new(),
                execution_proof: None,
                execution_proof_cell: None,
                execution_proof_new_commitment: None,
                custom_program_proofs: None,
                effect_binding_proofs: Vec::new(),
                cross_effect_dependencies: Vec::new(),
                effect_witness_index_map: Vec::new(),
            };
            let resp = self.runtime.submit_envelope(&turn).await?;
            if resp.accepted {
                return Ok(RemoteReceipt {
                    turn_hash: resp
                        .turn_hash
                        .unwrap_or_else(|| hex_encode(&turn.hash())),
                });
            }
            last_error = resp
                .error
                .unwrap_or_else(|| "node refused the turn".to_string());
            let racy = last_error.contains("receipt chain mismatch")
                || last_error.to_ascii_lowercase().contains("nonce");
            if attempt == 0 && racy {
                continue; // a racing commit moved the bindings; rebind once
            }
            break;
        }
        Err(SdkError::Rejected(last_error))
    }
}

/// The method symbol helper, re-exported for callers staging raw actions
/// against the node's verifier (`request_action = hex(blake3(name))`).
pub fn method_symbol(name: &str) -> [u8; 32] {
    symbol(name)
}
