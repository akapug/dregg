//! # The deos-host private-server CLIENT
//!
//! The CLIENT side of the deos-host split. A dregg node can host a headless userspace
//! deos-js "private server" (`node`'s `deos-host` feature): it holds state on the node's
//! ledger and publishes a cap-gated affordance surface. The cockpit is just ONE client of
//! that; this module is a thin, gpui-free client any program (a cockpit, a bot, a thin
//! terminal) reuses to:
//!
//!   * **discover** a hosted server's affordances — `GET /api/server/{cell}/affordances`
//!     ([`discover_server_affordances`]) — projected for the viewer's held authority (the
//!     proven attenuation lattice: a weaker viewer sees a strictly smaller set); and
//!   * **fire** one affordance — build a signed [`Turn`] carrying the affordance's effects
//!     and POST it to the node's `/turns/submit` ingress ([`fire_affordance`]) — a real
//!     verified turn on the node's live ledger.
//!
//! The discovery surface carries `(name, required)` per affordance plus the executor's
//! federation id (the binding a fire action is signed over). It does NOT carry the
//! effects: the effects a fire commits are the CLIENT's intent (what it wants to do with
//! the cap it holds), exactly as in the real protocol — the published surface advertises
//! *which* messages a holder may send and the authority each needs, and the holder
//! supplies the concrete effects. The node re-checks every effect against the executor's
//! authority gate, so a client cannot fire effects its caps do not authorize.

use dregg_turn::action::Effect;
use dregg_turn::{ComputronCosts, Turn, TurnExecutor};
use dregg_types::CellId;

use dregg_sdk::AgentCipherclerk;
use dregg_sdk::error::SdkError;

/// One affordance discovered on a hosted server's surface: its `name` and the authority a
/// client must HOLD to fire it (the cap tooth). The effects a fire commits are the
/// client's own intent (supplied to [`fire_affordance`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiscoveredAffordance {
    /// The affordance name (the action method a fire names).
    pub name: String,
    /// The authority label the viewer must hold ("none"/"signature"/"proof"/"either").
    pub required: String,
}

/// The result of discovering a hosted server's surface: the affordances visible to the
/// viewer's held authority, plus the executor's federation id (the binding a fire action
/// is signed over — a remote client cannot derive it, so discovery hands it back).
#[derive(Clone, Debug)]
pub struct ServerDiscovery {
    /// The server (or forked instance) cell the surface belongs to.
    pub cell: String,
    /// The affordances visible to the viewer (projected per the attenuation lattice).
    pub affordances: Vec<DiscoveredAffordance>,
    /// The executor's federation id (hex) — the binding [`fire_affordance`] signs over.
    pub executor_federation_id: String,
}

impl ServerDiscovery {
    /// Whether an affordance of `name` is visible to the discovering viewer.
    pub fn has(&self, name: &str) -> bool {
        self.affordances.iter().any(|a| a.name == name)
    }
}

/// **Discover** a hosted server's cap-gated affordance surface.
///
/// `GET {node_url}/api/server/{server_cell_hex}/affordances?viewer={viewer}`. `viewer` is
/// the held-authority label the surface is projected for ("none"/"signature"/"proof"/
/// "either"); a weaker viewer sees a strictly smaller set (the proven attenuation
/// lattice). `server_cell_hex` is the server cell OR a forked-instance cell — both publish
/// their own surface, so a client connects to a specific party/session instance by its id.
pub async fn discover_server_affordances(
    node_url: &str,
    server_cell_hex: &str,
    viewer: &str,
) -> Result<ServerDiscovery, SdkError> {
    let url = format!(
        "{}/api/server/{}/affordances?viewer={}",
        node_url.trim_end_matches('/'),
        server_cell_hex,
        viewer,
    );
    let client = reqwest::Client::new();
    let resp = client
        .get(&url)
        .send()
        .await
        .map_err(|e| SdkError::Wire(format!("server-affordance discovery request failed: {e}")))?;

    if !resp.status().is_success() {
        return Err(SdkError::Wire(format!(
            "server-affordance discovery returned status {}",
            resp.status()
        )));
    }

    let body: serde_json::Value = resp
        .json()
        .await
        .map_err(|e| SdkError::Wire(format!("failed to parse discovery response: {e}")))?;

    let affordances = body
        .get("affordances")
        .and_then(|a| a.as_array())
        .map(|arr| {
            arr.iter()
                .filter_map(|a| {
                    let name = a.get("name")?.as_str()?.to_string();
                    let required = a
                        .get("required")
                        .and_then(|r| r.as_str())
                        .unwrap_or("none")
                        .to_string();
                    Some(DiscoveredAffordance { name, required })
                })
                .collect()
        })
        .unwrap_or_default();

    let executor_federation_id = body
        .get("executor_federation_id")
        .and_then(|f| f.as_str())
        .ok_or_else(|| SdkError::Wire("discovery response missing executor_federation_id".into()))?
        .to_string();

    Ok(ServerDiscovery {
        cell: server_cell_hex.to_string(),
        affordances,
        executor_federation_id,
    })
}

/// The outcome of firing an affordance: whether the node accepted the turn, plus the
/// node's reported turn hash and any rejection reason.
#[derive(Clone, Debug)]
pub struct FireOutcome {
    /// Whether the node's `/turns/submit` ingress committed the turn.
    pub accepted: bool,
    /// The committed (or attempted) turn hash, if the node reported one.
    pub turn_hash: Option<String>,
    /// The node's rejection reason, if any.
    pub error: Option<String>,
}

/// **Fire** one affordance: build a signed [`Turn`] under `signer` (acting as its OWN cell
/// `agent`), carrying `effects`, named `method`, and POST it to the node's `/turns/submit`
/// ingress — a real verified turn on the node's live ledger.
///
/// The flow is the genuine remote-client path:
///   1. read the agent cell's current nonce off the node (`GET /api/cell/{agent}`) — the
///      executor rejects a stale nonce;
///   2. build a single-action turn (`signer.make_action` over `effects`, signed against
///      the executor's `federation_id` from discovery), with `previous_receipt_hash =
///      None` (no chain-head pin — the node accepts an unpinned turn) and a `fee` set to
///      the turn's estimated computron cost (the node's budget gate caps `used ≤ fee`,
///      and the cost is a pure function of the effects — the standard `ComputronCosts`,
///      the same the node's executor uses — so a client estimates it without a ledger);
///   3. POST the postcard-encoded `SignedTurn` to `/turns/submit` and read the verdict.
///
/// The node re-checks every effect against the executor's authority gate, so the fire only
/// commits effects the agent's caps authorize. `federation_id_hex` is
/// [`ServerDiscovery::executor_federation_id`].
pub async fn fire_affordance(
    node_url: &str,
    signer: &AgentCipherclerk,
    agent: CellId,
    method: &str,
    effects: Vec<Effect>,
    federation_id_hex: &str,
) -> Result<FireOutcome, SdkError> {
    let node_url = node_url.trim_end_matches('/');

    let federation_id = decode_32(federation_id_hex)
        .ok_or_else(|| SdkError::Wire("federation id is not 32 bytes of hex".into()))?;

    // (1) the agent cell's current nonce off the live node ledger.
    let nonce = fetch_cell_nonce(node_url, &agent).await?;

    // (2) build + sign the single-action fire turn.
    let action = signer.make_action(agent, method, effects, &federation_id);
    let mut turn: Turn = signer.make_turn_with_actions(vec![action]);
    turn.agent = agent;
    turn.nonce = nonce;
    turn.memo = Some(format!("deos_server_{method}"));
    turn.valid_until = Some(i64::MAX / 2);
    // No chain-head pin: the node's ingress accepts an unpinned turn (it only verifies a
    // `previous_receipt_hash` when one is supplied), so a remote client need not track the
    // node's receipt chain head.
    turn.previous_receipt_hash = None;
    // The fee is the budget ceiling the node's gate caps `used` against. The cost is a pure
    // function of the effects (standard `ComputronCosts`, the same the node uses), so a
    // client estimates it with a bare executor — no ledger needed.
    turn.fee = TurnExecutor::new(ComputronCosts::default()).estimate_cost(&turn);

    let signed = signer.sign_turn(&turn);
    let signed_bytes =
        postcard::to_stdvec(&signed).map_err(|e| SdkError::Wire(format!("serialize SignedTurn: {e}")))?;

    // (3) POST the postcard SignedTurn to the genuine remote ingress.
    let url = format!("{node_url}/turns/submit");
    let client = reqwest::Client::new();
    let resp = client
        .post(&url)
        .header("Content-Type", "application/octet-stream")
        .body(signed_bytes)
        .send()
        .await
        .map_err(|e| SdkError::Wire(format!("fire (turns/submit) request failed: {e}")))?;

    if !resp.status().is_success() {
        return Err(SdkError::Wire(format!(
            "turns/submit returned status {}",
            resp.status()
        )));
    }

    let body: serde_json::Value = resp
        .json()
        .await
        .map_err(|e| SdkError::Wire(format!("failed to parse submit response: {e}")))?;

    Ok(FireOutcome {
        accepted: body.get("accepted").and_then(|a| a.as_bool()).unwrap_or(false),
        turn_hash: body.get("turn_hash").and_then(|h| h.as_str()).map(String::from),
        error: body.get("error").and_then(|e| e.as_str()).map(String::from),
    })
}

/// Read one cell's current nonce off the node (`GET /api/cell/{id}`). The executor rejects
/// a turn whose nonce does not match the agent cell's, so a fire must use this fresh value.
async fn fetch_cell_nonce(node_url: &str, cell: &CellId) -> Result<u64, SdkError> {
    let url = format!(
        "{}/api/cell/{}",
        node_url.trim_end_matches('/'),
        dregg_types::hex_encode(cell.as_bytes()),
    );
    let client = reqwest::Client::new();
    let resp = client
        .get(&url)
        .send()
        .await
        .map_err(|e| SdkError::Wire(format!("cell-detail request failed: {e}")))?;

    if !resp.status().is_success() {
        return Err(SdkError::Wire(format!(
            "cell-detail returned status {}",
            resp.status()
        )));
    }

    let body: serde_json::Value = resp
        .json()
        .await
        .map_err(|e| SdkError::Wire(format!("failed to parse cell-detail response: {e}")))?;

    if body.get("found").and_then(|f| f.as_bool()) != Some(true) {
        return Err(SdkError::Wire(format!(
            "agent cell {} not found on the node",
            dregg_types::hex_encode(cell.as_bytes())
        )));
    }

    Ok(body.get("nonce").and_then(|n| n.as_u64()).unwrap_or(0))
}

/// Decode a 64-char hex string into a 32-byte array. `None` on malformed input.
fn decode_32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(s.get(i * 2..i * 2 + 2)?, 16).ok()?;
    }
    Some(out)
}
