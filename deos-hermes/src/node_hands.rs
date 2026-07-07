//! THE DISTRIBUTED HANDS — a confined brain's `run_js` drives a REMOTE node's World.
//!
//! Pillar 4 of `GOAL-DISTRIBUTED-DEOS.md` (node-backed transport, the RESOLVED
//! decision). This module composes three already-built pieces into one path:
//!
//!   * [`RunJsTool::run_attached_on`](crate::run_js::RunJsTool::run_attached_on) —
//!     the agent's hands, bound to ANY `Box<dyn `[`WorldSink`]`>` under the agent's
//!     `held` (the cap tooth in [`deos_js::AttachedApplet::fire`], mounted under the
//!     attenuated cap, never root);
//!   * [`NodeWorldSink`](dregg_sdk_net::NodeWorldSink) (Pillar 0, in `dregg-sdk-net`)
//!     — a `WorldSink` whose `fire_effects` builds a signed [`Turn`](dregg_turn::Turn)
//!     and POSTs it to a node's `/turns/submit` over HTTP, returning the REAL receipt
//!     hash the node recorded. Fail-CLOSED: a node refusal or transport fault is an
//!     `Err`, never a silent success;
//!   * the provider-only [`EgressPolicy`](crate::egress::EgressPolicy) socket door —
//!     the ONE outbound `host:port` a jailed brain may reach ([`grant_provider`]).
//!
//! [`NodeJsHands`] welds them: it binds the agent's `run_js` to a `NodeWorldSink`
//! pointed at a node whose `host:port` IS the jail's sole granted egress door. A
//! `run_js` fire then becomes a real verified turn committed to the REMOTE node — a
//! cap-gated turn under the agent's `held`, landing on the node's ledger — while the
//! brain reaches the node ONLY through that one granted door (every other endpoint
//! stays EPERM'd inside the jail).
//!
//! The red-team invariant carries end-to-end and gains a THIRD gate:
//!   * EMPOWERED — the brain runs arbitrary `run_js`;
//!   * ACCOUNTABLE — the `run_js` tool-call is a metered, receipted
//!     [`HermesGateway`] turn; each fire that lands leaves a receipt — now on the
//!     REMOTE node's ledger;
//!   * BOUNDED — three teeth: (1) the cap tooth in `AttachedApplet::fire` (an
//!     over-reach commits nothing), (2) the NODE'S OWN executor re-checks every
//!     effect (an over-reaching effect is refused BY THE NODE — an `Err` out of
//!     `fire_effects`, never by the sink), and (3) the JAIL'S egress door — the
//!     `NodeWorldSink` can only be pointed at an endpoint the [`EgressPolicy`]
//!     admits ([`NodeJsHands::check_endpoint`]); an ungranted node is refused before
//!     a socket is ever opened, and the OS jail is the physical backstop
//!     (`tests/provider_egress.rs` proves the ungranted connect is EPERM'd in-PD).
//!
//! ## The cross-box seam (the b-bar), named
//!
//! When the brain runs in a jail on box A and commits to a node on box B, box B's
//! ledger is the source of truth for the turn. A cockpit repainting box A's view
//! from box B's ledger must CRAWL box B (`with_ledger` → the node's snapshot) — it
//! does NOT observe box A local state. `NodeWorldSink::with_ledger` fetches that
//! snapshot (Pillar 0 crawl fidelity: cells, not sovereign commitments), so a
//! repaint is a fresh crawl of the remote ledger, subject to the node's own
//! finality/gossip lag (the Pillar-2 handoff). This module wires the COMMIT leg; the
//! repaint-from-remote leg is the cockpit's crawl over the same client.

use deos_js::{JsRuntime, WorldSink};
use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, CellId};
use dregg_sdk::AgentCipherclerk;
use dregg_sdk_net::NodeWorldSink;

use crate::acp::ToolCallRequest;
use crate::bridge::HermesGateway;
use crate::egress::{EgressNetGrant, EgressPolicy};
use crate::run_js::{RunJsError, RunJsOutcome, RunJsTool};

/// The token-id label the agent's default cell is derived under — the SAME label
/// [`NodeWorldSink`] derives its committing cell from, so the cell the hands' turns
/// bind is exactly the cell the sink signs as.
const DEFAULT_TOKEN_LABEL: &[u8] = b"default";

/// Why the distributed hands could not be built or driven.
#[derive(Debug)]
pub enum NodeHandsError {
    /// THE EGRESS TOOTH — the requested node `host:port` is NOT a granted egress
    /// door, so the hands refuse to point a sink at it (a socket the jail would
    /// EPERM anyway). The confinement pole at the admits layer; the OS jail is the
    /// physical backstop.
    EndpointNotGranted { host: String, port: u16 },
    /// The single pre-built node sink was already consumed by a prior `run_call`
    /// (these hands hold one node identity + its runtime; rebuild the hands for
    /// another committing session).
    SinkConsumed,
    /// Building the [`NodeWorldSink`] failed (e.g. its blocking runtime could not be
    /// stood up).
    Sink(String),
    /// SpiderMonkey failed to boot, or the script failed to compile/evaluate.
    Engine(String),
}

impl std::fmt::Display for NodeHandsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NodeHandsError::EndpointNotGranted { host, port } => write!(
                f,
                "node endpoint {host}:{port} is not a granted egress door (the jail denies it)"
            ),
            NodeHandsError::SinkConsumed => {
                write!(f, "the node sink was already consumed by a prior run_call")
            }
            NodeHandsError::Sink(e) => write!(f, "build node sink: {e}"),
            NodeHandsError::Engine(e) => write!(f, "deos-js engine error: {e}"),
        }
    }
}
impl std::error::Error for NodeHandsError {}

/// The agent cell a [`NodeWorldSink`] built from `cipherclerk` commits AS — the
/// cipherclerk's DEFAULT cell (`derive_raw(public_key, blake3("default"))`). The
/// hands build their [`RunJsTool`] over this SAME identity so a committed turn binds
/// the agent's own held cell (never a cross-vessel reach).
pub fn agent_cell_of(cipherclerk: &AgentCipherclerk) -> CellId {
    let token_id = *blake3::hash(DEFAULT_TOKEN_LABEL).as_bytes();
    CellId::derive_raw(&cipherclerk.public_key().0, &token_id)
}

/// THE EGRESS TOOTH, standalone — whether `node` is an endpoint the jail's egress
/// policy admits a connect to. This is the confinement pole modeled at the
/// [`EgressPolicy::admits_connect`] layer (exactly as `tests/provider_egress.rs`
/// models the granted/sibling doors); the OS jail physically EPERMs an ungranted
/// connect in the PD as the enforcing backstop.
pub fn check_endpoint(egress: &EgressPolicy, node: &EgressNetGrant) -> Result<(), NodeHandsError> {
    if egress.admits_connect(&node.host, node.port) {
        Ok(())
    } else {
        Err(NodeHandsError::EndpointNotGranted {
            host: node.host.clone(),
            port: node.port,
        })
    }
}

/// THE DISTRIBUTED HANDS — a confined brain's `run_js` bound to a [`NodeWorldSink`]
/// over the jail's SOLE granted node door. Owns the agent's [`RunJsTool`] (its `held`
/// + affordance surface — the cap tooth), the accountability [`HermesGateway`], the
/// granted node endpoint, a single pre-built node sink (the node identity + its
/// blocking runtime), and a process-global [`JsRuntime`].
pub struct NodeJsHands<'gw> {
    tool: RunJsTool,
    agent: CellId,
    gateway: HermesGateway<'gw>,
    node: EgressNetGrant,
    sink: Option<Box<dyn WorldSink>>,
    rt: JsRuntime,
}

impl<'gw> NodeJsHands<'gw> {
    /// Build the distributed hands over the jail's egress policy + the node door.
    ///
    /// `egress` is the host's structured egress policy; `node` is the endpoint the
    /// hands commit to — it MUST be a granted socket door (else
    /// [`NodeHandsError::EndpointNotGranted`], BEFORE SpiderMonkey boots). The
    /// [`NodeWorldSink`] is built with `base_url = http://<node>` (exactly the
    /// granted door), committing AS `cipherclerk`'s default cell, signed over
    /// `federation_id` (the node's executor federation id — see
    /// [`NodeHttpClient::fetch_executor_federation_id`](dregg_sdk_net::NodeHttpClient::fetch_executor_federation_id)).
    /// The agent's [`RunJsTool`] is built over the SAME cell identity, `held`,
    /// `seed_fields`, and `affordances_spec`, so a fire commits a turn binding the
    /// agent's own held cell on the remote node.
    ///
    /// Boots the process-global SpiderMonkey engine (one-shot) — call once per
    /// process, or use [`NodeJsHands::with_runtime`].
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        egress: &EgressPolicy,
        node: EgressNetGrant,
        cipherclerk: AgentCipherclerk,
        federation_id: [u8; 32],
        held: AuthRequired,
        seed_fields: Vec<(usize, FieldElement)>,
        affordances_spec: Vec<(String, AuthRequired)>,
        gateway: HermesGateway<'gw>,
    ) -> Result<Self, NodeHandsError> {
        // THE EGRESS TOOTH FIRST — refuse an ungranted node before booting mozjs or
        // building any sink (nothing is opened for an endpoint the jail denies).
        check_endpoint(egress, &node)?;
        let rt = JsRuntime::new().map_err(NodeHandsError::Engine)?;
        Self::with_runtime(
            egress,
            node,
            cipherclerk,
            federation_id,
            held,
            seed_fields,
            affordances_spec,
            gateway,
            rt,
        )
    }

    /// As [`NodeJsHands::new`], but on a CALLER-OWNED [`JsRuntime`]. SpiderMonkey's
    /// engine init is process-global + one-shot, so a host (or a test running both
    /// poles) that has already booted a runtime threads it here instead of booting
    /// another (a second `JsRuntime::new()` errors `AlreadyInitialized`).
    #[allow(clippy::too_many_arguments)]
    pub fn with_runtime(
        egress: &EgressPolicy,
        node: EgressNetGrant,
        cipherclerk: AgentCipherclerk,
        federation_id: [u8; 32],
        held: AuthRequired,
        seed_fields: Vec<(usize, FieldElement)>,
        affordances_spec: Vec<(String, AuthRequired)>,
        gateway: HermesGateway<'gw>,
        rt: JsRuntime,
    ) -> Result<Self, NodeHandsError> {
        check_endpoint(egress, &node)?;

        // The agent identity: the cipherclerk's default cell — read the public key
        // BEFORE the cipherclerk is moved into the sink.
        let public_key = cipherclerk.public_key().0;
        let token_id = *blake3::hash(DEFAULT_TOKEN_LABEL).as_bytes();
        let tool = RunJsTool::new(held, public_key, token_id, seed_fields, affordances_spec);
        let agent = tool.agent_cell();

        // The sink points at EXACTLY the granted door (base_url = http://host:port).
        // No network happens here — the sink talks to the node only on a fire/crawl.
        let base_url = format!("http://{}", node.endpoint());
        let sink = NodeWorldSink::new(base_url, cipherclerk, federation_id)
            .map_err(|e| NodeHandsError::Sink(e.to_string()))?;

        Ok(NodeJsHands {
            tool,
            agent,
            gateway,
            node,
            sink: Some(Box::new(sink)),
            rt,
        })
    }

    /// The agent cell every committed turn binds (the cipherclerk's default cell) —
    /// the principal on the remote node's ledger. Seed THIS cell (open + funded) on
    /// the node for its own-cell affordance fires to commit.
    pub fn agent(&self) -> CellId {
        self.agent
    }

    /// The granted node endpoint these hands commit to (the sole egress door).
    pub fn node_endpoint(&self) -> &EgressNetGrant {
        &self.node
    }

    /// RUN ONE `run_js` CALL against the REMOTE node. Admits the `run_js` tool-call
    /// as a metered, receipted [`HermesGateway`] turn, then (iff admitted) evals the
    /// model's chosen script (`rawInput.script`) on a runtime ATTACHED to the
    /// [`NodeWorldSink`]: `deos.world` crawls the node's snapshot ledger, and a fire
    /// commits a real verified turn to the node (through
    /// [`NodeWorldSink::fire_effects`], POSTing a signed turn to `/turns/submit`),
    /// its receipt landing on the node's ledger. An over-reach is refused in-band by
    /// the cap tooth (no turn leaves) and, past it, by the node's own executor (an
    /// `Err` out of `fire_effects` — fail-closed, never a silent success).
    ///
    /// Consumes the single pre-built node sink; a second call returns
    /// [`NodeHandsError::SinkConsumed`] (rebuild the hands for another session).
    pub fn run_call(
        &mut self,
        call: &ToolCallRequest,
        now: i64,
    ) -> Result<RunJsOutcome, NodeHandsError> {
        let sink = self.sink.take().ok_or(NodeHandsError::SinkConsumed)?;
        let script = crate::live_js::script_of_call(call);
        self.run_script(sink, call, now, &script)
    }

    /// As [`NodeJsHands::run_call`], but with an explicit `script` (the direct path a
    /// test drives, bypassing `rawInput` extraction).
    pub fn run_script_call(
        &mut self,
        call: &ToolCallRequest,
        now: i64,
        script: &str,
    ) -> Result<RunJsOutcome, NodeHandsError> {
        let sink = self.sink.take().ok_or(NodeHandsError::SinkConsumed)?;
        self.run_script(sink, call, now, script)
    }

    fn run_script(
        &mut self,
        sink: Box<dyn WorldSink>,
        call: &ToolCallRequest,
        now: i64,
        script: &str,
    ) -> Result<RunJsOutcome, NodeHandsError> {
        match self.tool.run_attached_on(
            &mut self.rt,
            sink,
            self.agent,
            &mut self.gateway,
            call,
            now,
            script,
        ) {
            Ok(outcome) => Ok(outcome),
            Err(RunJsError::Engine(e)) => Err(NodeHandsError::Engine(e)),
        }
    }
}
