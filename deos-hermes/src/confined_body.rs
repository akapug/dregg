//! THE WELD — Hermes runs as a grain-jail CONFINED BODY, not just tool-call-gated.
//!
//! Everywhere else in this crate the confinement is deos-hermes's OWN wiring: the
//! [`crate::bridge`] gate confines each tool-call (a receipted turn), and
//! [`crate::host::DreggHost`] runs the agent brain inside a firmament PD driven by
//! the ACP client. This module WELDS Hermes's confined body onto the CANONICAL
//! confined-body primitive — grain-jail's [`BodyChannel`](grain_jail::BodyChannel)
//! (`grain_jail::Proposal` / `grain_jail::Verdict` line protocol) — the SAME seam a
//! rented grain's OS-jailed body rides in `agent_platform::AgentPlatform::drive_serving`.
//!
//! ## The composition point (Option A: the BodyChannel carries the ACP stream)
//!
//! The confined Hermes body is a brain-driven ACP peer ([`crate::HermesAgentPeer`]
//! over the on-box [`crate::LocalBrain`], `execve`-free so it fits the jail). Its
//! ACP `tool_call` / `session/request_permission` stream is carried over a
//! [`AcpBodyChannel`], which IS a `grain_jail::BodyChannel`:
//!
//!   * [`BodyChannel::recv`](grain_jail::BodyChannel::recv) drives the confined
//!     body's ACP session forward and surfaces each `session/request_permission` as
//!     a `grain_jail::Proposal` (`BodyMsg::Propose`); the terminal `PromptResponse`
//!     becomes `BodyMsg::Done`; a closed body is a clean EOF (`Ok(None)`).
//!   * [`BodyChannel::send`](grain_jail::BodyChannel::send) feeds the host's
//!     `grain_jail::Verdict` back to the confined body AS the ACP permission
//!     outcome (`allow_once` + `deosReceipt`, or `deny` + `deosRefusal`), so the
//!     body sees the verdict and its brain decides the next step under confinement.
//!
//! The HOST side ([`drive_confined_hermes`]) is the grain-jail drive rhythm
//! (`recv` a proposal → gate it → `send` the verdict), but the GATE is the proven
//! [`HermesGateway`] / `dregg_sdk::ToolGateway` — the interception STAYS: every
//! proposal is still a cap-gated, metered, RECEIPTED dregg turn (or an in-band
//! refusal). grain-jail contributes the confined-body TRANSPORT; the ToolGateway
//! stays the enforcement, unchanged.
//!
//! We picked Option A (and not "run the ACP client behind `ConfinedBrain`")
//! deliberately: `grain_jail::ConfinedBrain` routes proposals to the grain drive
//! loop's OWN caps (`agent_platform`), which would REPLACE the ToolGateway with a
//! different gate. Carrying the ACP stream over the `BodyChannel` and gating with
//! the ToolGateway keeps the proven interception that defines this crate.
//!
//! ## The one egress door
//!
//! A confined Hermes body reaches NOTHING but its granted door. [`model_egress_policy`]
//! builds the [`EgressPolicy`](crate::egress::EgressPolicy) that grants EXACTLY the
//! agent's model/tool endpoint and denies every other host, port, and path; on unix
//! [`drive_confined_hermes_in_jail`] threads it into a real firmament PD, so the
//! jailed body's ONLY outbound reach is that single provider socket while its ACP
//! tool-call stream rides the grain-jail `BodyChannel`.
//!
//! ## Real vs. the named seam
//!
//! REAL: the `BodyChannel` weld, the ToolGateway interception (receipted turns on
//! the verified executor), the on-box brain's closed decide→gate→observe loop, and
//! (unix) the OS jail with one egress door. The NAMED SEAM is a *live* model on the
//! granted socket — the on-box [`crate::LocalBrain`] stands in for the model (the
//! live provider is broken in-env), exactly as it does for [`crate::host::DreggHost`]
//! and grain-jail's own end-to-end test. The confinement + gating is the point.

use std::collections::BTreeMap;
use std::io;

use serde_json::{Value, json};

use grain_jail::BodyChannel;
use grain_jail::protocol::{BodyMsg, DoneNote, Proposal, Verdict};

use crate::acp::{PermissionOutcome, ToolCallRequest};
use crate::acp_client::{
    ACP_PROTOCOL_VERSION, AcpError, AcpPeer, RpcMessage, parse_permission_tool_call,
    permission_outcome_to_acp,
};
use crate::agent_peer::HermesAgentPeer;
use crate::brain::LlmBrain;
use crate::bridge::HermesGateway;

/// The reserved `Proposal.args` keys that carry the ACP correlation across the
/// confined-body line protocol (grain-jail's `Proposal` has no dedicated field for
/// them). They are stripped back out when the host reconstructs the tool-call, so
/// they never leak into the tool's witnessed arguments.
const ACP_TOOL_CALL_ID: &str = "__acp_tool_call_id";
const ACP_SESSION_ID: &str = "__acp_session_id";

/// Encode a Hermes ACP [`ToolCallRequest`] as a grain-jail [`Proposal`] — the
/// confined body's proposal on the `BodyChannel`. The tool name is the proposal's
/// `tool`; the ACP correlation (tool-call id, session id) and the flat `rawInput`
/// fields ride in `args`.
pub fn proposal_of_acp_call(call: &ToolCallRequest) -> Proposal {
    let mut args: BTreeMap<String, String> = BTreeMap::new();
    args.insert(ACP_TOOL_CALL_ID.into(), call.tool_call_id.clone());
    args.insert(ACP_SESSION_ID.into(), call.session_id.clone());
    if let Value::Object(map) = &call.arguments {
        for (k, v) in map {
            let s = match v {
                Value::String(s) => s.clone(),
                other => other.to_string(),
            };
            args.insert(k.clone(), s);
        }
    }
    Proposal {
        tool: call.name.clone(),
        args: Some(args),
        amount_cents: None,
        path: None,
        value: None,
    }
}

/// Decode a grain-jail [`Proposal`] back into the Hermes ACP [`ToolCallRequest`]
/// the [`HermesGateway`] gates. The reserved correlation keys are lifted out; the
/// remaining `args` become the tool's `rawInput` (the witnessed arguments).
pub fn acp_call_of_proposal(p: &Proposal) -> ToolCallRequest {
    let args = p.args.clone().unwrap_or_default();
    let tool_call_id = args
        .get(ACP_TOOL_CALL_ID)
        .cloned()
        .unwrap_or_else(|| "tc-0".into());
    let session_id = args
        .get(ACP_SESSION_ID)
        .cloned()
        .unwrap_or_else(|| "sess-0".into());
    let mut obj = serde_json::Map::new();
    for (k, v) in &args {
        if k == ACP_TOOL_CALL_ID || k == ACP_SESSION_ID {
            continue;
        }
        obj.insert(k.clone(), Value::String(v.clone()));
    }
    ToolCallRequest::new(session_id, tool_call_id, p.tool.clone(), Value::Object(obj))
}

/// Fold a [`HermesGateway`] verdict into the grain-jail [`Verdict`] the confined
/// body reads: an admitted call carries the receipt id (in `summary`); a refused
/// call carries the in-band reason (in `refusal`).
fn verdict_of_outcome(outcome: &PermissionOutcome) -> Verdict {
    match outcome {
        PermissionOutcome::Allow { receipt, .. } => Verdict {
            admitted: true,
            refusal: None,
            tool_ok: Some(true),
            summary: Some(receipt.clone()),
        },
        PermissionOutcome::Reject { reason, .. } => Verdict {
            admitted: false,
            refusal: Some(reason.clone()),
            tool_ok: None,
            summary: None,
        },
    }
}

/// Reconstruct the ACP [`PermissionOutcome`] the confined body sees from the
/// host's grain-jail [`Verdict`] + the pending tool-call id. `remaining`/`paid` are
/// cosmetic for the body (the brain reacts to allow/deny + the receipt/refusal
/// detail); the authoritative accounting lives in the gateway, host-side.
fn outcome_of_verdict(verdict: &Verdict, tool_call_id: &str) -> PermissionOutcome {
    if verdict.admitted {
        PermissionOutcome::Allow {
            tool_call_id: tool_call_id.to_string(),
            receipt: verdict
                .summary
                .clone()
                .unwrap_or_else(|| "(receipt)".into()),
            remaining: 0,
            paid: 0,
            whisper: None,
        }
    } else {
        PermissionOutcome::Reject {
            tool_call_id: tool_call_id.to_string(),
            reason: verdict
                .refusal
                .clone()
                .unwrap_or_else(|| "(refused)".into()),
        }
    }
}

fn io_err(e: AcpError) -> io::Error {
    io::Error::other(e.to_string())
}

/// Where the [`AcpBodyChannel`] is in driving the confined body's ACP session.
#[derive(PartialEq, Eq)]
enum Phase {
    /// The `initialize` → `session/new` → `session/prompt` handshake is owed.
    Fresh,
    /// In the tool-call drive loop (proposals ⇄ verdicts).
    Draining,
    /// The prompt turn completed (or the body closed); no more proposals.
    Finished,
}

/// A `grain_jail::BodyChannel` OVER a confined Hermes body's ACP stream.
///
/// It plays the ACP CLIENT half against the confined body (`P` is the body's ACP
/// peer — an in-process [`HermesAgentPeer`] for the portable weld, or a
/// `crate::confined::PdAcpTransport` to a firmament-jailed body). Each
/// `session/request_permission` the body raises is surfaced as a
/// [`BodyMsg::Propose`]; each host [`Verdict`] is fed back as the ACP permission
/// outcome. The confined body reaches the host ONLY through this channel.
pub struct AcpBodyChannel<P: AcpPeer> {
    peer: P,
    phase: Phase,
    next_id: i64,
    cwd: String,
    prompt: String,
    /// The `session/prompt` request id — its response is the turn's terminal
    /// `Done` signal.
    prompt_id: Option<Value>,
    /// The id of the `session/request_permission` currently surfaced as a
    /// proposal, awaiting the host's verdict via [`BodyChannel::send`].
    pending_perm_id: Option<Value>,
    /// The tool-call id of that pending proposal (echoed on the outcome).
    pending_tool_call_id: Option<String>,
    /// The agent's streamed text (accumulated for inspection).
    agent_text: String,
    /// Every tool-call the confined body reached for this turn.
    tool_calls: Vec<ToolCallRequest>,
    /// The final `stopReason`, once the turn completes.
    stop_reason: Option<String>,
}

impl<P: AcpPeer> AcpBodyChannel<P> {
    /// Open a channel over a confined body's ACP `peer`, driving a prompt in `cwd`.
    pub fn new(peer: P, cwd: &str, prompt: &str) -> AcpBodyChannel<P> {
        AcpBodyChannel {
            peer,
            phase: Phase::Fresh,
            next_id: 1,
            cwd: cwd.to_string(),
            prompt: prompt.to_string(),
            prompt_id: None,
            pending_perm_id: None,
            pending_tool_call_id: None,
            agent_text: String::new(),
            tool_calls: Vec::new(),
            stop_reason: None,
        }
    }

    /// The confined body's streamed final text (post-drive) — the brain's own
    /// account of its turn under confinement.
    pub fn agent_text(&self) -> &str {
        &self.agent_text
    }

    /// Every tool-call the confined body reached for this turn (for inspection).
    pub fn tool_calls_seen(&self) -> &[ToolCallRequest] {
        &self.tool_calls
    }

    /// Consume the channel, returning the underlying ACP peer (e.g. to inspect a
    /// [`HermesAgentPeer`]'s brain, or to close a jail transport).
    pub fn into_peer(self) -> P {
        self.peer
    }

    fn alloc_id(&mut self) -> i64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Send a client→body request and block for its matching response, absorbing
    /// any notifications along the way. Used for `initialize` / `session/new`.
    fn request_response(&mut self, method: &str, params: Value) -> io::Result<Value> {
        let id = self.alloc_id();
        self.peer
            .send(&RpcMessage::request(id, method, params))
            .map_err(io_err)?;
        loop {
            let msg = match self.peer.recv() {
                Ok(m) => m,
                Err(AcpError::Closed) => return Err(io::Error::other("body closed mid-handshake")),
                Err(e) => return Err(io_err(e)),
            };
            if (msg.result.is_some() || msg.error.is_some()) && msg.id == Some(json!(id)) {
                if let Some(err) = msg.error {
                    return Err(io::Error::other(format!("body handshake error: {err}")));
                }
                return Ok(msg.result.unwrap_or(Value::Null));
            }
            if msg.is_request() {
                // A body→client request during the handshake — deny so nothing wedges.
                let rid = msg.id.clone().unwrap_or(Value::Null);
                self.peer
                    .send(&RpcMessage::response(
                        rid,
                        json!({ "error": "unsupported during handshake" }),
                    ))
                    .map_err(io_err)?;
            } else {
                self.absorb_notification(&msg);
            }
        }
    }

    /// Run `initialize` → `session/new` → `session/prompt` (the prompt is sent but
    /// NOT awaited — its response is the turn's terminal `Done`, surfaced by the
    /// drain loop).
    fn handshake(&mut self) -> io::Result<()> {
        self.request_response(
            "initialize",
            json!({
                "protocolVersion": ACP_PROTOCOL_VERSION,
                "clientCapabilities": { "fs": { "readTextFile": false, "writeTextFile": false } },
                "clientInfo": { "name": "deos-hermes-confined-body", "version": "0.1.0" }
            }),
        )?;
        let new_session =
            self.request_response("session/new", json!({ "cwd": self.cwd, "mcpServers": [] }))?;
        let session_id = new_session
            .get("sessionId")
            .or_else(|| new_session.get("session_id"))
            .and_then(|v| v.as_str())
            .unwrap_or("sess-0")
            .to_string();
        let id = self.alloc_id();
        self.prompt_id = Some(json!(id));
        self.peer
            .send(&RpcMessage::request(
                id,
                "session/prompt",
                json!({
                    "sessionId": session_id,
                    "prompt": [ { "type": "text", "text": self.prompt } ]
                }),
            ))
            .map_err(io_err)?;
        Ok(())
    }

    /// Accumulate agent text / tool-call events from a `session/update`.
    fn absorb_notification(&mut self, msg: &RpcMessage) {
        if msg.method.as_deref() != Some("session/update") {
            return;
        }
        let Some(params) = &msg.params else { return };
        let update = params.get("update").unwrap_or(params);
        let kind = update
            .get("sessionUpdate")
            .or_else(|| update.get("session_update"))
            .and_then(|v| v.as_str())
            .unwrap_or("");
        // Only agent text is accumulated here; the authoritative tool-call record
        // is taken from the `session/request_permission` path in `recv`.
        if kind == "agent_message_chunk"
            && let Some(text) = update
                .get("content")
                .and_then(|c| c.get("text"))
                .and_then(|t| t.as_str())
        {
            self.agent_text.push_str(text);
        }
    }
}

impl<P: AcpPeer> BodyChannel for AcpBodyChannel<P> {
    fn recv(&mut self) -> io::Result<Option<BodyMsg>> {
        if self.phase == Phase::Finished {
            return Ok(None);
        }
        if self.phase == Phase::Fresh {
            self.handshake()?;
            self.phase = Phase::Draining;
        }
        loop {
            let msg = match self.peer.recv() {
                Ok(m) => m,
                Err(AcpError::Closed) => {
                    self.phase = Phase::Finished;
                    return Ok(None);
                }
                Err(e) => return Err(io_err(e)),
            };
            // The terminal `session/prompt` response — the turn is complete.
            if (msg.result.is_some() || msg.error.is_some()) && msg.id == self.prompt_id {
                self.stop_reason = msg
                    .result
                    .as_ref()
                    .and_then(|r| r.get("stopReason").or_else(|| r.get("stop_reason")))
                    .and_then(|v| v.as_str())
                    .map(|s| s.to_string());
                self.phase = Phase::Finished;
                return Ok(Some(BodyMsg::Done(DoneNote {
                    summary: self.stop_reason.clone(),
                })));
            }
            if msg.is_request() {
                let method = msg.method.as_deref().unwrap_or("");
                if method == "session/request_permission" {
                    let params = msg.params.clone().unwrap_or(Value::Null);
                    let call = parse_permission_tool_call(&params);
                    self.pending_perm_id = msg.id.clone();
                    self.pending_tool_call_id = Some(call.tool_call_id.clone());
                    self.tool_calls.push(call.clone());
                    return Ok(Some(BodyMsg::Propose(proposal_of_acp_call(&call))));
                }
                // Any other body→client request: deny so the drive never wedges.
                let rid = msg.id.clone().unwrap_or(Value::Null);
                self.peer
                    .send(&RpcMessage::response(
                        rid,
                        json!({ "error": format!("unsupported client method: {method}") }),
                    ))
                    .map_err(io_err)?;
                continue;
            }
            // A notification — absorb it and read on.
            self.absorb_notification(&msg);
        }
    }

    fn send(&mut self, verdict: &Verdict) -> io::Result<()> {
        let perm_id = self
            .pending_perm_id
            .take()
            .ok_or_else(|| io::Error::other("no pending permission request to answer"))?;
        let tool_call_id = self.pending_tool_call_id.take().unwrap_or_default();
        let outcome = outcome_of_verdict(verdict, &tool_call_id);
        self.peer
            .send(&RpcMessage::response(
                perm_id,
                permission_outcome_to_acp(&outcome),
            ))
            .map_err(io_err)
    }
}

/// A convenience channel over an IN-PROCESS confined Hermes body: a brain-driven
/// [`HermesAgentPeer`] (the on-box brain fits the exec-denied jail) carried as a
/// grain-jail `BodyChannel`. The body reaches the host only through the channel —
/// the portable confinement seam grain-jail's own tests use.
pub fn confined_hermes_channel<B: LlmBrain>(
    session_id: &str,
    brain: B,
    cwd: &str,
    prompt: &str,
) -> AcpBodyChannel<HermesAgentPeer<B>> {
    AcpBodyChannel::new(HermesAgentPeer::new(session_id, brain), cwd, prompt)
}

/// The tally of driving a confined Hermes body through the ToolGateway over the
/// grain-jail `BodyChannel`: how many proposals the gate admitted (each a receipted
/// turn) vs refused in-band.
#[derive(Clone, Debug, Default)]
pub struct ConfinedHermesReport {
    /// Every proposal the confined body raised over the channel.
    pub proposals: usize,
    /// Proposals ADMITTED — each a cap-gated, metered, RECEIPTED dregg turn.
    pub admitted: usize,
    /// Proposals REFUSED in-band (no turn, no spend) — the confinement biting.
    pub refused: usize,
    /// The hex receipt id of every admitted proposal (a committed turn hash).
    pub receipts: Vec<String>,
    /// The in-band refusal reason of every refused proposal (the leg that bit).
    pub refusals: Vec<String>,
}

/// DRIVE a confined Hermes body over its grain-jail [`BodyChannel`], gating every
/// proposal through the proven [`HermesGateway`].
///
/// This is the grain-jail drive rhythm — `recv` a proposal, decide it, `send` the
/// verdict back to the confined body — with the ToolGateway as the gate: each
/// proposal becomes a cap-gated, metered, RECEIPTED dregg turn on the verified
/// executor (or an in-band refusal the body's brain sees and adapts to). `Done` or
/// a closed body ends the drive. The confinement (the body reaches the host ONLY
/// through the channel) and the interception (every proposal is a gated turn) hold
/// together — Hermes is a confined BODY whose every proposal is a gated turn.
pub fn drive_confined_hermes<C: BodyChannel>(
    channel: &mut C,
    gateway: &mut HermesGateway<'_>,
    start_clock: i64,
) -> io::Result<ConfinedHermesReport> {
    let mut report = ConfinedHermesReport::default();
    let mut clock = start_clock;
    loop {
        match channel.recv()? {
            Some(BodyMsg::Propose(p)) => {
                report.proposals += 1;
                clock += 1;
                let call = acp_call_of_proposal(&p);
                // THE PROVEN INTERCEPTION — the confined body's proposal is a
                // cap-gated, metered, receipted turn (or an in-band refusal).
                let outcome = gateway.admit_call(&call, clock);
                match &outcome {
                    PermissionOutcome::Allow { receipt, .. } => {
                        report.admitted += 1;
                        report.receipts.push(receipt.clone());
                    }
                    PermissionOutcome::Reject { reason, .. } => {
                        report.refused += 1;
                        report.refusals.push(reason.clone());
                    }
                }
                // The verdict rides back to the confined body over the channel.
                channel.send(&verdict_of_outcome(&outcome))?;
            }
            Some(BodyMsg::Done(_)) | None => break,
        }
    }
    Ok(report)
}

/// THE ONE EGRESS DOOR — the [`EgressPolicy`](crate::egress::EgressPolicy) that
/// grants a confined Hermes body EXACTLY its model/tool endpoint (derived from the
/// provider base URL) and denies every other host, port, and path.
///
/// Sealed but for that single provider socket: threaded into a firmament PD's
/// sandbox profile (via [`drive_confined_hermes_in_jail`]), it is the jailed body's
/// only outbound reach — the door a *live* brain's model call rides, and nothing
/// else. Returns a sealed policy (no door) if `model_base_url` has no host.
#[cfg(unix)]
pub fn model_egress_policy(model_base_url: &str) -> crate::egress::EgressPolicy {
    let mut policy = crate::egress::EgressPolicy::sealed();
    policy.grant_provider_url(model_base_url);
    policy
}

/// DRIVE a REAL firmament-jailed Hermes body over the grain-jail `BodyChannel`,
/// with exactly one egress door.
///
/// The full weld on unix: the confined Hermes body (a brain-driven
/// [`HermesAgentPeer`], `execve`-free) runs INSIDE an OS-sandboxed firmament PD
/// whose ONLY outbound door is `egress`'s single granted provider socket (all other
/// files/hosts/exec denied). Its ACP tool-call stream rides the Endpoint as the
/// [`AcpBodyChannel`]'s grain-jail proposals; [`drive_confined_hermes`] gates each
/// through `gateway` (the ToolGateway, OUTSIDE the jail, on the verified executor).
///
/// Returns the gate tally AND the jail's confinement verdict (a
/// [`crate::confined::probe`] bitmask + the socket-door teeth): [`probe::ALL`] means
/// the four base jail teeth held, and — when `granted_net`/`ungranted_net` are given
/// — the granted endpoint was reachable while an out-of-door endpoint stayed denied.
#[cfg(unix)]
#[allow(clippy::too_many_arguments)]
pub fn drive_confined_hermes_in_jail<B: LlmBrain + Send + 'static>(
    kernel: &dregg_firmament::process_kernel::ProcessKernel,
    egress: &crate::egress::EgressPolicy,
    gateway: &mut HermesGateway<'_>,
    session_id: &str,
    goal: &str,
    brain: B,
    granted_net: Option<(&str, u16)>,
    ungranted_net: Option<(&str, u16)>,
) -> io::Result<(ConfinedHermesReport, i32)> {
    use crate::confined::{
        can_connect_tcp, launch_confined_with_egress, probe, run_sandbox_probes,
        serve_acp_peer_over_endpoint,
    };
    use std::io::{Read, Write};

    let session_id = session_id.to_string();
    let granted_net = granted_net.map(|(h, p)| (h.to_string(), p));
    let ungranted_net = ungranted_net.map(|(h, p)| (h.to_string(), p));

    // Launch the confined body: it runs the jail probes, emits its confinement
    // verdict as one line, then serves its brain-driven ACP peer over the Endpoint.
    let agent = launch_confined_with_egress(kernel, egress, move |sock| {
        let mut verdict = run_sandbox_probes();
        // The single granted provider socket must be reachable; an out-of-door one
        // must stay EPERM'd — the door is to a SPECIFIC endpoint, not "the network".
        if let Some((h, p)) = &granted_net
            && can_connect_tcp(h, *p)
        {
            verdict |= probe::EGRESS_NET_GRANTED_OPEN;
        }
        if let Some((h, p)) = &ungranted_net
            && !can_connect_tcp(h, *p)
        {
            verdict |= probe::EGRESS_NET_SIBLING_DENIED;
        }
        let reported = verdict | probe::IPC_WORKS;
        let line = format!("{{\"jailVerdict\":{reported}}}\n");
        let _ = sock.write_all(line.as_bytes()).and_then(|_| sock.flush());

        let mut peer = HermesAgentPeer::new(&session_id, brain);
        let served = serve_acp_peer_over_endpoint(sock, &mut peer, |p| p.turn_complete()).is_ok();
        if served {
            verdict |= probe::IPC_WORKS;
        }
        verdict & (probe::ALL | probe::EGRESS_NET_GRANTED_OPEN | probe::EGRESS_NET_SIBLING_DENIED)
    })?;

    // Read the one confinement-verdict line the body emits before it serves ACP
    // (byte by byte, so the ACP frames that follow stay on the socket).
    let endpoint_verdict = {
        let mut reader = agent.pd.kernel_sock.try_clone()?;
        let mut line: Vec<u8> = Vec::with_capacity(64);
        let mut byte = [0u8; 1];
        loop {
            match reader.read(&mut byte) {
                Ok(0) => break,
                Ok(_) if byte[0] == b'\n' => break,
                Ok(_) => line.push(byte[0]),
                Err(_) => break,
            }
        }
        serde_json::from_slice::<Value>(&line)
            .ok()
            .and_then(|v| v.get("jailVerdict").and_then(|x| x.as_i64()))
            .map(|n| n as i32)
            .unwrap_or(0)
    };

    // Drive the confined body over the grain-jail BodyChannel — gate each proposal
    // through the ToolGateway (outside the jail, on the verified executor).
    let report = {
        let transport = agent
            .transport()
            .map_err(|e| io::Error::other(e.to_string()))?;
        let mut channel = AcpBodyChannel::new(transport, "/sandboxed/cwd", goal);
        drive_confined_hermes(&mut channel, gateway, 100)?
    };

    let exit_verdict = agent.join_verdict()?;
    Ok((report, endpoint_verdict | (exit_verdict & probe::ALL)))
}
