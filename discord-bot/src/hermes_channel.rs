//! Drive-your-Hermes-from-your-channel — the per-user confined agent loop.
//!
//! A message in a user's semi-private channel ([`crate::channels`]) drives THAT
//! user's own Hermes instance. Every message becomes a cap-gated, metered,
//! RECEIPTED dregg turn through the PROVEN [`ToolGateway`](dregg_sdk::ToolGateway)
//! over the verified executor — or an in-band refusal the user sees. This is the
//! ADOS thesis (a turn = the exercise of an attenuable proof-carrying token over
//! owned state, leaving a verifiable receipt) realized per Discord user.
//!
//! # What is REAL vs. the named seam (honest)
//!
//! REAL — and proven offline by the tests in this module:
//! * the [`ToolGateway`](dregg_sdk::ToolGateway) path: `admit` + `invoke` run on
//!   the verified Lean executor and yield a genuine
//!   [`TurnReceipt`](dregg_turn::TurnReceipt) (the receipt hash is the proof the
//!   metered turn committed);
//! * the per-user binding: each user's runtime + root token are derived from
//!   THEIR own custodial seed (the same seed [`crate::cipherclerk::seed_for`]
//!   gives their cell), so a user's Hermes is bounded by their own identity and
//!   the grant ceilings deos pins — not an ambient one;
//! * the in-band refusal: an over-rate / out-of-mandate / past-deadline message
//!   is refused with NO turn and NO spend, naming the leg that bit.
//!
//! THE SEAM (the live-Hermes brain): here the *tool-call* is derived
//! DETERMINISTICALLY from the message text by [`classify`] — a small command
//! grammar (`read …`, `search …`, `fetch …`, `run …`, `write …`, else a `chat`).
//! In the live integration this classifier is replaced by the actual Hermes LLM
//! over the **Agent Client Protocol** (the canonical seam is `deos-hermes`'s
//! [`HermesGateway`] driving an `acp_client` against a real `hermes-acp`
//! subprocess). The *enforcement seam this module wires* — message → cap-gated
//! metered receipted turn → reply — is identical either way; only the producer of
//! the tool-call changes. This shim keeps zero new build surface (it reuses the
//! SDK's `ToolGateway` already in the bot's graph) while the heavyweight
//! `deos-hermes`/firmament ACP transport stays the named live target.

use std::collections::HashMap;
use std::sync::{Arc, RwLock};

use dregg_sdk::{
    AgentCipherclerk, AgentRuntime, GatewayRefusal, HeldToken, ToolCallError, ToolGateway,
    ToolGrant,
};

/// The ACP tool classes deos confines a Hermes session under (mirrors
/// `deos_hermes::ToolKind`). The classifier maps a message's leading verb to one
/// of these; each is an independently-metered cap-gated worker.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ToolKind {
    Read,
    Search,
    Fetch,
    Execute,
    Edit,
    Chat,
}

impl ToolKind {
    pub fn as_str(self) -> &'static str {
        match self {
            ToolKind::Read => "Read",
            ToolKind::Search => "Search",
            ToolKind::Fetch => "Fetch",
            ToolKind::Execute => "Execute",
            ToolKind::Edit => "Edit",
            ToolKind::Chat => "Chat",
        }
    }

    /// A stable, distinct in-band tool id per kind (the SCOPE's in-band face).
    fn tool_id(self) -> i64 {
        match self {
            ToolKind::Read => 10,
            ToolKind::Search => 20,
            ToolKind::Fetch => 30,
            ToolKind::Execute => 40,
            ToolKind::Edit => 50,
            ToolKind::Chat => 90,
        }
    }

    /// The executor method verb the worker's biscuit credential is scoped to.
    fn method(self) -> &'static str {
        match self {
            ToolKind::Read => "tool.read",
            ToolKind::Search => "tool.search",
            ToolKind::Fetch => "tool.fetch",
            ToolKind::Execute => "tool.execute",
            ToolKind::Edit => "tool.edit",
            ToolKind::Chat => "tool.chat",
        }
    }

    /// deos's default rate ceiling per kind — the dangerous classes are tight,
    /// the read-only / chat classes generous.
    fn default_rate(self) -> i64 {
        match self {
            ToolKind::Read => 200,
            ToolKind::Search => 100,
            ToolKind::Fetch => 50,
            ToolKind::Execute => 20,
            ToolKind::Edit => 30,
            ToolKind::Chat => 500,
        }
    }
}

/// A classified tool-call derived from a channel message: which class, the Hermes
/// tool name, and the remaining argument text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassifiedCall {
    pub kind: ToolKind,
    pub tool: String,
    pub arg: String,
}

/// Classify a channel message into a tool-call. THE SEAM: in the live
/// integration the Hermes LLM produces this over ACP; here a small command
/// grammar derives it deterministically so the enforcement loop is exercised
/// end-to-end without model credentials.
pub fn classify(message: &str) -> ClassifiedCall {
    let trimmed = message.trim();
    let (verb, rest) = match trimmed.split_once(char::is_whitespace) {
        Some((v, r)) => (v, r.trim()),
        None => (trimmed, ""),
    };
    let (kind, tool) = match verb.to_ascii_lowercase().as_str() {
        "read" | "cat" | "open" => (ToolKind::Read, "read_file"),
        "search" | "grep" | "find" => (ToolKind::Search, "search"),
        "fetch" | "get" | "browse" => (ToolKind::Fetch, "web_search"),
        "run" | "exec" | "shell" | "terminal" => (ToolKind::Execute, "terminal"),
        "write" | "edit" | "patch" => (ToolKind::Edit, "write_file"),
        _ => (ToolKind::Chat, "chat"),
    };
    ClassifiedCall {
        kind,
        tool: tool.to_string(),
        arg: rest.to_string(),
    }
}

/// The verdict the channel loop posts back to the user.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HermesVerdict {
    /// The classified call this verdict is for.
    pub call: ClassifiedCall,
    /// Whether the gateway admitted the call (a metered turn committed).
    pub allowed: bool,
    /// The committed turn hash (hex), present iff `allowed`.
    pub receipt: Option<String>,
    /// Calls remaining on this kind's mandate after the call.
    pub remaining: Option<i64>,
    /// The refusal reason naming the leg that bit, present iff `!allowed`.
    pub reason: Option<String>,
}

impl HermesVerdict {
    /// The user-facing one-line summary posted to the channel.
    pub fn summary(&self) -> String {
        if self.allowed {
            let r = self.receipt.as_deref().unwrap_or("");
            let short = &r[..r.len().min(16)];
            format!(
                "✅ `{}` ({}) — cap-gated turn committed · receipt `{}…` · {} calls left",
                self.call.tool,
                self.call.kind.as_str(),
                short,
                self.remaining.unwrap_or_default()
            )
        } else {
            format!(
                "⛔ `{}` ({}) refused in-band — {}",
                self.call.tool,
                self.call.kind.as_str(),
                self.reason.as_deref().unwrap_or("no mandate")
            )
        }
    }
}

/// One user's confined Hermes session: a runtime + root token derived from the
/// user's own seed, and a lazily-admitted cap-gated worker per [`ToolKind`].
///
/// Held across messages so rate budgets accumulate within the session window —
/// a user who burns their `Execute` mandate sees the next `run` refused in-band.
pub struct ChannelHermes {
    runtime: AgentRuntime,
    root: HeldToken,
    deadline: i64,
    grants: HashMap<ToolKind, ToolGrant>,
    gateways: HashMap<ToolKind, ToolGateway>,
}

impl ChannelHermes {
    /// Open a confined session for a user, bound to their own custodial `seed`
    /// (the same 32-byte seed [`crate::cipherclerk::seed_for`] derives — so this
    /// agent descends from the user's identity). `deadline` is the session-wide
    /// mandate expiry (a clock/height ceiling shared by every grant).
    pub fn for_user(seed: [u8; 32], deadline: i64) -> Self {
        let mut cclerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(seed));
        // The root token the user delegates each worker's mandate from, minted
        // under the user's own seed (their authority, not an ambient one).
        let root = cclerk.mint_token(&seed, "hermes-channel");
        let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "hermes-channel");

        let mut grants = HashMap::new();
        for kind in [
            ToolKind::Read,
            ToolKind::Search,
            ToolKind::Fetch,
            ToolKind::Execute,
            ToolKind::Edit,
            ToolKind::Chat,
        ] {
            grants.insert(
                kind,
                ToolGrant {
                    tool_id: kind.tool_id(),
                    rate_limit: kind.default_rate(),
                    deadline,
                    tool_method: kind.method().to_string(),
                },
            );
        }

        ChannelHermes {
            runtime,
            root,
            deadline,
            grants,
            gateways: HashMap::new(),
        }
    }

    /// Override a kind's grant (tighten a rate ceiling / deny a class). Used by
    /// the deny-by-default tests and available for per-user policy.
    pub fn with_grant(mut self, kind: ToolKind, rate_limit: i64) -> Self {
        let grant = ToolGrant {
            tool_id: kind.tool_id(),
            rate_limit,
            deadline: self.deadline,
            tool_method: kind.method().to_string(),
        };
        self.grants.insert(kind, grant);
        self
    }

    /// Lazily admit (or fetch) the cap-gated worker for a kind.
    fn gateway_for(&mut self, kind: ToolKind) -> Result<&mut ToolGateway, ToolCallError> {
        if !self.gateways.contains_key(&kind) {
            let grant = self.grants.get(&kind).cloned().expect("grant per kind");
            let gw =
                ToolGateway::admit(&self.runtime, &self.root, grant).map_err(ToolCallError::Sdk)?;
            self.gateways.insert(kind, gw);
        }
        Ok(self.gateways.get_mut(&kind).expect("just inserted"))
    }

    /// THE LOOP — drive a channel message as a cap-gated, metered, receipted turn
    /// (or an in-band refusal). `now` is the presentation clock (message arrival
    /// height/time). Returns the verdict to post back.
    pub fn drive(&mut self, message: &str, now: i64) -> HermesVerdict {
        let call = classify(message);
        let kind = call.kind;
        let tool_id = kind.tool_id();

        let gw = match self.gateway_for(kind) {
            Ok(gw) => gw,
            Err(e) => {
                return HermesVerdict {
                    call,
                    allowed: false,
                    receipt: None,
                    remaining: None,
                    reason: Some(format!("could not admit worker: {e}")),
                };
            }
        };

        // The metering alone IS the receipted proof the call was authorized; we
        // pass an empty work witness (the live brain's tool payload would ride
        // here — the named seam). The receipt witnesses the authorization.
        match gw.invoke(tool_id, now, vec![]) {
            Ok(receipt) => HermesVerdict {
                call,
                allowed: true,
                receipt: Some(hex32(&receipt.receipt.turn_hash)),
                remaining: Some(receipt.remaining),
                reason: None,
            },
            Err(ToolCallError::Refused(refusal)) => HermesVerdict {
                call,
                allowed: false,
                receipt: None,
                remaining: None,
                reason: Some(describe_refusal(&refusal)),
            },
            Err(ToolCallError::Sdk(e)) => HermesVerdict {
                call,
                allowed: false,
                receipt: None,
                remaining: None,
                reason: Some(format!("executor rejected the metered turn: {e}")),
            },
        }
    }

    /// Calls committed so far on a kind's mandate (0 if never invoked).
    pub fn calls_made(&self, kind: ToolKind) -> i64 {
        self.gateways.get(&kind).map_or(0, |gw| gw.calls_made())
    }
}

/// A human-readable refusal naming the mandate leg that bit (the text the user
/// sees in their channel).
fn describe_refusal(refusal: &GatewayRefusal) -> String {
    match refusal {
        GatewayRefusal::OutOfScope { presented, granted } => {
            format!("out of scope: tool {presented} not granted (mandate covers {granted})")
        }
        GatewayRefusal::PastDeadline { now, deadline } => {
            format!("past deadline: presented at {now}, mandate expired at {deadline}")
        }
        GatewayRefusal::OverRate {
            calls_made,
            rate_limit,
        } => format!("rate exhausted: {calls_made} of {rate_limit} calls used this mandate window"),
        GatewayRefusal::OverBudget {
            spent,
            price,
            budget,
        } => format!(
            "budget exhausted: {spent} spent + {price} price exceeds the {budget} allowance"
        ),
    }
}

/// Seconds since the Unix epoch — the presentation clock for a channel message.
fn now_secs() -> i64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

/// THE CHANNEL LOOP — route a Discord message in a managed channel to its
/// owner's confined Hermes, commit the cap-gated turn, record it, reply.
///
/// Called from the gateway message handler. Non-managed channels and bot
/// messages are ignored. Only the channel owner (or the admin co-driving) drives
/// the owner's session; the session is held in [`crate::BotState`] so rate
/// budgets accumulate across messages.
pub async fn on_message(
    ctx: &serenity::all::Context,
    msg: &serenity::all::Message,
    state: &crate::BotState,
) {
    if msg.author.bot {
        return;
    }
    let content = msg.content.trim();
    if content.is_empty() {
        return;
    }

    let channel_id = msg.channel_id.get().to_string();
    let chan = match state.db.get_user_channel(&channel_id).await {
        Ok(Some(c)) => c,
        _ => return, // not a DreggNet Cloud per-user channel
    };

    let author = msg.author.id.get();
    let owner: u64 = chan.discord_id.parse().unwrap_or(0);
    let is_admin = state.config.admin_discord_id == Some(author);
    if author != owner && !is_admin {
        // Semi-private posture: peers may read (if permitted) but only the owner
        // or the admin drives the owner's agent.
        return;
    }

    let now = now_secs();
    // Drive the owner's session synchronously; the std lock is never held across
    // an await (the verdict is produced, then the guard drops).
    let verdict = {
        let mut sessions = state
            .channel_hermes
            .lock()
            .unwrap_or_else(|p| p.into_inner());
        let hermes = sessions.entry(owner).or_insert_with(|| {
            let seed = crate::cipherclerk::seed_for(&state.config.bot_secret, owner);
            // A generous 30-day session window; the live bound is the per-kind rate.
            ChannelHermes::for_user(seed, now + 60 * 60 * 24 * 30)
        });
        hermes.drive(content, now)
    };

    // Append to the per-channel agent ledger (the admin portal monitors this).
    let _ = state
        .db
        .record_hermes_activity(
            &owner.to_string(),
            &channel_id,
            content,
            &verdict.call.tool,
            verdict.call.kind.as_str(),
            verdict.allowed,
            verdict.receipt.as_deref(),
            verdict.remaining,
            verdict.reason.as_deref(),
            now,
        )
        .await;

    let _ = msg.channel_id.say(&ctx.http, verdict.summary()).await;
}

/// Hex-encode a 32-byte receipt hash.
fn hex32(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed() -> [u8; 32] {
        [3u8; 32]
    }

    #[test]
    fn classify_maps_verbs_to_tool_kinds() {
        assert_eq!(classify("read README.md").kind, ToolKind::Read);
        assert_eq!(classify("search for foo").kind, ToolKind::Search);
        assert_eq!(classify("fetch https://x").kind, ToolKind::Fetch);
        assert_eq!(classify("run ls -la").kind, ToolKind::Execute);
        assert_eq!(classify("write notes.txt hi").kind, ToolKind::Edit);
        // Anything not a known verb is a chat (the generous default class).
        assert_eq!(classify("hello there agent").kind, ToolKind::Chat);
        assert_eq!(classify("run rm -rf /").tool, "terminal");
        assert_eq!(classify("read foo").arg, "foo");
    }

    #[test]
    fn a_message_becomes_a_real_cap_gated_receipted_turn() {
        // GENUINE ✓ — a `read` message, in-time, within the Read rate. The
        // metered turn COMMITS on the verified executor and the verdict carries a
        // real 64-hex turn hash + the remaining budget. This is the proven loop:
        // message → cap-gated hermes turn → reply.
        let mut hermes = ChannelHermes::for_user(seed(), 1_000_000);
        let verdict = hermes.drive("read README.md", 100);

        assert!(verdict.allowed, "an in-rate read commits: {verdict:?}");
        let receipt = verdict
            .receipt
            .clone()
            .expect("a committed turn has a receipt");
        assert_eq!(
            receipt.len(),
            64,
            "receipt is a hex-encoded 32-byte turn hash"
        );
        assert!(receipt.chars().all(|c| c.is_ascii_hexdigit()));
        assert_eq!(verdict.remaining, Some(199), "one Read-200 budget consumed");
        assert_eq!(hermes.calls_made(ToolKind::Read), 1);
        assert!(verdict.summary().contains("committed"));
    }

    #[test]
    fn over_rate_message_refused_in_band_no_turn() {
        // CHEAT ✗ — tighten Execute to rate 1; the second `run` exceeds it and is
        // refused IN-BAND naming the rate leg. No turn, no counter advance.
        let mut hermes =
            ChannelHermes::for_user(seed(), 1_000_000).with_grant(ToolKind::Execute, 1);

        let first = hermes.drive("run echo hi", 100);
        assert!(first.allowed, "first call commits: {first:?}");

        let second = hermes.drive("run echo again", 100);
        assert!(!second.allowed, "second exceeds the rate-1 mandate");
        assert!(
            second.reason.as_deref().unwrap().contains("rate exhausted"),
            "names the rate leg: {second:?}"
        );
        assert_eq!(
            hermes.calls_made(ToolKind::Execute),
            1,
            "the refusal did not advance the counter"
        );
        assert!(second.summary().contains("refused"));
    }

    #[test]
    fn denied_class_refuses_on_first_attempt() {
        // deos can deny a whole class: Execute rate 0 → every `run` fails closed
        // in-band on the first attempt.
        let mut hermes =
            ChannelHermes::for_user(seed(), 1_000_000).with_grant(ToolKind::Execute, 0);
        let verdict = hermes.drive("run anything", 100);
        assert!(!verdict.allowed);
        assert!(
            verdict
                .reason
                .as_deref()
                .unwrap()
                .contains("rate exhausted")
        );
        assert_eq!(hermes.calls_made(ToolKind::Execute), 0);
    }

    #[test]
    fn past_deadline_message_refused_in_band() {
        // A message presented after the session mandate deadline is refused
        // in-band even with rate head-room.
        let mut hermes = ChannelHermes::for_user(seed(), 1_000);
        let verdict = hermes.drive("read file", 2_000);
        assert!(!verdict.allowed);
        assert!(verdict.reason.as_deref().unwrap().contains("past deadline"));
    }

    #[test]
    fn kinds_are_independently_metered() {
        let mut hermes = ChannelHermes::for_user(seed(), 1_000_000);
        assert!(hermes.drive("read a", 10).allowed);
        assert!(hermes.drive("search b", 10).allowed);
        assert_eq!(hermes.calls_made(ToolKind::Read), 1);
        assert_eq!(hermes.calls_made(ToolKind::Search), 1);
        assert_eq!(
            hermes.calls_made(ToolKind::Execute),
            0,
            "untouched class stays 0"
        );
    }
}
