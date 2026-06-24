//! The deos-side mandate registry — what each Hermes tool is GRANTED.
//!
//! The [`ToolGateway`](dregg_sdk::ToolGateway) is policy-free: the GRANTOR pins
//! a [`ToolGrant`](dregg_sdk::ToolGrant) (SCOPE ∧ DEADLINE ∧ RATE) at delegation
//! time, and `ToolGateway::invoke` admits a call IFF the proven `delegAdmit`
//! predicate holds. The grantor here is DEOS: for Hermes to assist deos
//! development *confined*, deos decides — per tool — the scope, the rate
//! ceiling, and the deadline. This registry is that decision.
//!
//! ## Per-TOOL grants over per-KIND defaults
//!
//! The seam's first slice keyed confinement off the ACP [`ToolKind`]. That is
//! the legible floor (the dangerous classes get tight rate ceilings; the
//! read-only classes get generous ones; an unknown tool falls into `Other` —
//! fail-closed by classification). But a kind is coarse: `web_search` and
//! `web_extract` are both `Fetch`, yet deos may want to ration the
//! world-reading `web_extract` harder than a `web_search`; `terminal` and
//! `delegate_task` are both `Execute` yet deserve different ceilings.
//!
//! So the registry is now a TWO-LEVEL lookup, tightest-wins:
//!
//! 1. a per-TOOL [`ToolGrant`] keyed by the exact Hermes tool name (the
//!    tight scope deos pins for a specific tool), if present;
//! 2. else the per-KIND default for the tool's [`ToolKind`] (the class floor).
//!
//! Each grant fixes a distinct `tool_id` (the SCOPE's in-band face) and a
//! `tool_method` (the SCOPE's executor face — the verb the worker's biscuit
//! credential covers). A worker admitted under a tool's grant therefore
//! refuses, in-band, any call presenting a different tool id — so a per-tool
//! grant is its OWN cap-gated, independently-metered worker, not a sub-budget
//! of the kind.

use std::collections::HashMap;

use dregg_sdk::ToolGrant;

use crate::acp::ToolKind;

/// The confinement key the gateway admits a worker under. Either a whole ACP
/// kind (the class floor) or a specific Hermes tool (the tight scope). Each key
/// is its OWN cap-gated worker with its OWN metered `calls_made` counter.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MandateKey {
    /// A per-KIND mandate (the class floor — every tool of this kind that lacks
    /// a per-tool grant routes here).
    Kind(ToolKind),
    /// A per-TOOL mandate (deos pinned a tighter grant for this exact tool name).
    Tool(String),
}

impl MandateKey {
    /// A short human label for an inspector / dock surface.
    pub fn label(&self) -> String {
        match self {
            MandateKey::Kind(k) => format!("kind:{k:?}"),
            MandateKey::Tool(name) => format!("tool:{name}"),
        }
    }
}

/// A stable, distinct base tool id per kind (the SCOPE's in-band face for the
/// class floor). Arbitrary but fixed: the gate only checks the presented id
/// equals the granted one.
fn kind_tool_id(kind: ToolKind) -> i64 {
    match kind {
        ToolKind::Read => 10,
        ToolKind::Search => 20,
        ToolKind::Fetch => 30,
        ToolKind::Execute => 40,
        ToolKind::Edit => 50,
        ToolKind::Other => 90,
    }
}

/// The executor method verb the worker's credential is scoped to (the SCOPE's
/// executor face). A turn under any other verb is rejected by the executor with
/// `TokenInsufficientCapability`. Per-tool grants reuse their kind's method so
/// the executor-side scope stays the kind's verb; the tighter confinement is the
/// distinct `tool_id` + the distinct rate ceiling on the per-tool worker.
fn method_for(kind: ToolKind) -> &'static str {
    match kind {
        ToolKind::Read => "tool.read",
        ToolKind::Search => "tool.search",
        ToolKind::Fetch => "tool.fetch",
        ToolKind::Execute => "tool.execute",
        ToolKind::Edit => "tool.edit",
        ToolKind::Other => "tool.other",
    }
}

/// The DEFAULT rate ceiling per kind — deos's confinement of how many times,
/// per mandate window, Hermes may exercise this class of tool. The dangerous
/// classes are tight; the read-only classes are generous.
fn default_rate(kind: ToolKind) -> i64 {
    match kind {
        ToolKind::Read => 200,
        ToolKind::Search => 100,
        ToolKind::Fetch => 50,
        ToolKind::Execute => 20,
        ToolKind::Edit => 30,
        ToolKind::Other => 10,
    }
}

/// A distinct in-band tool id per per-tool grant, derived from the kind base id
/// plus a small offset so it never collides with the kind floor id (or another
/// tool's id within reasonable session sizes). The actual value is immaterial —
/// only that it is STABLE and DISTINCT from every other grant's id, so a call
/// landing on the wrong worker is out-of-scope there.
fn per_tool_id(kind: ToolKind, name: &str) -> i64 {
    // FNV-1a-ish small hash of the name, folded into a band above the kind id.
    let mut h: u64 = 1469598103934665603;
    for b in name.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(1099511628211);
    }
    // 100_000-band per kind, 1..=9999 within the band — never the kind floor id.
    kind_tool_id(kind) * 100_000 + 1 + (h % 9999) as i64
}

/// deos's mandate over a Hermes ACP session: per-KIND defaults plus optional
/// tighter per-TOOL overrides.
///
/// Built with [`GrantRegistry::default_for_session`] (the standard confinement)
/// and consulted by [`crate::HermesGateway`] to admit a worker per
/// [`MandateKey`] on first use. `deadline` is the session-wide mandate expiry (a
/// clock/height ceiling); every grant shares it unless overridden.
#[derive(Clone, Debug)]
pub struct GrantRegistry {
    /// The per-kind class floors (always all six present after construction).
    kind_grants: HashMap<ToolKind, ToolGrant>,
    /// Tighter per-tool overrides, keyed by exact Hermes tool name.
    tool_grants: HashMap<String, ToolGrant>,
}

impl GrantRegistry {
    /// The standard deos confinement for a Hermes session: every kind gets its
    /// default-rate grant, all sharing `deadline` (the session mandate expiry).
    /// No per-tool overrides yet (add them with [`GrantRegistry::with_tool_grant`]
    /// or the curated [`GrantRegistry::with_standard_tool_grants`]).
    pub fn default_for_session(deadline: i64) -> GrantRegistry {
        let mut kind_grants = HashMap::new();
        for kind in [
            ToolKind::Read,
            ToolKind::Search,
            ToolKind::Fetch,
            ToolKind::Execute,
            ToolKind::Edit,
            ToolKind::Other,
        ] {
            kind_grants.insert(
                kind,
                ToolGrant {
                    tool_id: kind_tool_id(kind),
                    rate_limit: default_rate(kind),
                    deadline,
                    tool_method: method_for(kind).to_string(),
                },
            );
        }
        GrantRegistry {
            kind_grants,
            tool_grants: HashMap::new(),
        }
    }

    /// Override a single KIND's grant (e.g. tighten `Execute` to rate 0 to deny
    /// shell entirely, or extend a deadline). Returns `self` for chaining.
    pub fn with_grant(mut self, kind: ToolKind, grant: ToolGrant) -> Self {
        self.kind_grants.insert(kind, grant);
        self
    }

    /// Pin a tighter per-TOOL grant by exact Hermes tool name. The grant's
    /// `tool_id` and `tool_method` are auto-derived to the right scope (a
    /// distinct id in the tool's kind band, the kind's executor verb); only the
    /// `rate_limit` and `deadline` you pass are honored. This keeps the
    /// per-tool mandate's executor-scope consistent with its kind while metering
    /// it on its OWN counter.
    pub fn with_tool_grant(mut self, name: &str, rate_limit: i64, deadline: i64) -> Self {
        let kind = ToolKind::of_tool(name);
        self.tool_grants.insert(
            name.to_string(),
            ToolGrant {
                tool_id: per_tool_id(kind, name),
                rate_limit,
                deadline,
                tool_method: method_for(kind).to_string(),
            },
        );
        self
    }

    /// DENY a specific tool entirely: pin it a per-tool grant with rate 0, so
    /// EVERY call to it fails closed in-band on the first attempt (the gate's
    /// `delegAdmit` rate conjunct `new(=1) <= 0` is false). This is the
    /// whole-tool "out of mandate" face — deos confines the session to NOT use
    /// this tool at all, and the agent sees an in-band refusal if it reaches for
    /// it. Distinct id + its own (zero) counter, like any per-tool grant.
    pub fn with_grant_for_tool_deny(self, name: &str) -> Self {
        let deadline = self.kind_grants[&ToolKind::Other].deadline;
        self.with_tool_grant(name, 0, deadline)
    }

    /// A curated set of standard per-tool tightenings deos applies on top of the
    /// kind floors: the genuinely dangerous specific tools get their own tight,
    /// independently-metered mandates.
    ///
    /// * `terminal` — arbitrary shell: rate 5 (well under the Execute-20 floor).
    /// * `write_file` / `patch` — workspace mutation: rate 10 / 8.
    /// * `web_extract` — pulls arbitrary page bodies: rate 15 (under Fetch-50).
    /// * `delegate_task` — spawns a sub-agent loop: rate 3.
    /// * `create_card` / `edit_card` — the agent AUTHORS the world's UI (a receipted,
    ///   cap-gated view-patch through the [`CardEditor`](deos_js::CardEditor)): rate 12 /
    ///   20 (authoring is bounded but not as scarce as a sub-agent spawn). Each is its
    ///   own independently-metered worker under the Edit kind — and the deeper bound is
    ///   the card's own `edit_authority` cap tooth, which a rate ceiling never replaces.
    pub fn with_standard_tool_grants(self, deadline: i64) -> Self {
        self.with_tool_grant("terminal", 5, deadline)
            .with_tool_grant("write_file", 10, deadline)
            .with_tool_grant("patch", 8, deadline)
            .with_tool_grant("web_extract", 15, deadline)
            .with_tool_grant("delegate_task", 3, deadline)
            .with_tool_grant("create_card", 12, deadline)
            .with_tool_grant("edit_card", 20, deadline)
    }

    /// The mandate KEY a given tool name routes to: its per-tool grant if one is
    /// pinned, else its kind floor. This is the tightest-wins resolution the
    /// gateway uses to pick (and lazily admit) the worker for a call.
    pub fn key_for_tool(&self, name: &str) -> MandateKey {
        if self.tool_grants.contains_key(name) {
            MandateKey::Tool(name.to_string())
        } else {
            MandateKey::Kind(ToolKind::of_tool(name))
        }
    }

    /// The grant for a resolved [`MandateKey`].
    pub fn grant_for_key(&self, key: &MandateKey) -> &ToolGrant {
        match key {
            MandateKey::Tool(name) => self
                .tool_grants
                .get(name)
                .expect("a Tool key is only produced when a per-tool grant exists"),
            MandateKey::Kind(kind) => self.grant_for(*kind),
        }
    }

    /// The per-kind grant for a kind. Always present after `default_for_session`.
    pub fn grant_for(&self, kind: ToolKind) -> &ToolGrant {
        self.kind_grants
            .get(&kind)
            .expect("every kind has a grant after default_for_session")
    }

    /// The canonical in-band tool id a call routed to `key` must present to be
    /// in-scope under its grant.
    pub fn tool_id_for_key(&self, key: &MandateKey) -> i64 {
        self.grant_for_key(key).tool_id
    }

    /// Every mandate key that has a grant (all six kind floors + every pinned
    /// per-tool grant) — for the mandate inspector / dock surface.
    pub fn all_keys(&self) -> Vec<MandateKey> {
        let mut keys: Vec<MandateKey> = self
            .kind_grants
            .keys()
            .copied()
            .map(MandateKey::Kind)
            .collect();
        keys.sort_by_key(|k| k.label());
        let mut tools: Vec<MandateKey> = self
            .tool_grants
            .keys()
            .cloned()
            .map(MandateKey::Tool)
            .collect();
        tools.sort_by_key(|k| k.label());
        keys.extend(tools);
        keys
    }
}
