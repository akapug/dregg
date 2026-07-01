//! The hosted-agent **session** as the web attach sees it — the
//! [`dreggnet_exec::live::LiveRun`] contract record plus *whose* it is (the
//! authenticated `dga1_` subject) and a stable id, so the [`crate::store`] can
//! cap-scope it to exactly its owner.
//!
//! The session is NOT a new shape: [`AgentSession::run`] is the very `LiveRun` the
//! SSH attach surfaces and `dregg-agent verify run.json` re-witnesses. The web
//! attach only adds the `owner`/`id`/`created_at` envelope the multi-tenant
//! browser surface needs.

use serde::{Deserialize, Serialize};

use dreggnet_exec::live::LiveRun;

/// A resource that belongs to exactly one subject — the single seam the
/// cap-scoping in [`crate::store`] rides: a session is shown/driven for a user
/// iff `self.owner() == subject`.
pub trait Owned {
    /// The subject (`dregg:<16 hex>`) that owns this resource.
    fn owner(&self) -> &str;
}

/// What the **goal box** submits: the natural-language goal, the budget the user
/// sets, and the cap bundle they choose. The flexible-live-run inputs (the goal +
/// budget + cap bundle), straight off the page.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct GoalRequest {
    /// The natural-language goal typed into the goal box.
    pub goal: String,
    /// The budget ceiling (in the session asset's units; the demo uses cents).
    pub budget: i64,
    /// The services the agent may `invoke` — each becomes an `invoke:<service>`
    /// cap in the granted bundle. The visible part of "set the cap bundle".
    #[serde(default)]
    pub services: Vec<String>,
    /// The cells the agent may read+write — each becomes a `cell-read:`/
    /// `cell-write:` cap pair.
    #[serde(default)]
    pub cells: Vec<String>,
}

impl GoalRequest {
    /// A goal request with a budget and no caps (a bare agent).
    pub fn new(goal: impl Into<String>, budget: i64) -> GoalRequest {
        GoalRequest {
            goal: goal.into(),
            budget,
            services: Vec::new(),
            cells: Vec::new(),
        }
    }

    /// Grant `invoke:<service>`.
    pub fn with_service(mut self, service: impl Into<String>) -> GoalRequest {
        self.services.push(service.into());
        self
    }

    /// Grant read+write over `cell`.
    pub fn with_cell(mut self, cell: impl Into<String>) -> GoalRequest {
        self.cells.push(cell.into());
        self
    }

    /// A sanitized copy: the goal trimmed, the budget floored at 0, and the cap
    /// lists de-duplicated. The store applies this before driving so a hostile
    /// body cannot drive a negative budget or a degenerate goal.
    pub fn sanitized(&self) -> GoalRequest {
        let mut services = self.services.clone();
        services.retain(|s| !s.trim().is_empty());
        services.sort();
        services.dedup();
        let mut cells = self.cells.clone();
        cells.retain(|c| !c.trim().is_empty());
        cells.sort();
        cells.dedup();
        GoalRequest {
            goal: self.goal.trim().to_string(),
            budget: self.budget.max(0),
            services,
            cells,
        }
    }
}

/// A hosted agent session owned by exactly one subject — the `LiveRun` record
/// plus its owner + id, the unit the web attach drives, streams, and re-witnesses.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AgentSession {
    /// The stable session id (`sess_<hex>`).
    pub id: String,
    /// The owning subject (the `dga1_` cap holder that drove it).
    pub owner: String,
    /// When the session was created (RFC3339).
    pub created_at: String,
    /// When this session is a **fork** of another, the parent's id — the cell
    /// superpower made explicit: a fork runs over an *attenuated* cap bundle (a
    /// subset of the parent's authority), owned by the same subject. `None` for a
    /// root session.
    #[serde(default)]
    pub parent: Option<String>,
    /// The hosted-session contract record — the goal, the budget bound, the
    /// granted cap bundle, the receipt chain, and the reason→act→observe
    /// transcript. The same `LiveRun` the SSH attach surfaces.
    pub run: LiveRun,
}

impl Owned for AgentSession {
    fn owner(&self) -> &str {
        &self.owner
    }
}

impl AgentSession {
    /// The natural-language goal.
    pub fn goal(&self) -> &str {
        &self.run.goal
    }
    /// The granted cap bundle (display strings).
    pub fn caps(&self) -> &[String] {
        &self.run.caps
    }
    /// The budget ceiling (the hard bound).
    pub fn budget(&self) -> i64 {
        self.run.run.budget
    }
    /// The budget consumed over the run.
    pub fn consumed(&self) -> i64 {
        self.run.run.consumed
    }
    /// The un-drawn headroom — the ceiling on everything the agent could still
    /// have done.
    pub fn headroom(&self) -> i64 {
        self.run.run.headroom
    }
    /// The number of sealed receipts (admitted actions).
    pub fn receipts(&self) -> usize {
        self.run.run.receipts.len()
    }
    /// Actions refused by the cap-gate (outside the bundle) — the visible teeth.
    pub fn cap_refused(&self) -> u64 {
        self.run.run.cap_refused
    }
    /// Actions refused by the meter (over the budget ceiling).
    pub fn budget_refused(&self) -> u64 {
        self.run.run.budget_refused
    }
}
