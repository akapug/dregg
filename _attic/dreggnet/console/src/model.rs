//! The resource VIEW types the console renders — one per surface the customer
//! owns — plus the [`Owned`] trait that names *whose* a resource is.
//!
//! Each view carries an `owner` field (for a server, the `lessee`): the stable
//! **subject** of the dregg credential that minted/holds it (`dregg:<16 hex>`,
//! the same `dreggnet_webauth::subject_of` the domains + storage surfaces already
//! bind their `owner` to). The console never invents ownership — it reads the
//! owner the resource surface already records, and [`crate::scope`] filters the
//! cloud-wide [`Catalog`] down to exactly the authenticated subject's own cells.
//!
//! These are projections, not new state: a `SiteView` is the published
//! `webapp::SiteCell` as the user sees it, a `ServerView` the
//! `control::ServerRecord`, an `AgentView` a deployed `dreggnet_exec::agent`
//! run (its budget bound + receipt chain + QA proof), a `DomainView` a
//! `dregg_domains::DomainBinding`, a `StorageBucketView` a `storage::BucketCell`,
//! and the `DreggLedgerView` the meter/settle spend the user was charged.

use serde::{Deserialize, Serialize};

use dreggnet_exec::agent::AgentRunReport;

/// A resource that belongs to exactly one subject. The single seam the cap-
/// scoping in [`crate::scope`] rides: a resource is shown to a user iff
/// `self.owner() == subject`.
pub trait Owned {
    /// The subject (`dregg:<16 hex>`) that owns this resource.
    fn owner(&self) -> &str;
}

/// A published site the user hosts.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct SiteView {
    /// The owning subject.
    pub owner: String,
    /// The site `<name>` (its `*.example.com` host).
    pub name: String,
    /// `"published"` / `"draft"`.
    pub status: String,
    /// The custom domain bound to it, if any.
    pub domain: Option<String>,
    /// The committed content root (the Poseidon2 cell-heap commitment a verify
    /// re-witnesses) — what `dregg-cloud verify` checks the served bytes against.
    pub content_root: String,
    /// The byte size of the published content.
    pub bytes: u64,
}

impl Owned for SiteView {
    fn owner(&self) -> &str {
        &self.owner
    }
}

/// A persistent server the user rents (held Running, metered per uptime period).
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ServerView {
    /// The lessee renting the server — the owning subject.
    pub lessee: String,
    /// The server id (`srv_…`).
    pub id: String,
    /// A human name.
    pub name: String,
    /// `"running"` / `"stopped"` / `"reaped"`.
    pub state: String,
    /// The region it is placed in.
    pub region: String,
    /// The compute size (`small`/`medium`/`large`).
    pub size: String,
    /// The total uptime budget, in meter units (the hard ceiling).
    pub budget_units: i64,
    /// The cost charged per uptime period.
    pub per_period_units: i64,
    /// How many uptime periods have been metered + settled (the durable cursor).
    pub periods_metered: i64,
}

impl ServerView {
    /// The total uptime units settled so far (`periods_metered × per_period_units`).
    pub fn settled_units(&self) -> i64 {
        self.periods_metered.saturating_mul(self.per_period_units)
    }
    /// The remaining uptime headroom (`budget − settled`).
    pub fn headroom_units(&self) -> i64 {
        (self.budget_units - self.settled_units()).max(0)
    }
}

impl Owned for ServerView {
    fn owner(&self) -> &str {
        &self.lessee
    }
}

/// A deployed agent: the run (the proof of everything it did) + the budget cell
/// (the hard bound on everything it could have done) + the QA proof (the
/// witnessed-execution verdicts the run sealed). The console's centerpiece —
/// the agent panel shows the bound, the receipt chain, and the QA proof, and the
/// re-verify button re-witnesses the whole report in-page.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AgentView {
    /// The owning subject (the deployer).
    pub owner: String,
    /// The agent id.
    pub id: String,
    /// The granted cap bundle (display + the no-amplify story).
    pub caps: Vec<String>,
    /// The full re-witnessable run report: the budget ceiling, the consumed +
    /// headroom bound, the receipt chain, and the per-action QA verdicts. Carried
    /// verbatim so the re-verify button re-witnesses the *real* proof, not a flag.
    pub report: AgentRunReport,
    /// The deployed code's content root the witnessed QA must have run against
    /// (the site/deploy `content_root` the run's `code_root` is checked equal to).
    pub deployed_root: String,
}

impl AgentView {
    /// The budget ceiling (the hard bound).
    pub fn budget(&self) -> i64 {
        self.report.budget
    }
    /// The budget consumed over the run.
    pub fn consumed(&self) -> i64 {
        self.report.consumed
    }
    /// The un-drawn headroom — the ceiling on everything the agent could still
    /// have done.
    pub fn headroom(&self) -> i64 {
        self.report.headroom
    }
    /// The number of sealed receipts (admitted actions).
    pub fn receipts(&self) -> usize {
        self.report.receipts.len()
    }
    /// Whether every tool the run invoked returned a passing verdict (and ≥1 ran).
    pub fn qa_passed(&self) -> bool {
        self.report.all_tools_passed()
    }
    /// The QA/ops verdicts: `(action, ok, summary)` per invoked tool.
    pub fn qa_results(&self) -> Vec<(String, bool, String)> {
        self.report.tool_results()
    }
}

impl Owned for AgentView {
    fn owner(&self) -> &str {
        &self.owner
    }
}

/// A custom domain the user bound (verified / pending).
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct DomainView {
    /// The owning subject (the binding cap holder).
    pub owner: String,
    /// The custom domain.
    pub domain: String,
    /// The site `<name>` it points at.
    pub site: String,
    /// `"verified"` / `"pending"`.
    pub state: String,
    /// The registry sequence at which it verified, if verified.
    pub verified_seq: Option<u64>,
}

impl Owned for DomainView {
    fn owner(&self) -> &str {
        &self.owner
    }
}

/// A storage bucket the user owns.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct StorageBucketView {
    /// The owning subject.
    pub owner: String,
    /// The bucket name.
    pub name: String,
    /// The committed content root (the trustless-read commitment).
    pub content_root: String,
    /// The number of objects in the bucket.
    pub objects: u64,
    /// The total bytes stored.
    pub bytes: u64,
}

impl Owned for StorageBucketView {
    fn owner(&self) -> &str {
        &self.owner
    }
}

/// One line of the user's $DREGG spend ledger — a charge the meter/settle rail
/// recorded against one of their resources.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct SpendEntry {
    /// The owning subject the charge was billed to.
    pub owner: String,
    /// The resource kind charged (`"site"` / `"server"` / `"agent"` / `"storage"`).
    pub resource_kind: String,
    /// The specific resource id/name charged.
    pub resource_id: String,
    /// The billing period label (e.g. an uptime-period index or a date).
    pub period: String,
    /// The units charged.
    pub units: i64,
}

impl Owned for SpendEntry {
    fn owner(&self) -> &str {
        &self.owner
    }
}

/// The user's $DREGG balance + spend, assembled from the entries scoped to them.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct DreggLedgerView {
    /// The subject this ledger is for.
    pub subject: String,
    /// The current $DREGG balance.
    pub balance: i64,
    /// The total spent across all the user's resources (Σ of `entries`).
    pub total_spent: i64,
    /// The per-resource/period spend lines (already scoped to the subject).
    pub entries: Vec<SpendEntry>,
}

/// The assembled, cap-scoped console view for one signed-in user — everything
/// "my stuff", and nothing that is not theirs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConsoleView {
    /// The authenticated subject this view belongs to.
    pub subject: String,
    /// When the view was assembled (RFC3339).
    pub generated_at: String,
    /// The user's published sites.
    pub sites: Vec<SiteView>,
    /// The user's persistent servers.
    pub servers: Vec<ServerView>,
    /// The user's deployed agents (budget bound + receipts + QA proof each).
    pub agents: Vec<AgentView>,
    /// The user's bound custom domains.
    pub domains: Vec<DomainView>,
    /// The user's storage buckets.
    pub buckets: Vec<StorageBucketView>,
    /// The user's $DREGG balance + spend.
    pub dregg: DreggLedgerView,
}

impl ConsoleView {
    /// `true` iff the view is empty (a brand-new account with nothing yet).
    pub fn is_empty(&self) -> bool {
        self.sites.is_empty()
            && self.servers.is_empty()
            && self.agents.is_empty()
            && self.domains.is_empty()
            && self.buckets.is_empty()
            && self.dregg.entries.is_empty()
    }
}
