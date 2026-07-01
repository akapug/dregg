//! `workflow` — the deploy as a crash-resumable, metered durable workflow.
//!
//! A `dregg deploy` is a `duroxide` orchestration whose activities are **Clone → Build →
//! Publish**, each a durably-checkpointed, exactly-once, metered step:
//!
//! ```text
//!   ORCH_DEPLOY (deterministic coordination)
//!     ├─ gate budget → ACT_CLONE   → ACT_METER (period 1)   the source commitment
//!     ├─ gate budget → ACT_BUILD   → ACT_METER (period 2)   cap-bounded build → dist/
//!     ├─ (optional pause point — the crash/resume proof)
//!     └─ gate budget → ACT_PUBLISH → ACT_METER (period 3)   dist/ → a SiteCell + receipt
//! ```
//!
//! Durability is the `Provider` store's: on the on-disk SQLite store a deploy that crashes
//! mid-build resumes from its last checkpoint — a completed Clone/Build is **replayed from
//! history, never re-run** (no re-clone, no re-build), and the meter is never double-charged.
//! This mirrors `dreggnet-durable`'s pattern exactly; it builds its OWN registries because the
//! deploy's activities (git/build/publish) are not the compute+meter activities that crate
//! registers.
//!
//! The build runs in the cap-bounded exec tier (or as a bounded build subprocess), metered
//! against the deploy budget; an over-budget step fails the workflow before it runs (the
//! deploy-lease lapse → the build is reaped, never run-and-not-paid).

use std::path::{Path, PathBuf};
use std::sync::Arc;

use serde::{Deserialize, Serialize};

use dreggnet_webapp::hosting::SiteRegistry;
use dreggnet_webapp::receipt::ReceiptBody;

use crate::plan::BuildPlan;
use crate::publish::DeployManifestAsset;

/// The deploy orchestration name registered with duroxide.
pub const ORCH_DEPLOY: &str = "DreggDeploy";
/// The clone activity — fetch the repo at a pinned commit (the source commitment).
pub const ACT_CLONE: &str = "DeployClone";
/// The build activity — detect + run the cap-bounded build into a `dist/` tree.
pub const ACT_BUILD: &str = "DeployBuild";
/// The publish activity — `dist/` tree → a published `SiteCell` (commit folded into the root).
pub const ACT_PUBLISH: &str = "DeployPublish";
/// The meter-tick activity — charge one period of the deploy budget (exactly-once).
pub const ACT_METER: &str = "DeployMeterTick";

// ---------------------------------------------------------------------------
// Public spec / receipt.
// ---------------------------------------------------------------------------

/// Which stage the deploy parks on at its (test-only) pause point.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum DeployStage {
    Clone,
    Build,
    Publish,
}

/// The input to a deploy: a repo, a site name, an owner, a budget, and an optional build
/// override + pause point.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeploySpec {
    /// The repo to deploy (a remote URL, a `file://`, or a local path).
    pub repo_url: String,
    /// The ref to pin (branch/tag/commit); `None` = the remote default branch.
    #[serde(default)]
    pub git_ref: Option<String>,
    /// The subdomain label to publish under (`<name>.dregg.works`).
    pub site_name: String,
    /// The publishing owner/agent (the cap holder).
    pub owner: String,
    /// The deploy-lease budget, in meter units. The three steps each charge `cost_per_step`;
    /// a step whose charge would exceed this fails the deploy (lease lapse → reap).
    pub budget_units: i64,
    /// Meter cost charged per step.
    pub cost_per_step: i64,
    /// An explicit build plan that overrides detection (and `dregg.toml`).
    #[serde(default)]
    pub build_override: Option<BuildPlan>,
    /// Park on `pause_event` after this stage is durably checkpointed + metered (the crash/
    /// resume proof drives it). Production deploys leave it `None`.
    #[serde(default)]
    pub pause_after: Option<DeployStage>,
    /// The external event the deploy parks on at the pause point.
    #[serde(default)]
    pub pause_event: Option<String>,
}

impl DeploySpec {
    /// A straight deploy of `repo_url` as the site `site_name` for `owner`, with a default
    /// 1000-unit budget at 1 unit/step and no pause point.
    pub fn new(
        repo_url: impl Into<String>,
        site_name: impl Into<String>,
        owner: impl Into<String>,
    ) -> DeploySpec {
        DeploySpec {
            repo_url: repo_url.into(),
            git_ref: None,
            site_name: site_name.into(),
            owner: owner.into(),
            budget_units: 1000,
            cost_per_step: 1,
            build_override: None,
            pause_after: None,
            pause_event: None,
        }
    }

    /// This deploy as an [`ExecutionModel`](dreggnet_exec::model::ExecutionModel) point:
    /// a run-to-completion, **prepaid** (`budget_units`) deploy under the `deploy`
    /// cap-bundle, started by a push. The descriptor the workflow's funding is sourced
    /// from — the deploy path consuming the shared vocabulary, not a bespoke budget.
    pub fn execution_model(&self) -> dreggnet_exec::model::ExecutionModel {
        dreggnet_exec::model::ExecutionModel::deploy(
            self.site_name.clone(),
            DEPLOY_ASSET,
            self.budget_units,
        )
    }
}

/// The verifiable record a deploy leaves: which site, from which commit, at what content
/// commitment, for how much.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct DeployReceipt {
    /// The published subdomain label.
    pub site_name: String,
    /// The publishing owner.
    pub owner: String,
    /// The live URL.
    pub url: String,
    /// The source commitment — the commit the site was built from.
    pub commit: String,
    /// The published cell's content commitment (folds in the commit via the deploy manifest).
    pub content_root: String,
    /// The publish sequence in the site registry.
    pub publish_seq: u64,
    /// How many assets the published site holds (including the injected deploy manifest).
    pub asset_count: usize,
    /// The build plan that ran (`static`/`command`/`compute`).
    pub build_plan: String,
    /// Total meter units charged against the deploy budget.
    pub meter_units: i64,
    /// The receipt hash of the **publish turn receipt** this deploy is a view of.
    /// A deploy IS a publish turn (the kernel receipt is already the receipt);
    /// the `DeployReceipt` is a typed VIEW carrying that turn-receipt hash rather
    /// than a parallel notion. `Some` when the deploy engine's `SiteRegistry` is
    /// signed (the publish receipt is then prev-hash-chained + signed, so a
    /// client re-witnesses the deploy via that chain); `None` for the unsigned
    /// local default. See `docs/RECEIPT-CONTRACT.md`.
    #[serde(default)]
    pub turn_receipt_hash: Option<[u8; 32]>,
}

// ---------------------------------------------------------------------------
// The engine the activities run against (shared workdir root + site registry).
// ---------------------------------------------------------------------------

/// What the deploy activities operate on: a working-directory root (per-instance clone/build
/// dirs live under it, so they survive a crash) and the [`SiteRegistry`] the Publish writes
/// into (the hosting data plane the gateway serves).
pub struct DeployEngine {
    /// Root for per-deploy working directories (`<workroot>/<instance>/{repo,dist}`).
    pub workroot: PathBuf,
    /// The site registry the deploy publishes into.
    pub registry: Arc<SiteRegistry>,
}

impl DeployEngine {
    /// A deploy engine over `workroot`, publishing into `registry`.
    pub fn new(workroot: impl Into<PathBuf>, registry: Arc<SiteRegistry>) -> DeployEngine {
        DeployEngine {
            workroot: workroot.into(),
            registry,
        }
    }

    fn instance_root(&self, instance: &str) -> PathBuf {
        self.workroot.join(sanitize(instance))
    }
    fn repo_dir(&self, instance: &str) -> PathBuf {
        self.instance_root(instance).join("repo")
    }
    fn dist_dir(&self, instance: &str) -> PathBuf {
        self.instance_root(instance).join("dist")
    }
}

/// Make an instance id safe as a single path component.
fn sanitize(instance: &str) -> String {
    instance
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Deploy metering — funding on the ONE verified replenishing-budget primitive.
// ---------------------------------------------------------------------------

/// The asset a deploy-lease budget is denominated in. A deploy's `budget_units` is a
/// prepaid ceiling ([`Funding::Prepaid`](dreggnet_exec::model::Funding::Prepaid)); this
/// names the cell it lowers onto.
pub const DEPLOY_ASSET: &str = "deploy";

/// Observable per-deploy counters + the **verified funding meter**.
///
/// Two distinct things live here, deliberately separated:
/// - the activity **run counters** (`run:clone`/`run:build`/`run:publish`) — pure
///   observability so callers/tests can witness exactly-once (a replayed activity's
///   real-execution count stays `1` across a crash), NOT the funding path;
/// - [`units`] — the deploy's metered consumption, drawn through the one verified
///   [`ReplenishingMeter`](dreggnet_exec::meter::ReplenishingMeter) cell (no
///   process-local, non-verified counter): every charge is an exactly-once
///   `(instance, period)` draw against the deploy's prepaid budget, fail-closed over
///   the ceiling, the same primitive the server/agent meter through.
pub mod meter {
    use std::collections::HashMap;
    use std::sync::{Mutex, OnceLock};

    use dreggnet_exec::budget::BudgetTerms;
    use dreggnet_exec::meter::{Meter, MeterError, MeterKey, ReplenishingMeter};

    fn ledger() -> &'static Mutex<HashMap<(String, String), i64>> {
        static LEDGER: OnceLock<Mutex<HashMap<(String, String), i64>>> = OnceLock::new();
        LEDGER.get_or_init(|| Mutex::new(HashMap::new()))
    }

    /// The single verified funding meter for every deploy in this process — the
    /// replenishing-budget primitive the funding axis collapses onto. Persists across a
    /// runtime restart (the same-process crash/resume proof), so a replayed meter tick is
    /// the meter's own exactly-once `(instance, period)` dedup, never a fresh count.
    fn funding_meter() -> &'static ReplenishingMeter {
        static M: OnceLock<ReplenishingMeter> = OnceLock::new();
        M.get_or_init(ReplenishingMeter::new)
    }

    pub(crate) fn add(instance: &str, key: &str, delta: i64) -> i64 {
        let mut g = ledger().lock().expect("meter poisoned");
        let e = g
            .entry((instance.to_string(), key.to_string()))
            .or_insert(0);
        *e += delta;
        *e
    }

    /// Read an observability counter (`0` if never touched).
    pub fn get(instance: &str, key: &str) -> i64 {
        let g = ledger().lock().expect("meter poisoned");
        *g.get(&(instance.to_string(), key.to_string()))
            .copied()
            .get_or_insert(0)
    }

    /// How many times an activity (`clone`/`build`/`publish`) actually executed for this
    /// deploy. Exactly-once means this stays `1` across a crash + resume.
    pub fn run_calls(instance: &str, activity: &str) -> i64 {
        get(instance, &format!("run:{activity}"))
    }

    /// Open the deploy's prepaid budget cell (idempotent — re-opening is a no-op, the
    /// terms are sealed once). The ceiling is `budget` units of `asset`, drawn through
    /// the verified meter.
    pub(crate) fn open_budget(instance: &str, asset: &str, budget: i64) -> Result<(), MeterError> {
        funding_meter().open(instance, BudgetTerms::ceiling(asset, budget, i64::MAX, 0))
    }

    /// Draw one metered `period` (exactly-once) of `amount` against the deploy's budget,
    /// returning the deploy's total drawn so far (the running meter total). A replayed
    /// tick re-draws nothing and reports the same total.
    pub(crate) fn draw(instance: &str, period: i64, amount: i64) -> Result<i64, MeterError> {
        // The block is the period ordinal: monotone (1, 2, 3…), and with an i64::MAX
        // refill period no replenishment ever matures, so the cell is a pure ceiling.
        funding_meter().draw(&MeterKey::new(instance, period), amount, period)?;
        Ok(funding_meter().drawn_total(instance))
    }

    /// The meter units charged against this deploy — the verified cell's drawn total.
    pub fn units(instance: &str) -> i64 {
        funding_meter().drawn_total(instance)
    }
}

// ---------------------------------------------------------------------------
// Activity input/output payloads (JSON over the duroxide wire).
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize)]
struct CloneArgs {
    repo_url: String,
    git_ref: Option<String>,
}
#[derive(Serialize, Deserialize)]
struct CloneOut {
    commit: String,
}
#[derive(Serialize, Deserialize)]
struct BuildArgs {
    override_plan: Option<BuildPlan>,
}
#[derive(Serialize, Deserialize)]
struct BuildOut {
    plan_label: String,
}
#[derive(Serialize, Deserialize)]
struct PublishArgs {
    site_name: String,
    owner: String,
    repo_url: String,
    commit: String,
    plan_label: String,
}
#[derive(Serialize, Deserialize)]
struct PublishOut {
    content_root: String,
    publish_seq: u64,
    asset_count: usize,
    url: String,
    /// The receipt hash of the underlying publish turn receipt, when the deploy
    /// engine's `SiteRegistry` is signed. A deploy IS a publish turn; the
    /// `DeployReceipt` is a typed VIEW that carries this hash (re-witnessable
    /// against the registry's publish receipt chain).
    #[serde(default)]
    publish_receipt_hash: Option<[u8; 32]>,
}
#[derive(Serialize, Deserialize)]
struct MeterCharge {
    period: i64,
    amount: i64,
    /// The deploy's prepaid ceiling (so the meter tick can open the verified budget
    /// cell idempotently). Carried in the durable input ⇒ deterministic on replay.
    budget: i64,
    /// The asset the budget is denominated in.
    asset: String,
}

// ---------------------------------------------------------------------------
// Registry builder.
// ---------------------------------------------------------------------------

/// Build the duroxide registries (Clone/Build/Publish/MeterTick activities + the Deploy
/// orchestration) bound to `engine`. Register these with a `duroxide` runtime over any
/// `Provider` store. Sharing one `engine` across two runtimes (same `workroot` + `registry`)
/// is the crash-resume path.
pub fn build_deploy_registries(
    engine: Arc<DeployEngine>,
) -> (
    duroxide::runtime::registry::ActivityRegistry,
    duroxide::OrchestrationRegistry,
) {
    use duroxide::runtime::registry::ActivityRegistry;
    use duroxide::{OrchestrationContext, OrchestrationRegistry};

    let engine_clone = engine.clone();
    let engine_build = engine.clone();
    let engine_pub = engine.clone();

    let activities = ActivityRegistry::builder()
        // CLONE: fetch the repo into <workroot>/<instance>/repo, return the commit.
        .register(
            ACT_CLONE,
            move |ctx: duroxide::ActivityContext, input: String| {
                let engine = engine_clone.clone();
                async move {
                    let instance = ctx.instance_id().to_string();
                    let args: CloneArgs =
                        serde_json::from_str(&input).map_err(|e| format!("clone args: {e}"))?;
                    let repo_dir = engine.repo_dir(&instance);
                    let res = tokio::task::spawn_blocking(move || {
                        crate::clone::clone_repo(&args.repo_url, args.git_ref.as_deref(), &repo_dir)
                    })
                    .await
                    .map_err(|e| format!("clone join: {e}"))?
                    .map_err(|e| format!("clone: {e}"))?;
                    meter::add(&instance, "run:clone", 1);
                    serde_json::to_string(&CloneOut { commit: res.commit })
                        .map_err(|e| e.to_string())
                }
            },
        )
        // BUILD: detect + run the cap-bounded build into <workroot>/<instance>/dist.
        .register(
            ACT_BUILD,
            move |ctx: duroxide::ActivityContext, input: String| {
                let engine = engine_build.clone();
                async move {
                    let instance = ctx.instance_id().to_string();
                    let args: BuildArgs =
                        serde_json::from_str(&input).map_err(|e| format!("build args: {e}"))?;
                    let repo_dir = engine.repo_dir(&instance);
                    let dist_dir = engine.dist_dir(&instance);
                    let outcome = tokio::task::spawn_blocking(
                        move || -> Result<crate::build::BuildOutcome, String> {
                            let plan = crate::plan::detect(&repo_dir, args.override_plan.as_ref())
                                .map_err(|e| e.to_string())?;
                            crate::build::run_build(&plan, &repo_dir, &dist_dir)
                                .map_err(|e| e.to_string())
                        },
                    )
                    .await
                    .map_err(|e| format!("build join: {e}"))??;
                    meter::add(&instance, "run:build", 1);
                    serde_json::to_string(&BuildOut {
                        plan_label: outcome.plan_label,
                    })
                    .map_err(|e| e.to_string())
                }
            },
        )
        // PUBLISH: <workroot>/<instance>/dist → a published SiteCell (commit folded in).
        .register(
            ACT_PUBLISH,
            move |ctx: duroxide::ActivityContext, input: String| {
                let engine = engine_pub.clone();
                async move {
                    let instance = ctx.instance_id().to_string();
                    let args: PublishArgs =
                        serde_json::from_str(&input).map_err(|e| format!("publish args: {e}"))?;
                    let dist_dir = engine.dist_dir(&instance);
                    let registry = engine.registry.clone();
                    let manifest = DeployManifestAsset {
                        repo: args.repo_url.clone(),
                        commit: args.commit.clone(),
                        build_plan: args.plan_label.clone(),
                        site: args.site_name.clone(),
                    };
                    let name = args.site_name.clone();
                    let owner = args.owner.clone();
                    let receipt = tokio::task::spawn_blocking(move || {
                        crate::publish::publish_dist(&registry, &owner, &name, &dist_dir, &manifest)
                            .map_err(|e| e.to_string())
                    })
                    .await
                    .map_err(|e| format!("publish join: {e}"))??;
                    meter::add(&instance, "run:publish", 1);
                    let url = format!("https://{}.dregg.works/", args.site_name);
                    // Capture the publish turn-receipt hash before moving fields out:
                    // the DeployReceipt is a typed VIEW carrying it.
                    let publish_receipt_hash = receipt.receipt_hash();
                    serde_json::to_string(&PublishOut {
                        content_root: receipt.content_root,
                        publish_seq: receipt.seq,
                        asset_count: receipt.asset_count,
                        url,
                        publish_receipt_hash,
                    })
                    .map_err(|e| e.to_string())
                }
            },
        )
        // METER_TICK: charge one period of the deploy budget against the ONE verified
        // replenishing-budget cell; exactly-once on replay (the meter's own
        // `(instance, period)` dedup). Returns the deploy's running drawn total.
        .register(
            ACT_METER,
            |ctx: duroxide::ActivityContext, input: String| async move {
                let instance = ctx.instance_id().to_string();
                let charge: MeterCharge =
                    serde_json::from_str(&input).map_err(|e| format!("meter charge: {e}"))?;
                meter::open_budget(&instance, &charge.asset, charge.budget)
                    .map_err(|e| format!("deploy meter open: {e}"))?;
                let total = meter::draw(&instance, charge.period, charge.amount)
                    .map_err(|e| format!("deploy meter draw: {e}"))?;
                Ok(total.to_string())
            },
        )
        .build();

    let orchestrations = OrchestrationRegistry::builder()
        .register(
            ORCH_DEPLOY,
            |ctx: OrchestrationContext, input: String| async move {
                let spec: DeploySpec =
                    serde_json::from_str(&input).map_err(|e| format!("bad DeploySpec: {e}"))?;

                // The deploy's funding is the prepaid ceiling its ExecutionModel declares —
                // the gate + meter draw against THIS one descriptor-sourced budget, not a
                // bespoke per-path number.
                let budget = spec.execution_model().funding.terms().budget;
                let mut total: i64 = 0;

                // --- ① CLONE (gate, run, meter). ---
                gate(total, spec.cost_per_step, budget, "clone")?;
                let clone_args = serde_json::to_string(&CloneArgs {
                    repo_url: spec.repo_url.clone(),
                    git_ref: spec.git_ref.clone(),
                })
                .map_err(|e| e.to_string())?;
                let clone: CloneOut =
                    serde_json::from_str(&ctx.schedule_activity(ACT_CLONE, clone_args).await?)
                        .map_err(|e| format!("clone out: {e}"))?;
                total = meter_tick(&ctx, 1, spec.cost_per_step, budget).await?;
                if spec.pause_after == Some(DeployStage::Clone) {
                    if let Some(ev) = spec.pause_event.as_ref() {
                        let _ = ctx.schedule_wait(ev).await;
                    }
                }

                // --- ② BUILD (gate, run, meter). ---
                gate(total, spec.cost_per_step, budget, "build")?;
                let build_args = serde_json::to_string(&BuildArgs {
                    override_plan: spec.build_override.clone(),
                })
                .map_err(|e| e.to_string())?;
                let build: BuildOut =
                    serde_json::from_str(&ctx.schedule_activity(ACT_BUILD, build_args).await?)
                        .map_err(|e| format!("build out: {e}"))?;
                total = meter_tick(&ctx, 2, spec.cost_per_step, budget).await?;
                if spec.pause_after == Some(DeployStage::Build) {
                    if let Some(ev) = spec.pause_event.as_ref() {
                        let _ = ctx.schedule_wait(ev).await;
                    }
                }

                // --- ③ PUBLISH (gate, run, meter). ---
                gate(total, spec.cost_per_step, budget, "publish")?;
                let publish_args = serde_json::to_string(&PublishArgs {
                    site_name: spec.site_name.clone(),
                    owner: spec.owner.clone(),
                    repo_url: spec.repo_url.clone(),
                    commit: clone.commit.clone(),
                    plan_label: build.plan_label.clone(),
                })
                .map_err(|e| e.to_string())?;
                let published: PublishOut =
                    serde_json::from_str(&ctx.schedule_activity(ACT_PUBLISH, publish_args).await?)
                        .map_err(|e| format!("publish out: {e}"))?;
                total = meter_tick(&ctx, 3, spec.cost_per_step, budget).await?;
                if spec.pause_after == Some(DeployStage::Publish) {
                    if let Some(ev) = spec.pause_event.as_ref() {
                        let _ = ctx.schedule_wait(ev).await;
                    }
                }

                let receipt = DeployReceipt {
                    site_name: spec.site_name,
                    owner: spec.owner,
                    url: published.url,
                    commit: clone.commit,
                    content_root: published.content_root,
                    publish_seq: published.publish_seq,
                    asset_count: published.asset_count,
                    build_plan: build.plan_label,
                    meter_units: total,
                    turn_receipt_hash: published.publish_receipt_hash,
                };
                serde_json::to_string(&receipt).map_err(|e| e.to_string())
            },
        )
        .build();

    (activities, orchestrations)
}

/// Budget gate: refuse a step whose charge would exceed the deploy budget (the lease
/// lapse). The headroom decision routes through the one verified prepaid-ceiling core
/// ([`prepaid_ceiling_admits`](dreggnet_exec::budget::prepaid_ceiling_admits)) — the
/// same primitive the server/agent meter through — not a hand-rolled comparison.
fn gate(total: i64, cost: i64, budget: i64, step: &str) -> Result<(), String> {
    if !dreggnet_exec::budget::prepaid_ceiling_admits(budget, total, cost) {
        let projected = total.saturating_add(cost);
        return Err(format!(
            "deploy-lease exhausted: {step} charge would reach {projected} > budget {budget}"
        ));
    }
    Ok(())
}

/// Schedule a meter tick for `period` against the deploy's `budget` cell, returning the
/// running drawn total.
async fn meter_tick(
    ctx: &duroxide::OrchestrationContext,
    period: i64,
    amount: i64,
    budget: i64,
) -> Result<i64, String> {
    let charge = serde_json::to_string(&MeterCharge {
        period,
        amount,
        budget,
        asset: DEPLOY_ASSET.to_string(),
    })
    .map_err(|e| e.to_string())?;
    ctx.schedule_activity(ACT_METER, charge)
        .await?
        .parse()
        .map_err(|e| format!("meter total: {e}"))
}

// ---------------------------------------------------------------------------
// One-shot runners.
// ---------------------------------------------------------------------------

/// Run a deploy to completion over a fresh **in-memory** SQLite durable store, blocking the
/// caller, and return its [`DeployReceipt`]. Proves the clone→build→publish→serve weld end to
/// end; does NOT survive the process (use [`deploy_on_disk_blocking`] for crash-resume).
///
/// Must NOT be called from inside an existing tokio runtime (it builds its own).
pub fn deploy_in_memory_blocking(
    engine: Arc<DeployEngine>,
    spec: &DeploySpec,
    instance: &str,
) -> Result<DeployReceipt, String> {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|e| format!("deploy: tokio runtime build failed: {e}"))?;
    rt.block_on(deploy_in_memory(engine, spec, instance))
}

/// The async core of [`deploy_in_memory_blocking`].
pub async fn deploy_in_memory(
    engine: Arc<DeployEngine>,
    spec: &DeploySpec,
    instance: &str,
) -> Result<DeployReceipt, String> {
    use duroxide::providers::sqlite::SqliteProvider;
    let store = Arc::new(
        SqliteProvider::new_in_memory()
            .await
            .map_err(|e| format!("deploy: open in-memory store: {e}"))?,
    );
    run_to_completion(store, engine, spec, instance).await
}

/// Run a deploy to completion over an **on-disk** SQLite durable store at `db_path`, blocking
/// the caller, and return its [`DeployReceipt`].
///
/// This is the persistent, crash-resumable path: the workflow's checkpoints live at `db_path`
/// and the cloned/built tree lives under the engine's `workroot`, so if the process crashes
/// mid-deploy, a fresh process over the SAME `db_path` + `workroot` resumes from the last
/// checkpoint — a completed Clone/Build is replayed (never re-run), the meter never doubled.
///
/// Must NOT be called from inside an existing tokio runtime (it builds its own).
pub fn deploy_on_disk_blocking(
    engine: Arc<DeployEngine>,
    spec: &DeploySpec,
    instance: &str,
    db_path: &Path,
) -> Result<DeployReceipt, String> {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|e| format!("deploy: tokio runtime build failed: {e}"))?;
    rt.block_on(deploy_on_disk(engine, spec, instance, db_path))
}

/// The async core of [`deploy_on_disk_blocking`]. Starts the instance if new; if it is already
/// present (a crashed deploy being recovered), it does not re-start — the runtime auto-resumes
/// the in-flight instance and this awaits its completion.
pub async fn deploy_on_disk(
    engine: Arc<DeployEngine>,
    spec: &DeploySpec,
    instance: &str,
    db_path: &Path,
) -> Result<DeployReceipt, String> {
    use duroxide::providers::sqlite::SqliteProvider;
    if let Some(parent) = db_path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)
                .map_err(|e| format!("deploy: create store dir {}: {e}", parent.display()))?;
        }
    }
    let db_url = format!("sqlite:{}?mode=rwc", db_path.display());
    let store = Arc::new(
        SqliteProvider::new(&db_url, None)
            .await
            .map_err(|e| format!("deploy: open on-disk store {}: {e}", db_path.display()))?,
    );
    run_to_completion(store, engine, spec, instance).await
}

/// Shared runner: register the deploy registries over `store`, start-or-resume `instance`, and
/// await its [`DeployReceipt`].
async fn run_to_completion(
    store: Arc<duroxide::providers::sqlite::SqliteProvider>,
    engine: Arc<DeployEngine>,
    spec: &DeploySpec,
    instance: &str,
) -> Result<DeployReceipt, String> {
    use duroxide::runtime::Runtime;
    use duroxide::{Client, OrchestrationStatus};
    use std::time::Duration;

    let input_json = serde_json::to_string(spec).map_err(|e| e.to_string())?;
    let (activities, orchestrations) = build_deploy_registries(engine);
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());

    let result = async {
        let present = matches!(
            client.get_orchestration_status(instance).await,
            Ok(s) if !matches!(s, OrchestrationStatus::NotFound)
        );
        if !present {
            client
                .start_orchestration(instance, ORCH_DEPLOY, input_json)
                .await
                .map_err(|e| format!("deploy: start orchestration: {e}"))?;
        }
        let status = client
            .wait_for_orchestration(instance, Duration::from_secs(120))
            .await
            .map_err(|e| format!("deploy: await orchestration: {e}"))?;
        match status {
            OrchestrationStatus::Completed { output, .. } => {
                serde_json::from_str(&output).map_err(|e| format!("deploy: decode receipt: {e}"))
            }
            OrchestrationStatus::Failed { details, .. } => Err(details.display_message()),
            other => Err(format!("deploy: unexpected status: {other:?}")),
        }
    }
    .await;

    rt.shutdown(None).await;
    result
}
