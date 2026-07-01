//! `dregg-cloud` — the DreggNet CLI: the operator face (open/fund a lease, run a
//! metered durable workload, check status) AND the developer onramp (the §3.4
//! verbs over the same control plane):
//!
//! ```text
//!   dregg-cloud login                    # connect a cap-account (a dga1_ credential, or --new)
//!   dregg-cloud deploy <repo|.>          # clone → build → publish a site cell (§3.1)
//!   dregg-cloud domains add/list/verify  # bind + DNS-verify a BYO custom domain (§3.2)
//!   dregg-cloud ls / logs <id> / destroy # my sites/leases/domains · output · teardown
//! ```
//!
//! The developer verbs persist into the same JSON state dir the operator verbs
//! use, drive the REAL dregg-domains registry + the webauth cred core, and run
//! the whole local/in-process path (no live edge — that is reviewed-go).
//!
//! Every subcommand routes through [`dreggnet_control::Scheduler`] over the in-process
//! [`dreggnet_control::LocalProvider`] — the path that genuinely runs the workload:
//!
//! ```text
//!   dregg-cloud lease open   → register a funded (mock) execution-lease
//!   dregg-cloud run --source → Scheduler::place_workload(lease, the declared program)
//!                             → LocalProvider provisions a machine
//!                               → the bridge fulfills it as a durable metered workflow
//!                                 (the YOUR-WAT program runs, metered against the budget)
//!   dregg-cloud status       → the lifecycle + meter of every scheduled workload
//! ```
//!
//! ## Real vs mock (honest)
//!
//! - **Real:** the control-plane place→provision→fulfill path; the durable the owned sandbox
//!   workflow (the wasmi steps genuinely run in the sandbox); `run --source` threads
//!   the caller's declared WAT program all the way into the durable workflow, so the
//!   program you wrote is the program that runs; the meter (each durable step charges
//!   `per_period` against the lease budget, an over-budget tick lapses the workflow →
//!   the machine is reaped); the cross-invocation lease + workload registry (a JSON
//!   state dir).
//! - **Mock:** the [`dreggnet_control::Lease`] itself — `lease open` registers a plain
//!   funded lease record rather than reading a real funded lease from a dregg node /
//!   light client (the bridge's named next sub-step, `dreggnet_bridge::dregg_verify`).

use std::path::{Path, PathBuf};

use anyhow::{Context, Result, anyhow, bail};
use clap::{Parser, Subcommand, ValueEnum};
use serde::{Deserialize, Serialize};

use std::sync::Arc;

use dregg_deploy::{DeployEngine, DeploySpec, deploy_on_disk};
use dregg_domains::{
    ChallengeMethod, DomainBinding, DomainCap, DomainRegistry, LiveDns, VerificationState,
};
use dreggnet_control::{
    CapGrade, Lease, LocalProvider, MachineSize, Scheduler, WorkloadSource, WorkloadState,
};
use dreggnet_exec::agent::{
    AgentAction, AgentCloud, AgentRunReport, AgentSpec, PlannedBrain, verify_agent_run,
};
use dreggnet_exec::budget::BudgetTerms;
use dreggnet_exec::meter::ReplenishingMeter;
use dreggnet_exec::model::ExecutionModel;
use dreggnet_logs::{LogError, LogLine, LogSink};
use dreggnet_webapp::hosting::SiteRegistry;
use dreggnet_webapp::{
    SiteReceiptBundle, fetch_site_bundle, hex32, parse_hex32, serve_registry, verify_site_bundle,
};
use dreggnet_webauth::cred::{PublicKey, RootKey};
use dreggnet_webauth::grant::mint_caps;
use dreggnet_webauth::subject_of;

mod cloud;
use cloud::{
    CloudClient, CreateMachineRequest, GuestConfig, ListOutcome, MachineConfig, MachineOutcome,
};

/// The MCP server — the agent-facing twin of this CLI (`dregg-cloud mcp`).
mod mcp;

/// The file the CLI persists its lease + workload registry to, under the state dir.
const STATE_FILE: &str = "state.json";

/// The program name to print in copy-pasteable next-step prompts — derived from
/// `argv[0]` so every printed instruction names the ACTUAL invoked binary (e.g.
/// `dregg-cloud`), never a name that collides with a different tool. Falls back to
/// `dregg-cloud` when `argv[0]` is unavailable.
fn prog() -> String {
    std::env::args()
        .next()
        .as_deref()
        .map(Path::new)
        .and_then(|p| p.file_name())
        .map(|f| f.to_string_lossy().into_owned())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "dregg-cloud".to_string())
}

#[derive(Parser)]
#[command(
    name = "dregg-cloud",
    version,
    about = "dregg-cloud — the DreggNet operator CLI: open/fund a lease, run a metered durable workload, check status."
)]
struct Cli {
    /// Directory the CLI persists its lease + workload registry in, so `lease open`,
    /// `run`, and `status` share state across invocations.
    #[arg(
        long,
        global = true,
        env = "DREGGNET_STATE_DIR",
        default_value = ".dreggnet"
    )]
    state_dir: PathBuf,

    /// Interface with a LIVE DreggNet cloud at this gateway URL (e.g.
    /// `https://dreggnet.fg-goose.online`) instead of the in-process local
    /// simulation. When set, the cloud verbs (`deploy`, `run`, `status`/`ls`, and
    /// the `machines` subcommands) make REAL HTTP calls to the gateway's
    /// fly-compatible machines API — funded, metered, and receipted by the live
    /// node. The account's `dga1_` credential (from `login`) is presented as the
    /// bearer. Unset → the local-simulation behavior (clearly labeled).
    #[arg(long, global = true, env = "DREGGNET_ENDPOINT")]
    endpoint: Option<String>,

    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Manage execution-leases (the authorization a workload runs under).
    Lease {
        #[command(subcommand)]
        action: LeaseAction,
    },
    /// Schedule a funded lease onto the LocalProvider, fulfill it as a durable the owned sandbox
    /// workflow, and print the result + the meter.
    Run {
        /// The lease id (from `dregg-cloud lease open`).
        #[arg(long)]
        lease: String,
        /// The workload language. Only `wat` is wired at this rung.
        #[arg(long, default_value = "wat")]
        lang: String,
        /// Path to the workload source (the declared program; WAT text). The
        /// module MUST export a function named `run` (the workload ABI) — e.g.
        /// `(func (export "run") (result i32) ...)`. A module that exports `main`
        /// (or anything else) instead will be refused with `export 'run' not found`.
        #[arg(long)]
        source: PathBuf,
    },
    /// List scheduled workloads and their lifecycle + meter.
    Status {
        /// Restrict to one lease id.
        #[arg(long)]
        lease: Option<String>,
        /// With `--endpoint`: the live-cloud app whose machines to list (the
        /// gateway lists machines per app). Ignored for the local simulation.
        #[arg(long)]
        app: Option<String>,
    },
    /// Auto-deploy a git repo: clone → detect → build (cap-bounded) → publish a site cell,
    /// as a crash-resumable, metered durable workflow. The keystone DX (the verifiable
    /// "you ship, we host"): the cloned commit lands in the receipt + the published cell.
    Deploy {
        /// The repo to deploy — a git URL, a `file://` path, or a local path.
        repo: String,
        /// The subdomain label to publish under (`<name>.dregg.works`). Defaults to the
        /// repo's basename.
        #[arg(long)]
        name: Option<String>,
        /// The ref to pin (branch/tag/commit). Defaults to the remote default branch.
        #[arg(long = "ref")]
        git_ref: Option<String>,
        /// The owner/agent publishing the site (the cap holder). Defaults to the
        /// logged-in account's subject (`login`), matching `domains`; falls back to
        /// `operator` only when no account is connected.
        #[arg(long)]
        owner: Option<String>,
        /// The deploy-lease budget, in meter units (clone+build+publish each charge 1/step).
        #[arg(long, default_value_t = 100)]
        budget: i64,
        /// After publishing, serve the site LOCALLY over HTTP and print the real local
        /// URL (a genuine round-trip you can `curl`), instead of just recording it. The
        /// public `<name>.dregg.works` edge is a separate gateway-mount step.
        #[arg(long)]
        serve: bool,
        /// The port `--serve` binds (on `127.0.0.1`).
        #[arg(long, default_value_t = 8080)]
        port: u16,
    },
    /// Connect a cap-account identity (the chain-as-account, but delegable): bind a
    /// wallet-held `dga1_` cipherclerk credential as the developer account, or mint a
    /// fresh local one. Subsequent `deploy` / `domains` default their owner to it.
    Login {
        /// Bind an existing wallet-held credential (`dga1_…`) as the account.
        #[arg(long, conflicts_with = "new")]
        credential: Option<String>,
        /// The verifying root public key (hex) the `--credential` was minted under.
        /// Supply it so a wallet-bound login can also bind domains (without it, the
        /// wallet path can deploy but not bind domains — there is no local root to
        /// verify a binding against).
        #[arg(long, requires = "credential")]
        root: Option<String>,
        /// Mint a fresh local cap-account (a new root + a credential) for the
        /// developer onramp / demo, instead of binding a wallet credential.
        #[arg(long)]
        new: bool,
        /// The caps the minted credential grants (only with `--new`).
        #[arg(long = "cap", default_values_t = [String::from("deploy"), String::from("domains")])]
        caps: Vec<String>,
        /// Print the full `dga1_` credential (a bearer SECRET) to stdout. Off by
        /// default — the credential is redacted unless you pass this. Pass it ALONE
        /// (no `--new` / `--credential`) to reveal the CURRENT account's credential
        /// without minting a new one.
        #[arg(long)]
        show_credential: bool,
    },
    /// Bind, list, or verify a custom (BYO) domain over the dregg-domains crate —
    /// a `DomainBinding` cell, cap-gated, with DNS proof-of-control before routing.
    Domains {
        #[command(subcommand)]
        action: DomainAction,
    },
    /// The Verifiable Agent Cloud: deploy an autonomous agent with a budget + a cap
    /// bundle, run it confined (every action cap-gated + budget-metered + receipted),
    /// and get back the proof (the receipt chain) + the bound (the budget ceiling).
    Agent {
        #[command(subcommand)]
        action: AgentCommand,
    },
    /// Run a declared **execution model** over the one verified meter. The substrate is
    /// not a fixed menu of paradigms — an execution model is a point in
    /// `lifecycle × funding × authority × trigger` (see `docs/EXECUTION-MODELS.md`).
    /// The three models that drop in as declarations — `cron`, `streaming`,
    /// `escrow-bonded` — are real, receipted entry points here, not demos.
    Model {
        #[command(subcommand)]
        action: ModelCommand,
    },
    /// List my sites, leases, domains, and workloads recorded in this state dir.
    Ls,
    /// Re-verify a deployed site WITHOUT trusting the host: fetch its receipt chain
    /// + the served bytes and re-witness that the bytes match the committed content
    /// root and the receipt chain is intact. The literal "you verify, you don't
    /// trust" check a stranger runs.
    Verify {
        /// The deploy id (a prefix is enough) or the site name to verify.
        target: String,
        /// Fetch the receipt bundle from a RUNNING server over HTTP (e.g.
        /// `127.0.0.1:8080`, what `deploy --serve` binds) instead of the locally
        /// recorded bundle — the genuine non-witness read path over the wire.
        #[arg(long)]
        url: Option<String>,
        /// SELF-DEMO: flip one served byte before re-witnessing, to PROVE the check
        /// catches tampering. The verify must report `✗ MISMATCH` — and because a
        /// caught tamper is the intended outcome, the command exits 0. The
        /// "verify-don't-trust" story in one command (mirrors `dregg-agent verify
        /// --tamper`).
        #[arg(long)]
        tamper: bool,
    },
    /// Interface DIRECTLY with the live cloud's fly-compatible machines API
    /// (requires `--endpoint`): create / list / get / stop / delete machines on a
    /// remote DreggNet gateway — funded, metered, and receipted by the live node.
    Machines {
        #[command(subcommand)]
        action: MachineAction,
    },
    /// Tail / follow / search a resource's REAL runtime logs (its captured
    /// stdout/stderr), cap-scoped to the caller. Replaces the old metadata-only
    /// stub: a workload's logs are the lines its run actually produced. A deploy
    /// (no capture wired yet) still shows its recorded build metadata.
    Logs {
        /// The workload / deploy id (a prefix is enough).
        id: String,
        /// Stream new lines as they are appended (poll the durable store), like
        /// `tail -f` / `kubectl logs -f`. Ctrl-C to stop.
        #[arg(long)]
        follow: bool,
        /// Show only lines containing this substring.
        #[arg(long)]
        search: Option<String>,
        /// Show only the last N lines (0 = all). Ignored with `--search`.
        #[arg(long, default_value_t = 200)]
        tail: usize,
    },
    /// Tear down a recorded site / lease / workload / domain by id (or domain).
    Destroy {
        /// The id (deploy / lease / workload) or the domain to destroy.
        target: String,
    },
    /// Serve this CLI as an MCP (Model Context Protocol) server over JSON-RPC stdio —
    /// the agent-facing twin of `dregg-cloud`. Any MCP client (Claude, an agent
    /// runtime, an IDE) drives the SAME verifiable cloud through it: deploy/run/verify
    /// sites + budget-bounded agents, read the cloud status + cells, cap-scoped by the
    /// account credential. Each tool reuses the same library every CLI verb routes
    /// through (no second object model, no mock). Honors the global `--endpoint` (and
    /// per-call `endpoint`) for the live gateway.
    Mcp,
}

#[derive(Subcommand)]
enum DomainAction {
    /// Bind a custom domain to a published site (cap-gated) + emit the DNS challenge.
    Add {
        /// The custom domain to bind (e.g. `shop.example.com`).
        domain: String,
        /// The site `<name>` (whose `<name>.dregg.works` cell serves the bytes).
        #[arg(long)]
        site: String,
        /// Prove control by CNAME (`<domain>` → `<site>.dregg.works`) instead of TXT.
        #[arg(long)]
        cname: bool,
        /// The binding owner (the cap holder). Defaults to the logged-in account.
        #[arg(long)]
        owner: Option<String>,
    },
    /// List bound custom domains + their verification state.
    List,
    /// Verify a bound domain by supplying the DNS record the owner published.
    Verify {
        /// The domain to verify.
        domain: String,
        /// The published TXT value (for a TXT-challenge binding).
        #[arg(long, conflicts_with = "cname")]
        txt: Option<String>,
        /// The published CNAME target (for a CNAME-challenge binding).
        #[arg(long)]
        cname: Option<String>,
    },
}

#[derive(Subcommand)]
enum MachineAction {
    /// `POST /v1/apps/{app}/machines` — create (and, on a dispatch-configured
    /// gateway, run) a machine on the live cloud. Renders the gateway's funded
    /// result (the real metered outcome) or its honest refusal.
    Create {
        /// The app (tenant) to create the machine under.
        app: String,
        /// An optional machine name (the gateway auto-generates one when omitted).
        #[arg(long)]
        name: Option<String>,
        /// The workload image / artifact reference (the bridge resolves it).
        #[arg(long)]
        image: Option<String>,
        /// The guest CPU class: `shared` or `performance`.
        #[arg(long, default_value = "shared")]
        cpu_kind: String,
        /// Number of vCPUs.
        #[arg(long, default_value_t = 1)]
        cpus: u32,
        /// Memory in MiB.
        #[arg(long, default_value_t = 256)]
        memory_mb: u32,
        /// A region placement hint.
        #[arg(long)]
        region: Option<String>,
    },
    /// `GET /v1/apps/{app}/machines` — list the app's machines on the live cloud.
    List {
        /// The app (tenant) whose machines to list.
        app: String,
    },
    /// `GET /v1/apps/{app}/machines/{id}` — one machine's status on the live cloud.
    Get {
        /// The app (tenant).
        app: String,
        /// The machine id.
        id: String,
    },
    /// `POST /v1/apps/{app}/machines/{id}/stop` — reap a machine on the live cloud.
    Stop {
        /// The app (tenant).
        app: String,
        /// The machine id.
        id: String,
    },
    /// `DELETE /v1/apps/{app}/machines/{id}` — destroy a machine record on the live cloud.
    Delete {
        /// The app (tenant).
        app: String,
        /// The machine id.
        id: String,
    },
}

#[derive(Subcommand)]
enum AgentCommand {
    /// Deploy an agent with a replenishing-budget cell (the spend bound) + a cap
    /// bundle (the attenuable authority), run it confined against a mock-LLM brain,
    /// and surface the proof (the receipt chain) + the bound (the budget ceiling).
    /// A sub-agent gets an attenuated child budget + cap (it cannot exceed the parent).
    Deploy {
        /// The agent id (the meter subject + receipt identity). Defaults to a fresh id.
        #[arg(long)]
        id: Option<String>,
        /// The spend ceiling, in budget units (the hard could-have bound).
        #[arg(long, default_value_t = 50)]
        budget: i64,
        /// The budget cost charged per action.
        #[arg(long, default_value_t = 1)]
        cost: i64,
        /// A service the agent may `invoke` (repeatable). Defaults to `search` + `fetch`.
        #[arg(long = "service")]
        services: Vec<String>,
        /// A cell the agent may read+write (repeatable). Defaults to `/scratch`.
        #[arg(long = "cell")]
        cells: Vec<String>,
        /// The asset the budget is denominated in.
        #[arg(long, default_value = "DREGG")]
        asset: String,
        /// Also deploy an ATTENUATED sub-agent (half the budget, the first service
        /// only) and run it, to show a child cannot exceed the parent.
        #[arg(long)]
        subagent: bool,
        /// The brain that decides the agent's actions: `mock` (a scripted plan —
        /// the self-contained demo), `kimi` (the LIVE Kimi/Moonshot LLM over the
        /// BYO key in `~/.kimikey`), or `openai` (ANY OpenAI-compatible endpoint —
        /// point `--llm-base` at a local proxy, ollama, vLLM, OpenRouter, …). The
        /// live brains need the `live-brain` build feature.
        #[arg(long, value_enum, default_value_t = BrainArg::Mock)]
        brain: BrainArg,
        /// The OpenAI-compatible base URL the `openai`/`kimi` brain calls (e.g.
        /// `http://localhost:11434/v1` for ollama, `https://openrouter.ai/api/v1`).
        /// Defaults to OpenAI for `--brain openai`, Moonshot for `--brain kimi`.
        #[arg(long)]
        llm_base: Option<String>,
        /// The model id to request (e.g. `gpt-4o-mini`, `qwen2.5-coder:7b`).
        /// Defaults to the Kimi agentic model for `--brain kimi`; required for
        /// `--brain openai` unless your endpoint has a single default model.
        #[arg(long)]
        llm_model: Option<String>,
        /// A file holding the BYO bearer key (defaults to `~/.kimikey` for `kimi`).
        #[arg(long)]
        llm_key_file: Option<PathBuf>,
        /// An environment variable holding the BYO bearer key (e.g. `OPENAI_API_KEY`).
        /// Takes precedence over `--llm-key-file`. Omit both for a local unauthed
        /// endpoint (ollama / vLLM with auth off).
        #[arg(long)]
        llm_key_env: Option<String>,
    },
    /// Re-witness a recorded agent run WITHOUT trusting the host: re-verify the
    /// receipt chain (signed + unbroken + tamper-evident) and that the consumed
    /// budget stays under the ceiling (the bound holds). Prints ✓ / ✗.
    Verify {
        /// The agent id (a prefix is enough).
        id: String,
    },
}

/// The declared execution models invocable as real, receipted runs over the shared meter.
#[derive(Subcommand)]
enum ModelCommand {
    /// **Cron / scheduled.** A workload that fires every `--every` blocks, each firing a
    /// fresh run metered against a per-window `--budget`. A well-funded schedule runs
    /// every firing; an underfunded one throttles to its window budget (exactly-once per
    /// firing). Drops in over the shared meter — a firing is just a charge at the block.
    Cron {
        /// The model label (the workload kind).
        #[arg(long, default_value = "nightly")]
        name: String,
        /// The per-window spend ceiling.
        #[arg(long, default_value_t = 30)]
        budget: i64,
        /// Blocks between firings (the schedule granularity).
        #[arg(long, default_value_t = 100)]
        every: i64,
        /// How many firings to drive.
        #[arg(long, default_value_t = 10)]
        firings: i64,
        /// The budget cost charged per firing.
        #[arg(long, default_value_t = 1)]
        cost: i64,
        /// The isolation grade the firings run under.
        #[arg(long, default_value = "caged")]
        grade: String,
        /// The asset the budget is denominated in.
        #[arg(long, default_value = "DREGG")]
        asset: String,
    },
    /// **Streaming / long-lived.** A workload that stays up consuming a REFILLING budget:
    /// it draws each tick, is throttled (an in-band 402 — paused, not killed) when the
    /// window's headroom is momentarily gone, and resumes as the budget refills.
    Stream {
        /// The model label.
        #[arg(long, default_value = "feed")]
        name: String,
        /// The per-window spend ceiling.
        #[arg(long, default_value_t = 10)]
        budget: i64,
        /// The replenishment window, in blocks.
        #[arg(long, default_value_t = 1000)]
        period: i64,
        /// How many ticks to drive (within one window, to show throttle-then-resume).
        #[arg(long, default_value_t = 15)]
        ticks: i64,
        /// The budget cost charged per tick.
        #[arg(long, default_value_t = 1)]
        cost: i64,
        /// The asset the budget is denominated in.
        #[arg(long, default_value = "DREGG")]
        asset: String,
    },
    /// **Escrow-bonded compute market.** A payer bonds `--bond` up front; a worker runs a
    /// genuine receipted agent job; its verified verdict decides the payout — a
    /// verified-ok result RELEASES the bond to the worker, a failed/forged one REFUNDS the
    /// payer. Release is exactly-once (a bond cannot be double-paid).
    Escrow {
        /// The job label.
        #[arg(long, default_value = "render-job")]
        name: String,
        /// The bonded amount, held in escrow.
        #[arg(long, default_value_t = 100)]
        bond: i64,
        /// The party putting up the bond (the hirer).
        #[arg(long, default_value = "buyer")]
        payer: String,
        /// The party that earns the bond on a verified result (the compute provider).
        #[arg(long, default_value = "worker")]
        worker: String,
        /// The service the worker's agent invokes for the job.
        #[arg(long, default_value = "render")]
        service: String,
        /// The asset the bond is denominated in.
        #[arg(long, default_value = "DREGG")]
        asset: String,
        /// Force the result to FAIL verification (to demonstrate the refund path).
        #[arg(long)]
        fail: bool,
    },
    /// Run an execution model declared in a JSON file (the model IS data — a new model is
    /// a declaration, not code). The file is an `ExecutionModel`; cron/streaming drive a
    /// metered run, escrow-bonded settles a bond.
    Run {
        /// Path to the `ExecutionModel` JSON declaration.
        file: PathBuf,
        /// Firings/ticks to drive for a metered (cron/streaming) model.
        #[arg(long, default_value_t = 10)]
        runs: i64,
        /// The cost per firing/tick.
        #[arg(long, default_value_t = 1)]
        cost: i64,
        /// For an escrow-bonded model: force the verdict to FAIL (the refund path).
        #[arg(long)]
        fail: bool,
    },
}

#[derive(Subcommand)]
enum LeaseAction {
    /// Open + fund a (mock) execution-lease and register it.
    Open {
        /// The isolation grade the lease authorizes.
        #[arg(long, value_name = "TIER")]
        cap_tier: CapTierArg,
        /// The total metered budget to fund the lease with, in meter units.
        #[arg(long, value_name = "N")]
        budget: i64,
        /// The meter cost charged per durable step (one period). Must be > 0.
        #[arg(long, default_value_t = 1, value_name = "N")]
        per_period: i64,
        /// The asset the budget is denominated in.
        #[arg(long, default_value = "USD")]
        asset: String,
        /// The lessee tag (the renting agent).
        #[arg(long, default_value = "operator")]
        lessee: String,
    },
}

/// Which brain decides the agent's actions on `agent deploy`.
#[derive(Clone, Copy, ValueEnum)]
enum BrainArg {
    /// A scripted plan (the self-contained demo — an admitted call, an
    /// out-of-bundle refusal, then a runaway the budget bounds).
    Mock,
    /// The LIVE Kimi (Moonshot) LLM, reasoning over tool-use with the BYO key in
    /// `~/.kimikey` (needs the `live-brain` build feature).
    Kimi,
    /// ANY OpenAI-compatible endpoint (a local proxy, ollama, vLLM, OpenRouter, a
    /// harness-exposed OpenAI endpoint) — set `--llm-base` / `--llm-model` / the
    /// key source. The same chat+tool-use shape as `kimi` (needs `live-brain`).
    #[value(alias = "llm")]
    Openai,
}

/// The live-LLM brain configuration gathered from the `--brain` / `--llm-*` flags:
/// which provider shape, and the configurable base URL + model + key source that
/// point it at ANY OpenAI-compatible endpoint.
struct BrainConfig {
    brain: BrainArg,
    base: Option<String>,
    model: Option<String>,
    key_file: Option<PathBuf>,
    key_env: Option<String>,
}

/// The cap-tier a lease opens at — maps to the bridge [`CapGrade`] (the isolation grade).
#[derive(Clone, Copy, ValueEnum)]
enum CapTierArg {
    /// In-process wasm sandbox (wasmi).
    Sandboxed,
    /// Native process under seccomp + landlock.
    Caged,
    /// Hardware-isolated microVM (firecracker).
    Microvm,
}

impl CapTierArg {
    fn to_grade(self) -> CapGrade {
        match self {
            CapTierArg::Sandboxed => CapGrade::Sandboxed,
            CapTierArg::Caged => CapGrade::Caged,
            CapTierArg::Microvm => CapGrade::MicroVm,
        }
    }
}

fn grade_str(g: CapGrade) -> &'static str {
    match g {
        CapGrade::Sandboxed => "sandboxed",
        CapGrade::Caged => "caged",
        CapGrade::MicroVm => "microvm",
    }
}

fn grade_from_str(s: &str) -> Result<CapGrade> {
    Ok(match s {
        "sandboxed" => CapGrade::Sandboxed,
        "caged" => CapGrade::Caged,
        "microvm" => CapGrade::MicroVm,
        other => bail!("unknown cap-grade `{other}`"),
    })
}

/// A render-friendly label for a workload's lifecycle state.
fn state_label(s: &WorkloadState) -> String {
    match s {
        WorkloadState::Running => "running".to_string(),
        WorkloadState::Completed => "completed".to_string(),
        WorkloadState::Lapsed(why) => format!("lapsed: {why}"),
        WorkloadState::Reaped => "reaped".to_string(),
    }
}

// ---------------------------------------------------------------------------
// The cross-invocation registry: a JSON state file holding the leases that have
// been opened + the workloads that have been scheduled. `Lease`/`WorkloadState`
// are not `serde`-serializable (and live in another crate), so the CLI persists
// its own plain records and converts at the edge.
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize, Clone)]
struct LeaseRecord {
    id: String,
    lessee: String,
    cap_grade: String,
    asset: String,
    budget_units: i64,
    per_period_units: i64,
    funded: bool,
}

impl LeaseRecord {
    /// The bridge [`Lease`] this record denotes.
    fn lease(&self) -> Result<Lease> {
        Ok(Lease {
            lessee: self.lessee.clone(),
            cap_grade: grade_from_str(&self.cap_grade)?,
            asset: self.asset.clone(),
            budget_units: self.budget_units,
            per_period_units: self.per_period_units,
            funded: self.funded,
        })
    }
}

#[derive(Serialize, Deserialize, Clone)]
struct WorkloadRecord {
    id: String,
    lease_id: String,
    lessee: String,
    cap_grade: String,
    lang: String,
    source: String,
    state: String,
    machine_id: String,
    step1: Option<String>,
    step2: Option<String>,
    meter_units: i64,
}

/// A recorded deploy — the verifiable record `dregg-cloud deploy` leaves in the state dir.
#[derive(Serialize, Deserialize, Clone)]
struct DeployRecord {
    id: String,
    repo: String,
    site_name: String,
    owner: String,
    url: String,
    commit: String,
    content_root: String,
    build_plan: String,
    asset_count: usize,
    meter_units: i64,
    /// The owner signing key (hex) the publish receipt was sealed under — the trust
    /// anchor `verify` pins against (so a forged/re-signed receipt is caught). Empty
    /// for a deploy recorded before signed publishing (then it is not verifiable).
    #[serde(default)]
    signer_pubkey: String,
}

/// The connected cap-account — the `dregg-cloud login` identity. A wallet-held (or
/// freshly minted) `dga1_` credential, its derived subject, and the root pubkey
/// it verifies under. The chain-as-account made delegable: a deploy/domains turn
/// can attenuate this credential rather than share the root key.
#[derive(Serialize, Deserialize, Clone)]
struct IdentityRecord {
    /// The stable subject derived from the credential (`dregg:<16hex>`).
    subject: String,
    /// The wallet-held credential (`dga1_…`) bound as the account.
    credential: String,
    /// The root public key (hex) the credential verifies under.
    root_pubkey: String,
    /// The caps the credential grants (informational; for a minted account).
    caps: Vec<String>,
}

#[derive(Serialize, Deserialize, Default)]
struct Store {
    leases: Vec<LeaseRecord>,
    workloads: Vec<WorkloadRecord>,
    #[serde(default)]
    deploys: Vec<DeployRecord>,
    /// The connected cap-account (`dregg-cloud login`), if any.
    #[serde(default)]
    identity: Option<IdentityRecord>,
    /// The bound custom-domain cells (`dregg-cloud domains add`), the persisted
    /// `DomainBinding` set the CLI re-adopts into a registry each invocation.
    #[serde(default)]
    domains: Vec<DomainBinding>,
    /// The Verifiable Agent Cloud runs (`dregg-cloud agent deploy`): the proof+bound
    /// report of each deployed agent (parent + any sub-agent), re-witnessable by
    /// `dregg-cloud agent verify`.
    #[serde(default)]
    agents: Vec<AgentRunReport>,
}

impl Store {
    fn file(dir: &Path) -> PathBuf {
        dir.join(STATE_FILE)
    }

    fn load(dir: &Path) -> Result<Store> {
        let path = Store::file(dir);
        if !path.exists() {
            return Ok(Store::default());
        }
        let raw = std::fs::read_to_string(&path)
            .with_context(|| format!("read state {}", path.display()))?;
        serde_json::from_str(&raw).with_context(|| format!("parse state {}", path.display()))
    }

    fn save(&self, dir: &Path) -> Result<()> {
        std::fs::create_dir_all(dir)
            .with_context(|| format!("create state dir {}", dir.display()))?;
        let path = Store::file(dir);
        let raw = serde_json::to_string_pretty(self)?;
        std::fs::write(&path, raw).with_context(|| format!("write state {}", path.display()))?;
        // The state file holds the account's `dga1_` bearer credential — owner-only
        // (0600), so it never lands group/world-readable on a shared host.
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600))
                .with_context(|| format!("chmod 0600 {}", path.display()))?;
        }
        Ok(())
    }

    fn lease(&self, id: &str) -> Option<&LeaseRecord> {
        self.leases.iter().find(|l| l.id == id)
    }
}

/// Install a quiet log subscriber so a SUCCESSFUL deploy/run does not leak the
/// duroxide / durable-layer `Database locked` / activity-failure WARN noise to
/// stderr (the #1 first-impression liability — it reads as failure even when the
/// run succeeded). The default silences the noisy targets to `error`; the rest of
/// the app stays at `warn`. `RUST_LOG` is honored for opt-in verbosity (e.g.
/// `RUST_LOG=debug` to debug a deploy).
fn install_quiet_logging() {
    use tracing_subscriber::EnvFilter;
    // Default: app at `warn`, but the chatty durable/orchestration targets at
    // `error` so their benign retries (the SQLite `Database locked` contention the
    // durable layer recovers from, and activity-failure-then-retry lines) stay off
    // a clean run. A user can override the whole thing with `RUST_LOG`.
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| {
        EnvFilter::new("warn")
            .add_directive("duroxide=error".parse().expect("static directive"))
            .add_directive("dreggnet_durable=error".parse().expect("static directive"))
            .add_directive("dreggnet_bridge=error".parse().expect("static directive"))
            .add_directive("dreggnet_control=error".parse().expect("static directive"))
    });
    // `try_init` so we never panic if something already installed a subscriber.
    let _ = tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_writer(std::io::stderr)
        .try_init();
}

#[tokio::main]
async fn main() -> Result<()> {
    install_quiet_logging();
    let cli = Cli::parse();
    let endpoint = cli.endpoint.clone();
    match cli.command {
        Command::Lease { action } => match action {
            LeaseAction::Open {
                cap_tier,
                budget,
                per_period,
                asset,
                lessee,
            } => cmd_lease_open(
                &cli.state_dir,
                cap_tier.to_grade(),
                budget,
                per_period,
                &asset,
                &lessee,
            ),
        },
        Command::Run {
            lease,
            lang,
            source,
        } => cmd_run(&cli.state_dir, endpoint.as_deref(), &lease, &lang, &source).await,
        Command::Status { lease, app } => cmd_status(
            &cli.state_dir,
            endpoint.as_deref(),
            lease.as_deref(),
            app.as_deref(),
        ),
        Command::Deploy {
            repo,
            name,
            git_ref,
            owner,
            budget,
            serve,
            port,
        } => {
            cmd_deploy(
                &cli.state_dir,
                endpoint.as_deref(),
                &repo,
                name,
                git_ref,
                owner,
                budget,
                serve,
                port,
            )
            .await
        }
        Command::Machines { action } => cmd_machines(&cli.state_dir, endpoint.as_deref(), action),
        Command::Login {
            credential,
            root,
            new,
            caps,
            show_credential,
        } => cmd_login(&cli.state_dir, credential, root, new, caps, show_credential),
        Command::Domains { action } => match action {
            DomainAction::Add {
                domain,
                site,
                cname,
                owner,
            } => cmd_domains_add(&cli.state_dir, &domain, &site, cname, owner),
            DomainAction::List => cmd_domains_list(&cli.state_dir),
            DomainAction::Verify { domain, txt, cname } => {
                cmd_domains_verify(&cli.state_dir, &domain, txt, cname)
            }
        },
        Command::Agent { action } => match action {
            AgentCommand::Deploy {
                id,
                budget,
                cost,
                services,
                cells,
                asset,
                subagent,
                brain,
                llm_base,
                llm_model,
                llm_key_file,
                llm_key_env,
            } => cmd_agent_deploy(
                &cli.state_dir,
                id,
                budget,
                cost,
                services,
                cells,
                &asset,
                subagent,
                BrainConfig {
                    brain,
                    base: llm_base,
                    model: llm_model,
                    key_file: llm_key_file,
                    key_env: llm_key_env,
                },
            ),
            AgentCommand::Verify { id } => cmd_agent_verify(&cli.state_dir, &id),
        },
        Command::Model { action } => match action {
            ModelCommand::Cron {
                name,
                budget,
                every,
                firings,
                cost,
                grade,
                asset,
            } => cmd_model_cron(name, asset, budget, every, firings, cost, grade),
            ModelCommand::Stream {
                name,
                budget,
                period,
                ticks,
                cost,
                asset,
            } => cmd_model_stream(name, asset, budget, period, ticks, cost),
            ModelCommand::Escrow {
                name,
                bond,
                payer,
                worker,
                service,
                asset,
                fail,
            } => cmd_model_escrow(name, asset, bond, payer, worker, service, !fail),
            ModelCommand::Run {
                file,
                runs,
                cost,
                fail,
            } => cmd_model_run(&file, runs, cost, !fail),
        },
        Command::Ls => cmd_ls(&cli.state_dir, endpoint.as_deref()),
        Command::Verify {
            target,
            url,
            tamper,
        } => cmd_verify(&cli.state_dir, &target, url.as_deref(), tamper),
        Command::Logs {
            id,
            follow,
            search,
            tail,
        } => cmd_logs(&cli.state_dir, &id, follow, search.as_deref(), tail),
        Command::Destroy { target } => cmd_destroy(&cli.state_dir, &target),
        Command::Mcp => mcp::run(cli.state_dir.clone(), endpoint).await,
    }
}

/// Redact a bearer credential for display: keep the `dga1_` scheme + a short prefix,
/// hide the rest. So scrollback / logs never carry the full secret unless asked.
fn redact_credential(cred: &str) -> String {
    // Keep enough to recognize the token, never enough to use it.
    let shown: String = cred.chars().take(12).collect();
    format!("{shown}… (secret — hidden; rerun with --show-credential to reveal)")
}

/// `dregg-cloud login` — connect a cap-account identity (bind a wallet credential or
/// mint a fresh local one). The subject becomes the default owner for `deploy` /
/// `domains`.
fn cmd_login(
    dir: &Path,
    credential: Option<String>,
    root: Option<String>,
    new: bool,
    caps: Vec<String>,
    show_credential: bool,
) -> Result<()> {
    let mut store = Store::load(dir)?;

    // `login --show-credential` ALONE (no `--new` / `--credential`) reveals the
    // CURRENT account's credential without minting a new one — the honest "reveal
    // it" path the post-login hint points at.
    if !new && credential.is_none() {
        if show_credential {
            let id = store.identity.as_ref().ok_or_else(|| {
                anyhow!(
                    "no connected account to reveal — run `{} login --new` (or \
                     `--credential <dga1_…>`) first",
                    prog()
                )
            })?;
            println!("account {}", id.subject);
            println!("  credential {}", id.credential);
            eprintln!(
                "warning: a `dga1_` credential is a BEARER SECRET — anyone holding it acts as \
                 this account. Do not share it or paste it into logs/chat."
            );
            return Ok(());
        }
        bail!(
            "`{} login` needs `--credential <dga1_…>`, `--new`, or `--show-credential` \
             (to reveal the current account)",
            prog()
        );
    }

    // True when this login produced/persisted a credential the operator must keep
    // secret (a freshly minted root credential is a bearer key in `state.json`).
    let mut minted_secret = false;
    let identity = if let Some(cred) = credential {
        // Bind a wallet-held credential: it must decode + yield a subject.
        let subject = subject_of(&cred).ok_or_else(|| {
            anyhow!("`--credential` did not decode as a dregg `dga1_` credential")
        })?;
        // The root pubkey of a wallet credential is not recoverable from the wire;
        // the wallet holds it. Supplying `--root <hex>` records the verifying root so
        // this wallet login can ALSO bind domains (otherwise the wallet path can
        // deploy but `domains` has no local root to verify a binding against).
        let root_pubkey = match root {
            Some(hex) => {
                PublicKey::from_hex(&hex)
                    .map_err(|e| anyhow!("`--root` is not a valid public key hex: {e}"))?;
                hex
            }
            None => String::new(),
        };
        IdentityRecord {
            subject,
            credential: cred,
            root_pubkey,
            caps: Vec::new(),
        }
    } else if new {
        // Mint a fresh local cap-account: a new root + a credential granting `caps`.
        let root = RootKey::generate();
        let cred = mint_caps(&root, caps.iter().cloned(), None).encode();
        let subject = subject_of(&cred)
            .ok_or_else(|| anyhow!("minted credential did not decode (internal)"))?;
        minted_secret = true;
        IdentityRecord {
            subject,
            credential: cred,
            root_pubkey: root.public().to_hex(),
            caps,
        }
    } else {
        bail!(
            "`{} login` needs either `--credential <dga1_…>` or `--new`",
            prog()
        );
    };

    println!("logged in as {}", identity.subject);
    if !identity.caps.is_empty() {
        println!("  caps    {}", identity.caps.join(", "));
    }
    if !identity.root_pubkey.is_empty() {
        println!("  root    {}", identity.root_pubkey);
    }
    if show_credential {
        println!("  account {}", identity.credential);
    } else {
        println!("  account {}", redact_credential(&identity.credential));
    }
    // Persist with 0600 perms (Store::save) — the credential is a bearer secret.
    store.identity = Some(identity);
    store.save(dir)?;

    if minted_secret {
        eprintln!(
            "warning: a `dga1_` credential is a BEARER SECRET — anyone holding it acts as this \
             account.\n         it is stored in {} (0600); do not share it or paste it into \
             logs/chat.",
            Store::file(dir).display()
        );
    }
    if !show_credential && credential_is_local(&store) {
        eprintln!(
            "note: the credential is hidden above; reveal THIS account's credential with \
             `{} login --show-credential` (no `--new` — that would mint a different account).",
            prog()
        );
    }
    Ok(())
}

/// Whether the connected account carries a locally-minted credential (vs a
/// wallet-bound one) — used only to tailor the post-login hint.
fn credential_is_local(store: &Store) -> bool {
    store
        .identity
        .as_ref()
        .is_some_and(|id| !id.root_pubkey.is_empty())
}

/// The local cap-account's binding authority: the trusted root public key and the
/// `dga1_` credential to present. A domain bind verifies the credential under this
/// root, so a self-asserted token cannot bind. Requires a minted local account
/// (`dregg-cloud login --new`, or `--credential … --root <hex>`) — a wallet-bound
/// credential WITHOUT a supplied root carries no verifying key to bind against locally.
fn account_authority(store: &Store) -> Result<(PublicKey, String)> {
    let id = store.identity.as_ref().ok_or_else(|| {
        anyhow!(
            "domain binding needs a cap-account — run `{} login --new` first",
            prog()
        )
    })?;
    if id.root_pubkey.is_empty() {
        bail!(
            "this account is a wallet-bound credential with no local root key to verify a binding \
             against; re-login carrying the verifying root (`{p} login --credential <dga1_…> \
             --root <hex>`), or mint a local account (`{p} login --new`)",
            p = prog()
        );
    }
    let root = PublicKey::from_hex(&id.root_pubkey)
        .map_err(|e| anyhow!("stored root pubkey did not decode: {e}"))?;
    Ok((root, id.credential.clone()))
}

/// `dregg-cloud domains add` — bind a custom domain to a site as a cap-gated turn over a
/// real [`DomainRegistry`], emit the DNS challenge, and persist the binding cell.
fn cmd_domains_add(
    dir: &Path,
    domain: &str,
    site: &str,
    cname: bool,
    _owner: Option<String>,
) -> Result<()> {
    let mut store = Store::load(dir)?;
    // Binding is gated by a REAL dregg credential verified under the trusted root
    // authority (not a self-asserted token). The local cap-account supplies both:
    // the `dga1_` credential and the root pubkey it verifies under.
    let (root, credential) = account_authority(&store)?;

    // Re-adopt the persisted bindings into a fresh registry under that authority,
    // then bind. The owner is the credential's subject, so only that account can
    // later rebind/unbind this domain.
    let registry = DomainRegistry::with_authority(root);
    for b in &store.domains {
        registry.adopt(b.clone());
    }
    let method = if cname {
        ChallengeMethod::Cname
    } else {
        ChallengeMethod::Txt
    };
    let cap = DomainCap::new(credential, domain);
    let receipt = registry
        .bind(&cap, domain, site, method)
        .map_err(|e| anyhow!("bind failed: {e}"))?;

    let challenge = &receipt.challenge;
    let prog = prog();
    println!(
        "bound {} → {}.dregg.works (owner {})",
        receipt.domain, receipt.site, receipt.owner
    );
    println!("  state     pending — publish this DNS record to prove control:");
    match challenge.record_type {
        ChallengeMethod::Txt => {
            println!(
                "    TXT  {}  =  {}",
                challenge.record_name, challenge.expected_value
            );
            println!(
                "  then    {prog} domains verify {} --txt {}",
                receipt.domain, challenge.expected_value
            );
        }
        ChallengeMethod::Cname => {
            println!(
                "    CNAME  {}  →  {}",
                challenge.record_name, challenge.expected_value
            );
            println!(
                "  then    {prog} domains verify {} --cname {}",
                receipt.domain, challenge.expected_value
            );
        }
    }

    // Persist the full binding set (the new/replaced binding included).
    store.domains = registry.list();
    store.save(dir)?;
    Ok(())
}

/// `dregg-cloud domains list` — the bound custom domains + their verification state.
fn cmd_domains_list(dir: &Path) -> Result<()> {
    let store = Store::load(dir)?;
    let registry = DomainRegistry::new();
    for b in &store.domains {
        registry.adopt(b.clone());
    }
    let bindings = registry.list();
    if bindings.is_empty() {
        println!(
            "no custom domains bound yet (`{} domains add <domain> --site <name>`)",
            prog()
        );
        return Ok(());
    }
    println!(
        "{:<32}  {:<16}  {:<10}  {}",
        "DOMAIN", "SITE", "STATE", "OWNER"
    );
    for b in bindings {
        let state = match b.state {
            VerificationState::Pending => "pending",
            VerificationState::Verified => "verified",
        };
        println!(
            "{:<32}  {:<16}  {:<10}  {}",
            b.domain, b.site, state, b.owner
        );
    }
    Ok(())
}

/// `dregg-cloud domains verify` — query REAL DNS for the binding's challenge record and
/// flip the binding to Verified iff live DNS proves control.
///
/// The check resolves the binding's own `_dregg-verify.<domain>` TXT (or the
/// `<domain>` CNAME) through [`LiveDns::from_system`] — the resolver is **never**
/// seeded from client/CLI input, so claiming a domain you do not control fails (the
/// record is not actually published). The `--txt`/`--cname` args are accepted only
/// as a reminder of what the owner should have published; they are not consulted as
/// the answer.
fn cmd_domains_verify(
    dir: &Path,
    domain: &str,
    txt: Option<String>,
    cname: Option<String>,
) -> Result<()> {
    let mut store = Store::load(dir)?;
    let registry = DomainRegistry::new();
    for b in &store.domains {
        registry.adopt(b.clone());
    }
    let binding = registry.get(domain).ok_or_else(|| {
        anyhow!(
            "no binding for `{domain}` (bind it with `{} domains add`)",
            prog()
        )
    })?;
    let challenge = binding.dns_challenge();
    if txt.is_some() || cname.is_some() {
        eprintln!(
            "note: --txt/--cname are advisory only; control is proven by a live DNS query for \
             {} (not by the value you pass)",
            challenge.record_name
        );
    }

    // Resolve through LIVE DNS — a real query for the real challenge record. No
    // client-seeded resolver: an unowned domain has no such record and is refused.
    let dns =
        LiveDns::from_system().map_err(|e| anyhow!("could not start the DNS resolver: {e}"))?;
    let verified = registry.verify(domain, &dns).map_err(|e| {
        anyhow!(
            "verify failed: {e}\n  publish this DNS record, then retry:\n    {} {}  =  {}",
            match challenge.record_type {
                ChallengeMethod::Txt => "TXT",
                ChallengeMethod::Cname => "CNAME",
            },
            challenge.record_name,
            challenge.expected_value,
        )
    })?;
    println!(
        "verified {} — control proven via live DNS (turn {:?})",
        verified.domain, verified.verified_seq
    );
    println!(
        "  now routes {} → {}.dregg.works (and is cert-eligible)",
        verified.domain, verified.site
    );

    store.domains = registry.list();
    store.save(dir)?;
    Ok(())
}

/// `dregg-cloud ls` — my sites, leases, domains, and workloads in this state dir.
///
/// This is a LOCAL notebook: the records live in `state.json` under the state dir,
/// not (yet) on the public network. The header makes that explicit so nothing here
/// is mistaken for live cloud state.
fn cmd_ls(dir: &Path, endpoint: Option<&str>) -> Result<()> {
    let store = Store::load(dir)?;
    if let Some(id) = &store.identity {
        println!("account  {}", id.subject);
    } else {
        println!("account  (none — `{} login`)", prog());
    }
    println!(
        "state    {} (local notebook — these records are not yet on the public network)",
        Store::file(dir).display()
    );
    // `ls` reads the LOCAL notebook; live machine state is per-app on the gateway.
    if let Some(ep) = endpoint {
        println!(
            "endpoint {ep}  (live machines are per-app — list them with `{} machines list <app>`)",
            prog()
        );
    }

    println!("\nsites ({})", store.deploys.len());
    for d in &store.deploys {
        // The site name + the canonical public address it WILL serve at; published
        // locally today (not served on the public edge — see `deploy` output).
        println!(
            "  {:<24}  {}.dregg.works  ({})  (local — published, not served)",
            short(&d.id),
            d.site_name,
            short(&d.commit)
        );
    }

    println!("\nleases ({})", store.leases.len());
    for l in &store.leases {
        // Leases are mock records at this rung (no live funded-lease read from a node).
        println!(
            "  {:<24}  {} {}  budget {}  (mock record)",
            short(&l.id),
            l.cap_grade,
            l.lessee,
            l.budget_units
        );
    }

    println!("\ndomains ({})", store.domains.len());
    for b in &store.domains {
        let state = if b.is_verified() {
            "verified"
        } else {
            "pending"
        };
        println!("  {:<24}  → {}.dregg.works  ({state})", b.domain, b.site);
    }

    println!("\nworkloads ({})", store.workloads.len());
    for w in &store.workloads {
        println!("  {:<24}  {}  {}", short(&w.id), w.state, w.lang);
    }

    println!("\nagents ({})", store.agents.len());
    for a in &store.agents {
        println!(
            "  {:<24}  consumed {}/{} {}  ({} receipts)",
            a.agent,
            a.consumed,
            a.budget,
            a.asset,
            a.receipts.len()
        );
    }
    Ok(())
}

/// Where a deploy's re-witnessable receipt bundle is persisted under the state dir.
fn bundle_path(dir: &Path, id: &str) -> PathBuf {
    dir.join("receipts").join(format!("{id}.json"))
}

/// Persist a deploy's [`SiteReceiptBundle`] (owner key + signed receipt + served
/// content) so `dregg-cloud verify` can re-witness it offline.
fn save_bundle(dir: &Path, id: &str, bundle: &SiteReceiptBundle) -> Result<()> {
    let path = bundle_path(dir, id);
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .with_context(|| format!("create receipts dir {}", parent.display()))?;
    }
    let raw = serde_json::to_vec_pretty(bundle)?;
    std::fs::write(&path, raw).with_context(|| format!("write bundle {}", path.display()))?;
    Ok(())
}

/// Load a deploy's persisted [`SiteReceiptBundle`] by id.
fn load_bundle(dir: &Path, id: &str) -> Result<SiteReceiptBundle> {
    let path = bundle_path(dir, id);
    let raw =
        std::fs::read(&path).with_context(|| format!("read receipt bundle {}", path.display()))?;
    serde_json::from_slice(&raw).with_context(|| format!("parse receipt bundle {}", path.display()))
}

/// `dregg-cloud verify <target>` — re-verify a deployed site WITHOUT trusting the host.
///
/// Fetches the site's receipt chain + the served bytes (from the locally recorded
/// bundle, or `--url` over HTTP from a running server) and re-witnesses, against the
/// owner's pinned key, that (1) the receipt chain verifies — signed + unbroken +
/// tamper-evident, (2) the served bytes re-hash to the receipt's committed content
/// root (a lying host that flipped a byte is caught), and (3) the source-commitment
/// manifest matches the recorded deploy commit. Prints a clear ✓ / ✗.
fn cmd_verify(dir: &Path, target: &str, url: Option<&str>, tamper: bool) -> Result<()> {
    let store = Store::load(dir)?;
    let deploy = store
        .deploys
        .iter()
        .find(|d| d.id.starts_with(target) || d.site_name == target)
        .ok_or_else(|| anyhow!("no deploy matching `{target}` (try `{} ls`)", prog()))?;

    if deploy.signer_pubkey.is_empty() {
        bail!(
            "deploy `{}` was recorded without a signed receipt, so it is not re-witnessable; \
             re-run `{} deploy` to produce a verifiable bundle",
            short(&deploy.id),
            prog()
        );
    }
    let expected_signer = parse_hex32(&deploy.signer_pubkey)
        .ok_or_else(|| anyhow!("recorded signer pubkey did not decode as 32-byte hex"))?;

    // Fetch the bundle: over the wire from a running server (`--url`, the genuine
    // non-witness read path), else from the locally recorded bundle.
    let mut bundle = match url {
        Some(addr) => {
            let host = format!("{}.dregg.works", deploy.site_name);
            println!(
                "fetching the receipt bundle from http://{addr}{} (Host: {host}) ...",
                dreggnet_webapp::SITE_RECEIPT_PATH
            );
            fetch_site_bundle(addr, &host)
                .map_err(|e| anyhow!("fetch receipt bundle from {addr}: {e}"))?
                .ok_or_else(|| {
                    anyhow!(
                        "the server at {addr} served no signed receipt for `{}`",
                        deploy.site_name
                    )
                })?
        }
        None => load_bundle(dir, &deploy.id)?,
    };

    // SELF-DEMO: flip one served byte so the bytes no longer re-hash to the
    // committed content_root. The verify below MUST catch it (✗ MISMATCH). A caught
    // tamper is the INTENDED outcome, so `--tamper` exits 0 — the proof, demonstrated.
    if tamper {
        let flipped = flip_one_served_byte(&mut bundle);
        match flipped {
            Some(path) => println!(
                "[tamper] flipped one byte of the served asset `{path}` — the verify must now catch it\n"
            ),
            None => {
                println!("[tamper] the bundle has no served bytes to flip; nothing to demonstrate");
                return Ok(());
            }
        }
    }

    match verify_site_bundle(&bundle, Some(expected_signer)) {
        Ok(v) => {
            if tamper {
                // A tamper that slipped through is a REAL failure of the check.
                bail!(
                    "verification PASSED a tampered bundle — the tamper check did not bite (this \
                     is a defect)"
                );
            }
            println!("✓ verified: served bytes match the committed root, receipt chain intact");
            println!("  site         {}", v.name);
            println!("  owner        {}", v.owner);
            println!("  content-root {}", v.content_root);
            println!("  assets       {}", v.asset_count);
            println!("  signer       {}", deploy.signer_pubkey);
            match &v.commit {
                Some(commit) => {
                    println!("  commit       {commit}");
                    if *commit != deploy.commit {
                        println!(
                            "✗ MISMATCH: the served source-commitment manifest names commit \
                             {commit}, but the recorded deploy is {}",
                            deploy.commit
                        );
                        bail!("source-commitment manifest does not match the recorded deploy");
                    }
                    println!(
                        "  (the source-commitment manifest matches the recorded deploy commit)"
                    );
                }
                None => println!("  commit       (no deploy manifest committed in the content)"),
            }
            Ok(())
        }
        Err(e) => {
            println!("✗ MISMATCH: {e}");
            if tamper {
                // The check BIT the flipped byte — exactly what `--tamper` proves.
                println!(
                    "\n✓ the tamper was CAUGHT — the served bytes no longer re-witness to the \
                     committed root. The proof does not lie."
                );
                return Ok(());
            }
            bail!("verification failed — the served bytes/receipt do not re-witness");
        }
    }
}

/// Flip one byte of the first served asset in a bundle (for the `verify --tamper`
/// self-demo), returning the asset path that was tampered. `None` if there are no
/// served bytes to flip.
fn flip_one_served_byte(bundle: &mut SiteReceiptBundle) -> Option<String> {
    let (path, asset) = bundle
        .content
        .assets
        .iter_mut()
        .find(|(_, a)| !a.body.is_empty())?;
    asset.body[0] ^= 0x01;
    Some(path.clone())
}

/// The state-dir subdirectory holding the durable per-tenant log store (the
/// `LogSink` root). The `run` capture writes here; `logs` reads from here.
const LOGS_SUBDIR: &str = "logs";

/// Open the durable per-tenant log store under the state dir.
fn logs_sink(dir: &Path) -> Result<LogSink> {
    LogSink::open(dir.join(LOGS_SUBDIR)).map_err(|e| anyhow!("open log store: {e}"))
}

/// Resolve a resource-id prefix to `(full_id, owner)` from the workload registry,
/// then (for capture seams not in that registry) the captured-log census.
fn resolve_logged_resource(store: &Store, sink: &LogSink, id: &str) -> Option<(String, String)> {
    if let Some(w) = store.workloads.iter().find(|w| w.id.starts_with(id)) {
        return Some((w.id.clone(), w.lessee.clone()));
    }
    if let Ok(resources) = sink.resources() {
        if let Some(full) = resources.into_iter().find(|r| r.starts_with(id)) {
            // The owner is recorded on the lines; the requester is checked against
            // it by the sink. Use the logged-in subject as the owner hint so a
            // local read scopes to the caller.
            let owner = store
                .identity
                .as_ref()
                .map(|i| i.subject.clone())
                .unwrap_or_default();
            return Some((full, owner));
        }
    }
    None
}

/// Render one captured log line: `seq ts out|err  text`.
fn print_log_line(l: &LogLine) {
    println!(
        "{:>6} {:<13} {}  {}",
        l.seq,
        l.ts_millis,
        l.stream.label(),
        l.line
    );
}

/// `dregg-cloud logs <resource> [--follow] [--search q] [--tail n]` — the REAL
/// runtime logs of a workload (its captured stdout/stderr), cap-scoped to the
/// caller. A deploy (capture is a named seam) still shows its build metadata.
fn cmd_logs(dir: &Path, id: &str, follow: bool, search: Option<&str>, tail: usize) -> Result<()> {
    let store = Store::load(dir)?;
    let sink = logs_sink(dir)?;

    if let Some((resource, owner)) = resolve_logged_resource(&store, &sink, id) {
        // The cap-scope requester: the logged-in subject if any, else the owner
        // (local single-tenant mode reads its own logs). A DIFFERENT logged-in
        // subject than the owner is refused by the sink — the cap-scoping teeth.
        let requester = store
            .identity
            .as_ref()
            .map(|i| i.subject.clone())
            .unwrap_or_else(|| owner.clone());

        // Read the captured logs (search filters; otherwise the tail window).
        let read = if let Some(q) = search {
            sink.search(&resource, q, &requester)
        } else {
            sink.tail(&resource, tail, &requester)
        };

        match read {
            Ok(lines) => {
                println!(
                    "logs {resource} ({} line{})",
                    lines.len(),
                    if lines.len() == 1 { "" } else { "s" }
                );
                for l in &lines {
                    print_log_line(l);
                }
                if follow {
                    follow_logs(&sink, &resource, &requester, lines.last().map(|l| l.seq))?;
                }
                return Ok(());
            }
            Err(LogError::Forbidden {
                owner, requester, ..
            }) => {
                bail!(
                    "forbidden: resource `{resource}` is owned by `{owner}`, not `{requester}` \
                     — you can only read your own logs"
                )
            }
            Err(LogError::NotFound(_)) => {
                // No captured logs yet (e.g. a workload run before capture was
                // wired). Fall back to the recorded step metadata, clearly named.
                if let Some(w) = store.workloads.iter().find(|w| w.id == resource) {
                    println!(
                        "workload {} (no captured runtime logs yet — step metadata)",
                        w.id
                    );
                    println!("  lease    {} (lessee {})", w.lease_id, w.lessee);
                    println!("  source   lang={} {}", w.lang, w.source);
                    println!("  state    {}", w.state);
                    if let Some(s1) = &w.step1 {
                        println!("  output   {s1}");
                    }
                    if let Some(s2) = w.step2.as_deref().filter(|s| !s.is_empty()) {
                        println!("  output2  {s2}");
                    }
                    println!("  meter    {} units", w.meter_units);
                    return Ok(());
                }
                bail!("no captured logs for `{resource}`")
            }
            Err(e) => bail!("read logs: {e}"),
        }
    }

    // A deploy: runtime-log capture for the build is a named seam (the deploy lane
    // owns the clone/build child stdout); for now show the recorded build metadata.
    if let Some(d) = store.deploys.iter().find(|d| d.id.starts_with(id)) {
        println!(
            "deploy {} (build metadata — runtime-log capture is a named seam)",
            d.id
        );
        println!("  repo         {}", d.repo);
        println!("  url          {}", d.url);
        println!("  commit       {}", d.commit);
        println!("  build-plan   {}", d.build_plan);
        println!("  content-root {}", d.content_root);
        println!("  assets       {}", d.asset_count);
        println!("  meter        {} units", d.meter_units);
        return Ok(());
    }

    bail!(
        "no workload or deploy matching `{id}` (try `{} ls`)",
        prog()
    )
}

/// Stream new lines for a resource as they are appended, by polling the durable
/// store (`since`). Cross-process `tail -f`: the writer is another process (a
/// run / server), and this re-reads the store each tick. Runs until interrupted.
///
/// `from_seq` is the highest seq already printed by the preceding tail (so we do
/// not reprint it); `None` means nothing was shown and we stream from the start.
fn follow_logs(
    sink: &LogSink,
    resource: &str,
    requester: &str,
    from_seq: Option<u64>,
) -> Result<()> {
    let mut seen = from_seq;
    loop {
        // When nothing has been seen, `tail(0)` gets the whole log (including
        // seq 0); afterwards `since(seen)` gets only the newer lines.
        let fresh = match seen {
            Some(s) => sink.since(resource, s, requester),
            None => sink.tail(resource, 0, requester),
        };
        let fresh = match fresh {
            Ok(lines) => lines,
            Err(LogError::NotFound(_)) => Vec::new(),
            Err(e) => bail!("follow logs: {e}"),
        };
        for l in &fresh {
            print_log_line(l);
            seen = Some(l.seq);
        }
        std::thread::sleep(std::time::Duration::from_millis(500));
    }
}

/// `dregg-cloud destroy <target>` — remove a recorded site / lease / workload, or a
/// bound domain, by id (prefix) or domain name.
fn cmd_destroy(dir: &Path, target: &str) -> Result<()> {
    let mut store = Store::load(dir)?;
    let mut removed = Vec::new();

    store.deploys.retain(|d| {
        let hit = d.id.starts_with(target) || d.site_name == target;
        if hit {
            removed.push(format!("site {} ({})", d.site_name, d.url));
        }
        !hit
    });

    store.domains.retain(|b| {
        let hit = b.domain == target;
        if hit {
            removed.push(format!("domain {}", b.domain));
        }
        !hit
    });

    let mut dropped_leases = Vec::new();
    store.leases.retain(|l| {
        let hit = l.id.starts_with(target);
        if hit {
            removed.push(format!("lease {}", l.id));
            dropped_leases.push(l.id.clone());
        }
        !hit
    });

    store.workloads.retain(|w| {
        let hit = w.id.starts_with(target) || dropped_leases.iter().any(|l| *l == w.lease_id);
        if hit {
            removed.push(format!("workload {}", w.id));
        }
        !hit
    });

    if removed.is_empty() {
        bail!(
            "nothing matching `{target}` to destroy (try `{} ls`)",
            prog()
        );
    }
    store.save(dir)?;
    for r in &removed {
        println!("destroyed {r}");
    }
    Ok(())
}

/// `dregg-cloud agent deploy` — the Verifiable Agent Cloud, runnable in one command.
///
/// Deploys an agent with (a) a replenishing-budget cell (the spend bound) and (b) a
/// cap bundle (the attenuable authority), then runs it confined against a mock-LLM
/// brain: every action is cap-gated (an out-of-bundle invoke is REFUSED), metered
/// (drawn from the budget cell, refused when exhausted — the runaway is contained),
/// and receipted (the chain). Surfaces the PROOF (the receipt chain, re-witnessable
/// via `agent verify`) + the BOUND (the budget ceiling; un-drawn headroom = the hard
/// could-have bound). With `--subagent`, also deploys an ATTENUATED child and shows
/// it cannot exceed the parent.
#[allow(clippy::too_many_arguments)]
fn cmd_agent_deploy(
    dir: &Path,
    id: Option<String>,
    budget: i64,
    cost: i64,
    services: Vec<String>,
    cells: Vec<String>,
    asset: &str,
    subagent: bool,
    brain_cfg: BrainConfig,
) -> Result<()> {
    if budget <= 0 {
        bail!("--budget must be > 0 (got {budget})");
    }
    if cost <= 0 {
        bail!("--cost must be > 0 (got {cost})");
    }
    // Sensible defaults so the demo is self-contained.
    let services = if services.is_empty() {
        vec!["search".to_string(), "fetch".to_string()]
    } else {
        services
    };
    let cells = if cells.is_empty() {
        vec!["/scratch".to_string()]
    } else {
        cells
    };
    let id = id.unwrap_or_else(|| format!("agent:{}", &uuid::Uuid::new_v4().to_string()[..8]));

    // The cloud holds the root authority + the shared meter.
    let cloud = AgentCloud::new();
    let mut spec = AgentSpec::new(&id, budget);
    spec.asset = asset.to_string();
    spec.cost_per_action = cost;
    spec.services = services.clone();
    spec.cells = cells.clone();
    let handle = cloud
        .deploy(&spec)
        .map_err(|e| anyhow!("deploy failed: {e}"))?;

    println!("deployed {id}");
    println!("  budget       {budget} {asset} (cost {cost}/action)");
    println!("  cap bundle   {}", handle.caps.join(", "));

    let svc0 = &services[0];
    let cell0 = &cells[0];

    let report = match brain_cfg.brain {
        BrainArg::Mock => {
            println!(
                "running confined against a mock-LLM brain (the scripted path; the live LLM brain"
            );
            println!(
                "is `--brain kimi` / `--brain openai`, the same cap/budget/receipt seam) ...\n"
            );
            // The mock-LLM plan: an admitted invoke + cell-write, an OUT-OF-BUNDLE
            // invoke (cap-refused), then a runaway of repeated invokes (budget-bounded).
            let mut plan = vec![
                AgentAction::Invoke {
                    service: svc0.clone(),
                },
                AgentAction::CellWrite {
                    path: cell0.clone(),
                    value: "agent-scratch".to_string(),
                },
                AgentAction::Invoke {
                    service: "exfiltrate".to_string(),
                },
            ];
            let runaway = budget / cost + 5;
            for _ in 0..runaway {
                plan.push(AgentAction::Invoke {
                    service: svc0.clone(),
                });
            }
            cloud.run(&handle, &mut PlannedBrain::new(plan))
        }
        BrainArg::Kimi | BrainArg::Openai => {
            run_llm_brain(&cloud, &handle, &services, &cells, &brain_cfg)?
        }
    };
    print_agent_report(&report);

    let mut store = Store::load(dir)?;
    store.agents.retain(|a| a.agent != report.agent);
    store.agents.push(report);

    if subagent {
        // An attenuated child: half the budget, only the FIRST service.
        let child_id = format!("{id}/child");
        let mut child_spec = AgentSpec::new(&child_id, (budget / 2).max(1));
        child_spec.asset = asset.to_string();
        child_spec.cost_per_action = cost;
        child_spec.services = vec![svc0.clone()];
        let child = cloud
            .deploy_subagent(&handle, &child_spec)
            .map_err(|e| anyhow!("sub-agent deploy failed: {e}"))?;

        println!("\nsub-agent {child_id} (attenuated off the parent):");
        println!(
            "  budget       {} {asset}  (≤ parent {budget})",
            child.budget
        );
        println!("  cap bundle   {}  (⊆ parent)", child.caps.join(", "));

        // The child runs a runaway + a parent-only service attempt (cap-refused).
        let child_runaway = child.budget / cost + 3;
        let mut child_plan: Vec<AgentAction> = (0..child_runaway)
            .map(|_| AgentAction::Invoke {
                service: svc0.clone(),
            })
            .collect();
        if let Some(parent_only) = services.get(1) {
            child_plan.push(AgentAction::Invoke {
                service: parent_only.clone(),
            });
        }
        let child_report = cloud.run(&child, &mut PlannedBrain::new(child_plan));
        print_agent_report(&child_report);
        store.agents.retain(|a| a.agent != child_report.agent);
        store.agents.push(child_report);
    }

    store.save(dir)?;
    println!("\nverify it    re-witness the run WITHOUT trusting the host:");
    println!("             {} agent verify {id}", prog());
    Ok(())
}

/// Run a deployed agent against a LIVE OpenAI-compatible LLM brain: the model
/// reasons over tool-use, each decided action cap-gated + metered + receipted by
/// the same braid as the mock path. The brain is PROVIDER-AGNOSTIC — `--brain kimi`
/// defaults to Moonshot + `~/.kimikey`; `--brain openai` (alias `llm`) points at
/// ANY OpenAI-compatible base via `--llm-base` / `--llm-model` / `--llm-key-file` /
/// `--llm-key-env` (a local proxy, ollama, vLLM, OpenRouter, …). The BYO key reaches
/// only the provider. Behind the `live-brain` feature (the real HTTP transport).
#[cfg(feature = "live-brain")]
fn run_llm_brain(
    cloud: &AgentCloud,
    handle: &dreggnet_exec::agent::AgentHandle,
    services: &[String],
    cells: &[String],
    cfg: &BrainConfig,
) -> Result<AgentRunReport> {
    use dreggnet_exec::agent_toolkit::{HealthSnapshot, Toolkit};
    use dreggnet_exec::openai_compat::{
        DEFAULT_KIMI_ENDPOINT, DEFAULT_KIMI_MODEL, DEFAULT_OPENAI_BASE, LiveOpenAICompatCaller,
        OpenAICompatBrain, ProviderKey, chat_completions_url,
    };

    // The provider shape sets the defaults; the `--llm-*` flags override.
    let is_kimi = matches!(cfg.brain, BrainArg::Kimi);
    let provider = if is_kimi { "moonshot" } else { "openai-compat" };

    // (1) Endpoint = the configured base (+ the chat route), or the provider default.
    let endpoint = match &cfg.base {
        Some(base) => chat_completions_url(base),
        None if is_kimi => DEFAULT_KIMI_ENDPOINT.to_string(),
        None => chat_completions_url(DEFAULT_OPENAI_BASE),
    };

    // (2) Model = `--llm-model`, or the Kimi agentic model for `--brain kimi`.
    let model = match &cfg.model {
        Some(m) => m.clone(),
        None if is_kimi => DEFAULT_KIMI_MODEL.to_string(),
        None => bail!(
            "`--brain openai` needs a model: pass `--llm-model <name>` \
             (e.g. --llm-model gpt-4o-mini, --llm-model qwen2.5-coder:7b)"
        ),
    };

    // (3) Key source: `--llm-key-env` > `--llm-key-file` > the provider default.
    // For `kimi` the default is `~/.kimikey`; for `openai` it is `OPENAI_API_KEY`
    // if set, else UNAUTHENTICATED (a local ollama/vLLM with auth off — no bearer).
    let key = if let Some(var) = &cfg.key_env {
        ProviderKey::from_env(provider, var)
            .ok_or_else(|| anyhow!("env var `{var}` is unset or empty"))?
    } else if let Some(path) = &cfg.key_file {
        ProviderKey::from_file(provider, path)
            .ok_or_else(|| anyhow!("no key at {} (file missing or empty)", path.display()))?
    } else if is_kimi {
        ProviderKey::from_file("moonshot", dirs_kimikey()?)
            .ok_or_else(|| anyhow!("no Kimi key at ~/.kimikey (BYO the Moonshot key)"))?
    } else {
        ProviderKey::from_env(provider, "OPENAI_API_KEY")
            .unwrap_or_else(ProviderKey::unauthenticated)
    };

    let auth = if key.is_authenticated() {
        "the BYO key reaches only the provider"
    } else {
        "no auth (local endpoint)"
    };
    println!("running confined against the LIVE OpenAI-compatible LLM brain");
    println!("  endpoint   {endpoint}");
    println!("  model      {model}");
    println!("  auth       {auth}; every tool-call is cap-gated, metered, receipted ...\n");

    // A toolkit so an admitted `invoke` does real work; an unregistered granted
    // service still returns a receipted (honest) "no tool" result.
    let toolkit = Toolkit::new()
        .with_check_health("check_health", || {
            HealthSnapshot::healthy("node up · 0 divergence")
        })
        .with_verify_deploy("verify_deploy", || {
            Ok("served bytes match the committed root".to_string())
        });

    let task = format!(
        "You are deployed with the services [{}] and cells [{}]. Check the node is \
         healthy, verify the deploy if you can, then finish.",
        services.join(", "),
        cells.join(", ")
    );
    let mut brain = OpenAICompatBrain::new(
        task,
        services.to_vec(),
        cells.to_vec(),
        key,
        endpoint,
        model,
        LiveOpenAICompatCaller::new(),
    )
    .with_step_cap(12);
    let report = cloud.run_with_toolkit(handle, &mut brain, &toolkit);
    if !brain.key_reached_provider() {
        println!("(the live call did not complete — endpoint unreachable, model rejected, or key");
        println!(
            " refused; the brain fail-closed; the run below is an empty but sound receipt chain)\n"
        );
    }
    Ok(report)
}

/// The conventional `~/.kimikey` path (the `kimi`-brain default key file).
#[cfg(feature = "live-brain")]
fn dirs_kimikey() -> Result<PathBuf> {
    dreggnet_exec::openai_compat::kimi_key_path()
        .ok_or_else(|| anyhow!("cannot resolve ~/.kimikey (no $HOME)"))
}

/// Without the `live-brain` feature the live transport is not linked — `--brain
/// kimi`/`openai` bails with a rebuild hint (the std-only build stays HTTP/TLS-free).
#[cfg(not(feature = "live-brain"))]
fn run_llm_brain(
    _cloud: &AgentCloud,
    _handle: &dreggnet_exec::agent::AgentHandle,
    _services: &[String],
    _cells: &[String],
    _cfg: &BrainConfig,
) -> Result<AgentRunReport> {
    bail!(
        "the live LLM brains need the HTTP transport: rebuild with `--features live-brain` \
         (e.g. `cargo run -p dreggnet-cli --features live-brain -- agent deploy --brain openai \
         --llm-base http://localhost:11434/v1 --llm-model qwen2.5-coder:7b`)"
    )
}

/// Print an agent run's proof + bound.
fn print_agent_report(report: &AgentRunReport) {
    println!("{}", report.agent);
    println!(
        "  ✓ admitted      {:>4} actions  (cap ✓ · drawn from budget · receipted)",
        report.admitted
    );
    println!(
        "  ⊘ cap-refused   {:>4} actions  (outside the cap bundle — never reached)",
        report.cap_refused
    );
    println!(
        "  ⊘ budget-bound  {:>4} actions  (over the ceiling — the runaway is contained)",
        report.budget_refused
    );
    let tip = report
        .tip()
        .map(|h| hex32(&h))
        .unwrap_or_else(|| "(none)".to_string());
    let pct = if report.budget > 0 {
        report.consumed * 100 / report.budget
    } else {
        0
    };
    println!("  proof  receipt chain: {} receipts", report.receipts.len());
    println!("         tip    {tip}");
    println!("         signer {}", hex32(&report.signer));
    println!(
        "  bound  consumed {} / {} {} ({pct}% of the ceiling)",
        report.consumed, report.budget, report.asset
    );
    println!(
        "         headroom {} {} un-drawn  (the hard could-have bound — un-exercised authority)",
        report.headroom, report.asset
    );
}

/// `dregg-cloud agent verify <id>` — re-witness a recorded agent run.
fn cmd_agent_verify(dir: &Path, id: &str) -> Result<()> {
    let store = Store::load(dir)?;
    let report = store
        .agents
        .iter()
        .find(|a| a.agent == id || a.agent.starts_with(id))
        .ok_or_else(|| anyhow!("no agent run matching `{id}` (try `{} ls`)", prog()))?;

    match verify_agent_run(report) {
        Ok(v) => {
            println!("✓ verified: receipt chain intact, consumed stays under the ceiling");
            println!("  agent     {}", report.agent);
            println!("  actions   {} admitted (re-witnessed)", v.actions);
            println!("  consumed  {} / {} {}", v.consumed, v.budget, report.asset);
            println!(
                "  headroom  {} {} un-drawn  (the proven could-have bound)",
                v.headroom, report.asset
            );
            println!("  signer    {}", hex32(&report.signer));
            Ok(())
        }
        Err(e) => {
            println!("✗ MISMATCH: {e}");
            bail!("agent run did not re-witness — the proof or the bound failed");
        }
    }
}

// ---------------------------------------------------------------------------
// `dregg-cloud model …` — declared execution models as real, receipted runs.
// ---------------------------------------------------------------------------

/// Print a [`ModelRun`](dreggnet_exec::model::ModelRun) receipt as JSON + a human summary.
fn print_model_run(model: &ExecutionModel, run: &dreggnet_exec::model::ModelRun) -> Result<()> {
    println!("{}", serde_json::to_string_pretty(run)?);
    println!();
    println!("✓ ran declared model `{}` ({})", run.name, run.lifecycle);
    println!("  funding   {:?}", model.funding);
    println!("  admitted  {} firing(s)", run.admitted);
    if run.throttled > 0 {
        println!(
            "  throttled {} (in-band 402 — paused, not killed)",
            run.throttled
        );
    }
    println!("  drawn     {} {}", run.units_drawn, run.asset);
    if let Some(s) = &run.settlement {
        println!("  payout    {s:?}");
    }
    Ok(())
}

/// `dregg-cloud model cron` — drive a scheduled model over the shared meter.
fn cmd_model_cron(
    name: String,
    asset: String,
    budget: i64,
    every: i64,
    firings: i64,
    cost: i64,
    grade: String,
) -> Result<()> {
    let model = ExecutionModel::cron(name, asset, budget, every, grade);
    let meter = ReplenishingMeter::new();
    let subject = model.name.clone();
    let run = model
        .run_metered(&meter, &subject, firings, cost, every, 0)
        .map_err(|e| anyhow!("cron run failed: {e}"))?;
    print_model_run(&model, &run)
}

/// `dregg-cloud model stream` — drive a streaming model over a refilling budget.
fn cmd_model_stream(
    name: String,
    asset: String,
    budget: i64,
    period: i64,
    ticks: i64,
    cost: i64,
) -> Result<()> {
    // A refilling budget that returns the whole window's chunk each period.
    let terms = BudgetTerms::new(asset, budget, period, budget, 1, 0);
    let model = ExecutionModel::streaming(name, terms, vec!["invoke:emit".into()]);
    let meter = ReplenishingMeter::new();
    let subject = model.name.clone();
    // block_step 0: all ticks in one window, so a burst throttles (then would resume).
    let run = model
        .run_metered(&meter, &subject, ticks, cost, 0, 100)
        .map_err(|e| anyhow!("stream run failed: {e}"))?;
    print_model_run(&model, &run)
}

/// `dregg-cloud model escrow` — bond a job, run a genuine receipted agent, settle the bond
/// on the verified verdict.
fn cmd_model_escrow(
    name: String,
    asset: String,
    bond: i64,
    payer: String,
    worker: String,
    service: String,
    want_ok: bool,
) -> Result<()> {
    let model = ExecutionModel::escrow_bonded(
        name.clone(),
        asset,
        bond,
        payer,
        worker,
        vec![format!("invoke:{service}")],
    );

    // Run the hired work as a genuine receipted agent run; its receipt chain is the
    // verified verdict that decides the payout (unless `--fail` forces a refund).
    let cloud = AgentCloud::from_seed([42u8; 32]);
    let handle = cloud
        .deploy(&AgentSpec::new(format!("worker:{name}"), 10).with_service(&service))
        .map_err(|e| anyhow!("worker agent deploy failed: {e}"))?;
    let plan = vec![AgentAction::Invoke { service }];
    let report = cloud.run(&handle, &mut PlannedBrain::new(plan));
    let verified_ok = want_ok && verify_agent_run(&report).is_ok();

    let meter = ReplenishingMeter::new();
    let run = model
        .run_escrow(&meter, &format!("escrow:{name}"), 0, verified_ok)
        .map_err(|e| anyhow!("escrow settle failed: {e}"))?;
    print_model_run(&model, &run)
}

/// `dregg-cloud model run <file>` — run an `ExecutionModel` declared in JSON.
fn cmd_model_run(file: &Path, runs: i64, cost: i64, want_ok: bool) -> Result<()> {
    use dreggnet_exec::model::Funding;
    let text = std::fs::read_to_string(file)
        .map_err(|e| anyhow!("read model declaration {}: {e}", file.display()))?;
    let model: ExecutionModel =
        serde_json::from_str(&text).map_err(|e| anyhow!("bad ExecutionModel JSON: {e}"))?;
    let meter = ReplenishingMeter::new();
    let subject = model.name.clone();

    let run = match &model.funding {
        Funding::EscrowBonded { .. } => model
            .run_escrow(&meter, &format!("escrow:{subject}"), 0, want_ok)
            .map_err(|e| anyhow!("escrow settle failed: {e}"))?,
        _ => {
            // A scheduled model fires one window apart; anything else ticks in-window.
            let block_step = match model.lifecycle {
                dreggnet_exec::model::Lifecycle::Scheduled { every_blocks } => every_blocks,
                _ => 0,
            };
            model
                .run_metered(&meter, &subject, runs, cost, block_step, 0)
                .map_err(|e| anyhow!("metered run failed: {e}"))?
        }
    };
    print_model_run(&model, &run)
}

/// A short id for table display (first 8 chars).
fn short(id: &str) -> &str {
    &id[..id.len().min(8)]
}

/// `dregg-cloud lease open` — open + fund a (mock) execution-lease and register it.
fn cmd_lease_open(
    dir: &Path,
    grade: CapGrade,
    budget: i64,
    per_period: i64,
    asset: &str,
    lessee: &str,
) -> Result<()> {
    if per_period <= 0 {
        bail!("--per-period must be > 0 (got {per_period})");
    }
    if budget < 0 {
        bail!("--budget must be >= 0 (got {budget})");
    }

    let id = uuid::Uuid::new_v4().to_string();
    let record = LeaseRecord {
        id: id.clone(),
        lessee: lessee.to_string(),
        cap_grade: grade_str(grade).to_string(),
        asset: asset.to_string(),
        budget_units: budget,
        per_period_units: per_period,
        funded: true,
    };

    // The record must denote a genuinely active bridge lease (the scheduler refuses an
    // inactive one before provisioning any machine).
    let lease = record.lease()?;
    if !lease.is_active() {
        bail!(
            "opened lease is not active (funded={}, per_period={per_period}, budget={budget})",
            lease.funded
        );
    }
    let tier = lease.tier_binding().tier;

    let mut store = Store::load(dir)?;
    store.leases.push(record);
    store.save(dir)?;

    println!("lease opened: {id}");
    println!("  lessee     {lessee}");
    println!("  cap-grade  {grade} (tier {tier:?})");
    println!("  asset      {asset}");
    println!("  budget     {budget} units ({per_period}/step)");
    println!("  funded     true");
    Ok(())
}

/// The account credential to present as the live-cloud bearer, if logged in.
fn bearer_of(store: &Store) -> Option<String> {
    store.identity.as_ref().map(|i| i.credential.clone())
}

/// Whether a lapse reason names a genuine budget/lease lapse (vs a program/workflow
/// fault). A budget lapse should be blamed on the budget; anything else must surface
/// the real error rather than misdiagnosing it as a budget problem.
fn is_budget_lapse(why: &str) -> bool {
    let w = why.to_ascii_lowercase();
    w.contains("budget") || w.contains("over-budget") || w.contains("over budget")
}

/// Render a single-machine outcome from the live cloud, honestly distinguishing a
/// funded run (200 + the metered result) from the gateway's refusal. `verb` names the
/// CLI action for the error message. Returns `Err` on a refusal so the process exits
/// non-zero (the caller asked the live cloud to do work and it declined).
fn render_machine_outcome(outcome: MachineOutcome, verb: &str) -> Result<()> {
    match outcome {
        MachineOutcome::Ok(m) => {
            print_machine(&m, true);
            Ok(())
        }
        MachineOutcome::Refused { status, message } => {
            println!("✗ the live cloud refused the {verb} (HTTP {status}):");
            println!("    {message}");
            bail!("live-cloud {verb} refused (HTTP {status})");
        }
    }
}

/// Print a fly-compatible machine record + (when present) its real metered dispatch
/// result from the live node.
fn print_machine(m: &cloud::Machine, detail: bool) {
    println!("✓ machine {}", m.id);
    if !m.name.is_empty() {
        println!("  name      {}", m.name);
    }
    println!("  state     {}", m.state);
    if detail && !m.region.is_empty() {
        println!("  region    {}", m.region);
    }
    if let Some(d) = &m.dregg {
        let where_ = match &d.node {
            Some(node) => format!("{} via {node}", d.backend),
            None => d.backend.clone(),
        };
        println!("  backend   {where_}");
        if let Some(units) = d.meter_units {
            println!("  meter     {units} units charged by the live node");
        }
        for (i, o) in d.outputs.iter().enumerate() {
            println!("  output[{i}] {o}");
        }
        if let Some(err) = &d.error {
            println!("  ✗ lapse   {err}");
        }
    }
}

/// `dregg-cloud machines <create|list|get|stop|delete>` — the direct live-cloud
/// client over the gateway's fly-compatible machines API (requires `--endpoint`).
fn cmd_machines(dir: &Path, endpoint: Option<&str>, action: MachineAction) -> Result<()> {
    let ep = endpoint.ok_or_else(|| {
        anyhow!(
            "`{} machines` talks to a LIVE cloud — pass `--endpoint <gateway-url>` \
             (or set DREGGNET_ENDPOINT)",
            prog()
        )
    })?;
    let store = Store::load(dir)?;
    let client = CloudClient::new(ep, bearer_of(&store));
    eprintln!(
        "→ {}{}",
        client.endpoint(),
        if client.has_bearer() {
            ""
        } else {
            "  (no account — run `login` to present a credential)"
        }
    );
    match action {
        MachineAction::Create {
            app,
            name,
            image,
            cpu_kind,
            cpus,
            memory_mb,
            region,
        } => {
            let req = CreateMachineRequest {
                name,
                region,
                config: MachineConfig {
                    image: image.unwrap_or_default(),
                    guest: GuestConfig {
                        cpu_kind,
                        cpus,
                        memory_mb,
                    },
                    env: std::collections::BTreeMap::new(),
                },
            };
            render_machine_outcome(client.create_machine(&app, &req)?, "create")
        }
        MachineAction::List { app } => match client.list_machines(&app)? {
            ListOutcome::Ok(machines) => {
                if machines.is_empty() {
                    println!("no machines for app `{app}` on the live cloud");
                } else {
                    println!("{} machine(s) for app `{app}`:", machines.len());
                    for m in &machines {
                        print_machine(m, false);
                    }
                }
                Ok(())
            }
            ListOutcome::Refused { status, message } => {
                println!("✗ the live cloud refused the list (HTTP {status}):");
                println!("    {message}");
                bail!("live-cloud list refused (HTTP {status})");
            }
        },
        MachineAction::Get { app, id } => {
            render_machine_outcome(client.get_machine(&app, &id)?, "get")
        }
        MachineAction::Stop { app, id } => {
            render_machine_outcome(client.stop_machine(&app, &id)?, "stop")
        }
        MachineAction::Delete { app, id } => {
            let (ok, msg) = client.delete_machine(&app, &id)?;
            if ok {
                println!("✓ deleted machine {id} (app `{app}`)");
                Ok(())
            } else {
                println!("✗ the live cloud refused the delete:");
                println!("    {msg}");
                bail!("live-cloud delete refused");
            }
        }
    }
}

/// `dregg-cloud run` — schedule a funded lease onto the LocalProvider, fulfill it as a
/// durable metered workflow, and print the result + the meter.
async fn cmd_run(
    dir: &Path,
    endpoint: Option<&str>,
    lease_id: &str,
    lang: &str,
    source: &Path,
) -> Result<()> {
    if lang != "wat" {
        bail!("only `--lang wat` is wired at this rung (got `{lang}`)");
    }

    let mut store = Store::load(dir)?;
    let record = store
        .lease(lease_id)
        .ok_or_else(|| {
            anyhow!(
                "no lease `{lease_id}` (open one with `{} lease open`)",
                prog()
            )
        })?
        .clone();

    // LIVE PATH: with `--endpoint`, run on the remote cloud by creating a machine
    // under the lease's app (the fly-compatible machines API). The live node funds,
    // meters, and receipts it; we render its real result (or its honest refusal).
    if let Some(ep) = endpoint {
        let client = CloudClient::new(ep, bearer_of(&store));
        let app = &record.lessee;
        println!(
            "running on the LIVE cloud → {} (app `{app}`){}",
            client.endpoint(),
            if client.has_bearer() {
                ""
            } else {
                "  (no account — run `login` to present a credential)"
            }
        );
        let mut env = std::collections::BTreeMap::new();
        env.insert(
            "DREGG_WORKLOAD_SOURCE".to_string(),
            source.display().to_string(),
        );
        let req = CreateMachineRequest {
            name: None,
            region: None,
            config: MachineConfig {
                image: format!("wat:{}", source.display()),
                guest: GuestConfig {
                    cpu_kind: "shared".to_string(),
                    cpus: 1,
                    memory_mb: 256,
                },
                env,
            },
        };
        return render_machine_outcome(client.create_machine(app, &req)?, "run");
    }

    let src = std::fs::read_to_string(source)
        .with_context(|| format!("read workload source {}", source.display()))?;
    if src.trim().is_empty() {
        bail!("workload source {} is empty", source.display());
    }

    let lease = record.lease()?;

    // The caller's declared program — the WAT they actually wrote. This is threaded
    // all the way into the durable workflow (a single metered step at the sandboxed
    // floor), so `run --source X` runs X, not a fixed demo.
    let workload = WorkloadSource {
        lang: lang.to_string(),
        source: src,
    };

    // Route through the control plane: place the lease onto the LocalProvider, which
    // provisions a machine + fulfills the lease running the declared workload as a
    // durable metered workflow via the bridge. This is the genuine end-to-end path
    // (the wasmi steps really run).
    let scheduler = Scheduler::new(LocalProvider::new(), MachineSize::Small, "local");
    let workload_id = scheduler
        .place_workload(lease, Some(workload))
        .await
        .map_err(|e| anyhow!("placement failed: {e}"))?;
    let workload = scheduler
        .workload(&workload_id)
        .ok_or_else(|| anyhow!("scheduler lost the placed workload"))?;

    let label = state_label(&workload.state);
    let machine_id = workload.machine.id.to_string();
    let tier = workload.machine.spec.cap_tier;
    let (step1, step2, meter) = match &workload.output {
        Some(out) => (
            Some(out.step1.clone()),
            Some(out.step2.clone()),
            out.meter_units,
        ),
        None => (None, None, 0),
    };

    println!("workload {workload_id}");
    println!(
        "  lease     {lease_id} (lessee {})  (mock lease record)",
        record.lessee
    );
    println!("  machine   {machine_id} (local, tier {tier:?})");
    println!("  workload  lang={lang} source={}", source.display());
    println!("  state     {label}");
    match &workload.output {
        Some(out) => {
            // The declared program's durable step outputs, in order.
            if out.outputs.is_empty() {
                println!("  output    (none returned)");
            } else {
                for (i, v) in out.outputs.iter().enumerate() {
                    println!("  output[{i}]  {v}");
                }
            }
            println!(
                "  meter     {} units charged against budget {}",
                out.meter_units, record.budget_units
            );
        }
        None => {
            // Surface the REAL cause. A workflow that faulted (e.g. the WASM lacks
            // the required `run` export) carries its error in `lapse_reason`; only a
            // genuine budget lapse should be blamed on the budget. This replaces the
            // old message that misdiagnosed every failure as a lease/budget lapse.
            match &workload.lapse_reason {
                Some(why) if is_budget_lapse(why) => {
                    println!("  ✗ the lease lapsed (over budget) and the machine was reaped:");
                    println!("    {why}");
                }
                Some(why) => {
                    println!("  ✗ the workload failed and the machine was reaped:");
                    println!("    {why}");
                    if why.contains("export") && why.contains("run") {
                        println!(
                            "    hint: the module must export a function named `run` — \
                             e.g. `(func (export \"run\") ...)`."
                        );
                    }
                }
                None => {
                    println!(
                        "  ✗ (no output — the machine was reaped before the workload finished)"
                    );
                }
            }
        }
    }

    // THE CAPTURE WIRE: the workload's real output lines land in the durable
    // per-tenant log store, keyed by the workload id + the lessee (the owner
    // subject), so `dregg-cloud logs <workload>` tails the genuine output rather
    // than cached metadata. Capture is best-effort — a log-store hiccup must not
    // fail a run that already happened.
    {
        let sink = logs_sink(dir)?;
        match &workload.output {
            Some(out) if !out.outputs.is_empty() => {
                for line in &out.outputs {
                    if let Err(e) = sink.append(
                        &workload_id.to_string(),
                        &record.lessee,
                        dreggnet_logs::Stream::Stdout,
                        line,
                    ) {
                        eprintln!("warning: log capture failed: {e}");
                        break;
                    }
                }
            }
            Some(_) => {
                let _ = sink.append(
                    &workload_id.to_string(),
                    &record.lessee,
                    dreggnet_logs::Stream::Stdout,
                    "(workload returned no output)",
                );
            }
            None => {
                let reason = workload.lapse_reason.as_deref().unwrap_or(
                    "the machine was reaped before the workload finished (no reason recorded)",
                );
                let _ = sink.append(
                    &workload_id.to_string(),
                    &record.lessee,
                    dreggnet_logs::Stream::Stderr,
                    reason,
                );
            }
        }
    }

    store.workloads.push(WorkloadRecord {
        id: workload_id.to_string(),
        lease_id: lease_id.to_string(),
        lessee: record.lessee.clone(),
        cap_grade: record.cap_grade.clone(),
        lang: lang.to_string(),
        source: source.display().to_string(),
        state: label,
        machine_id,
        step1,
        step2,
        meter_units: meter,
    });
    store.save(dir)?;
    Ok(())
}

/// `dregg-cloud status` — list scheduled workloads + their lifecycle + meter.
fn cmd_status(
    dir: &Path,
    endpoint: Option<&str>,
    lease_filter: Option<&str>,
    app: Option<&str>,
) -> Result<()> {
    let store = Store::load(dir)?;

    // LIVE PATH: with `--endpoint`, list machines on the remote cloud. The gateway
    // lists per app, so an `--app` (or the `--lease` value, used as the app) is
    // required.
    if let Some(ep) = endpoint {
        let app = app.or(lease_filter).ok_or_else(|| {
            anyhow!(
                "live `status` lists machines per app — pass `--app <app>` (or `--lease <app>`)"
            )
        })?;
        let client = CloudClient::new(ep, bearer_of(&store));
        eprintln!("→ {}", client.endpoint());
        return match client.list_machines(app)? {
            ListOutcome::Ok(machines) => {
                if machines.is_empty() {
                    println!("no machines for app `{app}` on the live cloud");
                } else {
                    println!("{} machine(s) for app `{app}`:", machines.len());
                    for m in &machines {
                        print_machine(m, false);
                    }
                }
                Ok(())
            }
            ListOutcome::Refused { status, message } => {
                println!("✗ the live cloud refused the list (HTTP {status}):");
                println!("    {message}");
                bail!("live-cloud list refused (HTTP {status})");
            }
        };
    }

    let items: Vec<&WorkloadRecord> = store
        .workloads
        .iter()
        .filter(|w| lease_filter.is_none_or(|l| w.lease_id == l))
        .collect();

    if items.is_empty() {
        match lease_filter {
            Some(l) => println!("no workloads for lease {l}"),
            None => println!("no workloads scheduled yet"),
        }
        return Ok(());
    }

    println!(
        "{:<38}  {:<10}  {:<6}  {}",
        "WORKLOAD", "LEASE", "METER", "STATE"
    );
    for w in items {
        let short_lease = &w.lease_id[..w.lease_id.len().min(8)];
        println!(
            "{:<38}  {:<10}  {:<6}  {}",
            w.id, short_lease, w.meter_units, w.state
        );
    }
    Ok(())
}

/// `dregg-cloud deploy <repo>` — clone → detect → build → publish the repo as a site cell,
/// as a crash-resumable, metered durable workflow, and record the receipt.
#[allow(clippy::too_many_arguments)]
async fn cmd_deploy(
    dir: &Path,
    endpoint: Option<&str>,
    repo: &str,
    name: Option<String>,
    git_ref: Option<String>,
    owner: Option<String>,
    budget: i64,
    serve: bool,
    port: u16,
) -> Result<()> {
    if budget < 3 {
        bail!("--budget must be >= 3 (clone+build+publish each charge 1; got {budget})");
    }
    let site_name = name.unwrap_or_else(|| default_site_name(repo));

    let store_for_owner = Store::load(dir)?;
    // Honor the logged-in identity as the default owner (matching `domains` and the
    // `login` docstring), falling back to `operator` only when no account is
    // connected. An explicit `--owner` always wins.
    let owner = owner.unwrap_or_else(|| {
        store_for_owner
            .identity
            .as_ref()
            .map(|i| i.subject.clone())
            .unwrap_or_else(|| "operator".to_string())
    });
    let owner = owner.as_str();

    // LIVE PATH: with `--endpoint`, provision the deploy on the remote cloud by
    // creating a machine for the site's app (the fly deploy→machines model). The
    // live node funds, meters, and receipts it; we render its real result/refusal.
    if let Some(ep) = endpoint {
        let client = CloudClient::new(ep, bearer_of(&store_for_owner));
        println!(
            "deploying `{repo}` to the LIVE cloud → {} (app `{site_name}`){}",
            client.endpoint(),
            if client.has_bearer() {
                ""
            } else {
                "  (no account — run `login` to present a credential)"
            }
        );
        let mut env = std::collections::BTreeMap::new();
        env.insert("DREGG_DEPLOY_REPO".to_string(), repo.to_string());
        if let Some(r) = &git_ref {
            env.insert("DREGG_DEPLOY_REF".to_string(), r.clone());
        }
        let req = CreateMachineRequest {
            name: Some(site_name.clone()),
            region: None,
            config: MachineConfig {
                image: format!("deploy:{repo}"),
                guest: GuestConfig {
                    cpu_kind: "shared".to_string(),
                    cpus: 1,
                    memory_mb: 256,
                },
                env,
            },
        };
        return render_machine_outcome(client.create_machine(&site_name, &req)?, "deploy");
    }

    // The deploy runs against an in-process site registry rooted in the state dir; the
    // durable store + the cloned/built tree live under the state dir so a crashed deploy is
    // resumable. The CLI runs the pipeline end-to-end and publishes into `registry`; with
    // `--serve` it then serves that registry locally (a real round-trip). The public
    // `<name>.dregg.works` edge is the separate gateway-mount step.
    let id = uuid::Uuid::new_v4().to_string();
    let deploy_root = dir.join("deploys");
    let workroot = deploy_root.join("work");
    let db_path = deploy_root.join(format!("{id}.db"));

    // A SIGNED site registry: each publish is sealed into a prev-hash-chained,
    // ed25519-signed receipt stream, so the deploy leaves a re-witnessable bundle a
    // non-witness can verify with `dregg-cloud verify` (no trust in the host). The seed
    // is per-deploy random; its public key is recorded as the verify trust anchor.
    let mut seed = [0u8; 32];
    seed[..16].copy_from_slice(uuid::Uuid::new_v4().as_bytes());
    seed[16..].copy_from_slice(uuid::Uuid::new_v4().as_bytes());
    let registry = Arc::new(SiteRegistry::signed(seed));
    let engine = Arc::new(DeployEngine::new(&workroot, registry.clone()));

    let mut spec = DeploySpec::new(repo, &site_name, owner);
    spec.git_ref = git_ref;
    spec.budget_units = budget;
    spec.cost_per_step = 1;

    println!("deploying `{repo}` → {site_name}.dregg.works ...");
    let receipt = deploy_on_disk(engine, &spec, &id, &db_path)
        .await
        .map_err(|e| anyhow!("deploy failed: {e}"))?;

    // Honest output: the content is PUBLISHED LOCALLY (into the in-process registry +
    // recorded under the state dir). It is NOT yet served on the public edge — that is
    // the gateway-mount step. So we do not print a bare live URL as if it resolves.
    let prog = prog();
    println!("published locally (not yet served on the public edge):");
    println!(
        "  site         {}  (will serve at {})",
        receipt.site_name, receipt.url
    );
    println!("  repo         {repo}");
    println!("  commit       {}", receipt.commit);
    println!("  build-plan   {}", receipt.build_plan);
    println!("  content-root {}", receipt.content_root);
    println!(
        "  assets       {} (incl. the deploy manifest)",
        receipt.asset_count
    );
    println!("  owner        {}", receipt.owner);
    println!(
        "  meter        {} units charged against budget {budget}",
        receipt.meter_units
    );
    // The source-commitment manifest is a real, shippable differentiator: it folds the
    // built commit into the cell's content_root so a reader can re-witness which commit
    // a site was built from.
    println!(
        "  verify       the source-commitment manifest is at {}",
        dregg_deploy::DEPLOY_MANIFEST_PATH
    );
    if !serve {
        println!("  serve it     rerun with `--serve` to serve this deploy locally over HTTP:");
        println!(
            "               {prog} deploy {repo} --name {} --serve",
            receipt.site_name
        );
    }

    let served_name = receipt.site_name.clone();

    // Capture the re-witnessable bundle the signed publish produced (owner key +
    // signed receipt + served content) and persist it beside the deploy record, so
    // `dregg-cloud verify <id>` can re-witness it offline. The signer pubkey is the
    // verify trust anchor (it pins which key the receipt must be signed under).
    let bundle = registry.site_bundle(&served_name);
    let signer_pubkey = bundle
        .as_ref()
        .map(|b| hex32(&b.signer))
        .unwrap_or_default();
    if let Some(bundle) = &bundle {
        save_bundle(dir, &id, bundle)?;
    }
    if !signer_pubkey.is_empty() {
        println!("  verify it    re-witness it WITHOUT trusting the host:");
        println!("               {prog} verify {}", short(&id));
    }

    let mut store = Store::load(dir)?;
    store.deploys.push(DeployRecord {
        id,
        repo: repo.to_string(),
        site_name: receipt.site_name,
        owner: receipt.owner,
        url: receipt.url,
        commit: receipt.commit,
        content_root: receipt.content_root,
        build_plan: receipt.build_plan,
        asset_count: receipt.asset_count,
        meter_units: receipt.meter_units,
        signer_pubkey,
    });
    store.save(dir)?;

    if serve {
        // A real local round-trip: serve the just-published registry over HTTP and
        // print the actual local URL the operator can `curl` right now.
        let bind = format!("127.0.0.1:{port}");
        println!("\nserving locally at http://{bind}/ (Ctrl-C to stop):");
        println!("  curl -s -H 'Host: {served_name}.dregg.works' http://{bind}/");
        println!("  curl -s http://{bind}/{served_name}/   # no-DNS path-prefix fallback");
        // serve_registry blocks until a fatal bind/accept error; a successful serve
        // runs until the operator interrupts it.
        serve_registry(registry, &bind).map_err(|e| anyhow!("serving on {bind} failed: {e}"))?;
    }
    Ok(())
}

/// Derive a default subdomain label from a repo URL/path: the last path segment, `.git`
/// stripped, lowercased, non-label chars folded to `-`, trimmed. Falls back to `site`.
fn default_site_name(repo: &str) -> String {
    let trimmed = repo.trim_end_matches('/');
    let last = trimmed.rsplit(['/', '\\']).next().unwrap_or(trimmed);
    let last = last.strip_suffix(".git").unwrap_or(last);
    let mut label: String = last
        .chars()
        .map(|c| {
            let c = c.to_ascii_lowercase();
            if c.is_ascii_alphanumeric() || c == '-' {
                c
            } else {
                '-'
            }
        })
        .collect();
    label = label.trim_matches('-').to_string();
    if label.len() > 63 {
        label.truncate(63);
        label = label.trim_matches('-').to_string();
    }
    if label.is_empty() {
        "site".to_string()
    } else {
        label
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_site_name_derives_a_label() {
        assert_eq!(
            default_site_name("https://github.com/ember/blog.git"),
            "blog"
        );
        assert_eq!(default_site_name("/tmp/My_Site/"), "my-site");
        assert_eq!(default_site_name("file:///x/calc"), "calc");
        assert_eq!(default_site_name("---"), "site");
    }

    #[test]
    fn cap_grade_roundtrips_through_string() {
        for g in [CapGrade::Sandboxed, CapGrade::Caged, CapGrade::MicroVm] {
            assert_eq!(grade_from_str(grade_str(g)).unwrap(), g);
        }
        assert!(grade_from_str("bogus").is_err());
    }

    #[test]
    fn cap_tier_arg_maps_to_grade() {
        assert_eq!(CapTierArg::Sandboxed.to_grade(), CapGrade::Sandboxed);
        assert_eq!(CapTierArg::Caged.to_grade(), CapGrade::Caged);
        assert_eq!(CapTierArg::Microvm.to_grade(), CapGrade::MicroVm);
    }

    #[test]
    fn lease_record_denotes_an_active_lease() {
        let rec = LeaseRecord {
            id: "abc".into(),
            lessee: "agent".into(),
            cap_grade: "sandboxed".into(),
            asset: "USD".into(),
            budget_units: 100,
            per_period_units: 1,
            funded: true,
        };
        let lease = rec.lease().unwrap();
        assert!(lease.is_active());
        assert_eq!(lease.cap_grade, CapGrade::Sandboxed);
        assert_eq!(lease.budget_units, 100);
    }

    #[test]
    fn state_label_renders_each_lifecycle() {
        assert_eq!(state_label(&WorkloadState::Running), "running");
        assert_eq!(state_label(&WorkloadState::Completed), "completed");
        assert_eq!(state_label(&WorkloadState::Reaped), "reaped");
        assert_eq!(state_label(&WorkloadState::Lapsed("x".into())), "lapsed: x");
    }

    #[test]
    fn store_roundtrips_through_disk() {
        let dir = tempfile::tempdir().unwrap();
        let mut store = Store::default();
        store.leases.push(LeaseRecord {
            id: "L1".into(),
            lessee: "agent".into(),
            cap_grade: "sandboxed".into(),
            asset: "USD".into(),
            budget_units: 100,
            per_period_units: 1,
            funded: true,
        });
        store.save(dir.path()).unwrap();

        let reloaded = Store::load(dir.path()).unwrap();
        assert_eq!(reloaded.leases.len(), 1);
        assert_eq!(reloaded.lease("L1").unwrap().budget_units, 100);
        assert!(reloaded.lease("missing").is_none());
    }
}
