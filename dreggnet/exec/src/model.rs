//! `model` — the explicit **execution-model descriptor**: a workload-run declared
//! as a POINT in the space `lifecycle × funding × authority × trigger`, lowered
//! onto the shared primitives (the replenishing-budget [`Meter`], the cap bundle,
//! the receipt chain).
//!
//! # Why this exists
//!
//! DreggNet already runs several *kinds* of workload — a request-scoped lease
//! ([`crate`]/`dreggnet_control::scheduler`), a persistent server
//! (`dreggnet_control::server`), a deploy-as-durable-workflow (`dregg_deploy`), an
//! agent loop ([`crate::agent`]), and the autonomous orchestrator
//! (`dreggnet_control::orchestrator`). Each path was written as its OWN code, with
//! its own lifecycle state-machine enum and its own funding logic. That is the
//! rigidity this module names and dissolves: a substrate should express an
//! ARBITRARY execution model as a *declaration over primitives*, not as a new
//! bespoke code path.
//!
//! An [`ExecutionModel`] is that declaration. It is four orthogonal choices:
//!
//! - **[`Lifecycle`]** — how long the run lives and how it ends
//!   (run-to-completion · persistent-served · scheduled · streaming · reactive).
//! - **[`Funding`]** — where the spend bound comes from. EVERY variant lowers to a
//!   single [`BudgetTerms`] → one verified [`ReplenishingBudget`](crate::budget::ReplenishingBudget)
//!   cell, drawn through the one [`Meter`]. There is no second metering mechanism.
//! - **[`Authority`]** — what the run may do (a polyana cap-grade, or an
//!   attenuable `dga1_` cap bundle).
//! - **[`Trigger`]** — what causes a run (invoke · push-deploy · cron · event ·
//!   agent-brain · watch).
//!
//! The payoff is in the tests at the bottom: the five existing paths are recovered
//! as named *points* ([`ExecutionModel::lease`], [`ExecutionModel::persistent_server`],
//! [`ExecutionModel::deploy`], [`ExecutionModel::agent`],
//! [`ExecutionModel::orchestrated`]), and THREE NEW models that were never written
//! as code — **cron/scheduled**, **streaming/long-lived**, and an
//! **escrow-bonded compute market** — fall out as declarations that run over the
//! exact same [`ReplenishingMeter`](crate::meter::ReplenishingMeter), with no new
//! mechanism. A model that drops in this cheaply is the flexibility, proven.
//!
//! See `docs/EXECUTION-MODELS.md` for the full model-space map + the named seam
//! (the existing paths still carry their own lifecycle enums + funding code; this
//! descriptor is the shared vocabulary they migrate onto).

use serde::{Deserialize, Serialize};

use crate::budget::BudgetTerms;
use crate::meter::{Meter, MeterError, MeterKey, MeterReceipt};

// ---------------------------------------------------------------------------
// The four axes.
// ---------------------------------------------------------------------------

/// **Lifecycle** — how long a workload-run lives and how it ends. The dimension
/// the three separate `WorkloadState`/`ServerState` enums (scheduler, server,
/// orchestrator) each hard-code; here it is one declared choice.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Lifecycle {
    /// Run once, produce a result, exit (the request-scoped lease, the deploy
    /// workflow, one agent run). Ends in `Completed` or `Lapsed`.
    RunToCompletion,
    /// Held up continuously for as long as the funding lasts — it serves rather
    /// than returns (the persistent `ServerFleet`). Ends on stop/destroy/lapse.
    PersistentServed,
    /// Fires on a schedule; each firing is a fresh run-to-completion, metered per
    /// run. (NEW model: cron.)
    Scheduled {
        /// Blocks between firings (the schedule granularity).
        every_blocks: i64,
    },
    /// Stays up emitting a stream / consuming a refilling budget over a long life;
    /// throttled (not killed) when headroom is momentarily exhausted, resuming as
    /// the budget refills. (NEW model: streaming/long-lived.)
    Streaming,
    /// Dormant until an external event wakes it; each event is a fresh run (the
    /// reactive twin of `invoke`). Ends when the funding lapses.
    Reactive,
}

/// **Funding** — where the spend bound comes from. The substrate fact: every
/// variant lowers to ONE [`BudgetTerms`] (a [`ReplenishingBudget`](crate::budget::ReplenishingBudget)
/// cell), so the funding axis is genuinely a single primitive parameterized four
/// ways — never four metering mechanisms.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Funding {
    /// A fixed prepaid ceiling that does not refill within the run — the plain
    /// lease/deploy budget. Lowers to a ceiling cell with an effectively-infinite
    /// period.
    Prepaid {
        /// What the budget is denominated in.
        asset: String,
        /// The hard spend ceiling.
        budget: i64,
    },
    /// Metered per period against a ceiling — the per-step lease meter and the
    /// per-uptime-period server meter. Lowers to a ceiling cell with the metering
    /// `period` as its granularity.
    Metered {
        /// What the budget is denominated in.
        asset: String,
        /// The ceiling per `period` window.
        budget: i64,
        /// The metering granularity (one uptime period / one step window).
        period: i64,
    },
    /// A genuinely refilling budget — headroom returns `refill` every `period`
    /// (the seL4-MCS sporadic-server shape). The funding a long-lived/streaming or
    /// agent run wants. Carries the full [`BudgetTerms`] verbatim.
    Refilling {
        /// The replenishing-budget terms (asset · budget · period · refill · …).
        terms: BudgetTerms,
    },
    /// **Escrow-bonded** — a payer bonds `bond` up front; the bond is RELEASED to
    /// the worker on a verified-ok result and REFUNDED to the payer otherwise. The
    /// compute-market funding (another party hires the run). Lowers to a one-shot
    /// ceiling cell holding the bond. (NEW model.)
    EscrowBonded {
        /// What the bond is denominated in.
        asset: String,
        /// The bonded amount, held in escrow.
        bond: i64,
        /// The party putting up the bond (the hirer).
        payer: String,
        /// The party that earns the bond on a verified result (the compute provider).
        worker: String,
    },
}

impl Funding {
    /// The single lowering: the [`BudgetTerms`] this funding opens on the shared
    /// [`Meter`]. This is *why* the funding axis is one primitive — every variant
    /// becomes the same kind of verified cell.
    pub fn terms(&self) -> BudgetTerms {
        match self {
            // No refill within a run ⇒ an effectively-infinite period.
            Funding::Prepaid { asset, budget } => {
                BudgetTerms::ceiling(asset.clone(), *budget, i64::MAX, 0)
            }
            Funding::Metered {
                asset,
                budget,
                period,
            } => BudgetTerms::ceiling(asset.clone(), *budget, *period, 0),
            Funding::Refilling { terms } => terms.clone(),
            // The bond is a one-shot ceiling: drawing it (releasing) is terminal,
            // not-drawing it (refunding) leaves it whole.
            Funding::EscrowBonded { asset, bond, .. } => {
                BudgetTerms::ceiling(asset.clone(), *bond, i64::MAX, 0)
            }
        }
    }

    /// The asset the funding is denominated in.
    pub fn asset(&self) -> &str {
        match self {
            Funding::Prepaid { asset, .. }
            | Funding::Metered { asset, .. }
            | Funding::EscrowBonded { asset, .. } => asset,
            Funding::Refilling { terms } => &terms.asset,
        }
    }
}

/// **Authority** — what a run is allowed to do. The two shapes DreggNet actually
/// uses: a coarse polyana isolation grade (the lease paths) and the fine-grained
/// attenuable cap bundle (the agent path).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Authority {
    /// A polyana isolation grade name (`sandboxed` / `caged` / `microvm`) — the
    /// lease/server/orchestrator cap-grade.
    CapGrade(String),
    /// An attenuable `dga1_` cap bundle (the powerbox): `invoke:<svc>`,
    /// `cell-read:<path>`, `cell-write:<path>` caps. A child may only narrow.
    CapBundle(Vec<String>),
}

/// **Trigger** — what causes a run to start.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Trigger {
    /// Started by an explicit call (the gateway create-API / `dregg run`).
    Invoke,
    /// Started by a code push / `dregg deploy`.
    PushDeploy,
    /// Started by a schedule (cron). Carries the schedule granularity in blocks.
    Cron {
        /// Blocks between firings.
        schedule_blocks: i64,
    },
    /// Started by an external event on `topic` (the reactive twin of invoke).
    Event {
        /// The event topic the run subscribes to.
        topic: String,
    },
    /// Driven by an agent's brain emitting actions (the autonomous loop).
    AgentBrain,
    /// Started by the orchestrator watching a funded-lease source.
    Watch,
}

// ---------------------------------------------------------------------------
// The declaration.
// ---------------------------------------------------------------------------

/// An **execution model**: a workload-run declared as a point in
/// `lifecycle × funding × authority × trigger`. This is the whole shape — a value
/// you can write down (or load from config), not a code path you hand-write.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExecutionModel {
    /// A human label for the model (the workload kind).
    pub name: String,
    /// How long the run lives and how it ends.
    pub lifecycle: Lifecycle,
    /// Where the spend bound comes from (lowers to one [`BudgetTerms`]).
    pub funding: Funding,
    /// What the run may do.
    pub authority: Authority,
    /// What causes a run.
    pub trigger: Trigger,
}

impl ExecutionModel {
    /// Open this model's funding as a budget cell on the shared [`Meter`], keyed by
    /// `subject`. This is the one funding seam every model — existing or new —
    /// flows through; the lifecycle/trigger then decide *when* and *how often* the
    /// run draws against it.
    pub fn provision_funding(&self, meter: &dyn Meter, subject: &str) -> Result<(), MeterError> {
        meter.open(subject, self.funding.terms())
    }

    /// Draw `cost` for the `ordinal`-th run of this model against `subject`'s
    /// budget at `at_block`, exactly-once. The single admission gate every
    /// lifecycle reuses: a scheduled firing, a streaming tick, an agent action,
    /// and a one-shot lease all charge through here.
    pub fn charge_run(
        &self,
        meter: &dyn Meter,
        subject: &str,
        ordinal: i64,
        cost: i64,
        at_block: i64,
    ) -> Result<MeterReceipt, MeterError> {
        meter.draw(&MeterKey::new(subject, ordinal), cost, at_block)
    }

    // ---- the EXISTING five paths, recovered as points ---------------------

    /// The request-scoped **lease** (`dreggnet_control::scheduler`): run once,
    /// prepaid budget, a polyana cap-grade, started by invoke.
    pub fn lease(
        name: impl Into<String>,
        asset: impl Into<String>,
        budget: i64,
        grade: impl Into<String>,
    ) -> ExecutionModel {
        ExecutionModel {
            name: name.into(),
            lifecycle: Lifecycle::RunToCompletion,
            funding: Funding::Prepaid {
                asset: asset.into(),
                budget,
            },
            authority: Authority::CapGrade(grade.into()),
            trigger: Trigger::Invoke,
        }
    }

    /// The **persistent server** (`dreggnet_control::server`): held up, metered per
    /// uptime period, a cap-grade, created by invoke.
    pub fn persistent_server(
        name: impl Into<String>,
        asset: impl Into<String>,
        budget: i64,
        period: i64,
        grade: impl Into<String>,
    ) -> ExecutionModel {
        ExecutionModel {
            name: name.into(),
            lifecycle: Lifecycle::PersistentServed,
            funding: Funding::Metered {
                asset: asset.into(),
                budget,
                period,
            },
            authority: Authority::CapGrade(grade.into()),
            trigger: Trigger::Invoke,
        }
    }

    /// The **deploy** (`dregg_deploy`): clone→build→publish run-to-completion, a
    /// prepaid deploy budget, the `deploy` cap, started by a push.
    pub fn deploy(
        name: impl Into<String>,
        asset: impl Into<String>,
        budget: i64,
    ) -> ExecutionModel {
        ExecutionModel {
            name: name.into(),
            lifecycle: Lifecycle::RunToCompletion,
            funding: Funding::Prepaid {
                asset: asset.into(),
                budget,
            },
            authority: Authority::CapBundle(vec!["deploy".to_string()]),
            trigger: Trigger::PushDeploy,
        }
    }

    /// The **agent** ([`crate::agent`]): one run driven by a brain, a refilling
    /// budget cell, an attenuable cap bundle.
    pub fn agent(name: impl Into<String>, terms: BudgetTerms, caps: Vec<String>) -> ExecutionModel {
        ExecutionModel {
            name: name.into(),
            lifecycle: Lifecycle::RunToCompletion,
            funding: Funding::Refilling { terms },
            authority: Authority::CapBundle(caps),
            trigger: Trigger::AgentBrain,
        }
    }

    /// The **orchestrated** lease (`dreggnet_control::orchestrator`): dispatched
    /// per watched funded lease, metered per period, a cap-grade, started by watch.
    pub fn orchestrated(
        name: impl Into<String>,
        asset: impl Into<String>,
        budget: i64,
        period: i64,
        grade: impl Into<String>,
    ) -> ExecutionModel {
        ExecutionModel {
            name: name.into(),
            lifecycle: Lifecycle::RunToCompletion,
            funding: Funding::Metered {
                asset: asset.into(),
                budget,
                period,
            },
            authority: Authority::CapGrade(grade.into()),
            trigger: Trigger::Watch,
        }
    }

    // ---- the THREE NEW models, as declarations ----------------------------

    /// **NEW — cron/scheduled.** A workload that fires every `every_blocks`, each
    /// firing a fresh run metered against a per-window budget. Drops in over the
    /// shared meter: a firing is just a [`charge_run`](Self::charge_run) at the
    /// schedule block.
    pub fn cron(
        name: impl Into<String>,
        asset: impl Into<String>,
        budget: i64,
        every_blocks: i64,
        grade: impl Into<String>,
    ) -> ExecutionModel {
        ExecutionModel {
            name: name.into(),
            lifecycle: Lifecycle::Scheduled { every_blocks },
            funding: Funding::Metered {
                asset: asset.into(),
                budget,
                period: every_blocks,
            },
            authority: Authority::CapGrade(grade.into()),
            trigger: Trigger::Cron {
                schedule_blocks: every_blocks,
            },
        }
    }

    /// **NEW — streaming/long-lived.** A workload that stays up consuming a
    /// REFILLING budget: it draws each tick, is throttled when headroom is momentarily
    /// gone, and resumes as the budget refills. Drops in over the replenishing cell
    /// — the long life is just many draws against a `Refilling` funding.
    pub fn streaming(
        name: impl Into<String>,
        terms: BudgetTerms,
        caps: Vec<String>,
    ) -> ExecutionModel {
        ExecutionModel {
            name: name.into(),
            lifecycle: Lifecycle::Streaming,
            funding: Funding::Refilling { terms },
            authority: Authority::CapBundle(caps),
            trigger: Trigger::Invoke,
        }
    }

    /// **NEW — escrow-bonded compute market.** A workload another party hires: the
    /// payer bonds `bond`, the run executes, and the bond is RELEASED to the worker
    /// on a verified-ok result or REFUNDED on failure. Drops in over the budget +
    /// the receipt-chain verdict — see [`settle_escrow`].
    pub fn escrow_bonded(
        name: impl Into<String>,
        asset: impl Into<String>,
        bond: i64,
        payer: impl Into<String>,
        worker: impl Into<String>,
        caps: Vec<String>,
    ) -> ExecutionModel {
        ExecutionModel {
            name: name.into(),
            lifecycle: Lifecycle::RunToCompletion,
            funding: Funding::EscrowBonded {
                asset: asset.into(),
                bond,
                payer: payer.into(),
                worker: worker.into(),
            },
            authority: Authority::CapBundle(caps),
            trigger: Trigger::Invoke,
        }
    }
}

// ---------------------------------------------------------------------------
// Escrow settlement — the compute-market payout decision over the primitives.
// ---------------------------------------------------------------------------

/// How an escrow-bonded run paid out.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EscrowSettlement {
    /// The result verified: the bond was released to the worker.
    Released {
        /// The party paid.
        worker: String,
        /// The amount released.
        amount: i64,
    },
    /// The result did not verify: the bond was refunded to the payer (the run
    /// earned nothing).
    Refunded {
        /// The party refunded.
        payer: String,
        /// The amount refunded.
        amount: i64,
    },
}

/// Settle an escrow-bonded model against a verified result, over the shared
/// [`Meter`]: the bond budget is opened on `escrow_subject`; on `verified_ok` the
/// bond is DRAWN (released to the worker, a real committed consumption of the
/// escrow cell); on a failed result the bond is left undrawn (refunded — the
/// payer's headroom is intact).
///
/// This composes three existing primitives — the replenishing-budget cell (the
/// bond), the model's authority (who may hire), and the run's *verified verdict*
/// (the receipt-chain `verify_agent_run` / a tool's `ToolOutcome.ok`) — into the
/// compute-market payout, with no new mechanism.
pub fn settle_escrow(
    model: &ExecutionModel,
    meter: &dyn Meter,
    escrow_subject: &str,
    at_block: i64,
    verified_ok: bool,
) -> Result<EscrowSettlement, MeterError> {
    let Funding::EscrowBonded {
        bond,
        payer,
        worker,
        ..
    } = &model.funding
    else {
        // Not an escrow model — nothing to settle. Treat as a refund of zero.
        return Ok(EscrowSettlement::Refunded {
            payer: String::new(),
            amount: 0,
        });
    };
    model.provision_funding(meter, escrow_subject)?;
    if verified_ok {
        // Release: draw the whole bond from the escrow cell (a terminal, committed
        // consumption). Exactly-once per escrow subject (period 0).
        meter.draw(&MeterKey::new(escrow_subject, 0), *bond, at_block)?;
        Ok(EscrowSettlement::Released {
            worker: worker.clone(),
            amount: *bond,
        })
    } else {
        // Refund: leave the bond undrawn — the payer keeps full headroom.
        Ok(EscrowSettlement::Refunded {
            payer: payer.clone(),
            amount: *bond,
        })
    }
}

// ---------------------------------------------------------------------------
// Driving a declared model — the real entry point the CLI/API/config invoke.
// ---------------------------------------------------------------------------

/// The verifiable record a *declared* execution-model run leaves: what it was, what
/// it drew against the shared meter, and how it settled. This is what a `dregg-cloud
/// model run <declaration>` (or an API/config-driven run) produces — the proof a new
/// model is a real, receipted entry point, not a demo.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModelRun {
    /// The model's label.
    pub name: String,
    /// The lifecycle that drove the run (`scheduled`/`streaming`/`run-to-completion`/…).
    pub lifecycle: String,
    /// The asset the funding was denominated in.
    pub asset: String,
    /// Firings/ticks admitted (charged exactly-once against the budget).
    pub admitted: i64,
    /// Firings/ticks throttled by the budget (the in-band 402 — paused, not killed).
    pub throttled: i64,
    /// Total units drawn against the budget cell.
    pub units_drawn: i64,
    /// The escrow payout, when the model is escrow-bonded.
    #[serde(default)]
    pub settlement: Option<EscrowSettlement>,
}

impl ExecutionModel {
    /// A short label for this model's lifecycle (for the [`ModelRun`] receipt + display).
    pub fn lifecycle_label(&self) -> &'static str {
        match self.lifecycle {
            Lifecycle::RunToCompletion => "run-to-completion",
            Lifecycle::PersistentServed => "persistent-served",
            Lifecycle::Scheduled { .. } => "scheduled",
            Lifecycle::Streaming => "streaming",
            Lifecycle::Reactive => "reactive",
        }
    }

    /// **Drive a metered model** (the cron/streaming entry point): provision this model's
    /// funding on `meter` keyed by `subject`, then charge `runs` firings of `cost` each,
    /// exactly-once. A firing the budget cannot admit is **throttled** (counted, in-band
    /// 402) rather than fatal — the streaming/scheduled hallmark.
    ///
    /// Firing `i` draws at block `start + i * block_step`: a [`Scheduled`](Lifecycle::Scheduled)
    /// model passes `block_step = every_blocks` (each window's chunk refills, so a
    /// well-funded schedule runs every firing); a [`Streaming`](Lifecycle::Streaming) model
    /// passes `block_step = 0` (all ticks in one window, so a burst throttles then resumes
    /// as the budget matures). This is the one driver every metered lifecycle reuses.
    pub fn run_metered(
        &self,
        meter: &dyn Meter,
        subject: &str,
        runs: i64,
        cost: i64,
        block_step: i64,
        start: i64,
    ) -> Result<ModelRun, MeterError> {
        self.provision_funding(meter, subject)?;
        let mut admitted = 0i64;
        let mut throttled = 0i64;
        for i in 0..runs {
            let at = start.saturating_add(i.saturating_mul(block_step));
            match self.charge_run(meter, subject, i, cost, at) {
                Ok(_) => admitted += 1,
                Err(MeterError::OverBudget { .. }) => throttled += 1,
                Err(e) => return Err(e),
            }
        }
        Ok(ModelRun {
            name: self.name.clone(),
            lifecycle: self.lifecycle_label().to_string(),
            asset: self.funding.asset().to_string(),
            admitted,
            throttled,
            units_drawn: meter.drawn_total(subject),
            settlement: None,
        })
    }

    /// **Settle an escrow-bonded model** (the compute-market entry point): run the bond
    /// settlement over `meter` and package it as a [`ModelRun`]. `verified_ok` is the
    /// run's verified verdict (a verified-ok result releases the bond to the worker; a
    /// failed/forged one refunds the payer).
    pub fn run_escrow(
        &self,
        meter: &dyn Meter,
        escrow_subject: &str,
        at_block: i64,
        verified_ok: bool,
    ) -> Result<ModelRun, MeterError> {
        let settlement = settle_escrow(self, meter, escrow_subject, at_block, verified_ok)?;
        Ok(ModelRun {
            name: self.name.clone(),
            lifecycle: self.lifecycle_label().to_string(),
            asset: self.funding.asset().to_string(),
            admitted: if verified_ok { 1 } else { 0 },
            throttled: 0,
            units_drawn: meter.drawn_total(escrow_subject),
            settlement: Some(settlement),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::{AgentAction, AgentCloud, AgentSpec, PlannedBrain, verify_agent_run};
    use crate::meter::ReplenishingMeter;

    // ── the existing five paths ARE points in the space ───────────────────────

    #[test]
    fn the_five_existing_paths_are_points_with_one_funding_primitive() {
        let lease = ExecutionModel::lease("lease", "USD", 100, "sandboxed");
        let server = ExecutionModel::persistent_server("srv", "USD", 100, 60, "caged");
        let deploy = ExecutionModel::deploy("deploy", "DREGG", 1000);
        let agent = ExecutionModel::agent(
            "agent",
            BudgetTerms::new("DREGG", 50, 1000, 50, 2, 0),
            vec!["invoke:search".into()],
        );
        let orch = ExecutionModel::orchestrated("orch", "USD", 500, 10, "microvm");

        // Every path's funding lowers to a well-formed ReplenishingBudget cell —
        // ONE primitive under all five (no per-paradigm metering mechanism).
        for m in [&lease, &server, &deploy, &agent, &orch] {
            assert!(
                m.funding.terms().is_well_formed(),
                "{} funds a real cell",
                m.name
            );
            let meter = ReplenishingMeter::new();
            m.provision_funding(&meter, &m.name)
                .expect("funding opens on the shared meter");
        }

        // The axes recover each path's identity.
        assert_eq!(lease.lifecycle, Lifecycle::RunToCompletion);
        assert_eq!(server.lifecycle, Lifecycle::PersistentServed);
        assert_eq!(deploy.trigger, Trigger::PushDeploy);
        assert_eq!(agent.trigger, Trigger::AgentBrain);
        assert_eq!(orch.trigger, Trigger::Watch);
    }

    #[test]
    fn a_model_round_trips_through_config_json() {
        // A model is a DECLARATION: it serializes to config and back unchanged, so
        // a new execution model is data, not code.
        let m = ExecutionModel::cron("nightly-build", "DREGG", 30, 86_400, "caged");
        let json = serde_json::to_string(&m).unwrap();
        let back: ExecutionModel = serde_json::from_str(&json).unwrap();
        assert_eq!(m, back);
    }

    // ── NEW model 1: cron / scheduled (metered each run) ──────────────────────

    #[test]
    fn cron_fires_on_schedule_and_each_run_is_metered_exactly_once() {
        // A nightly job: budget 30 per window, fires every 100 blocks, 1 unit/run.
        let cron = ExecutionModel::cron("nightly", "DREGG", 30, 100, "caged");
        assert!(matches!(
            cron.lifecycle,
            Lifecycle::Scheduled { every_blocks: 100 }
        ));
        assert!(matches!(
            cron.trigger,
            Trigger::Cron {
                schedule_blocks: 100
            }
        ));

        let meter = ReplenishingMeter::new();
        cron.provision_funding(&meter, "nightly").unwrap();

        // Fire ten times, one firing per schedule block. Each is a fresh
        // run-to-completion charged through the shared meter, exactly-once.
        let mut admitted = 0;
        for run in 0..10 {
            let at = run * 100;
            match cron.charge_run(&meter, "nightly", run, 1, at) {
                Ok(r) => {
                    assert!(!r.replayed);
                    admitted += 1;
                }
                Err(MeterError::OverBudget { .. }) => break,
                other => panic!("unexpected {other:?}"),
            }
        }
        // Ten firings spaced a full window apart each have their consumed chunk
        // refilled by the next, so all ten run — the schedule is sustainable.
        assert_eq!(admitted, 10, "a well-funded cron runs every firing");

        // Re-firing the same ordinal moves nothing (a retried schedule tick).
        let replay = cron.charge_run(&meter, "nightly", 0, 1, 0).unwrap();
        assert!(replay.replayed, "a retried cron tick is exactly-once");
    }

    #[test]
    fn an_underfunded_cron_throttles_to_its_window_budget() {
        // Budget 3 per window, fires every block (no refill matures between firings)
        // — only 3 firings admit within the window, the rest are rate-bounded.
        let cron = ExecutionModel::cron("chatty", "DREGG", 3, 1, "sandboxed");
        let meter = ReplenishingMeter::new();
        cron.provision_funding(&meter, "chatty").unwrap();
        let mut admitted = 0;
        for run in 0..20 {
            // All at block 0..but within one period (period=1 ⇒ refill at run+1),
            // pin the block so refills don't mature: charge them all "now".
            if cron.charge_run(&meter, "chatty", run, 1, 0).is_ok() {
                admitted += 1;
            }
        }
        assert_eq!(admitted, 3, "the cron's per-window budget bounds the burst");
    }

    // ── NEW model 2: streaming / long-lived (refilling budget) ────────────────

    #[test]
    fn a_streaming_workload_is_throttled_then_resumes_as_the_budget_refills() {
        // A long-lived stream: budget 10 per 1000-block window, refills the whole
        // chunk each window. It draws 1/tick; when a burst exhausts the window it
        // is throttled (402), and after the refill matures it resumes — it is NOT
        // killed, the hallmark of a streaming lifecycle.
        let terms = BudgetTerms::new("DREGG", 10, 1000, 10, 1, 0);
        let stream = ExecutionModel::streaming("feed", terms, vec!["invoke:emit".into()]);
        assert_eq!(stream.lifecycle, Lifecycle::Streaming);

        let meter = ReplenishingMeter::new();
        stream.provision_funding(&meter, "feed").unwrap();

        // Burst the whole window at block 100 (refills scheduled at 1100).
        let mut tick = 0i64;
        let mut admitted = 0;
        for _ in 0..10 {
            stream.charge_run(&meter, "feed", tick, 1, 100).unwrap();
            tick += 1;
            admitted += 1;
        }
        assert_eq!(admitted, 10);
        // The next tick in the same window is throttled (the stream pauses, not dies).
        assert!(matches!(
            stream.charge_run(&meter, "feed", tick, 1, 100),
            Err(MeterError::OverBudget { .. })
        ));
        // Past the derived refill block the stream RESUMES — headroom came back.
        assert_eq!(meter.headroom("feed", 1100), 10);
        let resumed = stream.charge_run(&meter, "feed", tick, 1, 1100).unwrap();
        assert!(
            !resumed.replayed,
            "the long-lived stream resumes after the refill"
        );
    }

    // ── NEW model 3: escrow-bonded compute market ─────────────────────────────

    #[test]
    fn an_escrow_bond_is_released_on_a_verified_result() {
        // A hirer ("buyer") bonds 100 DREGG for a job a "worker" runs. The job is a
        // real agent run; its receipt chain is the verified verdict.
        let model = ExecutionModel::escrow_bonded(
            "render-job",
            "DREGG",
            100,
            "buyer",
            "worker",
            vec!["invoke:render".into()],
        );

        // Run the hired work as a genuine receipted agent run.
        let cloud = AgentCloud::from_seed([42u8; 32]);
        let handle = cloud
            .deploy(&AgentSpec::new("worker:render", 10).with_service("render"))
            .unwrap();
        let plan = vec![AgentAction::Invoke {
            service: "render".into(),
        }];
        let report = cloud.run(&handle, &mut PlannedBrain::new(plan));
        // The result verifies (the receipt chain re-witnesses) → release the bond.
        let verified_ok = verify_agent_run(&report).is_ok();
        assert!(verified_ok);

        let meter = ReplenishingMeter::new();
        let settlement =
            settle_escrow(&model, &meter, "escrow:render-job", 0, verified_ok).unwrap();
        assert_eq!(
            settlement,
            EscrowSettlement::Released {
                worker: "worker".into(),
                amount: 100
            }
        );
        // The bond was really drawn from the escrow cell (a committed payout).
        assert_eq!(meter.drawn_total("escrow:render-job"), 100);
    }

    #[test]
    fn an_escrow_bond_is_refunded_when_the_result_does_not_verify() {
        let model = ExecutionModel::escrow_bonded(
            "render-job",
            "DREGG",
            100,
            "buyer",
            "worker",
            vec!["invoke:render".into()],
        );
        // The result failed to verify (a forged / tampered report) → refund.
        let meter = ReplenishingMeter::new();
        let settlement = settle_escrow(&model, &meter, "escrow:render-job", 0, false).unwrap();
        assert_eq!(
            settlement,
            EscrowSettlement::Refunded {
                payer: "buyer".into(),
                amount: 100
            }
        );
        // Nothing was drawn — the payer keeps the full bond as headroom.
        assert_eq!(meter.drawn_total("escrow:render-job"), 0);
        assert_eq!(meter.headroom("escrow:render-job", 0), 100);
    }

    #[test]
    fn escrow_cannot_double_release_a_bond() {
        // A second release attempt for the same escrow draws nothing more
        // (exactly-once) — the worker is paid the bond once, never twice.
        let model = ExecutionModel::escrow_bonded("j", "DREGG", 50, "p", "w", vec![]);
        let meter = ReplenishingMeter::new();
        settle_escrow(&model, &meter, "escrow:j", 0, true).unwrap();
        settle_escrow(&model, &meter, "escrow:j", 0, true).unwrap();
        assert_eq!(
            meter.drawn_total("escrow:j"),
            50,
            "the bond releases exactly once"
        );
    }

    // ── the declared-model DRIVERS produce a receipted ModelRun ───────────────

    #[test]
    fn a_cron_declaration_runs_and_receipts_each_firing() {
        // The same well-funded nightly schedule, driven through the real entry point.
        let cron = ExecutionModel::cron("nightly", "DREGG", 30, 100, "caged");
        let meter = ReplenishingMeter::new();
        // 10 firings one window (100 blocks) apart, 1 unit each: all admit (sustainable).
        let run = cron.run_metered(&meter, "nightly", 10, 1, 100, 0).unwrap();
        assert_eq!(run.lifecycle, "scheduled");
        assert_eq!(run.admitted, 10);
        assert_eq!(run.throttled, 0);
        assert_eq!(run.units_drawn, 10);
        // The receipt round-trips as a declaration record.
        let back: ModelRun = serde_json::from_str(&serde_json::to_string(&run).unwrap()).unwrap();
        assert_eq!(run, back);
    }

    #[test]
    fn an_underfunded_cron_declaration_reports_throttled_firings() {
        // Budget 3, all firings pinned to one window (block_step 0): 3 admit, rest throttle.
        let cron = ExecutionModel::cron("chatty", "DREGG", 3, 1, "sandboxed");
        let meter = ReplenishingMeter::new();
        let run = cron.run_metered(&meter, "chatty", 20, 1, 0, 0).unwrap();
        assert_eq!(run.admitted, 3);
        assert_eq!(run.throttled, 17);
        assert_eq!(run.units_drawn, 3);
    }

    #[test]
    fn a_streaming_declaration_throttles_within_a_window() {
        // budget 10/window, 15 ticks in one window: 10 admit, 5 throttle (paused, not killed).
        let terms = BudgetTerms::new("DREGG", 10, 1000, 10, 1, 0);
        let stream = ExecutionModel::streaming("feed", terms, vec!["invoke:emit".into()]);
        let meter = ReplenishingMeter::new();
        let run = stream.run_metered(&meter, "feed", 15, 1, 0, 100).unwrap();
        assert_eq!(run.lifecycle, "streaming");
        assert_eq!(run.admitted, 10);
        assert_eq!(run.throttled, 5);
    }

    #[test]
    fn an_escrow_declaration_releases_on_verified_and_refunds_on_failure() {
        let model =
            ExecutionModel::escrow_bonded("render-job", "DREGG", 100, "buyer", "worker", vec![]);
        let meter = ReplenishingMeter::new();
        let released = model
            .run_escrow(&meter, "escrow:render-job", 0, true)
            .unwrap();
        assert_eq!(
            released.settlement,
            Some(EscrowSettlement::Released {
                worker: "worker".into(),
                amount: 100
            })
        );
        assert_eq!(released.units_drawn, 100);

        // A failed verdict refunds (a fresh escrow subject, nothing drawn).
        let meter2 = ReplenishingMeter::new();
        let refunded = model
            .run_escrow(&meter2, "escrow:render-job-2", 0, false)
            .unwrap();
        assert_eq!(
            refunded.settlement,
            Some(EscrowSettlement::Refunded {
                payer: "buyer".into(),
                amount: 100
            })
        );
        assert_eq!(refunded.units_drawn, 0);
    }
}
