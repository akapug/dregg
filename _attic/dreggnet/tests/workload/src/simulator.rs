//! The simulator — it stands up the REAL `Orchestrator` over a loopback fleet +
//! the `ConservingLedger` settlement rail, feeds it the tenant population's leases,
//! drives the loop to drain (or for a duration), and records the measurement.
//!
//! It re-implements nothing: the loop, the fleet pick/health/failover, the dispatch,
//! and the conserving exactly-once settlement are all the real control-plane code.
//! Only the lease source (a channel) and the compute backend (the `:8021/fulfill`
//! loopback stub) are mocked — at the same contract boundary the offline gauntlet
//! mocks them. See `docs/WORKLOAD-TEST-PLAN.md` §2.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::{Duration, Instant};

use dreggnet_control::mesh::{Mesh, TailscaleMesh};
use dreggnet_control::orchestrator::WorkloadState;
use dreggnet_control::{
    Backend, BackendRegistry, ChannelLeaseSource, ConservingLedger, Lease, Orchestrator, Settlement,
};

use crate::backends::{BackendHandle, spawn_fulfill_fleet};
use crate::faults::FaultPlan;
use crate::metrics::{LeaseEvent, Metrics, sample_process};
use crate::profile::{Arrival, LoadProfile, RunBound};
use crate::report::{RunReport, SloResult};
use crate::tenant::{self, Tenant};

/// The live simulation: the fleet, the ledger, the loop, the population, and the
/// measurement, wired and ready to `run`.
pub struct Simulator {
    pub profile: LoadProfile,
    pub ledger: Arc<ConservingLedger>,
    pub registry: Arc<BackendRegistry>,
    pub mesh: Arc<dyn Mesh>,
    pub handles: Vec<BackendHandle>,
    pub tenants: Vec<Tenant>,
    pub metrics: Arc<Metrics>,
    pub faults: FaultPlan,
}

impl Simulator {
    /// Build the simulation a profile describes: spawn the fleet, fund the
    /// tenants, register the backends. Does not run the loop yet.
    pub async fn new(profile: LoadProfile) -> Self {
        let ledger = Arc::new(ConservingLedger::new());
        let tenants = tenant::population(&profile, &ledger);

        let (fleet_n, capacity) = profile.backends;
        let handles = spawn_fulfill_fleet(fleet_n).await;

        let registry = Arc::new(BackendRegistry::new());
        for h in &handles {
            registry.register(Backend::new(h.name.clone(), h.mesh_node(), capacity));
            registry.mark_healthy(&h.name);
        }

        Simulator {
            profile,
            ledger,
            registry,
            mesh: Arc::new(TailscaleMesh::new()),
            handles,
            tenants,
            metrics: Arc::new(Metrics::new()),
            faults: FaultPlan::none(),
        }
    }

    /// Attach a fault schedule (the §5.3 injectors fire during `run`).
    pub fn with_faults(mut self, plan: FaultPlan) -> Self {
        self.faults = plan;
        self
    }

    /// Find a backend handle by name (the fault injectors flip its down flag).
    pub fn handle(&self, name: &str) -> Option<&BackendHandle> {
        self.handles.iter().find(|h| h.name == name)
    }

    /// Drive the loop: feed leases per the arrival process, tick to drain (or for
    /// the profile's wall-clock bound), sampling conservation + queue depth +
    /// (for a soak) resource use each tick, applying any due faults, and timing
    /// each lease's `watched → settled`. Returns the measured `RunReport`.
    pub async fn run(&self, scenario: &str) -> RunReport {
        let orch = Orchestrator::new(
            self.registry.clone(),
            self.mesh.clone(),
            self.ledger.clone() as Arc<dyn Settlement>,
        )
        .with_tick_interval(Duration::from_millis(5))
        .with_health_every(0);

        let (tx, mut source) = ChannelLeaseSource::channel();
        let mut feeder = Feeder::new(&self.profile, &self.tenants);

        let start_supply = self.ledger.total_supply(&self.profile.asset);
        self.metrics.sample_supply(start_supply);

        // Per-lease latency: when each instance was offered, and which settled
        // instances we have already timed (so we record each exactly once).
        let mut fed_at: HashMap<String, Instant> = HashMap::new();
        let mut timed: HashSet<String> = HashSet::new();

        let t0 = Instant::now();
        let mut total_sent = 0usize;
        let mut last_resource = t0;
        let resource_every = Duration::from_millis(500);

        // A generous iteration ceiling so a wedged run cannot spin forever; the real
        // termination is the drain / wall bound below. A Wall run is paced by the
        // wall clock (see the per-iteration yield), so its cap is large — an empty
        // tick is sub-microsecond and would otherwise blow a small count instantly.
        let max_iters = match self.profile.bound {
            // Generous headroom so a contended/slow drain (a backend retrying under
            // load) still completes rather than exiting with leases un-terminal.
            RunBound::Drain => self.profile.total_leases() * 20 + 4_000,
            RunBound::Wall(d) => (d.as_micros() as usize / 50).max(100_000),
        };

        for i in 0..max_iters {
            let elapsed = t0.elapsed();

            // The lease source is up unless a NodeDown window is open: while the
            // source is down the loop reads no new leases (no crash, no spurious
            // settlement), and resumes feeding when it returns.
            if !self.node_down_active(elapsed) {
                for (instance, lease) in feeder.due(elapsed) {
                    let _ = tx.send(instance.clone(), lease.clone());
                    self.metrics.observe(LeaseEvent::Watched);
                    fed_at.insert(instance, Instant::now());
                    total_sent += 1;
                }
            }

            // Apply faults whose offset has arrived (BackendDown/Partition flip the
            // live stub's down flag; the loop fails over on the next dispatch).
            self.apply_due_faults(elapsed);

            let _report = orch.tick(&mut source).await;

            // Sample conservation (must stay flat) + queue depth each tick.
            self.metrics
                .sample_supply(self.ledger.total_supply(&self.profile.asset));
            let inflight: u64 = self
                .registry
                .statuses()
                .iter()
                .map(|s| s.in_flight as u64)
                .sum();
            self.metrics.sample_inflight(inflight);

            // Time every newly-settled lease (watched → settled). In this in-process
            // driver the dispatch/meter/settle all complete within one tick, so this
            // watch→settle leg is also the dominant component of meter→settle finality.
            //
            // Only scan per-tick on a bounded Drain run — there `workloads()` is small
            // and the per-lease timing is the point. On a Wall/soak run the tracking
            // set grows with churn, so a per-tick O(n) clone would dominate cost (and
            // distort the resource series we are trying to measure); the soak takes a
            // single final pass after the loop instead.
            if matches!(self.profile.bound, RunBound::Drain) {
                self.record_newly_settled(&orch, &fed_at, &mut timed);
            }

            // Soak: sample resource use (RSS / open fds / store size) on a cadence.
            if matches!(self.profile.bound, RunBound::Wall(_))
                && last_resource.elapsed() >= resource_every
            {
                self.metrics.sample_resource(sample_process(
                    t0.elapsed().as_secs_f64(),
                    /* durable_store_bytes: the settle rail is in-memory here */ 0,
                ));
                last_resource = Instant::now();
            }

            // Termination.
            match self.profile.bound {
                RunBound::Drain => {
                    if feeder.exhausted() && self.all_terminal(&orch, total_sent) {
                        break;
                    }
                }
                RunBound::Wall(d) => {
                    if t0.elapsed() >= d {
                        break;
                    }
                    // Pace a Wall run to the wall clock: an empty tick is sub-µs, so
                    // without a yield the loop would burn a core spinning and the
                    // arrival feeder (which is elapsed-driven) would barely advance.
                    tokio::time::sleep(Duration::from_micros(200)).await;
                }
            }
            if i + 1 == max_iters {
                break;
            }
        }
        let elapsed = t0.elapsed();

        // Soak/Wall: a single final latency pass (the per-tick scan was skipped above
        // to keep the resource series clean).
        if !matches!(self.profile.bound, RunBound::Drain) {
            self.record_newly_settled(&orch, &fed_at, &mut timed);
        }

        // Tally the final lifecycle states from the real orchestrator records.
        for w in orch.workloads() {
            match w.state {
                WorkloadState::Settled {
                    meter_units,
                    settled_units,
                    ..
                } => self.metrics.observe(LeaseEvent::Settled {
                    meter_units,
                    settled_units,
                }),
                WorkloadState::Lapsed(_) => self.metrics.observe(LeaseEvent::Lapsed),
                WorkloadState::Unplaced(_) => self.metrics.observe(LeaseEvent::Unplaced),
                WorkloadState::SettleFailed { .. } => self.metrics.observe(LeaseEvent::Reaped),
                WorkloadState::Running => {}
            }
        }

        let snapshot = self.metrics.snapshot(elapsed);
        let prometheus = self.metrics.prometheus(scenario, elapsed);
        RunReport {
            scenario: scenario.to_string(),
            snapshot,
            // The shared §3 invariant assertions every scenario upholds. Scenarios
            // extend this with their own SLOs in `check()`.
            results: self.core_invariants(start_supply),
            prometheus,
        }
    }

    /// The §3 floor: conservation + meter=settle + no-unpaid-work. Checked in every
    /// run regardless of scenario (the plan §3).
    fn core_invariants(&self, start_supply: i64) -> Vec<SloResult> {
        let snap = self.metrics.snapshot(Duration::from_secs(1));
        let end_supply = self.ledger.total_supply(&self.profile.asset);
        let mut out = Vec::new();

        // 1. Conservation (Σδ = 0): total_supply unchanged + flat across the run.
        out.push(if end_supply == start_supply && snap.supply_flat {
            SloResult::pass(
                "conservation_supply_flat",
                end_supply,
                &format!("=={start_supply}"),
            )
        } else {
            SloResult::fail(
                "conservation_supply_flat",
                format!("end={end_supply} flat={}", snap.supply_flat),
                &format!("=={start_supply}"),
            )
        });

        // 2. Meter = settle: the settled total equals the metered total.
        out.push(if snap.metered_units == snap.settled_units {
            SloResult::pass("meter_eq_settle", snap.settled_units, "== metered")
        } else {
            SloResult::fail(
                "meter_eq_settle",
                format!(
                    "metered={} settled={}",
                    snap.metered_units, snap.settled_units
                ),
                "metered == settled",
            )
        });

        out
    }

    /// Record the `watched → settled` latency of any settled instance not yet timed.
    fn record_newly_settled(
        &self,
        orch: &Orchestrator,
        fed_at: &HashMap<String, Instant>,
        timed: &mut HashSet<String>,
    ) {
        for w in orch.workloads() {
            if let WorkloadState::Settled { .. } = w.state {
                if timed.insert(w.instance.clone()) {
                    if let Some(at) = fed_at.get(&w.instance) {
                        let d = at.elapsed();
                        self.metrics.record_lease_latency(d);
                        self.metrics.record_finality_latency(d);
                    }
                }
            }
        }
    }

    fn all_terminal(&self, orch: &Orchestrator, expected: usize) -> bool {
        let ws = orch.workloads();
        ws.len() >= expected
            && ws
                .iter()
                .all(|w| !matches!(w.state, WorkloadState::Running))
    }

    /// Whether a `NodeDown` window is currently open (the lease source is down).
    fn node_down_active(&self, elapsed: Duration) -> bool {
        use crate::faults::Fault;
        self.faults.0.iter().any(|f| match f {
            Fault::NodeDown { at, for_ } => elapsed >= *at && elapsed < *at + *for_,
            _ => false,
        })
    }

    /// Apply the faults whose offset has arrived. `BackendDown`/`Partition` flip the
    /// live backend stubs' down flags; `NodeDown` gates the feed (handled in
    /// [`node_down_active`]); `LeaseLapse` is realized via the budget model at
    /// construction; `SettlerRestart` is driven by the durable scenarios directly
    /// against the on-disk store (§5.5).
    fn apply_due_faults(&self, elapsed: Duration) {
        use crate::faults::Fault;
        for f in self.faults.due(elapsed) {
            match f {
                Fault::BackendDown { backend, .. } => {
                    if let Some(h) = self.handle(backend) {
                        h.take_down();
                    }
                }
                Fault::Partition { backend, for_, at } => {
                    // Down inside the window, healed after.
                    if let Some(h) = self.handle(backend) {
                        if elapsed >= *at && elapsed < *at + *for_ {
                            h.take_down();
                        } else if elapsed >= *at + *for_ {
                            h.bring_up();
                        }
                    }
                }
                Fault::NodeDown { .. }
                | Fault::SettlerRestart { .. }
                | Fault::LeaseLapse { .. } => {}
            }
        }
    }
}

/// The arrival-shaped lease feeder. `Burst` offers the whole population up front;
/// `Constant`/`Poisson` inject fresh, uniquely-keyed leases over time at the target
/// rate (the soak/churn driver — each lease is a NEW instance, so the orchestrator's
/// tracking grows the way a sustained real load grows it).
struct Feeder {
    arrival: Arrival,
    /// Pre-built population leases (Burst), drained on the first tick.
    burst: Vec<(String, Lease)>,
    burst_sent: bool,
    /// Per-tenant templates `(lessee, lease)` to clone fresh instances from (Constant).
    templates: Vec<(String, Lease)>,
    /// How many fresh leases have been injected so far (the unique-instance counter).
    injected: u64,
}

impl Feeder {
    fn new(profile: &LoadProfile, tenants: &[Tenant]) -> Self {
        let mut burst = Vec::new();
        let mut templates = Vec::new();
        for t in tenants {
            if let Some(first) = t.leases.first() {
                templates.push((t.id.clone(), first.lease.clone()));
            }
            for tl in &t.leases {
                burst.push((tl.instance.clone(), tl.lease.clone()));
            }
        }
        Feeder {
            arrival: profile.arrival,
            burst,
            burst_sent: false,
            templates,
            injected: 0,
        }
    }

    /// The leases due to be offered by `elapsed`.
    fn due(&mut self, elapsed: Duration) -> Vec<(String, Lease)> {
        match self.arrival {
            Arrival::Burst => {
                if self.burst_sent {
                    Vec::new()
                } else {
                    self.burst_sent = true;
                    std::mem::take(&mut self.burst)
                }
            }
            // A steady (or Poisson-mean) rate: inject up to `rate × elapsed` fresh
            // leases cumulatively, so the offered count tracks the target arrival.
            Arrival::Constant { .. } | Arrival::Poisson { .. } => {
                let per_sec = match self.arrival {
                    Arrival::Constant { per_sec } => per_sec as f64,
                    Arrival::Poisson { lambda } => lambda,
                    Arrival::Burst => unreachable!(),
                };
                if self.templates.is_empty() {
                    return Vec::new();
                }
                let target = (per_sec * elapsed.as_secs_f64()) as u64;
                let mut out = Vec::new();
                while self.injected < target {
                    let (lessee, lease) =
                        &self.templates[self.injected as usize % self.templates.len()];
                    let instance = format!("churn-{lessee}-{}", self.injected);
                    out.push((instance, lease.clone()));
                    self.injected += 1;
                    // Cap a single tick's burst so we don't starve the loop.
                    if out.len() >= 4_096 {
                        break;
                    }
                }
                out
            }
        }
    }

    /// Whether the feeder will offer no further leases (the drain bound reads this).
    fn exhausted(&self) -> bool {
        match self.arrival {
            Arrival::Burst => self.burst_sent && self.burst.is_empty(),
            // A rate feeder never self-exhausts; a Constant run is wall-bounded.
            Arrival::Constant { .. } | Arrival::Poisson { .. } => false,
        }
    }
}
