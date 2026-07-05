//! `orchestrator` — the autonomous lease-orchestration daemon: the loop that
//! makes DreggNet an actual cloud.
//!
//! Today a lease runs when someone calls the gateway create-API (manual). This is
//! the continuous control-plane loop that runs leases *by itself*:
//!
//! ```text
//!   ┌──────────────────────── Orchestrator::run_until_shutdown ───────────────────────┐
//!   │  every tick:                                                                     │
//!   │    1. WATCH   — poll the LeaseSource for funded/active execution-leases          │
//!   │    2. SCHEDULE— BackendRegistry::pick a healthy backend (round-robin, capacity)  │
//!   │    3. DISPATCH— dispatch_lease_over_mesh → the durable metered workload runs      │
//!   │                 on the backend's bridge agent (failover if a backend is down)    │
//!   │    4. METER   — the durable run ticks per-period against the lease budget         │
//!   │    5. SETTLE  — Payable: each metered period → one conserving Transfer            │
//!   │                 lessee → backend, EXACTLY-ONCE                                    │
//!   │    6. REAP    — a lapsed / refused lease yields no billable work; mark reaped     │
//!   │  on a cadence: health-check the whole fleet so pick draws from a fresh view      │
//!   └─────────────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! It is a **real daemon**, not a one-shot: [`Orchestrator::run_until_shutdown`]
//! loops on a `tokio` interval until a shutdown future fires. [`Orchestrator::tick`]
//! runs one iteration (the unit the tests drive).
//!
//! ## What is live vs mocked vs the named gap
//!
//! - **Live (real, here):** the loop, the multi-backend pick/health/failover
//!   ([`crate::fleet`]), the dispatch (the proven `:8021/fulfill` POST over the
//!   mesh — same path as the node-a deploy), and the conserving exactly-once
//!   settlement ([`dreggnet_durable::Settlement`]).
//! - **Mocked offline:** the lease source ([`ChannelLeaseSource`]) and, in tests,
//!   the backend (a loopback fulfill stub speaking the node-agent contract).
//! - **The named on-chain gap:** reading funded leases from a *live* dregg node.
//!   The verified decode is real behind `dreggnet-bridge`'s `dregg-verify` feature
//!   ([`dreggnet_bridge::DreggNodeFeed`] / `dregg_verify::read_funded_leases`); the
//!   remaining step is the light-client RPC transport that fetches the receipt-log
//!   records (it needs the arkworks / `dregg-verify` lane wired into the workspace
//!   lock — see `bridge/Cargo.toml`'s FLIP-ON note). Until then the daemon reads
//!   leases from a [`LeaseSource`] the operator feeds (the gateway create-API, a
//!   fixture, or — feature-on — the node feed).

use std::collections::HashMap;
use std::future::Future;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use dreggnet_bridge::{DurableOutput, Lease};
use dreggnet_durable::{LeaseCharge, Settlement};

use crate::fleet::{BackendRegistry, FleetError};
use crate::mesh::Mesh;

/// One funded lease to orchestrate, paired with the durable instance key its
/// workload runs (and is metered/settled) under.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrchestratedLease {
    /// The durable workflow instance id — the meter + settlement idempotency key.
    pub instance: String,
    /// The funded lease authorizing the work.
    pub lease: Lease,
}

impl OrchestratedLease {
    pub fn new(instance: impl Into<String>, lease: Lease) -> OrchestratedLease {
        OrchestratedLease {
            instance: instance.into(),
            lease,
        }
    }
}

/// Where the daemon reads funded leases from. The orchestrator polls this each
/// tick for whatever funded leases are ready *now* (non-blocking), so a single
/// daemon loop drives both arrival and lifecycle.
///
/// The real source is a dregg node read (see the module docs' named gap);
/// [`ChannelLeaseSource`] is the offline/dev source and the test driver.
pub trait LeaseSource: Send {
    /// Drain the funded leases ready right now (empty if none are waiting).
    fn poll(&mut self) -> Vec<OrchestratedLease>;
}

/// An in-memory channel lease source — the offline/dev driver. Push leases at the
/// daemon over its sender; the daemon picks them up on its next tick.
pub struct ChannelLeaseSource {
    rx: tokio::sync::mpsc::UnboundedReceiver<OrchestratedLease>,
}

/// The sender half of a [`ChannelLeaseSource`].
#[derive(Clone)]
pub struct LeaseSender {
    tx: tokio::sync::mpsc::UnboundedSender<OrchestratedLease>,
}

impl LeaseSender {
    /// Offer a funded lease to the daemon under durable instance `instance`.
    pub fn send(&self, instance: impl Into<String>, lease: Lease) -> Result<(), Lease> {
        self.tx
            .send(OrchestratedLease::new(instance, lease))
            .map_err(|e| e.0.lease)
    }
}

impl ChannelLeaseSource {
    /// A channel source plus its sender.
    pub fn channel() -> (LeaseSender, ChannelLeaseSource) {
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel();
        (LeaseSender { tx }, ChannelLeaseSource { rx })
    }
}

impl LeaseSource for ChannelLeaseSource {
    fn poll(&mut self) -> Vec<OrchestratedLease> {
        let mut out = Vec::new();
        while let Ok(item) = self.rx.try_recv() {
            out.push(item);
        }
        out
    }
}

/// Where a tracked workload is in its orchestrated lifecycle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorkloadState {
    /// Dispatched to a backend; the durable workflow is in flight.
    Running,
    /// Completed within budget **and settled**: the metered units were paid
    /// lessee → backend as a conserving, exactly-once transfer.
    Settled {
        backend: String,
        meter_units: i64,
        settled_units: i64,
    },
    /// The lease lapsed / was refused at the backend's bridge (over-budget /
    /// unfunded): no billable work, reaped. Nothing was settled.
    Lapsed(String),
    /// The fleet could not place the lease (every backend down / none available).
    /// Retryable: re-offer the lease once a backend recovers.
    Unplaced(String),
    /// The work ran but settlement failed (an anomaly — within a funded budget this
    /// should not happen). The output is retained; nothing was double-charged.
    SettleFailed {
        backend: String,
        meter_units: i64,
        reason: String,
    },
}

/// A workload the orchestrator is tracking.
#[derive(Debug, Clone)]
pub struct OrchestratedWorkload {
    pub instance: String,
    pub lessee: String,
    pub state: WorkloadState,
    /// The metered durable output, once the workload has run.
    pub output: Option<DurableOutput>,
}

/// A summary of one [`Orchestrator::tick`] — what the loop did this iteration.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TickReport {
    /// Leases pulled off the source this tick.
    pub watched: usize,
    /// Leases dispatched, metered, and settled.
    pub settled: usize,
    /// Leases reaped (lapsed / refused).
    pub reaped: usize,
    /// Leases the fleet could not place (retryable).
    pub unplaced: usize,
}

/// The autonomous lease-orchestration daemon.
pub struct Orchestrator {
    registry: Arc<BackendRegistry>,
    mesh: Arc<dyn Mesh>,
    settlement: Arc<dyn Settlement>,
    /// How often the daemon polls the source + advances the loop.
    tick_interval: Duration,
    /// Health-check the whole fleet every Nth tick (0 = never auto-check).
    health_every: u32,
    workloads: Mutex<HashMap<String, OrchestratedWorkload>>,
    tick_count: Mutex<u32>,
}

impl Orchestrator {
    /// An orchestrator scheduling across `registry`'s backends over `mesh`, settling
    /// metered work through `settlement`.
    pub fn new(
        registry: Arc<BackendRegistry>,
        mesh: Arc<dyn Mesh>,
        settlement: Arc<dyn Settlement>,
    ) -> Orchestrator {
        Orchestrator {
            registry,
            mesh,
            settlement,
            tick_interval: Duration::from_secs(2),
            health_every: 5,
            workloads: Mutex::new(HashMap::new()),
            tick_count: Mutex::new(0),
        }
    }

    /// Set how often the daemon loop ticks (default 2s).
    pub fn with_tick_interval(mut self, interval: Duration) -> Orchestrator {
        self.tick_interval = interval;
        self
    }

    /// Health-check the whole fleet every `n` ticks (default 5; `0` disables the
    /// automatic sweep — the operator can still call [`Orchestrator::health_check`]).
    pub fn with_health_every(mut self, n: u32) -> Orchestrator {
        self.health_every = n;
        self
    }

    /// The backend registry this orchestrator schedules across.
    pub fn registry(&self) -> &Arc<BackendRegistry> {
        &self.registry
    }

    /// The settlement sink (the Payable rail) this orchestrator pays through.
    pub fn settlement(&self) -> &Arc<dyn Settlement> {
        &self.settlement
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, HashMap<String, OrchestratedWorkload>> {
        self.workloads
            .lock()
            .expect("orchestrator registry poisoned")
    }

    /// A snapshot of a tracked workload.
    pub fn workload(&self, instance: &str) -> Option<OrchestratedWorkload> {
        self.lock().get(instance).cloned()
    }

    /// All tracked workloads.
    pub fn workloads(&self) -> Vec<OrchestratedWorkload> {
        self.lock().values().cloned().collect()
    }

    /// Proactively health-check the whole fleet over the mesh.
    pub async fn health_check(&self) {
        self.registry.health_check_all(self.mesh.as_ref()).await;
    }

    /// Run one iteration of the loop: watch the source, then schedule → dispatch →
    /// meter → settle → reap each funded lease it yields. Returns what happened.
    #[tracing::instrument(skip_all)]
    pub async fn tick(&self, source: &mut dyn LeaseSource) -> TickReport {
        // Health-check the fleet on the configured cadence so `pick` is fresh.
        if self.health_every > 0 {
            let n = {
                let mut c = self.tick_count.lock().expect("tick count poisoned");
                *c = c.wrapping_add(1);
                *c
            };
            if n % self.health_every == 1 {
                self.health_check().await;
            }
        }

        let leases = source.poll();
        let mut report = TickReport {
            watched: leases.len(),
            ..Default::default()
        };
        for item in leases {
            match self.process_lease(item).await {
                WorkloadState::Settled { .. } => report.settled += 1,
                WorkloadState::Lapsed(_) => report.reaped += 1,
                WorkloadState::Unplaced(_) => report.unplaced += 1,
                // A settle anomaly counts as neither cleanly settled nor reaped; it
                // is surfaced in the tracked state for the operator.
                WorkloadState::SettleFailed { .. } | WorkloadState::Running => {}
            }
        }
        report
    }

    /// Run the daemon until `shutdown` resolves. This is the real, continuous loop:
    /// it ticks on `tick_interval`, draining the source and advancing every lease's
    /// lifecycle, until the shutdown signal fires (e.g. `tokio::signal::ctrl_c()` in
    /// a binary, or a `oneshot` in a test).
    pub async fn run_until_shutdown<S, F>(&self, mut source: S, shutdown: F)
    where
        S: LeaseSource,
        F: Future<Output = ()>,
    {
        let mut interval = tokio::time::interval(self.tick_interval);
        interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        tokio::pin!(shutdown);
        loop {
            tokio::select! {
                _ = interval.tick() => {
                    self.tick(&mut source).await;
                }
                _ = &mut shutdown => break,
            }
        }
        // Drain anything that arrived right before shutdown so the final state is
        // observable (a clean stop, not a lost lease).
        self.tick(&mut source).await;
    }

    /// Schedule one lease onto the fleet, dispatch it, settle the metered work, and
    /// track the outcome. Idempotent: a lease already in a terminal state is left
    /// as-is (a re-offer never double-settles — the settlement is exactly-once too).
    #[tracing::instrument(skip(self, item), fields(instance = %item.instance, lessee = %item.lease.lessee))]
    async fn process_lease(&self, item: OrchestratedLease) -> WorkloadState {
        let OrchestratedLease { instance, lease } = item;

        // Skip a lease already settled/reaped (a re-poll). Re-attempt an Unplaced
        // one (a backend may have recovered).
        if let Some(existing) = self.lock().get(&instance) {
            match &existing.state {
                WorkloadState::Settled { .. }
                | WorkloadState::Lapsed(_)
                | WorkloadState::SettleFailed { .. } => return existing.state.clone(),
                WorkloadState::Running | WorkloadState::Unplaced(_) => {}
            }
        }

        // Track it Running before dispatch so it is observable for its whole life.
        self.lock().insert(
            instance.clone(),
            OrchestratedWorkload {
                instance: instance.clone(),
                lessee: lease.lessee.clone(),
                state: WorkloadState::Running,
                output: None,
            },
        );

        // 2+3. Schedule + dispatch over the mesh, with fleet failover.
        match self
            .registry
            .dispatch(self.mesh.as_ref(), &lease, &instance)
            .await
        {
            Ok(placement) => {
                // 4+5. The durable run already metered each period against the
                // budget; settle those metered periods as conserving transfers.
                let state =
                    self.settle_placement(&instance, &lease, &placement.backend, &placement.output);
                if let Some(w) = self.lock().get_mut(&instance) {
                    w.output = Some(placement.output);
                    w.state = state.clone();
                }
                state
            }
            // 6. The lease lapsed at the bridge — reap it (no billable work).
            Err(FleetError::Lapsed { detail, .. }) => {
                let state = WorkloadState::Lapsed(detail);
                if let Some(w) = self.lock().get_mut(&instance) {
                    w.state = state.clone();
                }
                state
            }
            // The fleet could not place it — retryable.
            Err(e @ (FleetError::NoBackendAvailable | FleetError::AllBackendsFailed(_))) => {
                let state = WorkloadState::Unplaced(e.to_string());
                if let Some(w) = self.lock().get_mut(&instance) {
                    w.state = state.clone();
                }
                state
            }
        }
    }

    /// Settle the metered work of a completed placement as conserving, exactly-once
    /// transfers lessee → backend — the metering→Payable fold.
    ///
    /// The durable output's metered total is decomposed into per-period charges (one
    /// per durable step, at the lease's `per_period_units`) and each is settled under
    /// `(instance, period)`. The settled total must equal the metered total — the
    /// coherence the fold guarantees.
    fn settle_placement(
        &self,
        instance: &str,
        lease: &Lease,
        backend: &str,
        output: &DurableOutput,
    ) -> WorkloadState {
        let charges = decompose_charges(instance, lease, backend, output);
        let mut settled_units = 0i64;
        for charge in &charges {
            match self.settlement.settle(charge) {
                Ok(receipt) => settled_units += receipt.amount,
                Err(e) => {
                    return WorkloadState::SettleFailed {
                        backend: backend.to_string(),
                        meter_units: output.meter_units,
                        reason: e.to_string(),
                    };
                }
            }
        }
        tracing::info!(
            lease_id = %instance,
            backend = %backend,
            meter_units = output.meter_units,
            settled_units,
            periods = charges.len(),
            "settled metered placement"
        );
        WorkloadState::Settled {
            backend: backend.to_string(),
            meter_units: output.meter_units,
            settled_units,
        }
    }
}

/// Decompose a durable run's metered total into per-period [`LeaseCharge`]s, lessee
/// → backend, in the lease's asset.
///
/// The faithful path: one charge per durable step (period), each at the lease's
/// `per_period_units` — exactly what the meter ticked. If the metered total does not
/// equal `steps × per_period_units` (a non-uniform or remote-metered run), the total
/// is settled as a single reconciling charge instead, so `Σ charges == meter_units`
/// always holds (the fold never invents or drops value).
fn decompose_charges(
    instance: &str,
    lease: &Lease,
    backend: &str,
    output: &DurableOutput,
) -> Vec<LeaseCharge> {
    let steps = output.outputs.len() as i64;
    let per = lease.per_period_units;
    if steps > 0 && per > 0 && steps * per == output.meter_units {
        (1..=steps)
            .map(|period| {
                LeaseCharge::new(&lease.lessee, backend, &lease.asset, instance, period, per)
            })
            .collect()
    } else if output.meter_units > 0 {
        // Reconcile to the metered total in one charge (period 1) so the settled
        // total matches the meter exactly.
        vec![LeaseCharge::new(
            &lease.lessee,
            backend,
            &lease.asset,
            instance,
            1,
            output.meter_units,
        )]
    } else {
        Vec::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fleet::Backend;
    use crate::mesh::{MeshKeypair, MeshNode, TailscaleMesh};
    use dreggnet_bridge::CapGrade;
    use dreggnet_durable::ConservingLedger;
    use std::net::{Ipv4Addr, SocketAddr};

    fn node_at(addr: SocketAddr) -> MeshNode {
        let ip = match addr.ip() {
            std::net::IpAddr::V4(v4) => v4,
            _ => Ipv4Addr::new(127, 0, 0, 1),
        };
        let mut n = MeshNode::new(
            crate::provider::MachineId("m".into()),
            MeshKeypair::generate().public_base64(),
            "203.0.113.1:51820",
            ip,
        );
        n.agent_port = addr.port();
        n
    }

    async fn spawn_fulfill_stub() -> SocketAddr {
        use tokio::io::{AsyncReadExt, AsyncWriteExt};
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        tokio::spawn(async move {
            loop {
                let (mut stream, _) = match listener.accept().await {
                    Ok(s) => s,
                    Err(_) => return,
                };
                tokio::spawn(async move {
                    let mut buf = Vec::new();
                    let mut tmp = [0u8; 4096];
                    let header_end = loop {
                        if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
                            break pos;
                        }
                        let n = stream.read(&mut tmp).await.unwrap_or(0);
                        if n == 0 {
                            return;
                        }
                        buf.extend_from_slice(&tmp[..n]);
                    };
                    let head = String::from_utf8_lossy(&buf[..header_end]).to_string();
                    let content_len = head
                        .split("\r\n")
                        .find_map(|l| {
                            let (k, v) = l.split_once(':')?;
                            (k.trim().eq_ignore_ascii_case("content-length"))
                                .then(|| v.trim().parse::<usize>().ok())
                                .flatten()
                        })
                        .unwrap_or(0);
                    let body_start = header_end + 4;
                    while buf.len() < body_start + content_len {
                        let n = stream.read(&mut tmp).await.unwrap_or(0);
                        if n == 0 {
                            break;
                        }
                        buf.extend_from_slice(&tmp[..n]);
                    }
                    let payload = serde_json::json!({
                        "ok": true, "step1": "42", "step2": "84",
                        "outputs": ["42", "84"], "meter_units": 2,
                    })
                    .to_string();
                    let resp = format!(
                        "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\
                         Content-Length: {}\r\nConnection: close\r\n\r\n{payload}",
                        payload.len()
                    );
                    let _ = stream.write_all(resp.as_bytes()).await;
                    let _ = stream.flush().await;
                });
            }
        });
        addr
    }

    fn orchestrator_with(reg: Arc<BackendRegistry>, ledger: Arc<ConservingLedger>) -> Orchestrator {
        Orchestrator::new(reg, Arc::new(TailscaleMesh::new()), ledger)
            .with_tick_interval(Duration::from_millis(10))
            .with_health_every(0)
    }

    #[tokio::test]
    async fn tick_dispatches_meters_and_settles() {
        let addr = spawn_fulfill_stub().await;
        let reg = Arc::new(BackendRegistry::new());
        reg.register(Backend::new("node-a", node_at(addr), 2));
        reg.mark_healthy("node-a");

        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("USD", "agent", 100); // the lease reserve

        let orch = orchestrator_with(reg, ledger.clone());
        let (tx, mut source) = ChannelLeaseSource::channel();
        tx.send(
            "wl-1",
            Lease::funded("agent", CapGrade::Sandboxed, "USD", 100, 1),
        )
        .unwrap();

        let report = orch.tick(&mut source).await;
        assert_eq!(report.watched, 1);
        assert_eq!(report.settled, 1);

        // Settled, metered, and paid lessee → backend (Σδ = 0).
        let w = orch.workload("wl-1").unwrap();
        match w.state {
            WorkloadState::Settled {
                backend,
                meter_units,
                settled_units,
            } => {
                assert_eq!(backend, "node-a");
                assert_eq!(meter_units, 2);
                assert_eq!(settled_units, 2, "settled total equals metered total");
            }
            other => panic!("expected Settled, got {other:?}"),
        }
        assert_eq!(ledger.balance("USD", "agent"), 98);
        assert_eq!(ledger.balance("USD", "node-a"), 2);
        assert_eq!(ledger.total_supply("USD"), 100);
    }

    #[tokio::test]
    async fn lapsed_lease_is_reaped_and_never_settled() {
        // A 4xx-refusing backend: the lease lapses → reaped, nothing settled.
        let addr = spawn_refuse_stub().await;
        let reg = Arc::new(BackendRegistry::new());
        reg.register(Backend::new("node-a", node_at(addr), 2));
        reg.mark_healthy("node-a");

        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("USD", "broke", 100);

        let orch = orchestrator_with(reg, ledger.clone());
        let (tx, mut source) = ChannelLeaseSource::channel();
        tx.send(
            "wl-broke",
            Lease::funded("broke", CapGrade::Sandboxed, "USD", 1, 1),
        )
        .unwrap();

        let report = orch.tick(&mut source).await;
        assert_eq!(report.reaped, 1);
        assert!(matches!(
            orch.workload("wl-broke").unwrap().state,
            WorkloadState::Lapsed(_)
        ));
        // No unpaid work billed: the reserve is untouched.
        assert_eq!(ledger.balance("USD", "broke"), 100);
        assert_eq!(ledger.balance("USD", "node-a"), 0);
    }

    #[tokio::test]
    async fn re_offering_a_settled_lease_does_not_double_charge() {
        let addr = spawn_fulfill_stub().await;
        let reg = Arc::new(BackendRegistry::new());
        reg.register(Backend::new("node-a", node_at(addr), 4));
        reg.mark_healthy("node-a");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("USD", "agent", 100);
        let orch = orchestrator_with(reg, ledger.clone());

        let (tx, mut source) = ChannelLeaseSource::channel();
        let lease = Lease::funded("agent", CapGrade::Sandboxed, "USD", 100, 1);
        tx.send("wl-1", lease.clone()).unwrap();
        orch.tick(&mut source).await;
        // Re-offer the SAME instance — exactly-once means no second charge.
        tx.send("wl-1", lease).unwrap();
        orch.tick(&mut source).await;

        assert_eq!(
            ledger.balance("USD", "node-a"),
            2,
            "charged once, not twice"
        );
        assert_eq!(ledger.balance("USD", "agent"), 98);
    }

    #[tokio::test]
    async fn run_until_shutdown_is_a_real_daemon_loop() {
        let addr = spawn_fulfill_stub().await;
        let reg = Arc::new(BackendRegistry::new());
        reg.register(Backend::new("node-a", node_at(addr), 4));
        reg.mark_healthy("node-a");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("USD", "agent", 100);
        let orch = Arc::new(orchestrator_with(reg, ledger.clone()));

        let (tx, source) = ChannelLeaseSource::channel();
        let (stop_tx, stop_rx) = tokio::sync::oneshot::channel::<()>();

        // Drive the daemon in the background.
        let daemon = {
            let orch = orch.clone();
            tokio::spawn(async move {
                orch.run_until_shutdown(source, async {
                    let _ = stop_rx.await;
                })
                .await;
            })
        };

        // Feed leases over time — the daemon picks each up on a later tick.
        tx.send(
            "d-1",
            Lease::funded("agent", CapGrade::Sandboxed, "USD", 100, 1),
        )
        .unwrap();
        tokio::time::sleep(Duration::from_millis(40)).await;
        tx.send(
            "d-2",
            Lease::funded("agent", CapGrade::Sandboxed, "USD", 100, 1),
        )
        .unwrap();
        tokio::time::sleep(Duration::from_millis(40)).await;

        // Stop the daemon and let it drain.
        let _ = stop_tx.send(());
        let _ = tokio::time::timeout(Duration::from_secs(2), daemon).await;

        // Both leases ran and settled over the lifetime of the running daemon.
        assert!(matches!(
            orch.workload("d-1").unwrap().state,
            WorkloadState::Settled { .. }
        ));
        assert!(matches!(
            orch.workload("d-2").unwrap().state,
            WorkloadState::Settled { .. }
        ));
        assert_eq!(ledger.balance("USD", "node-a"), 4);
    }

    /// A loopback server that refuses every `/fulfill` with a 402 (an over-budget /
    /// unfunded lease the bridge agent would reject) — to drive the lapse→reap path.
    async fn spawn_refuse_stub() -> SocketAddr {
        use tokio::io::{AsyncReadExt, AsyncWriteExt};
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        tokio::spawn(async move {
            loop {
                let (mut stream, _) = match listener.accept().await {
                    Ok(s) => s,
                    Err(_) => return,
                };
                tokio::spawn(async move {
                    let mut buf = Vec::new();
                    let mut tmp = [0u8; 4096];
                    let header_end = loop {
                        if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
                            break pos;
                        }
                        let n = stream.read(&mut tmp).await.unwrap_or(0);
                        if n == 0 {
                            return;
                        }
                        buf.extend_from_slice(&tmp[..n]);
                    };
                    let head = String::from_utf8_lossy(&buf[..header_end]).to_string();
                    let content_len = head
                        .split("\r\n")
                        .find_map(|l| {
                            let (k, v) = l.split_once(':')?;
                            (k.trim().eq_ignore_ascii_case("content-length"))
                                .then(|| v.trim().parse::<usize>().ok())
                                .flatten()
                        })
                        .unwrap_or(0);
                    let body_start = header_end + 4;
                    while buf.len() < body_start + content_len {
                        let n = stream.read(&mut tmp).await.unwrap_or(0);
                        if n == 0 {
                            break;
                        }
                        buf.extend_from_slice(&tmp[..n]);
                    }
                    let payload = r#"{"ok":false,"error":"execution-lease exhausted after step1"}"#;
                    let resp = format!(
                        "HTTP/1.1 402 Payment Required\r\nContent-Type: application/json\r\n\
                         Content-Length: {}\r\nConnection: close\r\n\r\n{payload}",
                        payload.len()
                    );
                    let _ = stream.write_all(resp.as_bytes()).await;
                    let _ = stream.flush().await;
                });
            }
        });
        addr
    }
}
