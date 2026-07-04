//! `server` — **persistent servers**: long-running, durable, per-period-metered
//! server instances (the fly.io-machines model, real — `docs/PERMISSIONLESS-CLOUD-PLAN.md`
//! §3.3).
//!
//! A request-scoped machine ([`crate::scheduler`]) is provisioned, runs a workload
//! to completion via [`VmProvider::run_lease`], and is reaped. A **persistent
//! server** is the generalization: a server cell + a cap-bounded compute workload
//! that **runs continuously** rather than computing a value and exiting. It is
//! provisioned on a compute backend ([`VmProvider::provision`] — the create→launch
//! seam, "dispatch to a compute backend"), **held up** for as long as its lease
//! funds it, **metered per period of uptime**, and reaped when the lease lapses.
//!
//! ```text
//!   create ─▶ launch ─▶ running (metered per uptime period) ─▶ stop/sleep ─▶ wake
//!                            │                                                 │
//!                            └────────────── destroy ◀─────────────────────────┘
//!                            └── lapse (budget exhausted) ─▶ reaped
//! ```
//!
//! ## Why request-scoped vs persistent split on the provider verb
//!
//! [`VmProvider::run_lease`] is the *run-to-completion* path: it fulfils a lease as
//! a durable workflow that meters **per step** and returns an output. A server does
//! not return — it serves. So a persistent server uses [`VmProvider::provision`]
//! (rent a machine and hold it Running) + per-**uptime-period** metering +
//! [`VmProvider::terminate`] (release on stop/destroy/lapse). The metering decision
//! is the §3.3 one: *per wall-clock period of uptime, not per step* — the rent
//! model, reusing the same exactly-once [`Settlement`] rail the orchestrator settles
//! compute through.
//!
//! ## Persistence = crash-survival (the new piece)
//!
//! Today a gateway "machine" is an in-memory `HashMap` entry: a control-plane
//! restart loses it. A persistent server's record lives in a durable [`ServerStore`]
//! (append-only, fsync'd — the same shape as [`crate::settle_ledger`]), so a
//! control-plane restart **reconstructs** the running servers ([`ServerFleet::reload`])
//! rather than losing them. The per-server **uptime-period cursor** (`periods_metered`)
//! is part of that durable record, so metering resumes exactly where it left off:
//! a restart never re-meters an already-settled period (the cursor is durable) and
//! never skips one. Combined with the [`Settlement`] dedup keyed `(server_id,
//! period)`, the uptime meter is **exactly-once across a restart**.
//!
//! ## Real vs the named fleet step (honest)
//!
//! - **Real (this module, in-process, tested):** the lifecycle state machine, the
//!   lease-gated admission, the durable record store + reconstruct-on-restart, the
//!   per-period uptime metering folded through the conserving exactly-once
//!   [`Settlement`], and the lapse→reap on budget exhaustion — all proven end to end
//!   over the [`crate::LocalProvider`].
//! - **The named reviewed-go step:** the live fleet boot (a real server process on a
//!   real KVM/Firecracker node, the data-plane ingress routed over the mesh). The
//!   [`VmProvider`] seam is identical — a real provider provisions a real box where
//!   [`LocalProvider`] holds this process — so the lifecycle + metering proven here
//!   carry over unchanged.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use serde::{Deserialize, Serialize};

use dreggnet_bridge::{CapGrade, Lease};
use dreggnet_durable::{LeaseCharge, SettleError, Settlement};

use crate::compute_cell::{ComputeCell, RestoreError};

use crate::provider::{
    Machine, MachineId, MachineSize, MachineSpec, MachineStatus, ProviderError, VmProvider,
};

/// Where a persistent server is in its lifecycle. Serialized into the durable
/// record, so a reconstructed server resumes in the state it was persisted in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ServerState {
    /// Admitted (lease-gated) but not yet launched onto a backend.
    Created,
    /// Launched + running on a backend; metered per uptime period.
    Running,
    /// Stopped / asleep: the backend machine was released, the record retained. A
    /// stopped server is metered nothing (no uptime) and can be [`woken`](ServerFleet::wake).
    Stopped,
    /// The lease lapsed (uptime budget exhausted): reaped — the machine was released.
    Lapsed,
    /// Destroyed: torn down for good. The record is retained (last-write-wins) so a
    /// reconstruct skips it rather than resurrecting it.
    Destroyed,
}

impl ServerState {
    /// The lowercase wire form.
    pub fn as_str(self) -> &'static str {
        match self {
            ServerState::Created => "created",
            ServerState::Running => "running",
            ServerState::Stopped => "stopped",
            ServerState::Lapsed => "lapsed",
            ServerState::Destroyed => "destroyed",
        }
    }

    /// Whether a server in this state still occupies a (billable) backend machine.
    fn is_up(self) -> bool {
        matches!(self, ServerState::Running)
    }

    /// Whether a reconstruct should re-provision a backend for a server persisted in
    /// this state (only a server that was Running when the control plane died).
    fn reconstructs_running(self) -> bool {
        matches!(self, ServerState::Running)
    }
}

/// The durable, serializable record of a persistent server — the unit the
/// [`ServerStore`] persists so a server survives a control-plane restart.
///
/// The [`Lease`] and [`MachineSpec`] are stored as their primitive fields (neither
/// derives `Serialize`); [`ServerRecord::lease`] / [`ServerRecord::spec`]
/// reconstruct them.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ServerRecord {
    /// The server id (`srv_…`).
    pub id: String,
    /// The fly-app namespace this server belongs to.
    pub app: String,
    /// A human name for the server.
    pub name: String,
    /// The current lifecycle state.
    pub state: ServerState,

    // --- the lease (flattened; `Lease` is not `Serialize`) ---
    /// The lessee renting the server (the lease holder).
    pub lessee: String,
    /// The isolation grade the lease authorizes (`sandboxed`/`caged`/`microvm`).
    pub cap_grade: String,
    /// The asset the uptime budget is denominated in.
    pub asset: String,
    /// The total uptime budget, in meter units.
    pub budget_units: i64,
    /// The meter cost charged per uptime period.
    pub per_period_units: i64,

    // --- the machine sizing (flattened; `MachineSpec` is not `Serialize`) ---
    /// The compute size (`small`/`medium`/`large`).
    pub size: String,
    /// The region the server is placed in.
    pub region: String,

    /// How many uptime periods have been **metered + settled** so far — the durable
    /// exactly-once cursor. A reconstruct resumes metering at `periods_metered + 1`.
    pub periods_metered: i64,
    /// The id of the backend machine currently holding the server, if up.
    #[serde(default)]
    pub machine_id: Option<String>,
    /// Unix-seconds wall-clock of the last successful meter (or the launch/wake that
    /// brought the server up) — the durable freshness mark the **independent reaper**
    /// ([`ServerFleet::reap_idle`], SRV-3) reads. If the metering driver stalls, a
    /// Running server whose `last_metered_at` falls behind a staleness bound is reaped
    /// on a separate timer rather than holding its backend indefinitely, unbilled.
    /// `None` for a record written before this field existed (treated as "never
    /// metered" — eligible for the idle reaper once it is up).
    #[serde(default)]
    pub last_metered_at: Option<i64>,

    /// **COMPUTE-AS-CELL** (`docs/COMPUTE-AS-CELL.md`): the server's dregg identity —
    /// the substrate cell id (hex of `CellId::derive_raw`) its state cell carries,
    /// content-addressed from `(lessee, app, name)`. The server's identity is its
    /// **cell id**, not the random `srv_…` row key. `#[serde(default)]` (empty) for a
    /// record written before this epoch — re-derived deterministically on load.
    #[serde(default)]
    pub cell_id: String,

    /// **COMPUTE-AS-CELL**: the committed umem **boundary root** the server's state
    /// cell was checkpointed to while it sleeps (`Stopped`). `Some(root)` iff the
    /// server is asleep (sleep = checkpoint); `None` while `Running` (awake — the
    /// live state is mutating, not yet committed) or `Created`. A wake restores the
    /// state from this root (fail-closed). The *commitment* is durable here; the
    /// reified image is the named Stage-B seam (`docs/COMPUTE-AS-CELL.md §3`).
    #[serde(default)]
    pub checkpoint_root: Option<String>,
}

impl ServerRecord {
    /// Reconstruct the [`Lease`] this record authorizes the server under.
    pub fn lease(&self) -> Lease {
        Lease::funded(
            self.lessee.clone(),
            cap_grade_from_str(&self.cap_grade),
            self.asset.clone(),
            self.budget_units,
            self.per_period_units,
        )
    }

    /// Reconstruct the [`MachineSpec`] the server provisions a backend to. The
    /// cap-grade resolves to its the owned sandbox isolation tier via the bridge's mapping —
    /// the same grade→tier routing the scheduler uses.
    pub fn spec(&self) -> MachineSpec {
        let tier = dreggnet_bridge::map_cap_grade(cap_grade_from_str(&self.cap_grade)).tier;
        MachineSpec::new(tier, size_from_str(&self.size), self.region.clone())
    }

    /// The total uptime units settled so far (`periods_metered × per_period_units`).
    pub fn settled_units(&self) -> i64 {
        self.periods_metered * self.per_period_units
    }
}

/// Map a [`CapGrade`] back from its lowercase wire string (the inverse of
/// [`CapGrade`]'s `Display`). An unknown string is the safest floor, `Sandboxed`.
fn cap_grade_from_str(s: &str) -> CapGrade {
    match s {
        "caged" => CapGrade::Caged,
        "microvm" => CapGrade::MicroVm,
        _ => CapGrade::Sandboxed,
    }
}

/// Map a [`MachineSize`] from its lowercase wire string. Unknown → `Small`.
fn size_from_str(s: &str) -> MachineSize {
    match s {
        "medium" => MachineSize::Medium,
        "large" => MachineSize::Large,
        _ => MachineSize::Small,
    }
}

/// The lowercase wire string for a [`MachineSize`].
fn size_to_str(size: MachineSize) -> &'static str {
    match size {
        MachineSize::Small => "small",
        MachineSize::Medium => "medium",
        MachineSize::Large => "large",
    }
}

/// Wall-clock now, in unix seconds (the durable freshness mark the idle reaper reads).
/// A pre-epoch clock saturates to `0` rather than panicking.
fn now_unix_secs() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

// ---------------------------------------------------------------------------
// The durable record store.
// ---------------------------------------------------------------------------

mod store {
    //! The durable persistent-server record store — now the REAL substrate umem heap
    //! (the registries-as-umem re-dregg, `docs/REGISTRIES-AS-UMEM.md`): a `ServerStore`
    //! IS a umem cell whose `(collection,key) -> value` heap holds the [`ServerRecord`]s
    //! (keyed by server id), committed to the kernel's sorted-Poseidon2 boundary root.
    //! Persistence + reconstruction IS the heap commit/restore — fail closed if the
    //! restored heap does not bind its sealed root — NOT an append-only JSON-lines log.
    //! This replaces the from-scratch durable log (the `dreggnet-store` myopia the
    //! compute-as-cell lane already named) with the real substrate, and unlocks fork
    //! (branch the whole fleet record-set) + time-travel (restore an earlier fleet root)
    //! the append-log could never give.

    use std::io;
    use std::path::Path;

    use dreggnet_umem::{Record, UmemRegistry};

    use super::{ServerRecord, ServerState};

    /// A [`ServerRecord`] is a durable record keyed by its server id — the unit the
    /// [`ServerStore`]'s umem cell lays into its heap, so a control-plane restart
    /// reconstructs the prior fleet FROM the committed heap.
    impl Record for ServerRecord {
        fn store_key(&self) -> String {
            self.id.clone()
        }
    }

    /// A durable, restart-surviving store of [`ServerRecord`]s, keyed by server id,
    /// **backed by a real umem cell** (the committed boundary is the kernel's
    /// sorted-Poseidon2 heap root).
    pub struct ServerStore {
        inner: UmemRegistry<ServerRecord>,
    }

    impl ServerStore {
        /// Open (or create) the store at `path`, **restoring** the umem cell's heap and
        /// reconstructing every persisted server FROM the committed heap so a restart
        /// sees the prior fleet. Fails closed if the restored heap does not bind its
        /// sealed boundary root (the `root_binds_get` discipline).
        pub fn open(path: impl AsRef<Path>) -> io::Result<ServerStore> {
            let inner = UmemRegistry::<ServerRecord>::open(path).map_err(|e| e.into_io())?;
            Ok(ServerStore { inner })
        }

        /// The path this store persists to.
        pub fn path(&self) -> &Path {
            self.inner.path()
        }

        /// Persist `record` (lay it into the cell's heap, reseal the boundary root,
        /// durably materialize the committed heap snapshot, then update the view). The
        /// record supersedes any prior record for the same id (last-write-wins,
        /// exactly-once on reload).
        pub fn put(&self, record: &ServerRecord) -> io::Result<()> {
            self.inner.append(record).map_err(|e| e.into_io())
        }

        /// The record for `id`, if any.
        pub fn get(&self, id: &str) -> Option<ServerRecord> {
            self.inner.get(id)
        }

        /// Every persisted server record (in id order).
        pub fn all(&self) -> Vec<ServerRecord> {
            self.inner.all()
        }

        /// How many distinct servers the store holds (including destroyed-not-yet-swept).
        pub fn len(&self) -> usize {
            self.inner.len()
        }

        /// **Sweep** terminal records out of the durable store (SRV-1): drop every
        /// `Lapsed`/`Destroyed` record from the committed heap (each removal reseals a
        /// new boundary root, so a swept record is **provably gone** from the committed
        /// state — not merely no longer replayed). Returns how many records were removed.
        pub fn sweep_terminated(&self) -> io::Result<usize> {
            let mut removed = 0usize;
            for rec in self.inner.all() {
                if matches!(rec.state, ServerState::Lapsed | ServerState::Destroyed)
                    && self.inner.remove(&rec.id).map_err(|e| e.into_io())?
                {
                    removed += 1;
                }
            }
            Ok(removed)
        }

        /// Whether the store holds no servers.
        pub fn is_empty(&self) -> bool {
            self.inner.is_empty()
        }

        /// The store's **committed umem boundary root** (hex): the real sorted-Poseidon2
        /// `compute_heap_root` over the fleet-record cell's heap — the 32-byte commitment
        /// a dregg light client understands for the whole fleet record-set.
        pub fn umem_root(&self) -> String {
            self.inner.boundary_root()
        }

        /// **Fork the whole fleet record-set** (a umem superpower the append-log can never
        /// give): copy the committed cell at `new_path`, returning a divergent
        /// `ServerStore` that starts byte-identical (same boundary root) and diverges as
        /// either side mutates — a branch/preview of the entire fleet's records.
        pub fn fork(&self, new_path: impl AsRef<Path>) -> io::Result<ServerStore> {
            let inner = self.inner.fork(new_path).map_err(|e| e.into_io())?;
            Ok(ServerStore { inner })
        }

        /// **Time-travel — checkpoint** the current fleet record-set: the committed
        /// boundary root, retained so [`restore`](Self::restore) can return to it.
        pub fn checkpoint(&self) -> String {
            self.inner.checkpoint()
        }

        /// **Time-travel — restore** the fleet record-set to an earlier committed `root`
        /// (from [`checkpoint`](Self::checkpoint)): the records revert to that committed
        /// state, durably (the rollback survives a restart). Fails closed if no such
        /// checkpoint exists or it does not bind.
        pub fn restore(&self, root: &str) -> io::Result<()> {
            self.inner.restore(root).map_err(|e| e.into_io())
        }
    }
}

pub use store::ServerStore;

// ---------------------------------------------------------------------------
// Errors + outcomes.
// ---------------------------------------------------------------------------

/// Why a persistent-server operation failed.
#[derive(Debug)]
pub enum ServerError {
    /// The lease is not active (unfunded / non-positive per-period / negative
    /// budget): no server is created for unpaid work.
    LeaseInactive { lessee: String },
    /// The lessee's **real funded balance** on the settlement rail does not cover even
    /// the first uptime period — admission reads the actual reserve, not the lease's
    /// self-asserted `funded` bool (SRV-1 fix). No machine is provisioned for a lessee
    /// who cannot pay for it.
    Underfunded {
        lessee: String,
        balance: i64,
        needed: i64,
    },
    /// A server-count quota (per-lessee or global) is exhausted: admission is refused
    /// rather than letting an unbounded number of records + backends accrue (SRV-1).
    QuotaExceeded {
        scope: &'static str,
        limit: usize,
        live: usize,
    },
    /// No server with this id (never created, or a typo).
    NotFound(String),
    /// The server is not in a state this operation accepts (e.g. launching an
    /// already-running server, or metering a stopped one).
    BadState {
        id: String,
        state: ServerState,
        op: &'static str,
    },
    /// A backend provider operation failed.
    Provider(ProviderError),
    /// **COMPUTE-AS-CELL**: restoring the server's state cell from its committed
    /// checkpoint boundary root failed (fail-closed) — a wake / rollback whose
    /// reified image does not reproduce the committed root is REFUSED before any
    /// backend is provisioned (no server resumes from a forged image).
    Restore(RestoreError),
    /// The durable store could not be read/written.
    Store(String),
    /// A settlement failed for a reason other than budget exhaustion (an anomaly).
    Settle(String),
}

impl std::fmt::Display for ServerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ServerError::LeaseInactive { lessee } => {
                write!(f, "lease for `{lessee}` is inactive: no server created")
            }
            ServerError::Underfunded {
                lessee,
                balance,
                needed,
            } => write!(
                f,
                "lessee `{lessee}` funded balance {balance} does not cover the {needed} \
                 period rent: no machine for unpaid work"
            ),
            ServerError::QuotaExceeded { scope, limit, live } => write!(
                f,
                "{scope} server quota exhausted ({live}/{limit} live): no server created"
            ),
            ServerError::NotFound(id) => write!(f, "no such server: {id}"),
            ServerError::BadState { id, state, op } => {
                write!(f, "server {id} cannot {op} in state {}", state.as_str())
            }
            ServerError::Provider(e) => write!(f, "provider error: {e}"),
            ServerError::Restore(e) => write!(f, "state restore refused: {e}"),
            ServerError::Store(e) => write!(f, "server store error: {e}"),
            ServerError::Settle(e) => write!(f, "settlement error: {e}"),
        }
    }
}

impl std::error::Error for ServerError {}

impl From<ProviderError> for ServerError {
    fn from(e: ProviderError) -> Self {
        ServerError::Provider(e)
    }
}

impl From<RestoreError> for ServerError {
    fn from(e: RestoreError) -> Self {
        ServerError::Restore(e)
    }
}

/// The outcome of metering one uptime period for a server.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MeterOutcome {
    /// The uptime period was metered + settled (one conserving transfer lessee →
    /// provider). Carries the period ordinal and the units settled.
    Metered { period: i64, units: i64 },
    /// The server's lease lapsed (the next period would exceed the budget, or the
    /// lessee's funds are exhausted): the server was reaped (machine released).
    Lapsed { reason: String },
    /// The server is not running, so no uptime was metered.
    NotRunning,
}

/// A summary of one [`ServerFleet::tick_uptime`] sweep.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UptimeReport {
    /// Servers metered one uptime period this sweep.
    pub metered: usize,
    /// Servers reaped (lease lapsed) this sweep.
    pub reaped: usize,
    /// Servers whose metering errored this sweep (a store/settle/provider anomaly).
    /// The sweep records the failure and CONTINUES to its siblings (SRV-2) rather than
    /// aborting — one reliably-erroring server can no longer let every server visited
    /// after it escape metering/reaping (a free run). The detail is in [`errors`].
    pub errored: usize,
    /// The `(server_id, reason)` of each errored server this sweep (for the operator).
    pub errors: Vec<(String, String)>,
}

// ---------------------------------------------------------------------------
// The live fleet.
// ---------------------------------------------------------------------------

/// A server held in the fleet: its durable record plus the backend machine it is
/// currently placed on (if up).
#[derive(Clone)]
struct LiveServer {
    record: ServerRecord,
    machine: Option<Machine>,
    /// **COMPUTE-AS-CELL**: the server's umem state cell — the witnessed
    /// working-state heap whose boundary root sleep/wake/fork/rollback operate over.
    /// Held in-process (the boundary-root *commitment* is durable in
    /// [`ServerRecord::checkpoint_root`]; the reified image durability across a
    /// control-plane restart is the named Stage-B seam, `docs/COMPUTE-AS-CELL.md §3`).
    cell: ComputeCell,
}

/// The persistent-server control surface over a single [`VmProvider`].
///
/// It owns the durable [`ServerStore`] (crash-survival), drives the
/// create→launch→meter→stop/wake→destroy lifecycle on the provider, and folds each
/// uptime period through the conserving exactly-once [`Settlement`] rail. Reconstruct
/// a fleet after a control-plane restart with [`ServerFleet::reload`].
pub struct ServerFleet<P: VmProvider> {
    provider: P,
    store: ServerStore,
    settlement: Arc<dyn Settlement>,
    /// The compute size every server provisions at (a single knob at this rung).
    size: MachineSize,
    /// The region every server is placed in.
    region: String,
    /// The payee the uptime rent settles to (the provider's account).
    beneficiary: String,
    /// Max live (non-terminal) servers a single lessee may hold, if capped.
    max_per_lessee: Option<usize>,
    /// Max live (non-terminal) servers across the whole fleet, if capped.
    max_global: Option<usize>,
    live: Mutex<HashMap<String, LiveServer>>,
}

impl<P: VmProvider> ServerFleet<P> {
    /// A fresh fleet over `provider`, persisting to `store`, settling uptime through
    /// `settlement`, renting `size` machines in `region`. Uptime rent is paid to
    /// `beneficiary` (the provider's account).
    pub fn new(
        provider: P,
        store: ServerStore,
        settlement: Arc<dyn Settlement>,
        size: MachineSize,
        region: impl Into<String>,
        beneficiary: impl Into<String>,
    ) -> ServerFleet<P> {
        ServerFleet {
            provider,
            store,
            settlement,
            size,
            region: region.into(),
            beneficiary: beneficiary.into(),
            max_per_lessee: None,
            max_global: None,
            live: Mutex::new(HashMap::new()),
        }
    }

    /// Set the server-count quota (SRV-1): at most `per_lessee` live servers for any
    /// one lessee, and at most `global` live servers across the whole fleet.
    /// `create` refuses with [`ServerError::QuotaExceeded`] over either cap. A
    /// terminal (lapsed/destroyed) record does not count against the quota — sweep it
    /// with [`sweep`](Self::sweep). Unset (the default) leaves serving uncapped.
    pub fn with_quota(mut self, per_lessee: usize, global: usize) -> ServerFleet<P> {
        self.max_per_lessee = Some(per_lessee);
        self.max_global = Some(global);
        self
    }

    /// Count the **live** (non-terminal) servers — those still occupying a quota slot
    /// (and, for Running, a backend machine). Lapsed/Destroyed records do not count.
    fn live_counts(&self, lessee: &str) -> (usize, usize) {
        let live = self.lock();
        let mut global = 0usize;
        let mut mine = 0usize;
        for s in live.values() {
            let counts = !matches!(s.record.state, ServerState::Lapsed | ServerState::Destroyed);
            if counts {
                global += 1;
                if s.record.lessee == lessee {
                    mine += 1;
                }
            }
        }
        (mine, global)
    }

    /// **Reconstruct** a fleet after a control-plane restart: open the durable store
    /// and re-provision a backend for every server that was Running when the control
    /// plane died, resuming each at its persisted uptime cursor. Non-running servers
    /// (created/stopped/lapsed/destroyed) are loaded as records without a backend.
    ///
    /// This is the crash-survival guarantee: a running server is **reconstructed**,
    /// not lost. The settlement rail is external (the dregg node / `Payable`), so it
    /// is passed back in — its exactly-once dedup plus the durable per-server period
    /// cursor make metering exactly-once across the restart.
    pub async fn reload(
        provider: P,
        store: ServerStore,
        settlement: Arc<dyn Settlement>,
        size: MachineSize,
        region: impl Into<String>,
        beneficiary: impl Into<String>,
    ) -> Result<ServerFleet<P>, ServerError> {
        let fleet = ServerFleet::new(provider, store, settlement, size, region, beneficiary);
        let records = fleet.store.all();
        let mut live = fleet.live.lock().expect("fleet poisoned");
        for mut rec in records {
            let machine = if rec.state.reconstructs_running() {
                // Re-provision a backend for the running server (crash-resume).
                match fleet.provider.provision(rec.spec()).await {
                    Ok(m) => {
                        rec.machine_id = Some(m.id.0.clone());
                        Some(m)
                    }
                    Err(e) => return Err(ServerError::Provider(e)),
                }
            } else {
                None
            };
            // Persist the refreshed machine_id for a reconstructed server, so the
            // record on disk reflects the new backend.
            if machine.is_some() {
                fleet
                    .store
                    .put(&rec)
                    .map_err(|e| ServerError::Store(e.to_string()))?;
            }
            // COMPUTE-AS-CELL: reconstruct the state cell with the same derived
            // identity. The boundary-root *commitment* survives in
            // `rec.checkpoint_root`; the reified *image* is the named Stage-B seam
            // (the node materializes it from the on-chain umem-ref), so a reloaded
            // cell starts empty under its stable id rather than re-implementing a
            // durable image side store (the `dreggnet-store` myopia).
            let cell = ComputeCell::new(&rec.lessee, &rec.app, &rec.name);
            live.insert(
                rec.id.clone(),
                LiveServer {
                    record: rec,
                    machine,
                    cell,
                },
            );
        }
        drop(live);
        Ok(fleet)
    }

    /// The underlying provider (e.g. to query a backend machine's status).
    pub fn provider(&self) -> &P {
        &self.provider
    }

    /// The durable store backing the fleet.
    pub fn store(&self) -> &ServerStore {
        &self.store
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, HashMap<String, LiveServer>> {
        self.live.lock().expect("fleet poisoned")
    }

    /// A snapshot of one server's durable record.
    pub fn server(&self, id: &str) -> Option<ServerRecord> {
        self.lock().get(id).map(|s| s.record.clone())
    }

    /// Every server the fleet is tracking (including stopped/destroyed records).
    pub fn servers(&self) -> Vec<ServerRecord> {
        self.lock().values().map(|s| s.record.clone()).collect()
    }

    /// Every **running** server (the metered fleet).
    pub fn running(&self) -> Vec<ServerRecord> {
        self.lock()
            .values()
            .filter(|s| s.record.state.is_up())
            .map(|s| s.record.clone())
            .collect()
    }

    /// **Create** a persistent server for `app` named `name`, authorized by `lease`.
    /// Lease-gated admission: an inactive lease is refused before any record is
    /// written (no server for unpaid work). The server starts in
    /// [`ServerState::Created`]; [`launch`](ServerFleet::launch) brings it up.
    #[tracing::instrument(skip(self, app, name), fields(lessee = %lease.lessee))]
    pub fn create(
        &self,
        app: impl Into<String>,
        name: impl Into<String>,
        lease: &Lease,
    ) -> Result<String, ServerError> {
        if !lease.is_active() {
            return Err(ServerError::LeaseInactive {
                lessee: lease.lessee.clone(),
            });
        }

        // SRV-1: admission reads the REAL funded reserve on the settlement rail (not
        // the lease's self-asserted `funded` bool) and refuses a lessee who cannot
        // even cover the first uptime period — no real machine for unpaid work.
        let funded = self.settlement.funded_balance(&lease.asset, &lease.lessee);
        if funded < lease.per_period_units {
            return Err(ServerError::Underfunded {
                lessee: lease.lessee.clone(),
                balance: funded,
                needed: lease.per_period_units,
            });
        }

        // SRV-1: enforce the per-lessee + global live-server quota before any record
        // is written (no unbounded record/backend growth from a single caller).
        let (mine, global) = self.live_counts(&lease.lessee);
        if let Some(limit) = self.max_global {
            if global >= limit {
                return Err(ServerError::QuotaExceeded {
                    scope: "global",
                    limit,
                    live: global,
                });
            }
        }
        if let Some(limit) = self.max_per_lessee {
            if mine >= limit {
                return Err(ServerError::QuotaExceeded {
                    scope: "per-lessee",
                    limit,
                    live: mine,
                });
            }
        }

        let id = format!("srv_{}", uuid::Uuid::new_v4().simple());
        let app = app.into();
        let name = name.into();
        // COMPUTE-AS-CELL: the server's dregg identity is its substrate cell id,
        // content-addressed from `(lessee, app, name)` — its umem state cell starts
        // empty (awake, no checkpoint).
        let cell = ComputeCell::new(&lease.lessee, &app, &name);
        let record = ServerRecord {
            id: id.clone(),
            app,
            name,
            state: ServerState::Created,
            lessee: lease.lessee.clone(),
            cap_grade: lease.cap_grade.to_string(),
            asset: lease.asset.clone(),
            budget_units: lease.budget_units,
            per_period_units: lease.per_period_units,
            size: size_to_str(self.size).to_string(),
            region: self.region.clone(),
            periods_metered: 0,
            machine_id: None,
            last_metered_at: None,
            cell_id: cell.cell_id().to_string(),
            checkpoint_root: None,
        };
        self.store
            .put(&record)
            .map_err(|e| ServerError::Store(e.to_string()))?;
        self.lock().insert(
            id.clone(),
            LiveServer {
                record,
                machine: None,
                cell,
            },
        );
        tracing::info!(server_id = %id, per_period_units = lease.per_period_units, "server created");
        Ok(id)
    }

    /// **Launch** a created server: provision a backend (the create→fulfill seam —
    /// "dispatch to a compute backend") and hold it Running. The server now serves
    /// continuously and is metered per uptime period until stopped/destroyed or its
    /// lease lapses.
    pub async fn launch(&self, id: &str) -> Result<(), ServerError> {
        self.bring_up(id, ServerState::Created, "launch").await
    }

    /// **Wake** a stopped/asleep server: re-provision a backend and resume serving.
    /// Metering resumes at the persisted uptime cursor (no lost or double-charged
    /// periods).
    ///
    /// **COMPUTE-AS-CELL — wake = restore.** The server's state cell is restored from
    /// its committed checkpoint boundary root (`docs/COMPUTE-AS-CELL.md`) **before**
    /// any backend is provisioned, so a corrupt checkpoint refuses the wake
    /// fail-closed (no backend for a server that cannot restore its genuine state).
    pub async fn wake(&self, id: &str) -> Result<(), ServerError> {
        let checkpoint_root = {
            let live = self.lock();
            let s = live
                .get(id)
                .ok_or_else(|| ServerError::NotFound(id.to_string()))?;
            s.record.checkpoint_root.clone()
        };
        if let Some(root) = checkpoint_root {
            let mut live = self.lock();
            if let Some(s) = live.get_mut(id) {
                // The in-process cell committed this root at `stop` — restore it,
                // re-witnessing the reified image folds back to the committed root
                // (fail-closed). Across a control-plane restart the image is not yet
                // durable in-process (the named Stage-B seam) so the root is unknown
                // to a reloaded cell — tolerate that (empty resume) rather than fail
                // the wake, but a TAMPERED in-process image is refused.
                match s.cell.time_travel(&root) {
                    Ok(()) => {}
                    Err(RestoreError::UnknownRoot(_)) => {}
                    Err(e @ RestoreError::ImageRootMismatch { .. }) => {
                        return Err(e.into());
                    }
                }
            }
        }
        self.bring_up(id, ServerState::Stopped, "wake").await
    }

    /// **COMPUTE-AS-CELL — fork (scale / clone).** Provision a SECOND server from
    /// `src_id`'s state cell: a new lease-gated `Created` server whose
    /// [`ComputeCell`] is `src.cell.fork(...)` — a distinct cell id over
    /// `(lessee, app, new_name)`, an independent heap that diverges from the source
    /// (a write to one does not touch the other) while sharing the source's
    /// fork-point boundary root (a provable common ancestor). The fork is
    /// lease-gated, funding-checked, and quota-checked exactly like [`create`], then
    /// can be [`launch`](Self::launch)ed and diverge with no effect on the source.
    /// This is `fork()` for real, metered compute — fork-to-scale.
    ///
    /// [`create`]: Self::create
    pub fn fork(
        &self,
        src_id: &str,
        new_name: impl Into<String>,
        lease: &Lease,
    ) -> Result<String, ServerError> {
        if !lease.is_active() {
            return Err(ServerError::LeaseInactive {
                lessee: lease.lessee.clone(),
            });
        }
        let new_name = new_name.into();
        // Snapshot the source's state cell + app namespace under the lock.
        let (forked_cell, app) = {
            let live = self.lock();
            let s = live
                .get(src_id)
                .ok_or_else(|| ServerError::NotFound(src_id.to_string()))?;
            (
                s.cell.fork(&lease.lessee, &s.record.app, &new_name),
                s.record.app.clone(),
            )
        };

        // Same admission discipline as `create`: real funded reserve, then quota.
        let funded = self.settlement.funded_balance(&lease.asset, &lease.lessee);
        if funded < lease.per_period_units {
            return Err(ServerError::Underfunded {
                lessee: lease.lessee.clone(),
                balance: funded,
                needed: lease.per_period_units,
            });
        }
        let (mine, global) = self.live_counts(&lease.lessee);
        if let Some(limit) = self.max_global {
            if global >= limit {
                return Err(ServerError::QuotaExceeded {
                    scope: "global",
                    limit,
                    live: global,
                });
            }
        }
        if let Some(limit) = self.max_per_lessee {
            if mine >= limit {
                return Err(ServerError::QuotaExceeded {
                    scope: "per-lessee",
                    limit,
                    live: mine,
                });
            }
        }

        let id = format!("srv_{}", uuid::Uuid::new_v4().simple());
        // The fork starts ASLEEP at its fork-point root: its state cell carries the
        // inherited image, committed to the shared boundary root.
        let checkpoint_root = forked_cell.latest_checkpoint_root().map(str::to_string);
        let record = ServerRecord {
            id: id.clone(),
            app,
            name: new_name,
            state: ServerState::Created,
            lessee: lease.lessee.clone(),
            cap_grade: lease.cap_grade.to_string(),
            asset: lease.asset.clone(),
            budget_units: lease.budget_units,
            per_period_units: lease.per_period_units,
            size: size_to_str(self.size).to_string(),
            region: self.region.clone(),
            periods_metered: 0,
            machine_id: None,
            last_metered_at: None,
            cell_id: forked_cell.cell_id().to_string(),
            checkpoint_root,
        };
        self.store
            .put(&record)
            .map_err(|e| ServerError::Store(e.to_string()))?;
        self.lock().insert(
            id.clone(),
            LiveServer {
                record,
                machine: None,
                cell: forked_cell,
            },
        );
        tracing::info!(server_id = %id, src = %src_id, "server forked from a checkpoint");
        Ok(id)
    }

    /// **COMPUTE-AS-CELL — time-travel / rollback.** Restore a server's state cell to
    /// an earlier committed boundary `root` from its checkpoint log (fail-closed: a
    /// root never committed by the cell, or one whose image does not reproduce it, is
    /// refused). The server's lifecycle state is untouched — this rolls the *state*
    /// back, not the lease.
    pub fn restore_to(&self, id: &str, root: &str) -> Result<(), ServerError> {
        let mut live = self.lock();
        let s = live
            .get_mut(id)
            .ok_or_else(|| ServerError::NotFound(id.to_string()))?;
        s.cell.time_travel(root)?;
        Ok(())
    }

    /// The server's substrate cell id (hex of `CellId::derive_raw`) — its dregg
    /// identity (COMPUTE-AS-CELL).
    pub fn cell_id(&self, id: &str) -> Option<String> {
        self.lock().get(id).map(|s| s.record.cell_id.clone())
    }

    /// The boundary root of the server's **live** state cell (COMPUTE-AS-CELL) — the
    /// 32-byte (64-hex) commitment that IS its current witnessed working state.
    pub fn live_root(&self, id: &str) -> Option<String> {
        self.lock().get(id).map(|s| s.cell.live_root())
    }

    /// Write a `(key, value)` cell into a server's live working-state heap
    /// (COMPUTE-AS-CELL) — the dregg-visible state a checkpoint commits. (The live
    /// in-sandbox process-image write is the named Stage-B seam; this is the
    /// host-API-visible working state.)
    pub fn write_state(
        &self,
        id: &str,
        key: impl Into<String>,
        value: impl Into<Vec<u8>>,
    ) -> Result<(), ServerError> {
        let mut live = self.lock();
        let s = live
            .get_mut(id)
            .ok_or_else(|| ServerError::NotFound(id.to_string()))?;
        s.cell.live_mut().write(key, value);
        Ok(())
    }

    /// Read a value from a server's live working-state heap (COMPUTE-AS-CELL).
    pub fn read_state(&self, id: &str, key: &str) -> Option<Vec<u8>> {
        self.lock()
            .get(id)
            .and_then(|s| s.cell.live().read(key).map(|v| v.to_vec()))
    }

    /// Shared launch/wake: from `expected` state, provision a backend → Running,
    /// **pre-paying the upcoming uptime period at bring-up** (SRV-4).
    ///
    /// A burst of launches must not hold N real machines for free in the window
    /// between provisioning and the first metering tick: bring-up settles the next
    /// uptime period (`periods_metered + 1`) up front — "no machine without payment".
    /// If the lessee cannot cover that period (budget exhausted, or insufficient funds
    /// on the rail), the just-provisioned backend is **torn down** and the bring-up is
    /// **refused** with the server left in its prior state — no Running machine ever
    /// exists unpaid. The metering tick then resumes at the *next* period, so the
    /// exactly-once `(server_id, period)` settlement cursor is never double-charged.
    #[tracing::instrument(skip(self), fields(server_id = %id, op))]
    async fn bring_up(
        &self,
        id: &str,
        expected: ServerState,
        op: &'static str,
    ) -> Result<(), ServerError> {
        let mut record = {
            let live = self.lock();
            let s = live
                .get(id)
                .ok_or_else(|| ServerError::NotFound(id.to_string()))?;
            if s.record.state != expected {
                return Err(ServerError::BadState {
                    id: id.to_string(),
                    state: s.record.state,
                    op,
                });
            }
            s.record.clone()
        };

        // SRV-4: the period this bring-up pre-pays (period 1 for a fresh launch, the
        // resume period for a wake). Refuse before provisioning if the lease budget
        // cannot even cover it — no backend is dispatched for unpayable uptime. The
        // ceiling decision is the shared replenishing-budget core (`lease_budget_admits`),
        // not a hand-rolled `period * per_period_units > budget` (one verified meter
        // decision over every uptime/lease site; overflow-safe).
        let charge_period = record.periods_metered + 1;
        if !dreggnet_exec::budget::lease_budget_admits(
            record.budget_units,
            record.per_period_units,
            charge_period,
        ) {
            return Err(ServerError::Underfunded {
                lessee: record.lessee.clone(),
                balance: self
                    .settlement
                    .funded_balance(&record.asset, &record.lessee),
                needed: record.per_period_units,
            });
        }

        let machine = self.provider.provision(record.spec()).await?;

        // SRV-4: settle the upcoming period BEFORE the server is held Running. On
        // insufficient funds (or any settle fault) the just-provisioned backend is
        // released and the bring-up is refused — the server stays in its prior state.
        let charge = LeaseCharge::new(
            &record.lessee,
            &self.beneficiary,
            &record.asset,
            &record.id,
            charge_period,
            record.per_period_units,
        );
        match self.settlement.settle(&charge) {
            Ok(_receipt) => {}
            Err(SettleError::InsufficientFunds { .. }) => {
                self.release_backend(&machine.id).await?;
                tracing::warn!(
                    period = charge_period,
                    needed = record.per_period_units,
                    "bring-up refused: lessee cannot pre-pay the period — backend torn down"
                );
                return Err(ServerError::Underfunded {
                    lessee: record.lessee.clone(),
                    balance: self
                        .settlement
                        .funded_balance(&record.asset, &record.lessee),
                    needed: record.per_period_units,
                });
            }
            Err(e) => {
                self.release_backend(&machine.id).await?;
                return Err(ServerError::Settle(e.to_string()));
            }
        }

        record.state = ServerState::Running;
        record.machine_id = Some(machine.id.0.clone());
        record.periods_metered = charge_period;
        // COMPUTE-AS-CELL: a Running server is AWAKE — its live state is mutating and
        // not yet committed, so it carries no checkpoint root (a wake's restore
        // already happened before this point; see `wake`).
        record.checkpoint_root = None;
        // Mark the bring-up time so the idle reaper (SRV-3) has a fresh baseline — a
        // just-launched server is not instantly "stale".
        record.last_metered_at = Some(now_unix_secs());
        self.store
            .put(&record)
            .map_err(|e| ServerError::Store(e.to_string()))?;
        // Update in place so the server's umem state cell (COMPUTE-AS-CELL) is
        // preserved across the bring-up rather than replaced with a fresh one.
        if let Some(s) = self.lock().get_mut(id) {
            s.record = record;
            s.machine = Some(machine);
        }
        tracing::info!(
            period = charge_period,
            "brought up Running, period pre-paid"
        );
        Ok(())
    }

    /// Release a backend machine, tolerating an already-gone machine (idempotent) —
    /// the rollback leg when a bring-up is refused after provisioning (SRV-4).
    async fn release_backend(&self, machine_id: &MachineId) -> Result<(), ServerError> {
        match self.provider.terminate(machine_id).await {
            Ok(()) | Err(ProviderError::NotFound(_)) => Ok(()),
            Err(e) => Err(ServerError::Provider(e)),
        }
    }

    /// **Meter one uptime period** for a running server: settle one period's rent
    /// (lessee → provider) as a conserving, exactly-once transfer keyed
    /// `(server_id, period)`, and advance the durable cursor. If the next period
    /// would exceed the lease budget (or the lessee's funds are exhausted), the
    /// server's lease has **lapsed** → it is reaped (machine released, state
    /// [`ServerState::Lapsed`]). Metering a non-running server is a no-op.
    #[tracing::instrument(skip(self), fields(server_id = %id))]
    pub async fn meter_period(&self, id: &str) -> Result<MeterOutcome, ServerError> {
        let record = {
            let live = self.lock();
            let s = live
                .get(id)
                .ok_or_else(|| ServerError::NotFound(id.to_string()))?;
            if !s.record.state.is_up() {
                return Ok(MeterOutcome::NotRunning);
            }
            s.record.clone()
        };

        let next_period = record.periods_metered + 1;

        // Budget gate: a period whose charge would exceed the funded budget is a
        // lapse — no uptime billed beyond what the lease authorizes. The ceiling is the
        // shared replenishing-budget decision core (the same one bring-up uses).
        if !dreggnet_exec::budget::lease_budget_admits(
            record.budget_units,
            record.per_period_units,
            next_period,
        ) {
            return self
                .reap(id, "uptime budget exhausted")
                .await
                .map(|reason| MeterOutcome::Lapsed { reason });
        }

        let charge = LeaseCharge::new(
            &record.lessee,
            &self.beneficiary,
            &record.asset,
            &record.id,
            next_period,
            record.per_period_units,
        );

        match self.settlement.settle(&charge) {
            Ok(_receipt) => {
                let mut updated = record;
                updated.periods_metered = next_period;
                // Refresh the durable freshness mark so the idle reaper (SRV-3) sees a
                // live server, and a stalled-then-resumed driver does not reap it.
                updated.last_metered_at = Some(now_unix_secs());
                self.store
                    .put(&updated)
                    .map_err(|e| ServerError::Store(e.to_string()))?;
                if let Some(s) = self.lock().get_mut(id) {
                    s.record = updated;
                }
                tracing::info!(
                    period = next_period,
                    units = charge.amount,
                    "metered uptime period"
                );
                Ok(MeterOutcome::Metered {
                    period: next_period,
                    units: charge.amount,
                })
            }
            // Funds exhausted on the rail is a lapse (the lessee can no longer pay).
            Err(SettleError::InsufficientFunds { .. }) => {
                tracing::warn!(
                    period = next_period,
                    "lessee funds exhausted — lapsing + reaping"
                );
                self.reap(id, "lessee funds exhausted")
                    .await
                    .map(|reason| MeterOutcome::Lapsed { reason })
            }
            Err(e) => Err(ServerError::Settle(e.to_string())),
        }
    }

    /// Meter one uptime period for **every running server** — the control loop's
    /// per-period uptime sweep. Returns how many were metered, reaped, and errored.
    ///
    /// **SRV-2:** a single server's metering error (a store-write fault, a non-budget
    /// settle error, a provider `terminate` fault during reap) is recorded into the
    /// report and the sweep **continues** to its siblings — it no longer `?`-aborts the
    /// whole sweep, so one reliably-erroring server cannot let every server visited
    /// after it (in arbitrary `HashMap` order) escape metering/reaping (a free run).
    /// This matches the orchestrator's per-lease isolation.
    #[tracing::instrument(skip(self))]
    pub async fn tick_uptime(&self) -> Result<UptimeReport, ServerError> {
        let ids: Vec<String> = self.running().into_iter().map(|r| r.id).collect();
        let mut report = UptimeReport::default();
        for id in ids {
            match self.meter_period(&id).await {
                Ok(MeterOutcome::Metered { .. }) => report.metered += 1,
                Ok(MeterOutcome::Lapsed { .. }) => report.reaped += 1,
                Ok(MeterOutcome::NotRunning) => {}
                Err(e) => {
                    report.errored += 1;
                    report.errors.push((id, e.to_string()));
                }
            }
        }
        tracing::info!(
            metered = report.metered,
            reaped = report.reaped,
            errored = report.errored,
            "uptime sweep complete"
        );
        Ok(report)
    }

    /// **Independent idle reaper** (SRV-3): reap every Running server whose last meter
    /// (or bring-up) is older than `max_idle_secs` relative to `now_unix`. Run this on
    /// a SEPARATE timer from [`tick_uptime`](Self::tick_uptime) so a stalled or wedged
    /// metering driver cannot leave a Running server holding its backend machine
    /// indefinitely, unbilled — the safety net the per-tick meter alone does not give
    /// (metering is only reached THROUGH a tick). Returns how many were reaped.
    ///
    /// `now_unix` is passed in (rather than read internally) so the reaper is
    /// deterministically testable; the production driver passes [`now_unix_secs`].
    #[tracing::instrument(skip(self))]
    pub async fn reap_idle(&self, now_unix: i64, max_idle_secs: i64) -> Result<usize, ServerError> {
        let stale: Vec<String> = self
            .lock()
            .values()
            .filter(|s| s.record.state.is_up())
            .filter(|s| {
                let last = s.record.last_metered_at.unwrap_or(0);
                now_unix.saturating_sub(last) > max_idle_secs
            })
            .map(|s| s.record.id.clone())
            .collect();
        let mut reaped = 0usize;
        for id in stale {
            self.reap(
                &id,
                "idle reaper: metering stalled past the staleness bound",
            )
            .await?;
            reaped += 1;
        }
        if reaped > 0 {
            tracing::warn!(
                reaped,
                max_idle_secs,
                "idle reaper released stalled servers"
            );
        }
        Ok(reaped)
    }

    /// **Stop / sleep** a running server: release its backend machine but retain the
    /// durable record (so it can be [`woken`](ServerFleet::wake)). A stopped server
    /// is metered nothing.
    pub async fn stop(&self, id: &str) -> Result<(), ServerError> {
        self.tear_down(id, ServerState::Stopped, "stop").await
    }

    /// **Destroy** a server: release its backend machine and mark it
    /// [`ServerState::Destroyed`]. The record is retained (last-write-wins) so a
    /// reconstruct skips it.
    pub async fn destroy(&self, id: &str) -> Result<(), ServerError> {
        self.tear_down(id, ServerState::Destroyed, "destroy").await
    }

    /// Shared stop/destroy: release the backend (if any) and persist the new state.
    async fn tear_down(
        &self,
        id: &str,
        new_state: ServerState,
        op: &'static str,
    ) -> Result<(), ServerError> {
        let (mut record, machine) = {
            let mut live = self.lock();
            let s = live
                .get_mut(id)
                .ok_or_else(|| ServerError::NotFound(id.to_string()))?;
            // Stopping/destroying an already-terminal server is rejected as a bad
            // state for stop, but destroy is idempotent over any non-destroyed state.
            if op == "stop" && s.record.state != ServerState::Running {
                return Err(ServerError::BadState {
                    id: id.to_string(),
                    state: s.record.state,
                    op,
                });
            }
            // COMPUTE-AS-CELL — stop = sleep = checkpoint: commit the live state to a
            // umem boundary root before the backend is released, so a wake can
            // restore it. The commitment rides the durable record; a sleeping
            // (checkpointed) server is metered nothing (pay-only-while-awake).
            if op == "stop" {
                let root = s.cell.checkpoint();
                s.record.checkpoint_root = Some(root);
            }
            (s.record.clone(), s.machine.clone())
        };

        if let Some(m) = machine {
            // Release the backend; a NotFound (already gone) is fine — idempotent.
            match self.provider.terminate(&m.id).await {
                Ok(()) | Err(ProviderError::NotFound(_)) => {}
                Err(e) => return Err(ServerError::Provider(e)),
            }
        }

        record.state = new_state;
        record.machine_id = None;
        self.store
            .put(&record)
            .map_err(|e| ServerError::Store(e.to_string()))?;
        if let Some(s) = self.lock().get_mut(id) {
            s.record = record;
            s.machine = None;
        }
        Ok(())
    }

    /// Reap a server whose lease lapsed: release the backend, mark Lapsed, persist.
    /// Returns the lapse reason (for the [`MeterOutcome::Lapsed`]).
    async fn reap(&self, id: &str, reason: &str) -> Result<String, ServerError> {
        let machine = self.lock().get(id).and_then(|s| s.machine.clone());
        if let Some(m) = machine {
            match self.provider.terminate(&m.id).await {
                Ok(()) | Err(ProviderError::NotFound(_)) => {}
                Err(e) => return Err(ServerError::Provider(e)),
            }
        }
        if let Some(mut record) = self.server(id) {
            record.state = ServerState::Lapsed;
            record.machine_id = None;
            self.store
                .put(&record)
                .map_err(|e| ServerError::Store(e.to_string()))?;
            if let Some(s) = self.lock().get_mut(id) {
                s.record = record;
                s.machine = None;
            }
        }
        Ok(reason.to_string())
    }

    /// **Sweep** terminal (lapsed/destroyed) server records out of both the in-memory
    /// `live` map and the durable [`ServerStore`] (SRV-1) — bounding the disk + memory
    /// an append-only fleet would otherwise grow without limit, and freeing the quota
    /// slots the terminal servers held. Returns how many records were swept. Run it on
    /// the control loop's periodic tick alongside [`tick_uptime`](Self::tick_uptime).
    pub fn sweep(&self) -> Result<usize, ServerError> {
        {
            let mut live = self.lock();
            live.retain(|_, s| {
                !matches!(s.record.state, ServerState::Lapsed | ServerState::Destroyed)
            });
        }
        self.store
            .sweep_terminated()
            .map_err(|e| ServerError::Store(e.to_string()))
    }

    /// **Health**: whether the server's backend machine is actually Running on the
    /// provider (the health probe the gateway ingress would gate routing on). A
    /// server with no backend (created/stopped/destroyed) is not healthy.
    pub async fn health(&self, id: &str) -> Result<bool, ServerError> {
        let machine_id = self
            .lock()
            .get(id)
            .and_then(|s| s.machine.as_ref().map(|m| m.id.clone()));
        match machine_id {
            Some(mid) => match self.provider.status(&mid).await {
                Ok(status) => Ok(status == MachineStatus::Running),
                Err(ProviderError::NotFound(_)) => Ok(false),
                Err(e) => Err(ServerError::Provider(e)),
            },
            None => Ok(false),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::local::LocalProvider;
    use dreggnet_durable::ConservingLedger;

    fn temp_store_path(tag: &str) -> std::path::PathBuf {
        let mut p = std::env::temp_dir();
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        p.push(format!("dreggnet-server-store-{tag}-{nanos}.jsonl"));
        p
    }

    fn lease(lessee: &str, budget: i64, per_period: i64) -> Lease {
        Lease::funded(lessee, CapGrade::Sandboxed, "DREGG", budget, per_period)
    }

    fn fleet(path: &std::path::Path, ledger: Arc<ConservingLedger>) -> ServerFleet<LocalProvider> {
        ServerFleet::new(
            LocalProvider::new(),
            ServerStore::open(path).unwrap(),
            ledger,
            MachineSize::Small,
            "local",
            "dreggnet-provider",
        )
    }

    #[tokio::test]
    async fn create_launch_meter_stop_wake_destroy_lifecycle() {
        let path = temp_store_path("lifecycle");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("DREGG", "agent", 100);
        let f = fleet(&path, ledger.clone());

        // create → Created (lease-gated).
        let id = f.create("my-app", "web", &lease("agent", 100, 2)).unwrap();
        assert_eq!(f.server(&id).unwrap().state, ServerState::Created);
        assert!(!f.health(&id).await.unwrap());

        // launch → Running, a backend is held; SRV-4 pre-pays period 1 at launch
        // (no machine held free until the first tick).
        f.launch(&id).await.unwrap();
        assert_eq!(f.server(&id).unwrap().state, ServerState::Running);
        assert!(f.health(&id).await.unwrap());
        assert_eq!(
            f.server(&id).unwrap().periods_metered,
            1,
            "launch pre-pays period 1"
        );
        assert_eq!(ledger.balance("DREGG", "dreggnet-provider"), 2);

        // meter two more uptime periods (2, 3) → settled lessee → provider, 2 units each.
        for expect_period in 2..=3 {
            let out = f.meter_period(&id).await.unwrap();
            assert_eq!(
                out,
                MeterOutcome::Metered {
                    period: expect_period,
                    units: 2
                }
            );
        }
        assert_eq!(f.server(&id).unwrap().periods_metered, 3);
        assert_eq!(ledger.balance("DREGG", "agent"), 94);
        assert_eq!(ledger.balance("DREGG", "dreggnet-provider"), 6);
        assert_eq!(ledger.total_supply("DREGG"), 100, "Σδ = 0");

        // stop → Stopped, backend released, no uptime billed while asleep.
        f.stop(&id).await.unwrap();
        assert_eq!(f.server(&id).unwrap().state, ServerState::Stopped);
        assert_eq!(f.meter_period(&id).await.unwrap(), MeterOutcome::NotRunning);

        // wake → Running again, SRV-4 pre-pays the resume period (4) at wake.
        f.wake(&id).await.unwrap();
        assert_eq!(
            f.server(&id).unwrap().periods_metered,
            4,
            "wake pre-pays period 4"
        );
        assert_eq!(ledger.balance("DREGG", "dreggnet-provider"), 8);

        // destroy → Destroyed, backend released.
        f.destroy(&id).await.unwrap();
        assert_eq!(f.server(&id).unwrap().state, ServerState::Destroyed);
        assert!(!f.health(&id).await.unwrap());

        std::fs::remove_file(&path).ok();
    }

    #[tokio::test]
    async fn uptime_budget_exhaustion_lapses_and_reaps() {
        let path = temp_store_path("lapse");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("DREGG", "agent", 100);
        let f = fleet(&path, ledger.clone());

        // budget 5, per-period 2 → periods 1,2 fit (4 ≤ 5); period 3 (6 > 5) lapses.
        let id = f.create("app", "srv", &lease("agent", 5, 2)).unwrap();
        // SRV-4: launch pre-pays period 1.
        f.launch(&id).await.unwrap();
        assert!(matches!(
            f.meter_period(&id).await.unwrap(),
            MeterOutcome::Metered { period: 2, .. }
        ));
        assert!(matches!(
            f.meter_period(&id).await.unwrap(),
            MeterOutcome::Lapsed { .. }
        ));

        // Reaped: state Lapsed, backend released, only the 2 affordable periods billed.
        assert_eq!(f.server(&id).unwrap().state, ServerState::Lapsed);
        assert_eq!(f.server(&id).unwrap().periods_metered, 2);
        assert_eq!(ledger.balance("DREGG", "dreggnet-provider"), 4);

        std::fs::remove_file(&path).ok();
    }

    #[tokio::test]
    async fn inactive_lease_creates_no_server() {
        let path = temp_store_path("inactive");
        let ledger = Arc::new(ConservingLedger::new());
        let f = fleet(&path, ledger);
        let dead = Lease {
            lessee: "broke".into(),
            cap_grade: CapGrade::Sandboxed,
            asset: "DREGG".into(),
            budget_units: 100,
            per_period_units: 1,
            funded: false,
        };
        assert!(matches!(
            f.create("app", "srv", &dead),
            Err(ServerError::LeaseInactive { lessee }) if lessee == "broke"
        ));
        assert!(f.store().is_empty());
        std::fs::remove_file(&path).ok();
    }

    // ---- SRV-1 / #9 ----

    /// Admission reads the REAL funded reserve, not the lease's self-asserted `funded`
    /// bool. A lease that asserts `funded: true` but whose lessee holds no reserve on
    /// the settlement rail is refused — no real machine for unpaid work.
    #[tokio::test]
    async fn create_refuses_a_self_asserted_lease_with_no_real_funding() {
        let path = temp_store_path("underfunded");
        let ledger = Arc::new(ConservingLedger::new());
        // NOTE: the ledger is NOT funded for "agent".
        let f = fleet(&path, ledger);

        // A self-asserted funded lease (the exact PoC bool) — but the rail shows 0.
        let liar = lease("agent", 100, 2);
        assert!(liar.funded, "the lease self-asserts funded");
        assert!(matches!(
            f.create("app", "srv", &liar),
            Err(ServerError::Underfunded { lessee, balance: 0, needed: 2 }) if lessee == "agent"
        ));
        assert!(
            f.store().is_empty(),
            "no record written for an unfunded lessee"
        );

        // Once the lessee is genuinely funded on the rail, admission passes.
        // (Re-open a funded ledger over a fresh fleet.)
        let funded_ledger = Arc::new(ConservingLedger::new());
        funded_ledger.fund("DREGG", "agent", 10);
        let f2 = fleet(&path, funded_ledger);
        assert!(f2.create("app", "srv", &lease("agent", 100, 2)).is_ok());
        std::fs::remove_file(&path).ok();
    }

    /// A per-lessee + global server-count quota refuses admission over the cap, so a
    /// caller cannot loop `create` to grow records + backends without bound.
    #[tokio::test]
    async fn create_enforces_the_server_count_quota() {
        let path = temp_store_path("quota");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("DREGG", "agent", 1_000);
        ledger.fund("DREGG", "other", 1_000);
        let f = ServerFleet::new(
            LocalProvider::new(),
            ServerStore::open(&path).unwrap(),
            ledger,
            MachineSize::Small,
            "local",
            "dreggnet-provider",
        )
        .with_quota(2, 3); // ≤2 per lessee, ≤3 global

        // The per-lessee cap (2) bites on the third for `agent`.
        f.create("app", "a1", &lease("agent", 100, 2)).unwrap();
        f.create("app", "a2", &lease("agent", 100, 2)).unwrap();
        assert!(matches!(
            f.create("app", "a3", &lease("agent", 100, 2)),
            Err(ServerError::QuotaExceeded {
                scope: "per-lessee",
                limit: 2,
                ..
            })
        ));

        // The global cap (3) bites once a third lessee-slot is taken.
        f.create("app", "o1", &lease("other", 100, 2)).unwrap(); // global now 3
        assert!(matches!(
            f.create("app", "o2", &lease("other", 100, 2)),
            Err(ServerError::QuotaExceeded {
                scope: "global",
                limit: 3,
                ..
            })
        ));
        std::fs::remove_file(&path).ok();
    }

    /// Sweeping terminal records frees both disk (the append-only store is compacted)
    /// and the quota slot the terminal server held.
    #[tokio::test]
    async fn sweep_compacts_terminal_records_and_frees_quota() {
        let path = temp_store_path("sweep");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("DREGG", "agent", 1_000);
        let f = ServerFleet::new(
            LocalProvider::new(),
            ServerStore::open(&path).unwrap(),
            ledger,
            MachineSize::Small,
            "local",
            "dreggnet-provider",
        )
        .with_quota(2, 10);

        let id1 = f.create("app", "s1", &lease("agent", 100, 2)).unwrap();
        let _id2 = f.create("app", "s2", &lease("agent", 100, 2)).unwrap();
        // At the per-lessee cap (2): a third is refused.
        assert!(matches!(
            f.create("app", "s3", &lease("agent", 100, 2)),
            Err(ServerError::QuotaExceeded { .. })
        ));

        // Destroy one → it becomes terminal but its record still sits in the store.
        f.destroy(&id1).await.unwrap();
        let before = f.store().len();
        assert_eq!(before, 2, "the destroyed record is retained until swept");

        // Sweep: the terminal record is compacted out, freeing a quota slot.
        let removed = f.sweep().unwrap();
        assert_eq!(removed, 1);
        assert_eq!(f.store().len(), 1, "the store is compacted");

        // The freed slot admits a new server again.
        assert!(f.create("app", "s4", &lease("agent", 100, 2)).is_ok());

        // The compacted store survives a reload (only the survivors come back).
        let reopened = ServerStore::open(&path).unwrap();
        assert_eq!(
            reopened.len(),
            2,
            "reload sees only the swept-and-survivor set"
        );
        std::fs::remove_file(&path).ok();
    }

    // ---- SRV-2 / SRV-3 ----

    /// A settlement that errors (non-budget `Backend` fault) for ONE designated
    /// lease/server id, delegating everything else to an inner conserving ledger —
    /// the failure injector for the SRV-2 sweep-isolation test.
    struct FlakySettlement {
        inner: Arc<ConservingLedger>,
        fail_for: String,
        /// Fault only from this period onward, so the SRV-4 launch pre-pay (period 1)
        /// still succeeds and the fault lands on the metering sweep (period ≥ this).
        fail_from_period: i64,
    }

    impl dreggnet_durable::Settlement for FlakySettlement {
        fn settle(
            &self,
            charge: &dreggnet_durable::LeaseCharge,
        ) -> Result<dreggnet_durable::SettleReceipt, SettleError> {
            if charge.lease_id == self.fail_for && charge.period >= self.fail_from_period {
                return Err(SettleError::Backend("injected sweep fault".into()));
            }
            self.inner.settle(charge)
        }
        fn settled_total(&self, lease_id: &str) -> i64 {
            self.inner.settled_total(lease_id)
        }
        fn funded_balance(&self, asset: &str, holder: &str) -> i64 {
            self.inner.funded_balance(asset, holder)
        }
    }

    /// SRV-2: one server's metering error does not abort the whole sweep — its
    /// siblings are still metered (no free run for servers iterated after the faulty
    /// one), and the failure is surfaced in the report.
    #[tokio::test]
    async fn a_failing_server_does_not_starve_the_sweep() {
        let path = temp_store_path("sweep-isolation");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("DREGG", "agent", 1_000);

        // Create three servers, then point the settlement fault at the middle one.
        let store = ServerStore::open(&path).unwrap();
        let pre = ServerFleet::new(
            LocalProvider::new(),
            store,
            ledger.clone(),
            MachineSize::Small,
            "local",
            "dreggnet-provider",
        );
        let a = pre.create("app", "a", &lease("agent", 100, 2)).unwrap();
        let bad = pre.create("app", "bad", &lease("agent", 100, 2)).unwrap();
        let c = pre.create("app", "c", &lease("agent", 100, 2)).unwrap();
        drop(pre); // release the store so the real fleet can re-open it

        // Reload the three persisted records into a fleet whose settlement faults on
        // the middle server, then launch all three.
        let f = ServerFleet::reload(
            LocalProvider::new(),
            ServerStore::open(&path).unwrap(),
            Arc::new(FlakySettlement {
                inner: ledger.clone(),
                fail_for: bad.clone(),
                fail_from_period: 2,
            }),
            MachineSize::Small,
            "local",
            "dreggnet-provider",
        )
        .await
        .unwrap();
        // Launch all three — the SRV-4 launch pre-pay (period 1) succeeds for each
        // (the injected fault is gated to period ≥ 2, the metering sweep).
        for id in [&a, &bad, &c] {
            f.launch(id).await.unwrap();
        }

        // The sweep continues past the faulty server: the two good servers are metered
        // (period 2) regardless of iteration order, and the fault is recorded — not
        // `?`-aborted.
        let report = f.tick_uptime().await.unwrap();
        assert_eq!(
            report.metered, 2,
            "both good servers metered despite the fault"
        );
        assert_eq!(report.errored, 1);
        assert_eq!(report.errors.len(), 1);
        assert_eq!(report.errors[0].0, bad);
        assert_eq!(f.server(&a).unwrap().periods_metered, 2);
        assert_eq!(f.server(&c).unwrap().periods_metered, 2);
        assert_eq!(
            f.server(&bad).unwrap().periods_metered,
            1,
            "the faulty one billed only its launch pre-pay, nothing on the faulting sweep"
        );
        std::fs::remove_file(&path).ok();
    }

    /// SRV-3: the independent idle reaper releases a Running server whose metering has
    /// stalled past the staleness bound — a wedged driver cannot hold a backend forever
    /// unbilled. A freshly-metered server is NOT reaped.
    #[tokio::test]
    async fn idle_reaper_releases_a_stalled_server() {
        let path = temp_store_path("idle-reaper");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("DREGG", "agent", 1_000);
        let f = fleet(&path, ledger);

        let id = f.create("app", "srv", &lease("agent", 100, 2)).unwrap();
        f.launch(&id).await.unwrap();
        let launched_at = f
            .server(&id)
            .unwrap()
            .last_metered_at
            .expect("launch stamps the clock");

        // Not yet stale (within the bound): no reap, still Running + healthy.
        assert_eq!(f.reap_idle(launched_at + 30, 60).await.unwrap(), 0);
        assert_eq!(f.server(&id).unwrap().state, ServerState::Running);
        assert!(f.health(&id).await.unwrap());

        // A metering tick refreshes the freshness mark (so a live, metered server is
        // never reaped by the safety net).
        f.meter_period(&id).await.unwrap();
        let metered_at = f.server(&id).unwrap().last_metered_at.unwrap();
        assert!(metered_at >= launched_at);
        assert_eq!(
            f.reap_idle(metered_at + 30, 60).await.unwrap(),
            0,
            "fresh meter ⇒ not reaped"
        );

        // The driver stalls: now far past the bound → the idle reaper releases it.
        let reaped = f.reap_idle(metered_at + 120, 60).await.unwrap();
        assert_eq!(reaped, 1);
        assert_eq!(f.server(&id).unwrap().state, ServerState::Lapsed);
        assert!(!f.health(&id).await.unwrap(), "backend released");
        std::fs::remove_file(&path).ok();
    }

    // ---- SRV-4 ----

    /// SRV-4: a launch pre-pays its first uptime period, and a launch the lessee can
    /// no longer fund is **refused** with the just-provisioned backend torn down — no
    /// real machine is ever held at zero up-front cost. Fund exactly one period, create
    /// two servers, launch both: the first gets a (paid) machine; the second's launch
    /// settle hits InsufficientFunds → refused, no Running machine, only one period
    /// ever billed.
    #[tokio::test]
    async fn launch_pre_pays_and_refuses_an_unfunded_launch() {
        let path = temp_store_path("launch-charge");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("DREGG", "agent", 2); // exactly one period of rent
        let f = fleet(&path, ledger.clone());

        // Both create: admission's funded-reserve check sees 2 ≥ the 2-unit period.
        let s1 = f.create("app", "s1", &lease("agent", 100, 2)).unwrap();
        let s2 = f.create("app", "s2", &lease("agent", 100, 2)).unwrap();

        // First launch pre-pays period 1 (2 units) → the lessee's funds are now spent.
        f.launch(&s1).await.unwrap();
        assert_eq!(f.server(&s1).unwrap().state, ServerState::Running);
        assert_eq!(f.server(&s1).unwrap().periods_metered, 1);
        assert_eq!(ledger.balance("DREGG", "agent"), 0);
        assert_eq!(ledger.balance("DREGG", "dreggnet-provider"), 2);

        // Second launch cannot pre-pay → refused, backend torn down, server unchanged.
        assert!(matches!(
            f.launch(&s2).await,
            Err(ServerError::Underfunded { lessee, .. }) if lessee == "agent"
        ));
        assert_eq!(
            f.server(&s2).unwrap().state,
            ServerState::Created,
            "no Running machine for unpaid work"
        );
        assert!(!f.health(&s2).await.unwrap(), "no backend held");
        assert_eq!(f.server(&s2).unwrap().periods_metered, 0);

        // Exactly one period was ever billed (s1's launch) — Σδ = 0 preserved.
        assert_eq!(ledger.balance("DREGG", "dreggnet-provider"), 2);
        assert_eq!(ledger.total_supply("DREGG"), 2, "Σδ = 0");

        // The budget-gate leg: a lease whose budget cannot cover even one period is
        // refused BEFORE any backend is provisioned.
        ledger.fund("DREGG", "agent", 10);
        let s3 = f.create("app", "s3", &lease("agent", 1, 2)).unwrap(); // budget 1 < per-period 2
        assert!(matches!(
            f.launch(&s3).await,
            Err(ServerError::Underfunded { .. })
        ));
        assert_eq!(f.server(&s3).unwrap().state, ServerState::Created);

        std::fs::remove_file(&path).ok();
    }

    // ---- COMPUTE-AS-CELL (docs/COMPUTE-AS-CELL.md) ----

    /// The server's identity IS its substrate cell id (content-addressed from
    /// `(lessee, app, name)`), not the random `srv_…` row key.
    #[tokio::test]
    async fn server_identity_is_the_substrate_cell_id() {
        let path = temp_store_path("cell-id");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("DREGG", "agent", 100);
        let f = fleet(&path, ledger);

        let id = f.create("my-app", "web", &lease("agent", 100, 2)).unwrap();
        let cell_id = f.cell_id(&id).unwrap();
        assert_eq!(
            cell_id.len(),
            64,
            "the cell id is a 64-hex substrate CellId"
        );
        assert_eq!(
            cell_id,
            crate::compute_cell::cell_id_hex("agent", "my-app", "web"),
            "derived deterministically from (lessee, app, name)"
        );
        assert_eq!(f.server(&id).unwrap().cell_id, cell_id);
        std::fs::remove_file(&path).ok();
    }

    /// TEETH — sleep = checkpoint, wake = restore: a server's working state is
    /// committed to a boundary root at stop and reconstructed at wake (continuous),
    /// fail-closed if the checkpoint cannot be reproduced.
    #[tokio::test]
    async fn sleep_checkpoints_and_wake_restores_state() {
        let path = temp_store_path("sleep-wake");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("DREGG", "agent", 100);
        let f = fleet(&path, ledger);

        let id = f.create("app", "srv", &lease("agent", 100, 2)).unwrap();
        f.launch(&id).await.unwrap();
        // Awake: write working state, no checkpoint root yet.
        f.write_state(&id, "session", b"alpha".to_vec()).unwrap();
        f.write_state(&id, "counter", b"7".to_vec()).unwrap();
        assert_eq!(
            f.server(&id).unwrap().checkpoint_root,
            None,
            "Running ⇒ awake, no checkpoint"
        );
        let awake_root = f.live_root(&id).unwrap();

        // Sleep = checkpoint: the boundary root commits + is persisted.
        f.stop(&id).await.unwrap();
        let cp = f.server(&id).unwrap().checkpoint_root;
        assert_eq!(
            cp.as_deref(),
            Some(awake_root.as_str()),
            "stop commits the live root"
        );

        // Wake = restore: the working state is reconstructed continuously, and the
        // server is awake again (no checkpoint root).
        f.wake(&id).await.unwrap();
        assert_eq!(f.read_state(&id, "session"), Some(b"alpha".to_vec()));
        assert_eq!(f.read_state(&id, "counter"), Some(b"7".to_vec()));
        assert_eq!(
            f.live_root(&id).unwrap(),
            awake_root,
            "restored state folds to the committed root"
        );
        assert_eq!(
            f.server(&id).unwrap().checkpoint_root,
            None,
            "woken ⇒ awake again"
        );
        std::fs::remove_file(&path).ok();
    }

    /// TEETH — pay-only-while-awake: a sleeping (checkpointed) server draws NOTHING;
    /// metering resumes only after a wake. Sleep = checkpoint makes pay-per-use real.
    #[tokio::test]
    async fn a_sleeping_server_is_not_billed() {
        let path = temp_store_path("pay-while-awake");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("DREGG", "agent", 100);
        let f = fleet(&path, ledger.clone());

        let id = f.create("app", "srv", &lease("agent", 100, 2)).unwrap();
        f.launch(&id).await.unwrap(); // period 1 pre-paid (2 units)
        f.meter_period(&id).await.unwrap(); // period 2 (2 units)
        let billed_awake = ledger.balance("DREGG", "dreggnet-provider");
        assert_eq!(billed_awake, 4);

        // Sleep: now metering is a no-op and bills nothing, for many ticks.
        f.stop(&id).await.unwrap();
        for _ in 0..5 {
            assert_eq!(f.meter_period(&id).await.unwrap(), MeterOutcome::NotRunning);
        }
        assert_eq!(
            ledger.balance("DREGG", "dreggnet-provider"),
            billed_awake,
            "a checkpointed (sleeping) server draws nothing"
        );

        // Wake: metering resumes (wake pre-pays the resume period).
        f.wake(&id).await.unwrap();
        assert!(
            ledger.balance("DREGG", "dreggnet-provider") > billed_awake,
            "billing resumes once awake"
        );
        std::fs::remove_file(&path).ok();
    }

    /// TEETH — fork (scale / clone): a second server from one checkpoint, a distinct
    /// cell id, diverging independently — a write to one does not touch the other.
    #[tokio::test]
    async fn fork_creates_a_divergent_second_server() {
        let path = temp_store_path("fork");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("DREGG", "agent", 1_000);
        let f = fleet(&path, ledger);

        // Primary: launch, write a shared base, checkpoint (sleep).
        let primary = f.create("app", "primary", &lease("agent", 100, 2)).unwrap();
        f.launch(&primary).await.unwrap();
        f.write_state(&primary, "shared", b"base".to_vec()).unwrap();
        f.stop(&primary).await.unwrap();
        let fork_point = f.server(&primary).unwrap().checkpoint_root.unwrap();

        // Fork → a second server from that checkpoint.
        let replica = f
            .fork(&primary, "replica", &lease("agent", 100, 2))
            .unwrap();
        assert_ne!(
            f.cell_id(&primary).unwrap(),
            f.cell_id(&replica).unwrap(),
            "the fork has a distinct cell id"
        );
        assert_eq!(
            f.server(&replica).unwrap().checkpoint_root.as_deref(),
            Some(fork_point.as_str()),
            "the fork descends from the same fork-point root"
        );
        assert_eq!(
            f.read_state(&replica, "shared"),
            Some(b"base".to_vec()),
            "fork inherits state"
        );

        // Diverge: wake both and write independently.
        f.wake(&primary).await.unwrap();
        f.launch(&replica).await.unwrap();
        f.write_state(&primary, "shared", b"primary-only".to_vec())
            .unwrap();
        f.write_state(&replica, "shared", b"replica-only".to_vec())
            .unwrap();
        assert_eq!(
            f.read_state(&primary, "shared"),
            Some(b"primary-only".to_vec())
        );
        assert_eq!(
            f.read_state(&replica, "shared"),
            Some(b"replica-only".to_vec())
        );
        assert_ne!(
            f.live_root(&primary).unwrap(),
            f.live_root(&replica).unwrap(),
            "the two servers diverged — the fork is real"
        );
        std::fs::remove_file(&path).ok();
    }

    /// TEETH — time-travel / rollback: restore a server's state cell to an earlier
    /// committed boundary root.
    #[tokio::test]
    async fn time_travel_rolls_state_back_to_an_earlier_root() {
        let path = temp_store_path("time-travel");
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund("DREGG", "agent", 1_000);
        let f = fleet(&path, ledger);

        let id = f.create("app", "srv", &lease("agent", 100, 2)).unwrap();
        f.launch(&id).await.unwrap();
        f.write_state(&id, "v", b"one".to_vec()).unwrap();
        f.stop(&id).await.unwrap(); // checkpoint root_one
        let root_one = f.server(&id).unwrap().checkpoint_root.unwrap();

        f.wake(&id).await.unwrap();
        f.write_state(&id, "v", b"two".to_vec()).unwrap();
        f.stop(&id).await.unwrap(); // checkpoint root_two
        let root_two = f.server(&id).unwrap().checkpoint_root.unwrap();
        assert_ne!(root_one, root_two);

        // Roll the state back to the first committed root.
        f.restore_to(&id, &root_one).unwrap();
        assert_eq!(f.read_state(&id, "v"), Some(b"one".to_vec()));
        // …and forward again to the second.
        f.restore_to(&id, &root_two).unwrap();
        assert_eq!(f.read_state(&id, "v"), Some(b"two".to_vec()));

        // A never-committed root is refused (fail-closed).
        assert!(matches!(
            f.restore_to(&id, "deadbeef"),
            Err(ServerError::Restore(
                crate::compute_cell::RestoreError::UnknownRoot(_)
            ))
        ));
        std::fs::remove_file(&path).ok();
    }
}
