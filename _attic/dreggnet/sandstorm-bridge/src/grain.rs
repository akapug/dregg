//! A **grain = a dregg cell + a cap-bounded compute workload**.
//!
//! In Sandstorm a *grain* is one running instance of an app together with its own
//! private data, isolated in the supervisor's sandbox. The mapping onto dregg:
//!
//! | Sandstorm grain piece            | dregg / DreggNet                                       |
//! |----------------------------------|-------------------------------------------------------|
//! | the grain's private data (`/var`)| the **cell's umem heap**, committed → a `data_root`   |
//! | the running app process          | a **leased compute workload** at a [`SandboxTier`]    |
//! | the supervisor jail (ns+seccomp) | the `Caged`/`MicroVm` tier (`dreggnet-exec`)          |
//! | grain id / ownership             | the **`CellId`** + its holder cap                     |
//! | start-on-demand / idle-shutdown  | **wake** (resume workload) / **sleep** (checkpoint)   |
//! | backup (zip of the grain)        | the committed cell image (umem heap snapshot)         |
//!
//! The lifecycle is the load-bearing reuse. A Sandstorm grain is *started on
//! demand* when someone opens it and *shut down when idle*; its data persists on
//! disk between. dregg already has exactly this shape: a **lease** funds the running
//! workload, the **durable** layer checkpoints it, and **umem** is the passable,
//! witnessed image. So:
//!
//! - **create** — mint a fresh cell (the grain's umem heap), run the manifest's
//!   *action* command once to initialize → [`GrainState::Running`].
//! - **open / wake** — resume the workload from the last umem checkpoint under a
//!   funded lease → [`GrainState::Running`]. (Sandstorm's `continueCommand`.)
//! - **sleep** — idle: checkpoint the umem heap, release the lease, reap the
//!   workload → [`GrainState::Sleeping`]. A sleeping grain costs only storage.
//! - **backup** — the committed cell image *is* the backup; it is content-addressed
//!   and (unlike a Sandstorm zip) **re-witnessable**.
//!
//! This module is the lifecycle state machine over those mappings, with the dregg
//! economic facts (a workload only runs under a funded lease) encoded as invariants.

use serde::{Deserialize, Serialize};

use crate::cell::{DataRoot, Umem};
use crate::limits::{LeaseError, ResourceLease};
use crate::manifest::AppId;
use crate::net::{NetworkPolicy, OutboundCap};
use crate::tenant::TenantId;

/// Sandstorm's idle-shutdown window: a grain with no activity for this long is checked
/// pointed and reaped (it then costs only storage until re-opened). Sandstorm uses ~90s.
pub const IDLE_SHUTDOWN_SECS: u64 = 90;

/// The dregg sandbox tier a grain runs at — a faithful subset of `dreggnet-exec`'s
/// `CapTier` (`exec/src/lib.rs`). A grain *never* routes weaker than `Caged`: the
/// Sandstorm supervisor is a namespace+seccomp jail, and an in-process wasm tier
/// would be a silent isolation **downgrade** (forbidden — `dreggnet-exec`'s
/// `check_floor` rule, applied to grains).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SandboxTier {
    /// Native process under seccomp-bpf + Landlock — the closest analog to the
    /// Sandstorm supervisor (shared host kernel, syscall + fs allowlist).
    Caged,
    /// Per-grain Firecracker microVM — its own guest kernel behind KVM. Strictly
    /// *stronger* than Sandstorm's shared-kernel supervisor.
    MicroVm,
}

/// The launch spec a [`crate::manifest::SpkManifest`] implies for a grain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainSpec {
    pub app_id: AppId,
    pub app_version: u32,
    /// The `continueCommand` argv used to wake the grain.
    pub wake_argv: Vec<String>,
    /// The localhost port the app serves on inside the sandbox (http-bridge apps),
    /// which the gateway routes the grain's verifiable HTTP session to.
    pub ingress_port: Option<u16>,
    /// The isolation tier the grain demands.
    pub tier: SandboxTier,
    /// The app's declared permission universe (for cap attenuation).
    pub declared_permissions: Vec<String>,
}

/// The lifecycle state of a grain. Mirrors Sandstorm's on-demand model, expressed
/// in dregg terms (a running grain holds a funded lease; a sleeping grain is a
/// checkpointed cell).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GrainState {
    /// Provisioned (cell minted) but never initialized.
    Created,
    /// The workload is live under a funded lease, serving sessions.
    Running,
    /// Idle: umem checkpointed, lease released, workload reaped. Costs only storage.
    Sleeping,
    /// Owner-deleted; the cell is tombstoned (its committed history remains).
    Deleted,
}

/// A grain instance: the cell identity + its data commitment + its lifecycle state.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainCell {
    /// The dregg `CellId` of the grain's cell (its data + identity).
    pub cell_id: String,
    /// The holder/owner cap principal (the user who created the grain).
    pub owner: String,
    /// What app this grain runs.
    pub spec: GrainSpec,
    /// A commitment to the grain's private data — the cell's umem heap root. `None`
    /// before first initialization; `Some` once data exists (the backup-as-cell).
    pub data_root: Option<String>,
    /// Lifecycle state.
    pub state: GrainState,
    /// Metered uptime charged so far (in lease units) — the "per-grain uptime"
    /// billing meter (StandingObligation per period; see the plan, §Metering).
    pub metered_units: i64,
    /// **L2** — the grain's network posture. Starts [`NetworkPolicy::confined`] (no
    /// ambient network); outbound grows only by powerbox-granted [`OutboundCap`]s.
    pub network: NetworkPolicy,
    /// **L4** — the funded lease's resource bounds + usage. Uptime metering charges
    /// against it; a grain that outruns its lease is refused.
    pub lease: ResourceLease,
    /// **L6** — the tenant this grain belongs to (the isolation partition). Defaults
    /// to a per-owner tenant.
    pub tenant: TenantId,
    /// Wall-clock seconds of the grain's last activity — the input to the Sandstorm
    /// idle-shutdown ([`idle_shutdown`](Self::idle_shutdown)). Bumped by
    /// [`touch`](Self::touch) on each served request.
    #[serde(default)]
    pub last_active_secs: u64,
}

/// A **receipt** for a witnessed grain lifecycle operation — the artifact a light client
/// (or an auditor) reads to confirm *what happened to which cell, by whom, leaving what
/// committed state*. Every cap-gated lifecycle op returns one; the `data_root` binds the
/// resulting `/var` image (a Sandstorm operation leaves only a log line — this leaves a
/// commitment).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainReceipt {
    /// The operation name (`"backup"`, `"restore"`, `"transfer"`, `"idle-shutdown"`, …).
    pub op: String,
    /// The grain cell the operation acted on.
    pub cell_id: String,
    /// The principal that exercised the operation (the holder cap subject).
    pub actor: String,
    /// The committed `/var` `data_root` after the operation, when it produces one.
    pub data_root: Option<String>,
}

impl GrainReceipt {
    fn new(op: &str, cell_id: &str, actor: &str, data_root: Option<String>) -> Self {
        GrainReceipt {
            op: op.to_string(),
            cell_id: cell_id.to_string(),
            actor: actor.to_string(),
            data_root,
        }
    }
}

/// A portable, **re-witnessable** backup of a grain: its app identity plus the committed
/// `/var` image. Unlike a Sandstorm backup zip, the `data_root` is a content commitment,
/// so a [`restore_grain`] reproduces *exactly* the backed-up state — and that it did so
/// is itself verifiable (the restored heap commits to the same root).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainBackup {
    /// The app the backed-up grain runs (so a restore re-derives the right spec).
    pub app_id: AppId,
    pub app_version: u32,
    /// The committed `data_root` of the `/var` image at backup time.
    pub data_root: String,
    /// The `/var` entries (`key -> bytes`), the portable heap image.
    pub var: Vec<(String, Vec<u8>)>,
}

/// A grain operation refused by the lifecycle/economic rules.
#[derive(Debug, PartialEq, Eq)]
pub enum GrainError {
    /// A workload was asked to run without a funded lease — Sandstorm "start the
    /// grain", dregg "no run beyond what the lease authorizes".
    Unfunded,
    /// An illegal lifecycle transition (e.g. wake a deleted grain).
    BadTransition { from: GrainState, op: &'static str },
    /// The grain outran a resource bound its funded lease authorizes (L4) — it is
    /// over budget and must be reaped. The charge was refused, not applied.
    LeaseExhausted(LeaseError),
    /// A lifecycle operation (backup / transfer / …) was attempted by a principal that
    /// is not the grain's owner — refused (the holder cap does not authorize it).
    Unauthorized { actor: String, op: &'static str },
    /// A restore's reconstructed `/var` did not commit to the backup's `data_root` —
    /// the backup is corrupt or was tampered with; the grain is NOT restored.
    BackupCorrupt,
}

impl From<LeaseError> for GrainError {
    fn from(e: LeaseError) -> Self {
        GrainError::LeaseExhausted(e)
    }
}

impl std::fmt::Display for GrainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GrainError::Unfunded => write!(f, "grain workload refused: no funded lease"),
            GrainError::BadTransition { from, op } => {
                write!(f, "illegal grain transition: {op} from {from:?}")
            }
            GrainError::LeaseExhausted(e) => write!(f, "grain over budget: {e}"),
            GrainError::Unauthorized { actor, op } => {
                write!(f, "grain {op} refused: {actor} is not the owner")
            }
            GrainError::BackupCorrupt => {
                write!(
                    f,
                    "grain restore refused: backup does not match its data_root"
                )
            }
        }
    }
}
impl std::error::Error for GrainError {}

impl GrainCell {
    /// Provision a grain cell for `owner` running the app in `spec`. No workload yet.
    /// Starts fully confined (L2: no ambient network), in its own per-owner tenant
    /// (L6), under an unbounded lease (L4) — a real deployment attaches a funded,
    /// bounded lease via [`with_lease`](Self::with_lease).
    pub fn create(cell_id: impl Into<String>, owner: impl Into<String>, spec: GrainSpec) -> Self {
        let owner = owner.into();
        let tenant = TenantId::new(format!("tenant:{owner}"));
        GrainCell {
            cell_id: cell_id.into(),
            owner,
            spec,
            data_root: None,
            state: GrainState::Created,
            metered_units: 0,
            network: NetworkPolicy::confined(),
            lease: ResourceLease::unbounded(),
            tenant,
            last_active_secs: 0,
        }
    }

    /// Whether `actor` holds the owner cap for this grain — the gate every cap-bounded
    /// lifecycle operation checks.
    fn require_owner(&self, actor: &str, op: &'static str) -> Result<(), GrainError> {
        if actor == self.owner {
            Ok(())
        } else {
            Err(GrainError::Unauthorized {
                actor: actor.to_string(),
                op,
            })
        }
    }

    /// Attach a funded, bounded resource lease (L4). Builder-style.
    pub fn with_lease(mut self, lease: ResourceLease) -> Self {
        self.lease = lease;
        self
    }

    /// Place the grain in an explicit tenant partition (L6). Builder-style.
    pub fn with_tenant(mut self, tenant: TenantId) -> Self {
        self.tenant = tenant;
        self
    }

    /// **L2** — the powerbox grants the grain outbound reach to one specific service.
    /// The *only* way the grain's egress allow-list grows. Returns the resulting
    /// network policy reach for that destination so the caller can confirm the grant.
    pub fn grant_outbound(&mut self, cap: OutboundCap) {
        self.network.grant_outbound(cap);
    }

    /// **Wake / open** the grain: resume the workload under a funded lease. Refused
    /// if the lease is unfunded (no unpaid work) or the grain is deleted.
    ///
    /// `lease_funded` stands in for the real `dreggnet_bridge::Lease::funded` gate.
    pub fn wake(&mut self, lease_funded: bool) -> Result<(), GrainError> {
        match self.state {
            GrainState::Deleted => Err(GrainError::BadTransition {
                from: self.state,
                op: "wake",
            }),
            _ if !lease_funded => Err(GrainError::Unfunded),
            _ => {
                // First wake initializes the data heap (the manifest action ran).
                if self.data_root.is_none() {
                    self.data_root = Some(format!("umem:{}:init", self.cell_id));
                }
                self.state = GrainState::Running;
                Ok(())
            }
        }
    }

    /// **Sleep** the grain: checkpoint the umem heap, release the lease, reap the
    /// workload. The committed `data_root` is the durable, re-witnessable image.
    pub fn sleep(&mut self, new_data_root: impl Into<String>) -> Result<(), GrainError> {
        match self.state {
            GrainState::Running => {
                self.data_root = Some(new_data_root.into());
                self.state = GrainState::Sleeping;
                Ok(())
            }
            other => Err(GrainError::BadTransition {
                from: other,
                op: "sleep",
            }),
        }
    }

    /// Charge `units` of metered uptime against the grain (one StandingObligation
    /// period). Only a running grain accrues uptime, and the charge is bounded by the
    /// funded lease (L4): if it would exceed the lease's uptime quota it is refused
    /// (the grain has outrun what it is funded for and must be reaped) and not applied.
    pub fn meter_period(&mut self, units: i64) -> Result<i64, GrainError> {
        if self.state != GrainState::Running {
            return Err(GrainError::BadTransition {
                from: self.state,
                op: "meter",
            });
        }
        // Charge the funded lease first; if it refuses, the uptime is not accrued.
        let periods = units.max(0) as u64;
        self.lease.charge_uptime(periods)?;
        self.metered_units += units;
        Ok(self.metered_units)
    }

    /// Charge CPU milliseconds against the funded lease (L4). Refused if over budget.
    pub fn charge_cpu(&mut self, ms: u64) -> Result<u64, GrainError> {
        Ok(self.lease.charge_cpu(ms)?)
    }

    /// Observe peak memory against the funded lease (L4). Refused if over the cap.
    pub fn observe_mem(&mut self, peak_bytes: u64) -> Result<u64, GrainError> {
        Ok(self.lease.observe_mem(peak_bytes)?)
    }

    /// Admit a new total `/var` size against the funded lease (L4). Refused if it
    /// would exceed the storage quota — the caller must not persist the write.
    pub fn admit_storage(&mut self, bytes: u64) -> Result<u64, GrainError> {
        Ok(self.lease.admit_storage(bytes)?)
    }

    /// Record activity at `now_secs` (the serving layer calls this on each request) —
    /// the input to the idle-shutdown clock.
    pub fn touch(&mut self, now_secs: u64) {
        self.last_active_secs = now_secs;
    }

    /// Seconds since the grain's last recorded activity.
    pub fn idle_secs(&self, now_secs: u64) -> u64 {
        now_secs.saturating_sub(self.last_active_secs)
    }

    /// **Idle-shutdown** (Sandstorm's start-on-demand reaper): if the grain is running
    /// and has been idle for at least [`IDLE_SHUTDOWN_SECS`], checkpoint its `/var` umem
    /// and sleep it (a re-witnessable checkpoint; the workload is reaped, costing only
    /// storage). Returns the receipt if it shut down, `None` if the grain is still
    /// active (within the window) or not running. A later [`wake`](Self::wake) resumes
    /// from the checkpoint.
    pub fn idle_shutdown(
        &mut self,
        now_secs: u64,
        var: &Umem,
    ) -> Result<Option<GrainReceipt>, GrainError> {
        if self.state != GrainState::Running || self.idle_secs(now_secs) < IDLE_SHUTDOWN_SECS {
            return Ok(None);
        }
        let root = var.commit();
        self.data_root = Some(root.0.clone());
        self.state = GrainState::Sleeping;
        Ok(Some(GrainReceipt::new(
            "idle-shutdown",
            &self.cell_id,
            "system",
            Some(root.0),
        )))
    }

    /// **Backup** the grain's `/var` to a portable, re-witnessable [`GrainBackup`]
    /// (cap-gated: owner only; receipted). The committed `data_root` binds the image, so
    /// a [`restore_grain`] reproduces exactly this state. Works in any non-deleted state
    /// (a backup is just a read of the committed image).
    pub fn backup(
        &self,
        actor: &str,
        var: &Umem,
    ) -> Result<(GrainBackup, GrainReceipt), GrainError> {
        self.require_owner(actor, "backup")?;
        if self.state == GrainState::Deleted {
            return Err(GrainError::BadTransition {
                from: self.state,
                op: "backup",
            });
        }
        let root = var.commit();
        let backup = GrainBackup {
            app_id: self.spec.app_id.clone(),
            app_version: self.spec.app_version,
            data_root: root.0.clone(),
            var: var
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_vec()))
                .collect(),
        };
        let receipt = GrainReceipt::new("backup", &self.cell_id, actor, Some(root.0));
        Ok((backup, receipt))
    }

    /// **Transfer** ownership of the grain to `new_owner` (cap-gated: only the current
    /// owner; receipted). Re-owns the cell and re-partitions it into the new owner's
    /// tenant (L6), so the old owner immediately loses access — a subsequent
    /// owner-gated operation by the old owner is [`GrainError::Unauthorized`]. The
    /// committed `/var` image is unchanged (a transfer re-owns, it does not mutate data).
    pub fn transfer(
        &mut self,
        actor: &str,
        new_owner: impl Into<String>,
    ) -> Result<GrainReceipt, GrainError> {
        self.require_owner(actor, "transfer")?;
        let new_owner = new_owner.into();
        self.owner = new_owner.clone();
        self.tenant = TenantId::new(format!("tenant:{new_owner}"));
        Ok(GrainReceipt::new(
            "transfer",
            &self.cell_id,
            actor,
            self.data_root.clone(),
        ))
    }

    /// **Delete** the grain. The cell is tombstoned; its committed history persists.
    pub fn delete(&mut self) {
        self.state = GrainState::Deleted;
    }
}

/// **Restore** a grain from a [`GrainBackup`] (receipted): reconstruct the `/var` umem
/// heap, **verify it commits to the backup's `data_root`** (re-witnessing that the
/// restore reproduced exactly the backed-up state — a corrupt/tampered backup is
/// refused), and provision a fresh grain cell for `owner` in the [`GrainState::Sleeping`]
/// state (ready to wake). Returns the new cell, its restored `/var`, and the receipt.
///
/// `spec` is the grain spec the restorer re-derives for `backup.app_id` (in a real flow,
/// by re-installing the app's `.spk`); a real deployment checks `spec.app_id ==
/// backup.app_id`.
pub fn restore_grain(
    backup: &GrainBackup,
    cell_id: impl Into<String>,
    owner: impl Into<String>,
    spec: GrainSpec,
) -> Result<(GrainCell, Umem, GrainReceipt), GrainError> {
    let mut var = Umem::new();
    for (k, v) in &backup.var {
        var.put(k.clone(), v.clone());
    }
    // Re-witness: the reconstructed heap must commit to the backup's recorded root.
    let restored = var.commit();
    if restored != DataRoot(backup.data_root.clone()) {
        return Err(GrainError::BackupCorrupt);
    }
    let cell_id = cell_id.into();
    let owner = owner.into();
    let mut cell = GrainCell::create(cell_id.clone(), owner.clone(), spec);
    cell.data_root = Some(restored.0.clone());
    cell.state = GrainState::Sleeping;
    let receipt = GrainReceipt::new("restore", &cell_id, &owner, Some(restored.0));
    Ok((cell, var, receipt))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::manifest::SpkManifest;

    fn etherpad_spec() -> GrainSpec {
        let json = r#"{
          "app_id": "vfnwptfn02ty21w715snyyczw0nqxkv3jvawcsk4180s",
          "app_title": "Etherpad",
          "app_version": 33,
          "continue_command": { "argv": ["/sandstorm-http-bridge", "8000", "--", "/start.sh"] },
          "bridge_config": { "api_port": 8000, "permissions": ["view", "edit"], "roles": [] }
        }"#;
        SpkManifest::from_json(json).unwrap().grain_spec()
    }

    #[test]
    fn full_lifecycle_create_wake_sleep_wake() {
        let mut g = GrainCell::create("cell:grain1", "user:alice", etherpad_spec());
        assert_eq!(g.state, GrainState::Created);
        assert!(g.data_root.is_none());

        // First wake initializes the data heap.
        g.wake(true).unwrap();
        assert_eq!(g.state, GrainState::Running);
        assert!(g.data_root.is_some());

        // Sleep checkpoints a new umem root (the backup-as-cell).
        g.sleep("umem:cell:grain1:rev7").unwrap();
        assert_eq!(g.state, GrainState::Sleeping);
        assert_eq!(g.data_root.as_deref(), Some("umem:cell:grain1:rev7"));

        // Wake resumes from the checkpoint.
        g.wake(true).unwrap();
        assert_eq!(g.state, GrainState::Running);
        // The data survived sleep (resumed from the checkpointed root).
        assert_eq!(g.data_root.as_deref(), Some("umem:cell:grain1:rev7"));
    }

    #[test]
    fn an_unfunded_lease_runs_no_workload() {
        let mut g = GrainCell::create("cell:grain1", "user:alice", etherpad_spec());
        assert_eq!(g.wake(false), Err(GrainError::Unfunded));
        // The grain never started — no unpaid work, exactly like the lease gate.
        assert_eq!(g.state, GrainState::Created);
    }

    #[test]
    fn uptime_is_metered_only_while_running() {
        let mut g = GrainCell::create("cell:grain1", "user:alice", etherpad_spec());
        // A sleeping/created grain accrues no uptime.
        assert!(g.meter_period(5).is_err());
        g.wake(true).unwrap();
        assert_eq!(g.meter_period(5).unwrap(), 5);
        assert_eq!(g.meter_period(5).unwrap(), 10);
    }

    #[test]
    fn a_deleted_grain_cannot_wake() {
        let mut g = GrainCell::create("cell:grain1", "user:alice", etherpad_spec());
        g.delete();
        assert!(matches!(
            g.wake(true),
            Err(GrainError::BadTransition { .. })
        ));
    }

    #[test]
    fn a_fresh_grain_starts_confined_in_its_own_tenant() {
        let g = GrainCell::create("cell:grain1", "user:alice", etherpad_spec());
        // L2: no ambient network until the powerbox grants an outbound cap.
        assert!(!g.network.has_any_egress());
        // L6: a per-owner tenant partition.
        assert_eq!(g.tenant, TenantId::new("tenant:user:alice"));
    }

    #[test]
    fn a_grain_that_outruns_its_lease_is_reaped() {
        use crate::limits::ResourceLease;
        // L4: a lease funding only 3 uptime periods.
        let mut g = GrainCell::create("cell:grain1", "user:alice", etherpad_spec())
            .with_lease(ResourceLease::bounded(3, u64::MAX, u64::MAX, u64::MAX));
        g.wake(true).unwrap();
        assert_eq!(g.meter_period(2).unwrap(), 2);
        // The next period exceeds the funded lease — refused, not accrued.
        assert!(matches!(
            g.meter_period(2),
            Err(GrainError::LeaseExhausted(_))
        ));
        assert_eq!(g.metered_units, 2);
    }

    #[test]
    fn idle_shutdown_checkpoints_then_wake_resumes() {
        let mut g = GrainCell::create("cell:grain1", "user:alice", etherpad_spec());
        g.wake(true).unwrap();
        g.touch(1000);
        let mut var = Umem::new();
        var.put("notes/welcome", b"hello".to_vec());

        // Within the idle window: no shutdown.
        assert!(g
            .idle_shutdown(1000 + IDLE_SHUTDOWN_SECS - 1, &var)
            .unwrap()
            .is_none());
        assert_eq!(g.state, GrainState::Running);

        // Past the window: checkpoint + sleep, with a receipt binding the umem root.
        let receipt = g
            .idle_shutdown(1000 + IDLE_SHUTDOWN_SECS, &var)
            .unwrap()
            .expect("idle shutdown fired");
        assert_eq!(g.state, GrainState::Sleeping);
        assert_eq!(receipt.op, "idle-shutdown");
        assert_eq!(receipt.data_root.as_deref(), Some(var.commit().0.as_str()));

        // Wake resumes from the checkpoint; the data survived.
        g.wake(true).unwrap();
        assert_eq!(g.state, GrainState::Running);
        assert_eq!(g.data_root.as_deref(), Some(var.commit().0.as_str()));
        assert_eq!(var.get("notes/welcome"), Some(&b"hello"[..]));
    }

    #[test]
    fn backup_then_restore_preserves_state() {
        let mut g = GrainCell::create("cell:grain1", "user:alice", etherpad_spec());
        g.wake(true).unwrap();
        let mut var = Umem::new();
        var.put("notes/a", b"alpha".to_vec());
        var.put("notes/b", b"beta".to_vec());

        // Owner backs up (cap-gated, receipted).
        let (backup, receipt) = g.backup("user:alice", &var).unwrap();
        assert_eq!(receipt.op, "backup");
        assert_eq!(backup.data_root, var.commit().0);

        // Restore into a fresh grain cell for a (possibly different) owner.
        let (restored_cell, restored_var, r_receipt) =
            restore_grain(&backup, "cell:grain1-copy", "user:carol", etherpad_spec()).unwrap();
        assert_eq!(r_receipt.op, "restore");
        // The restored heap is byte-identical and commits to the same root.
        assert_eq!(restored_var.get("notes/a"), Some(&b"alpha"[..]));
        assert_eq!(restored_var.get("notes/b"), Some(&b"beta"[..]));
        assert_eq!(restored_var.commit().0, backup.data_root);
        assert_eq!(
            restored_cell.data_root.as_deref(),
            Some(backup.data_root.as_str())
        );
        assert_eq!(restored_cell.state, GrainState::Sleeping);
    }

    #[test]
    fn a_non_owner_cannot_back_up() {
        let g = GrainCell::create("cell:grain1", "user:alice", etherpad_spec());
        let var = Umem::new();
        assert!(matches!(
            g.backup("user:mallory", &var),
            Err(GrainError::Unauthorized { .. })
        ));
    }

    #[test]
    fn a_tampered_backup_is_refused_on_restore() {
        let g = GrainCell::create("cell:grain1", "user:alice", etherpad_spec());
        let mut var = Umem::new();
        var.put("notes/a", b"alpha".to_vec());
        let (mut backup, _) = g.backup("user:alice", &var).unwrap();
        // Tamper with the image after backup (the committed root no longer matches).
        backup.var.push(("notes/evil".into(), b"injected".to_vec()));
        assert_eq!(
            restore_grain(&backup, "cell:x", "user:carol", etherpad_spec()).err(),
            Some(GrainError::BackupCorrupt)
        );
    }

    #[test]
    fn transfer_re_owns_and_the_old_owner_loses_access() {
        let mut g = GrainCell::create("cell:grain1", "user:alice", etherpad_spec());
        g.wake(true).unwrap();
        let var = Umem::new();

        // Alice transfers to Bob (cap-gated; receipted).
        let receipt = g.transfer("user:alice", "user:bob").unwrap();
        assert_eq!(receipt.op, "transfer");
        assert_eq!(g.owner, "user:bob");
        // Re-partitioned into Bob's tenant (L6).
        assert_eq!(g.tenant, TenantId::new("tenant:user:bob"));

        // The old owner has lost access: an owner-gated op is now refused for Alice.
        assert!(matches!(
            g.backup("user:alice", &var),
            Err(GrainError::Unauthorized { .. })
        ));
        // The new owner can.
        assert!(g.backup("user:bob", &var).is_ok());
        // And only the new owner can transfer onward.
        assert!(matches!(
            g.transfer("user:alice", "user:eve"),
            Err(GrainError::Unauthorized { .. })
        ));
        assert!(g.transfer("user:bob", "user:carol").is_ok());
    }

    #[test]
    fn cpu_and_memory_are_bounded_by_the_lease() {
        use crate::limits::ResourceLease;
        let mut g = GrainCell::create("cell:grain1", "user:alice", etherpad_spec()).with_lease(
            ResourceLease::bounded(u64::MAX, 500, 64 * 1024 * 1024, u64::MAX),
        );
        g.wake(true).unwrap();
        // A CPU busy-loop is capped.
        g.charge_cpu(400).unwrap();
        assert!(g.charge_cpu(200).is_err());
        // A memory balloon is capped.
        assert!(g.observe_mem(32 * 1024 * 1024).is_ok());
        assert!(g.observe_mem(128 * 1024 * 1024).is_err());
    }
}
