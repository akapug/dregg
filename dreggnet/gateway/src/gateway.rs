//! The machine gateway: an in-memory machine registry that maps fly create
//! calls onto dregg leases and drives the bridge.
//!
//! The gateway owns the machine records and the lease each one runs under. A
//! create runs the lease through the bridge's **real** validation gate
//! ([`dreggnet_bridge::workflow_input_for_lease`]) before recording the
//! machine; the durable launch is [`MachineGateway::fulfill`], which calls the
//! bridge's **real** [`dreggnet_bridge::fulfill`].

use std::collections::HashMap;
use std::net::Ipv4Addr;
use std::sync::Arc;
use std::sync::Mutex;
use std::time::{SystemTime, UNIX_EPOCH};

use dreggnet_bridge::{BridgeError, DurableOutput, Lease};
use dreggnet_control::{
    MachineId, Mesh, MeshNode, ProviderError, TailscaleMesh, dispatch_lease_over_mesh,
};
use dreggnet_guard::{Countable, Guard, GuardRefusal};

use crate::funding::{FundingError, FundingSource};
use crate::lease::{cap_grade_for_guest, required_budget};
use crate::types::{CreateMachineRequest, DispatchReport, Machine, MachineState};

/// Where a created machine's workload actually runs.
///
/// The gateway maps a fly create onto a dregg [`Lease`] and then dispatches that
/// lease's durable workload over the control plane's **real** dispatch primitive
/// ([`dreggnet_control::dispatch_lease_over_mesh`]) to a compute node over the
/// private overlay (the live edge→node-a path). Without one configured, the
/// gateway falls back to fulfilling the lease in-process on this host (the dev /
/// single-box path), so the default build stays self-contained.
pub struct ComputeBackend {
    /// The secure-plane mesh the dispatch rides (`TailscaleMesh` on the live edge,
    /// `StubMesh` in tests).
    mesh: Arc<dyn Mesh>,
    /// The compute node the workload is dispatched to (e.g. node-a at
    /// `100.64.0.2:8021`).
    node: MeshNode,
}

impl ComputeBackend {
    /// A compute backend that dispatches over `mesh` to `node`.
    pub fn new(mesh: Arc<dyn Mesh>, node: MeshNode) -> ComputeBackend {
        ComputeBackend { mesh, node }
    }

    /// The live edge backend: dispatch over the host's tailnet/headscale overlay
    /// (a [`TailscaleMesh`]) to the compute node at `overlay_addr:agent_port` (e.g.
    /// node-a, `100.64.0.2:8021`). This is the deployed path — the same overlay
    /// hop `deploy/COMPUTE-BACKEND.md` proved end to end.
    pub fn node_a(overlay_addr: Ipv4Addr, agent_port: u16) -> ComputeBackend {
        let mut node = MeshNode::new(
            MachineId("node-a".to_string()),
            // public_key + endpoint are cosmetic for the TailscaleMesh backend (it
            // rides the host overlay rather than standing up its own tunnel); the
            // overlay address + agent port are what carry the dispatch.
            "tailscale-overlay",
            format!("{overlay_addr}:{agent_port}"),
            overlay_addr,
        );
        node.agent_port = agent_port;
        ComputeBackend::new(Arc::new(TailscaleMesh::new()), node)
    }

    /// A short human label for the backend target (e.g. `"100.64.0.2:8021"`).
    pub fn target(&self) -> String {
        format!("{}:{}", self.node.overlay_addr, self.node.agent_port)
    }

    /// The mesh backend name (`"tailscale"` / `"stub"` / `"wireguard"`).
    pub fn backend(&self) -> &'static str {
        self.mesh.backend()
    }
}

/// A stored machine plus the lease + durable-instance handle it runs under.
#[derive(Debug, Clone)]
struct MachineEntry {
    machine: Machine,
    lease: Lease,
    /// The durable orchestration instance the bridge drives for this machine.
    instance: String,
}

#[derive(Default)]
struct State {
    /// machine id → entry.
    machines: HashMap<String, MachineEntry>,
    /// Monotonic id source.
    counter: u64,
}

/// Why a gateway operation failed.
#[derive(Debug)]
pub enum GatewayError {
    /// The lease the create maps to does not authorize work. Carries the
    /// bridge's own refusal (unfunded / ill-formed / grade-below-floor).
    LeaseRefused(BridgeError),
    /// The create demanded compute the chain does not fund: no verified on-chain
    /// funded lease for this app covers the request (or no funding source is
    /// configured). No machine is recorded — no free compute (LEASE-1a).
    Unfunded(String),
    /// No machine with that id under that app.
    NotFound,
    /// The durable workflow failed (most importantly an over-budget meter tick:
    /// lapse → reap). Carries the bridge's failure detail.
    WorkflowFailed(BridgeError),
    /// The dispatched lease lapsed — the compute node refused it (an unfunded /
    /// over-budget lease, `HTTP 4xx`). The machine reflects this as failed with the
    /// lapse reason; no work is claimed beyond what the lease authorized.
    Lapsed(String),
    /// The dispatch could not reach / run on the compute node (connect / transport
    /// fault, or no live overlay carrier). An infrastructure error, not a lapse.
    Dispatch(String),
    /// The per-account abuse-prevention [`Guard`] refused the create: the account
    /// is suspended (`403`), over a per-account quota (`402`), or over the deploy
    /// rate (`429`). No machine is recorded. The in-band refusal a permissionless
    /// cloud answers with so one anonymous account cannot spam the deploy path.
    Refused(GuardRefusal),
}

impl std::fmt::Display for GatewayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GatewayError::LeaseRefused(e) => write!(f, "lease refused: {e}"),
            GatewayError::Unfunded(why) => write!(f, "create not funded on-chain: {why}"),
            GatewayError::NotFound => write!(f, "machine not found"),
            GatewayError::WorkflowFailed(e) => write!(f, "workflow failed: {e}"),
            GatewayError::Lapsed(why) => write!(f, "lease lapsed: {why}"),
            GatewayError::Dispatch(why) => write!(f, "dispatch failed: {why}"),
            GatewayError::Refused(r) => write!(f, "create refused by abuse guard: {r}"),
        }
    }
}

impl std::error::Error for GatewayError {}

/// The fly-machines gateway over the dregg bridge.
pub struct MachineGateway {
    state: Mutex<State>,
    /// The compute node a created machine's workload is dispatched to. `None` means
    /// the gateway fulfills leases in-process on this host (the dev / single-box
    /// path); `Some` means it dispatches over the overlay to a real compute node.
    compute: Option<ComputeBackend>,
    /// The chain's attestation of which leases are funded — the ONLY source of a
    /// `funded` lease a create is admitted against (LEASE-1a). `None` ⇒ the gateway
    /// fails closed on create (no way to confirm real funding ⇒ no work admitted).
    funding: Option<Arc<dyn FundingSource>>,
    /// The per-account abuse-prevention gate (standing + quota + deploy-rate). `None`
    /// ⇒ no per-account bounding (the legacy/dev posture); `Some` ⇒ every create is
    /// admitted through the `Guard` before a machine is recorded, and the per-site/
    /// per-account request rate + resource suspension are enforced on the serving path.
    guard: Option<Arc<Guard>>,
}

impl Default for MachineGateway {
    fn default() -> Self {
        Self::new()
    }
}

impl MachineGateway {
    /// A fresh, empty gateway that fulfills leases in-process on this host.
    ///
    /// It has **no funding source**, so it admits no create until one is attached
    /// ([`funded_by`](Self::funded_by)) — the gateway never invents funding.
    pub fn new() -> Self {
        MachineGateway {
            state: Mutex::new(State::default()),
            compute: None,
            funding: None,
            guard: None,
        }
    }

    /// A gateway that dispatches a created machine's workload over the overlay to a
    /// real compute node (the live edge→node-a path) instead of running it
    /// in-process. Attach a funding source with [`funded_by`](Self::funded_by).
    pub fn with_compute(backend: ComputeBackend) -> Self {
        MachineGateway {
            state: Mutex::new(State::default()),
            compute: Some(backend),
            funding: None,
            guard: None,
        }
    }

    /// Gate creates on a [`FundingSource`] — the chain's attestation of funded
    /// leases. A create is admitted only against a real funded lease this source
    /// attests whose on-chain reserve covers the request (LEASE-1a); without it,
    /// every create fails closed.
    pub fn funded_by(mut self, funding: Arc<dyn FundingSource>) -> Self {
        self.funding = Some(funding);
        self
    }

    /// Attach the per-account abuse-prevention [`Guard`]: every create is admitted
    /// through it (account standing + per-account quota + deploy rate) before a
    /// machine is recorded, and [`admit_request`](Guard::admit_request) gates the
    /// serving path. Without it the gateway does no per-account bounding (the legacy
    /// posture). Hold the same `Arc<Guard>` the data plane / moderation surface uses.
    pub fn guarded_by(mut self, guard: Arc<Guard>) -> Self {
        self.guard = Some(guard);
        self
    }

    /// The abuse-prevention guard, if configured (for the serving path / moderation).
    pub fn guard(&self) -> Option<&Arc<Guard>> {
        self.guard.as_ref()
    }

    /// Whether a funding source is configured (creates are admittable).
    pub fn is_funded(&self) -> bool {
        self.funding.is_some()
    }

    /// Whether this gateway dispatches a created machine's workload to a remote
    /// compute node (vs. fulfilling it in-process).
    pub fn dispatches(&self) -> bool {
        self.compute.is_some()
    }

    /// The compute backend this gateway dispatches to, if any (for the status page).
    pub fn compute(&self) -> Option<&ComputeBackend> {
        self.compute.as_ref()
    }

    /// The total number of machine records this gateway holds, across all apps.
    pub fn count(&self) -> usize {
        self.state.lock().unwrap().machines.len()
    }

    /// **Create a machine** — the fly `POST .../machines`.
    ///
    /// The request's guest is the caller's **demand** (isolation floor + required
    /// budget); it is NOT evidence of funding. The gateway looks up the **funded**
    /// lease the chain attests for `app` via its [`FundingSource`] and admits the
    /// create only if that real on-chain reserve covers the demand (LEASE-1a) — so
    /// a fabricated guest size can never mint free compute. The admitted lease's
    /// budget is the REAL on-chain reserve, not anything derived from the request.
    ///
    /// The admitted lease is then run through the bridge's shape gate
    /// ([`dreggnet_bridge::workflow_input_for_lease`]) and a machine is recorded in
    /// [`MachineState::Created`]. If the chain funds no covering lease (or no
    /// funding source is configured) the create yields [`GatewayError::Unfunded`]
    /// and **no** machine record — no unpaid work is ever provisioned.
    ///
    /// The durable launch itself is [`MachineGateway::fulfill`]; create only
    /// admits the work (verifies funding + records), mirroring fly's create→start
    /// split.
    pub fn create(&self, app: &str, req: &CreateMachineRequest) -> Result<Machine, GatewayError> {
        // The DEMAND: what the requested guest wants to run (never funding).
        let floor = cap_grade_for_guest(&req.config.guest);
        let (need_budget, _per_period) = required_budget(&req.config.guest);

        // The FUNDING gate: a funded lease must be attested on-chain for this app,
        // with a reserve that covers the demand. Self-asserted funding is refused.
        let funding = self
            .funding
            .as_ref()
            .ok_or(GatewayError::Unfunded(FundingError::NoSource.to_string()))?;
        let lease = funding
            .authorize(app, floor, need_budget)
            .map_err(|e| GatewayError::Unfunded(e.to_string()))?
            .ok_or_else(|| {
                GatewayError::Unfunded(format!(
                    "no verified funded lease for `{app}` covers the request \
                     (need ≥ {need_budget} units at grade {floor} or stronger)"
                ))
            })?;

        // The bridge's shape gate over the REAL on-chain lease.
        dreggnet_bridge::workflow_input_for_lease(&lease, None)
            .map_err(GatewayError::LeaseRefused)?;

        // The per-account ABUSE gate (after funding, so a quota slot / deploy-rate
        // token is only consumed for a genuinely funded, otherwise-admissible
        // create): account standing (suspended ⇒ 403), deploy rate (⇒ 429), and the
        // per-account machine quota (⇒ 402). Keyed on the funded lessee account. A
        // refusal records NO machine — the in-band signal a permissionless cloud
        // answers with so one anonymous account cannot spam the deploy path.
        if let Some(guard) = &self.guard {
            guard
                .admit_create(&lease.lessee, Countable::Server, now_unix_secs())
                .map_err(GatewayError::Refused)?;
        }

        let mut state = self.state.lock().unwrap();
        state.counter += 1;
        let n = state.counter;
        let id = gen_machine_id(n);
        let instance = gen_instance_id(app, n);
        let now = now_rfc3339();
        let name = req.name.clone().unwrap_or_else(|| format!("{app}-{id}"));

        let machine = Machine {
            id: id.clone(),
            name,
            state: MachineState::Created,
            region: req.region.clone().unwrap_or_else(|| "dreggnet".to_string()),
            instance_id: instance.clone(),
            private_ip: String::new(),
            config: req.config.clone(),
            created_at: now.clone(),
            updated_at: now,
            dregg: None,
        };

        state.machines.insert(
            id,
            MachineEntry {
                machine: machine.clone(),
                lease,
                instance,
            },
        );
        Ok(machine)
    }

    /// Machine status — the fly `GET .../machines/{id}`.
    pub fn get(&self, id: &str) -> Option<Machine> {
        self.state
            .lock()
            .unwrap()
            .machines
            .get(id)
            .map(|e| e.machine.clone())
    }

    /// List machines for an app — the fly `GET .../machines`.
    pub fn list(&self, app: &str) -> Vec<Machine> {
        self.state
            .lock()
            .unwrap()
            .machines
            .values()
            .filter(|e| e.lease.lessee == app)
            .map(|e| e.machine.clone())
            .collect()
    }

    /// Stop (reap) a machine — the fly `POST .../machines/{id}/stop`.
    ///
    /// Transitions the record to [`MachineState::Stopped`]. The actual reap of a
    /// running durable workload is the control-plane action (rung 4); here it
    /// reaps the record.
    pub fn stop(&self, id: &str) -> Option<Machine> {
        self.transition(id, MachineState::Stopped)
    }

    /// Start a machine — the fly `POST .../machines/{id}/start`.
    pub fn start(&self, id: &str) -> Option<Machine> {
        self.transition(id, MachineState::Started)
    }

    /// Destroy a machine record — the fly `DELETE .../machines/{id}`.
    ///
    /// Returns the lessee's per-account server quota slot to the abuse [`Guard`]
    /// (if configured), so destroying a machine lets the account create another —
    /// the quota tracks LIVE resources, not a lifetime count.
    pub fn delete(&self, id: &str) -> bool {
        let removed = self.state.lock().unwrap().machines.remove(id);
        match removed {
            Some(entry) => {
                if let Some(guard) = &self.guard {
                    guard.release(&entry.lease.lessee, Countable::Server);
                }
                true
            }
            None => false,
        }
    }

    fn transition(&self, id: &str, to: MachineState) -> Option<Machine> {
        let mut state = self.state.lock().unwrap();
        let entry = state.machines.get_mut(id)?;
        entry.machine.state = to;
        entry.machine.updated_at = now_rfc3339();
        Some(entry.machine.clone())
    }

    /// **Fulfill a created machine** — launch its durable workload and record the
    /// real metered result on the machine.
    ///
    /// With a [`ComputeBackend`] configured ([`MachineGateway::with_compute`]) the
    /// lease is **dispatched over the overlay to a real compute node** via the
    /// control plane's dispatch primitive
    /// ([`dreggnet_control::dispatch_lease_over_mesh`] →
    /// `POST <overlay-addr>:8021/fulfill`): the node runs it as a durable polyana
    /// workflow metered against the lease budget and returns the metered result.
    /// Without one, the lease is fulfilled **in-process** on this host
    /// ([`dreggnet_bridge::fulfill`]) — the dev / single-box path.
    ///
    /// Outcomes recorded on the machine:
    /// - **success** → [`MachineState::Started`] + a [`DispatchReport`] carrying the
    ///   real `meter_units` + step outputs;
    /// - **lapse** (the node refused an over-budget / unfunded lease, `HTTP 4xx`) →
    ///   [`MachineState::Failed`] + a report whose `error` is the lapse reason
    ///   ([`GatewayError::Lapsed`]); no work is claimed;
    /// - **infrastructure error** (could not reach / run on the node) →
    ///   [`MachineState::Failed`] + a report whose `error` is the fault
    ///   ([`GatewayError::Dispatch`] / [`GatewayError::WorkflowFailed`]).
    ///
    /// The serving binary blocks on this from the create request path (the gateway
    /// connection loop is a synchronous thread-per-connection model), so a
    /// `POST .../machines` against a dispatch-configured gateway runs the workload
    /// on the compute node and returns the machine already reflecting the outcome —
    /// `start` re-runs it (the fly create→start split is still honored).
    pub async fn fulfill(&self, id: &str) -> Result<DurableOutput, GatewayError> {
        // Snapshot the lease + instance under the lock, then run the (async)
        // dispatch / bridge call without holding it.
        let (lease, instance) = {
            let mut state = self.state.lock().unwrap();
            let entry = state.machines.get_mut(id).ok_or(GatewayError::NotFound)?;
            entry.machine.state = MachineState::Starting;
            entry.machine.updated_at = now_rfc3339();
            (entry.lease.clone(), entry.instance.clone())
        };

        match &self.compute {
            // The live path: dispatch the lease over the overlay to the compute node.
            Some(backend) => {
                let result = dispatch_lease_over_mesh(
                    backend.mesh.as_ref(),
                    &backend.node,
                    &lease,
                    &instance,
                )
                .await;
                self.record_dispatch(id, backend, result)
            }
            // The single-box path: fulfill the lease in-process via the bridge.
            None => {
                let result = dreggnet_bridge::fulfill(&lease, &instance).await;
                self.record_local(id, result)
            }
        }
    }

    /// Record the outcome of a remote dispatch on the machine, mapping the
    /// control-plane [`ProviderError`] onto the machine state + a [`DispatchReport`].
    fn record_dispatch(
        &self,
        id: &str,
        backend: &ComputeBackend,
        result: Result<DurableOutput, ProviderError>,
    ) -> Result<DurableOutput, GatewayError> {
        let mut state = self.state.lock().unwrap();
        match result {
            Ok(output) => {
                if let Some(entry) = state.machines.get_mut(id) {
                    entry.machine.state = MachineState::Started;
                    entry.machine.updated_at = now_rfc3339();
                    entry.machine.dregg = Some(DispatchReport {
                        backend: backend.backend().to_string(),
                        node: Some(backend.target()),
                        meter_units: Some(output.meter_units),
                        outputs: output.outputs.clone(),
                        error: None,
                    });
                }
                Ok(output)
            }
            Err(err) => {
                // A 4xx refusal is a lapse (the lease did not authorize the work);
                // anything else is an infrastructure fault. Either way the machine
                // reflects failed with the reason — no fabricated result.
                let (gw_err, reason) = match err {
                    ProviderError::WorkloadLapsed(why) => (GatewayError::Lapsed(why.clone()), why),
                    other => {
                        let why = other.to_string();
                        (GatewayError::Dispatch(why.clone()), why)
                    }
                };
                if let Some(entry) = state.machines.get_mut(id) {
                    entry.machine.state = MachineState::Failed;
                    entry.machine.updated_at = now_rfc3339();
                    entry.machine.dregg = Some(DispatchReport {
                        backend: backend.backend().to_string(),
                        node: Some(backend.target()),
                        meter_units: None,
                        outputs: Vec::new(),
                        error: Some(reason),
                    });
                }
                Err(gw_err)
            }
        }
    }

    /// Record the outcome of an in-process bridge fulfillment on the machine.
    fn record_local(
        &self,
        id: &str,
        result: Result<DurableOutput, BridgeError>,
    ) -> Result<DurableOutput, GatewayError> {
        let mut state = self.state.lock().unwrap();
        match result {
            Ok(output) => {
                if let Some(entry) = state.machines.get_mut(id) {
                    entry.machine.state = MachineState::Started;
                    entry.machine.updated_at = now_rfc3339();
                    entry.machine.dregg = Some(DispatchReport {
                        backend: "local".to_string(),
                        node: None,
                        meter_units: Some(output.meter_units),
                        outputs: output.outputs.clone(),
                        error: None,
                    });
                }
                Ok(output)
            }
            Err(e) => {
                if let Some(entry) = state.machines.get_mut(id) {
                    entry.machine.state = MachineState::Failed;
                    entry.machine.updated_at = now_rfc3339();
                    entry.machine.dregg = Some(DispatchReport {
                        backend: "local".to_string(),
                        node: None,
                        meter_units: None,
                        outputs: Vec::new(),
                        error: Some(e.to_string()),
                    });
                }
                Err(GatewayError::WorkflowFailed(e))
            }
        }
    }
}

/// A fly-shaped 14-hex-char machine id, derived from the monotonic counter and
/// the process clock. Not cryptographic — an opaque handle.
fn gen_machine_id(n: u64) -> String {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0);
    let mixed = nanos.rotate_left(13) ^ n.wrapping_mul(0x9E37_79B9_7F4A_7C15);
    format!("{:014x}", mixed & 0x00FF_FFFF_FFFF_FFFF)
}

/// A durable-instance handle for the bridge (`{app}-{id}`-style, unique).
fn gen_instance_id(app: &str, n: u64) -> String {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0);
    format!("{app}-{n}-{nanos:x}")
}

/// Current time as an RFC3339 string.
fn now_rfc3339() -> String {
    use time::OffsetDateTime;
    use time::format_description::well_known::Rfc3339;
    OffsetDateTime::now_utc()
        .format(&Rfc3339)
        .unwrap_or_default()
}

/// Wall-clock unix seconds — the block clock the abuse [`Guard`]'s sliding-window
/// rate limiter and governance timestamps run on.
fn now_unix_secs() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::funding::AttestedFunding;
    use crate::types::{GuestConfig, MachineConfig};
    use dreggnet_bridge::CapGrade;

    /// A test funding source standing in for the chain's verified attestation: it
    /// funds any app generously (a real on-chain reserve), so the lifecycle tests
    /// that aren't about the funding gate can admit a create. The funded-vs-not
    /// behavior is proven in [`funding`](crate::funding) + `tests/no_free_compute`.
    struct FundsAnyApp;
    impl FundingSource for FundsAnyApp {
        fn funded_leases(&self, app: &str) -> Result<Vec<Lease>, FundingError> {
            Ok(vec![Lease::funded(
                app,
                CapGrade::MicroVm,
                "computrons",
                1_000_000,
                1,
            )])
        }
    }

    /// A gateway whose funding source attests a generous on-chain lease for any app.
    fn funded_gw() -> MachineGateway {
        MachineGateway::new().funded_by(Arc::new(FundsAnyApp))
    }

    // ── the per-account abuse-prevention wire (the live enforcement) ──────────

    #[test]
    fn the_abuse_guard_refuses_an_over_quota_create_in_band() {
        // A funded gateway WITH the abuse guard: the default good-tier server quota
        // is 2, so the 3rd machine for one account is refused in-band (402), AFTER
        // the funding gate passed — the per-account ceiling a permissionless cloud
        // needs so one anonymous account cannot provision unboundedly.
        let guard = Arc::new(Guard::new([77u8; 32]));
        let gw = funded_gw().guarded_by(guard.clone());
        gw.create("acct-a", &CreateMachineRequest::default())
            .unwrap();
        gw.create("acct-a", &CreateMachineRequest::default())
            .unwrap();
        match gw.create("acct-a", &CreateMachineRequest::default()) {
            Err(GatewayError::Refused(GuardRefusal::Quota(_))) => {}
            other => panic!("expected an in-band quota refusal, got {other:?}"),
        }
        // The refused create recorded NO machine (the account still holds 2).
        assert_eq!(gw.list("acct-a").len(), 2);
        // A different account is unaffected (the quota is per-account).
        assert!(
            gw.create("acct-b", &CreateMachineRequest::default())
                .is_ok()
        );
    }

    #[test]
    fn deleting_a_machine_returns_the_account_quota_slot() {
        let guard = Arc::new(Guard::new([78u8; 32]));
        let gw = funded_gw().guarded_by(guard.clone());
        let m1 = gw
            .create("acct-c", &CreateMachineRequest::default())
            .unwrap();
        gw.create("acct-c", &CreateMachineRequest::default())
            .unwrap();
        // at the quota ceiling (2) → the next create is refused.
        assert!(matches!(
            gw.create("acct-c", &CreateMachineRequest::default()),
            Err(GatewayError::Refused(GuardRefusal::Quota(_)))
        ));
        // destroy one → the slot returns → a create admits again.
        assert!(gw.delete(&m1.id));
        assert!(
            gw.create("acct-c", &CreateMachineRequest::default())
                .is_ok()
        );
    }

    #[test]
    fn a_suspended_account_cannot_create_through_the_gateway() {
        let guard = Arc::new(Guard::new([79u8; 32]));
        let gw = funded_gw().guarded_by(guard.clone());
        gw.create("acct-d", &CreateMachineRequest::default())
            .unwrap();
        // an operator takes the account's resource down (a receipted governance turn).
        guard.suspend_resource("acct-d", "srv_x", "malware C2", "dregg:operator", 1000);
        // the suspended account now creates nothing (403).
        match gw.create("acct-d", &CreateMachineRequest::default()) {
            Err(GatewayError::Refused(GuardRefusal::Suspended { .. })) => {}
            other => panic!("expected a suspended refusal, got {other:?}"),
        }
    }

    #[test]
    fn create_records_a_machine_and_lists_it() {
        let gw = funded_gw();
        let m = gw
            .create("my-app", &CreateMachineRequest::default())
            .expect("default create is funded on-chain + valid");
        assert_eq!(m.state, MachineState::Created);
        assert!(!m.id.is_empty());
        assert!(!m.instance_id.is_empty());

        // It is retrievable + listed under the app.
        assert_eq!(gw.get(&m.id).map(|g| g.id), Some(m.id.clone()));
        assert_eq!(gw.list("my-app").len(), 1);
        assert_eq!(gw.list("other-app").len(), 0);
    }

    #[test]
    fn create_without_a_funding_source_fails_closed() {
        // No funding source ⇒ the gateway cannot confirm real on-chain funding ⇒ it
        // admits NO create (LEASE-1a: never invent funding from the request).
        let gw = MachineGateway::new();
        match gw.create("my-app", &CreateMachineRequest::default()) {
            Err(GatewayError::Unfunded(_)) => {}
            other => panic!("expected Unfunded, got {other:?}"),
        }
        assert_eq!(gw.count(), 0, "no machine recorded for unfunded work");
    }

    #[test]
    fn create_beyond_the_on_chain_reserve_is_refused() {
        // The chain funds app `a` with only a small reserve; a fabricated huge guest
        // demands far more, so it is refused — no free compute from a big request.
        let funding = AttestedFunding::from_leases([Lease::funded(
            "a",
            CapGrade::MicroVm,
            "computrons",
            8, // a tiny reserve
            1,
        )]);
        let gw = MachineGateway::new().funded_by(Arc::new(funding));
        let huge = CreateMachineRequest {
            config: MachineConfig {
                guest: GuestConfig {
                    cpu_kind: "performance".into(),
                    cpus: 8,
                    memory_mb: 1_048_576,
                },
                ..Default::default()
            },
            ..Default::default()
        };
        match gw.create("a", &huge) {
            Err(GatewayError::Unfunded(_)) => {}
            other => panic!("expected Unfunded for an over-reserve request, got {other:?}"),
        }
        assert_eq!(gw.count(), 0);
    }

    #[test]
    fn stop_start_delete_transition_the_record() {
        let gw = funded_gw();
        let m = gw.create("a", &CreateMachineRequest::default()).unwrap();
        assert_eq!(gw.stop(&m.id).unwrap().state, MachineState::Stopped);
        assert_eq!(gw.start(&m.id).unwrap().state, MachineState::Started);
        assert!(gw.delete(&m.id));
        assert!(gw.get(&m.id).is_none());
        assert!(!gw.delete(&m.id));
    }

    #[test]
    fn ids_are_unique_across_creates() {
        let gw = funded_gw();
        let a = gw.create("a", &CreateMachineRequest::default()).unwrap();
        let b = gw.create("a", &CreateMachineRequest::default()).unwrap();
        assert_ne!(a.id, b.id);
        assert_ne!(a.instance_id, b.instance_id);
    }

    /// A dispatch-configured gateway dispatches a created machine's lease over the
    /// mesh to a compute node and records the **real metered result** on the
    /// machine. This drives the genuine create→dispatch code path
    /// ([`dreggnet_control::dispatch_lease_over_mesh`]) against a loopback fulfill
    /// stub speaking the same `:8021/fulfill` contract the node-agent does — the
    /// gateway→node path with the overlay hop swapped for loopback.
    #[tokio::test]
    async fn create_then_fulfill_dispatches_and_records_the_metered_result() {
        let addr = spawn_fulfill_stub(200, None).await;

        // A compute backend whose stub mesh link sends the dispatch POST to the
        // loopback fulfill stub (StubMesh::dispatching_to is control's test seam).
        let node = MeshNode::new(
            MachineId("node-a".into()),
            "tailscale-overlay",
            format!("{addr}"),
            Ipv4Addr::new(100, 64, 0, 2),
        );
        let mesh = Arc::new(dreggnet_control::StubMesh::dispatching_to(addr));
        let gw = MachineGateway::with_compute(ComputeBackend::new(mesh, node))
            .funded_by(Arc::new(FundsAnyApp));
        assert!(gw.dispatches());

        let m = gw.create("demo", &CreateMachineRequest::default()).unwrap();
        assert_eq!(m.state, MachineState::Created);
        assert!(m.dregg.is_none());

        // Drive the dispatch — the real POST to the node, decoding the metered result.
        let out = gw
            .fulfill(&m.id)
            .await
            .expect("dispatch returns the metered result");
        assert_eq!(out.meter_units, 2);

        // The machine record now reflects the real durable metered outcome.
        let after = gw.get(&m.id).unwrap();
        assert_eq!(after.state, MachineState::Started);
        let report = after.dregg.expect("a dispatch report");
        assert_eq!(report.backend, "stub");
        assert_eq!(report.node.as_deref(), Some("100.64.0.2:8021"));
        assert_eq!(report.meter_units, Some(2));
        assert_eq!(report.outputs, vec!["42".to_string(), "84".to_string()]);
        assert!(report.error.is_none());
    }

    /// An over-budget lease the compute node refuses (`HTTP 402`) lands the machine
    /// in `failed` with the lapse reason recorded — no work is claimed.
    #[tokio::test]
    async fn dispatched_lapse_reflects_failed_with_a_reason() {
        let addr = spawn_fulfill_stub(
            402,
            Some(r#"{"ok":false,"error":"execution-lease exhausted after step2"}"#.into()),
        )
        .await;
        let node = MeshNode::new(
            MachineId("node-a".into()),
            "tailscale-overlay",
            format!("{addr}"),
            Ipv4Addr::new(100, 64, 0, 2),
        );
        let mesh = Arc::new(dreggnet_control::StubMesh::dispatching_to(addr));
        let gw = MachineGateway::with_compute(ComputeBackend::new(mesh, node))
            .funded_by(Arc::new(FundsAnyApp));

        let m = gw.create("demo", &CreateMachineRequest::default()).unwrap();
        match gw.fulfill(&m.id).await {
            Err(GatewayError::Lapsed(why)) => assert!(why.contains("exhausted")),
            other => panic!("expected a lapse, got {other:?}"),
        }
        let after = gw.get(&m.id).unwrap();
        assert_eq!(after.state, MachineState::Failed);
        let report = after.dregg.expect("a dispatch report");
        assert!(report.error.unwrap().contains("exhausted"));
        assert!(report.meter_units.is_none());
    }

    /// A minimal loopback server speaking the `:8021/fulfill` contract: it replies
    /// `status`, with a canned metered success envelope when `body` is `None`. This
    /// stands in for the node-agent so the gateway's dispatch path is exercised
    /// with no live overlay.
    async fn spawn_fulfill_stub(status: u16, body: Option<String>) -> std::net::SocketAddr {
        use tokio::io::{AsyncReadExt, AsyncWriteExt};
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        tokio::spawn(async move {
            loop {
                let (mut stream, _) = match listener.accept().await {
                    Ok(s) => s,
                    Err(_) => return,
                };
                let body = body.clone();
                tokio::spawn(async move {
                    let mut buf = Vec::new();
                    let mut tmp = [0u8; 4096];
                    // Read until the header terminator, then the Content-Length body.
                    let header_end = loop {
                        if let Some(p) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
                            break p;
                        }
                        let n = stream.read(&mut tmp).await.unwrap_or(0);
                        if n == 0 {
                            return; // a bare health-check probe
                        }
                        buf.extend_from_slice(&tmp[..n]);
                    };
                    let head = String::from_utf8_lossy(&buf[..header_end]).to_string();
                    let clen = head
                        .split("\r\n")
                        .find_map(|l| {
                            let (k, v) = l.split_once(':')?;
                            (k.trim().eq_ignore_ascii_case("content-length"))
                                .then(|| v.trim().parse::<usize>().ok())
                                .flatten()
                        })
                        .unwrap_or(0);
                    while buf.len() < header_end + 4 + clen {
                        let n = stream.read(&mut tmp).await.unwrap_or(0);
                        if n == 0 {
                            break;
                        }
                        buf.extend_from_slice(&tmp[..n]);
                    }
                    let payload = body.unwrap_or_else(|| {
                        serde_json::json!({
                            "ok": true, "lessee": "demo", "instance": "wl",
                            "step1": "42", "step2": "84",
                            "outputs": ["42", "84"], "meter_units": 2,
                        })
                        .to_string()
                    });
                    let resp = format!(
                        "HTTP/1.1 {status} X\r\nContent-Type: application/json\r\n\
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
