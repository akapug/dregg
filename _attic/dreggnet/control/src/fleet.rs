//! `fleet` — multi-backend scheduling over the growing compute fleet.
//!
//! The [`crate::Scheduler`] places one lease on one [`VmProvider`](crate::VmProvider).
//! This module is the layer that lets the control plane place leases across a
//! **set** of compute backends — node-a today, the other nodes as they join —
//! picking a healthy one per lease and failing over when one is down. It is the
//! "schedule each lease to a backend" half of the autonomous orchestration loop
//! ([`crate::orchestrator`]).
//!
//! ## What a backend is
//!
//! A [`Backend`] is a reachable compute node on the mesh: its [`MeshNode`] identity
//! (overlay address + bridge-agent port — where [`dispatch_lease_over_mesh`] POSTs
//! the lease), a name (`node-a`, `node-01`), and a `capacity` (the max
//! in-flight workloads it accepts). The [`BackendRegistry`] holds the live set.
//!
//! ## The three moves
//!
//! - **health-check** — [`BackendRegistry::health_check_all`] connects to each
//!   backend over the [`Mesh`] and probes its bridge-agent port
//!   ([`MeshLink::health_check`](crate::MeshLink::health_check)); a node that does
//!   not answer is marked [`Health::Unhealthy`] and is skipped by `pick`/`dispatch`.
//! - **pick** — [`BackendRegistry::pick`] chooses the next healthy backend with
//!   spare capacity, round-robin, so load spreads across the fleet rather than
//!   piling on one box.
//! - **dispatch + failover** — [`BackendRegistry::dispatch`] picks a backend and
//!   dispatches the lease to it over the mesh; if the backend is unreachable (a
//!   transport fault, not a lease lapse) it is marked unhealthy and the next
//!   healthy backend is tried, until one succeeds or the fleet is exhausted. A
//!   lease *lapse* (the backend's bridge refusing an over-budget lease) is NOT a
//!   failover — it is the lease's fault and is surfaced for the orchestrator to reap.
//!
//! All of this rides the same proven [`dispatch_lease_over_mesh`] POST the EC2
//! provider uses; the registry adds the fleet-wide health/pick/failover around it.

use std::sync::Mutex;

use dreggnet_bridge::{DurableOutput, Lease};

use crate::mesh::{Mesh, MeshNode, dispatch_lease_over_mesh};
use crate::provider::ProviderError;

/// One compute backend in the fleet: a named, capacity-bounded mesh node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Backend {
    /// A stable name for this backend (`node-a`, `node-01`). Also the
    /// settlement beneficiary — the box that ran the work is the one paid.
    pub name: String,
    /// The mesh identity the control plane reaches this backend at.
    pub node: MeshNode,
    /// The maximum number of in-flight workloads this backend accepts at once.
    pub capacity: usize,
}

impl Backend {
    /// A backend named `name`, reachable at `node`, accepting up to `capacity`
    /// concurrent workloads.
    pub fn new(name: impl Into<String>, node: MeshNode, capacity: usize) -> Backend {
        Backend {
            name: name.into(),
            node,
            capacity: capacity.max(1),
        }
    }
}

/// The health of a backend, as last observed by a health-check or a dispatch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Health {
    /// Never probed yet — eligible, but its health is unconfirmed.
    Unknown,
    /// Answered its last probe / dispatch — eligible for placement.
    Healthy,
    /// Did not answer — skipped by `pick`/`dispatch` until it recovers. The string
    /// carries the last failure detail.
    Unhealthy(String),
}

impl Health {
    /// Whether a backend in this state may be handed work.
    pub fn is_eligible(&self) -> bool {
        !matches!(self, Health::Unhealthy(_))
    }
}

/// A point-in-time snapshot of a backend's registry state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendStatus {
    pub name: String,
    pub health: Health,
    pub in_flight: usize,
    pub capacity: usize,
}

impl BackendStatus {
    /// Whether this backend can take another workload right now.
    pub fn has_spare_capacity(&self) -> bool {
        self.health.is_eligible() && self.in_flight < self.capacity
    }
}

/// Why a fleet dispatch could not place a lease.
#[derive(Debug, Clone)]
pub enum FleetError {
    /// No backend was eligible (none registered, or all unhealthy / at capacity).
    NoBackendAvailable,
    /// Every backend tried failed to carry the workload (a transport fault on
    /// each). Carries the per-backend error so the operator can see the fleet
    /// state. The lease itself was never refused — it can be retried once a
    /// backend recovers.
    AllBackendsFailed(Vec<(String, ProviderError)>),
    /// The lease lapsed at the backend's bridge (over-budget / unfunded — the
    /// bridge refused it). This is the lease's fault, not the fleet's: no failover
    /// is attempted; the orchestrator reaps it. Carries `(backend, detail)`.
    Lapsed { backend: String, detail: String },
}

impl std::fmt::Display for FleetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FleetError::NoBackendAvailable => {
                write!(f, "no healthy backend with spare capacity")
            }
            FleetError::AllBackendsFailed(errs) => {
                write!(f, "all {} backend(s) failed:", errs.len())?;
                for (name, e) in errs {
                    write!(f, " [{name}: {e}]")?;
                }
                Ok(())
            }
            FleetError::Lapsed { backend, detail } => {
                write!(f, "lease lapsed at backend `{backend}`: {detail}")
            }
        }
    }
}

impl std::error::Error for FleetError {}

/// A successful fleet placement: which backend ran the lease and the metered output.
#[derive(Debug, Clone)]
pub struct Placement {
    /// The backend that ran the workload (the settlement beneficiary).
    pub backend: String,
    /// The durable, metered result the backend's bridge agent returned.
    pub output: DurableOutput,
}

struct Entry {
    backend: Backend,
    health: Health,
    in_flight: usize,
}

struct Inner {
    entries: Vec<Entry>,
    /// Round-robin cursor into `entries`.
    cursor: usize,
}

/// The live set of compute backends the control plane schedules across.
pub struct BackendRegistry {
    inner: Mutex<Inner>,
}

impl Default for BackendRegistry {
    fn default() -> Self {
        BackendRegistry::new()
    }
}

impl BackendRegistry {
    /// An empty registry. Add backends with [`register`](BackendRegistry::register).
    pub fn new() -> BackendRegistry {
        BackendRegistry {
            inner: Mutex::new(Inner {
                entries: Vec::new(),
                cursor: 0,
            }),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Inner> {
        self.inner.lock().expect("backend registry poisoned")
    }

    /// Register (or replace, by name) a backend. A freshly registered backend is
    /// [`Health::Unknown`] until a health-check confirms it.
    pub fn register(&self, backend: Backend) {
        let mut g = self.lock();
        if let Some(e) = g
            .entries
            .iter_mut()
            .find(|e| e.backend.name == backend.name)
        {
            e.backend = backend;
            e.health = Health::Unknown;
        } else {
            g.entries.push(Entry {
                backend,
                health: Health::Unknown,
                in_flight: 0,
            });
        }
    }

    /// Remove a backend by name (e.g. a box leaving the fleet). Returns whether it
    /// was present.
    pub fn deregister(&self, name: &str) -> bool {
        let mut g = self.lock();
        let before = g.entries.len();
        g.entries.retain(|e| e.backend.name != name);
        g.entries.len() != before
    }

    /// How many backends are registered.
    pub fn len(&self) -> usize {
        self.lock().entries.len()
    }

    /// Whether the fleet is empty.
    pub fn is_empty(&self) -> bool {
        self.lock().entries.is_empty()
    }

    /// A snapshot of every backend's status (health, in-flight, capacity).
    pub fn statuses(&self) -> Vec<BackendStatus> {
        self.lock()
            .entries
            .iter()
            .map(|e| BackendStatus {
                name: e.backend.name.clone(),
                health: e.health.clone(),
                in_flight: e.in_flight,
                capacity: e.backend.capacity,
            })
            .collect()
    }

    /// The names of backends currently eligible (not unhealthy).
    pub fn healthy_names(&self) -> Vec<String> {
        self.lock()
            .entries
            .iter()
            .filter(|e| e.health.is_eligible())
            .map(|e| e.backend.name.clone())
            .collect()
    }

    /// Mark a backend healthy (e.g. it answered a probe). No-op if unknown name.
    pub fn mark_healthy(&self, name: &str) {
        if let Some(e) = self
            .lock()
            .entries
            .iter_mut()
            .find(|e| e.backend.name == name)
        {
            e.health = Health::Healthy;
        }
    }

    /// Mark a backend unhealthy with a reason (e.g. it failed a probe / dispatch).
    pub fn mark_unhealthy(&self, name: &str, reason: impl Into<String>) {
        if let Some(e) = self
            .lock()
            .entries
            .iter_mut()
            .find(|e| e.backend.name == name)
        {
            e.health = Health::Unhealthy(reason.into());
        }
    }

    /// Health-check every backend over `mesh`: connect to each and probe its
    /// bridge-agent port, updating its [`Health`]. Returns the resulting statuses.
    ///
    /// This is the proactive sweep an orchestrator runs on a cadence so `pick`
    /// always draws from a fresh view of the fleet. A live [`crate::TailscaleMesh`]
    /// link probes the node's real overlay address; a stub link reports its
    /// simulated reachability.
    pub async fn health_check_all(&self, mesh: &dyn Mesh) -> Vec<BackendStatus> {
        // Snapshot the backends to probe (don't hold the lock across awaits).
        let backends: Vec<Backend> = self
            .lock()
            .entries
            .iter()
            .map(|e| e.backend.clone())
            .collect();
        for b in backends {
            let health = match mesh.connect(&b.node).await {
                Ok(link) => match link.health_check().await {
                    Ok(()) => Health::Healthy,
                    Err(e) => Health::Unhealthy(e.to_string()),
                },
                Err(e) => Health::Unhealthy(e.to_string()),
            };
            if let Some(entry) = self
                .lock()
                .entries
                .iter_mut()
                .find(|e| e.backend.name == b.name)
            {
                entry.health = health;
            }
        }
        self.statuses()
    }

    /// Pick the next eligible backend with spare capacity (round-robin), reserving a
    /// slot on it (its in-flight count is incremented). Returns the chosen backend,
    /// or `None` if the fleet has no eligible, non-full backend. Release the slot
    /// with [`release`](BackendRegistry::release) when the workload settles.
    pub fn pick(&self) -> Option<Backend> {
        let mut g = self.lock();
        let n = g.entries.len();
        if n == 0 {
            return None;
        }
        let start = g.cursor;
        for offset in 0..n {
            let idx = (start + offset) % n;
            let e = &g.entries[idx];
            if e.health.is_eligible() && e.in_flight < e.backend.capacity {
                g.cursor = (idx + 1) % n;
                g.entries[idx].in_flight += 1;
                return Some(g.entries[idx].backend.clone());
            }
        }
        None
    }

    /// Release a reserved slot on a backend (its in-flight count is decremented).
    /// Called when a placed workload settles or fails. No-op if the name is unknown
    /// or already at zero.
    pub fn release(&self, name: &str) {
        if let Some(e) = self
            .lock()
            .entries
            .iter_mut()
            .find(|e| e.backend.name == name)
        {
            e.in_flight = e.in_flight.saturating_sub(1);
        }
    }

    /// Schedule `lease` onto a healthy backend and dispatch it over `mesh`, failing
    /// over across the fleet on a transport fault.
    ///
    /// The loop: pick a healthy backend (round-robin), dispatch the lease to its
    /// bridge agent over the mesh ([`dispatch_lease_over_mesh`]), and —
    /// - on success, return the [`Placement`] (which backend ran it + the metered
    ///   output);
    /// - on a **transport fault** ([`ProviderError::Bridge`] / unreachable / not
    ///   wired), mark that backend unhealthy and try the next eligible one;
    /// - on a **lease lapse** ([`ProviderError::WorkloadLapsed`] — the bridge
    ///   refused an over-budget / unfunded lease), stop: this is the lease's fault,
    ///   surfaced as [`FleetError::Lapsed`] for the orchestrator to reap (no point
    ///   re-dispatching a doomed lease to another box).
    ///
    /// Each backend's in-flight slot is reserved for its attempt and released after.
    pub async fn dispatch(
        &self,
        mesh: &dyn Mesh,
        lease: &Lease,
        instance: &str,
    ) -> Result<Placement, FleetError> {
        let mut failures: Vec<(String, ProviderError)> = Vec::new();
        // Bound the failover sweep by the fleet size: at most one attempt per
        // backend (pick reserves a distinct backend each call until exhausted).
        let max_attempts = self.lock().entries.len();
        let mut attempted: Vec<String> = Vec::new();

        for _ in 0..max_attempts {
            let backend = match self.pick() {
                Some(b) if !attempted.contains(&b.name) => b,
                // pick() returned a backend we already tried (capacity let it round
                // back) or nothing eligible — stop the sweep.
                Some(b) => {
                    self.release(&b.name);
                    break;
                }
                None => break,
            };
            attempted.push(backend.name.clone());

            let result = dispatch_lease_over_mesh(mesh, &backend.node, lease, instance).await;
            self.release(&backend.name);

            match result {
                Ok(output) => {
                    self.mark_healthy(&backend.name);
                    return Ok(Placement {
                        backend: backend.name,
                        output,
                    });
                }
                Err(ProviderError::WorkloadLapsed(detail)) => {
                    // The lease was refused by the bridge — not a backend fault.
                    // The backend itself answered, so it stays healthy.
                    self.mark_healthy(&backend.name);
                    return Err(FleetError::Lapsed {
                        backend: backend.name,
                        detail,
                    });
                }
                Err(other) => {
                    // A transport / not-wired fault: this backend can't carry the
                    // work right now — mark it down and fail over to the next.
                    self.mark_unhealthy(&backend.name, other.to_string());
                    failures.push((backend.name, other));
                }
            }
        }

        if failures.is_empty() {
            Err(FleetError::NoBackendAvailable)
        } else {
            Err(FleetError::AllBackendsFailed(failures))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mesh::{MeshKeypair, StubMesh, TailscaleMesh};
    use dreggnet_bridge::CapGrade;
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

    fn dead_node() -> MeshNode {
        // An overlay address on the documentation TEST-NET range with a port nothing
        // listens on — a connect to it is refused / times out (unhealthy).
        let mut n = MeshNode::new(
            crate::provider::MachineId("dead".into()),
            MeshKeypair::generate().public_base64(),
            "203.0.113.2:51820",
            Ipv4Addr::new(127, 0, 0, 1),
        );
        n.agent_port = 1; // port 1: nothing listens; connect refused
        n
    }

    /// Stand up a loopback server speaking the `:8021/fulfill` contract (the same
    /// shape `mesh`'s tests + the node-agent serve). Returns its address.
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
                            return; // a bare probe (health-check leg)
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

    #[test]
    fn register_pick_round_robins_and_respects_capacity() {
        let reg = BackendRegistry::new();
        reg.register(Backend::new("a", dead_node(), 1));
        reg.register(Backend::new("b", dead_node(), 1));
        reg.mark_healthy("a");
        reg.mark_healthy("b");

        // Round-robin: first pick a, then b.
        let first = reg.pick().expect("a");
        let second = reg.pick().expect("b");
        assert_ne!(first.name, second.name);
        // Both now at capacity (1 each) → the third pick finds nothing.
        assert!(reg.pick().is_none());

        // Release one → it becomes pickable again.
        reg.release(&first.name);
        assert_eq!(reg.pick().unwrap().name, first.name);
    }

    #[test]
    fn unhealthy_backends_are_skipped() {
        let reg = BackendRegistry::new();
        reg.register(Backend::new("a", dead_node(), 5));
        reg.register(Backend::new("b", dead_node(), 5));
        reg.mark_unhealthy("a", "down");
        reg.mark_healthy("b");
        // Only b is eligible, no matter how many times we pick.
        for _ in 0..3 {
            assert_eq!(reg.pick().unwrap().name, "b");
        }
        assert_eq!(reg.healthy_names(), vec!["b".to_string()]);
    }

    #[tokio::test]
    async fn health_check_marks_reachable_and_unreachable() {
        let addr = spawn_fulfill_stub().await;
        let reg = BackendRegistry::new();
        reg.register(Backend::new("live", node_at(addr), 2));
        reg.register(Backend::new("down", dead_node(), 2));

        reg.health_check_all(&TailscaleMesh::new()).await;
        let names = reg.healthy_names();
        assert!(
            names.contains(&"live".to_string()),
            "live backend is healthy"
        );
        assert!(
            !names.contains(&"down".to_string()),
            "dead backend marked down"
        );
    }

    #[tokio::test]
    async fn dispatch_places_on_a_healthy_backend() {
        let addr = spawn_fulfill_stub().await;
        let reg = BackendRegistry::new();
        reg.register(Backend::new("node-a", node_at(addr), 2));
        reg.mark_healthy("node-a");

        let lease = Lease::funded("agent", CapGrade::Sandboxed, "USD", 100, 1);
        let placement = reg
            .dispatch(&TailscaleMesh::new(), &lease, "wl-1")
            .await
            .expect("placed on node-a");
        assert_eq!(placement.backend, "node-a");
        assert_eq!(placement.output.meter_units, 2);
        // The slot was released after the dispatch.
        let s = reg.statuses();
        assert_eq!(s.iter().find(|s| s.name == "node-a").unwrap().in_flight, 0);
    }

    #[tokio::test]
    async fn dispatch_fails_over_from_a_dead_backend() {
        let addr = spawn_fulfill_stub().await;
        let reg = BackendRegistry::new();
        // The dead backend is first in round-robin order; dispatch must fail over.
        reg.register(Backend::new("node-down", dead_node(), 2));
        reg.register(Backend::new("node-a", node_at(addr), 2));
        reg.mark_healthy("node-down");
        reg.mark_healthy("node-a");

        let lease = Lease::funded("agent", CapGrade::Sandboxed, "USD", 100, 1);
        let placement = reg
            .dispatch(&TailscaleMesh::new(), &lease, "wl-failover")
            .await
            .expect("failed over to the live backend");
        assert_eq!(placement.backend, "node-a");
        // The dead backend was marked unhealthy by the failed attempt.
        let statuses = reg.statuses();
        let down = statuses.iter().find(|s| s.name == "node-down").unwrap();
        assert!(matches!(down.health, Health::Unhealthy(_)));
    }

    #[tokio::test]
    async fn dispatch_with_no_backends_is_an_error() {
        let reg = BackendRegistry::new();
        let lease = Lease::funded("agent", CapGrade::Sandboxed, "USD", 100, 1);
        assert!(matches!(
            reg.dispatch(&StubMesh::reachable(), &lease, "wl").await,
            Err(FleetError::NoBackendAvailable)
        ));
    }
}
