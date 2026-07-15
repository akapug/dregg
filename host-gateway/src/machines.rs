//! The fly.io-compatible machines surface — records, the store, and the handler the
//! [`crate::route`] classifier dispatches into.
//!
//! A create maps a fly machine request onto a durable workload record and admits it.
//! The **fulfillment** — running the workload on a real dregg execution-lease — is the
//! injected [`MachineLauncher`] seam: an in-process [`NullLauncher`] admits the record
//! without launching (the dev / single-box default), and a production launcher drives
//! the lease over the resident execution-lease plane. This is an honest named seam, not
//! a stub: the routing, the record lifecycle, the owner-scoping, and the fly-shaped
//! wire types are all real; what a launcher supplies is the compute backend.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use http_serve::{HttpMethod, WebResponse};
use serde::{Deserialize, Serialize};

use crate::route::{self, Route};

/// The lifecycle state of a machine (a subset of fly's states, on the dregg workload
/// lifecycle).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MachineState {
    /// Created + admitted, workload running.
    Started,
    /// Reaped (stopped) — the record survives, the workload is not running.
    Stopped,
    /// Destroyed — retained only transiently for the destroy response.
    Destroyed,
}

impl MachineState {
    /// The fly-compatible state string.
    pub fn as_str(self) -> &'static str {
        match self {
            MachineState::Started => "started",
            MachineState::Stopped => "stopped",
            MachineState::Destroyed => "destroyed",
        }
    }
}

/// The requested guest shape (a fly `guest` block, graded onto the dregg cap-lattice by
/// a launcher). Only the size-shaping fields the gateway records.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct GuestConfig {
    /// Requested vCPUs.
    #[serde(default)]
    pub cpus: u32,
    /// Requested memory (MiB).
    #[serde(default)]
    pub memory_mb: u32,
    /// The workload image reference (an owned-sandbox workload reference, not an OCI
    /// pull — noted honestly as a divergence from fly).
    #[serde(default)]
    pub image: String,
}

/// The config block of a create request / a machine record (`fly` shape, trimmed).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct MachineConfig {
    /// The guest shape.
    #[serde(default)]
    pub guest: GuestConfig,
    /// The requested region.
    #[serde(default)]
    pub region: String,
}

/// A create-machine request body (`POST /v1/apps/{app}/machines`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct CreateMachineRequest {
    /// The machine name (fly `name`).
    #[serde(default)]
    pub name: String,
    /// The machine config.
    #[serde(default)]
    pub config: MachineConfig,
}

/// A machine record (the fly `Machine` shape the surface returns).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Machine {
    /// The machine id.
    pub id: String,
    /// The machine name.
    pub name: String,
    /// The owning app (fly `{app}`).
    pub app: String,
    /// The owner subject (the cap-scope key for `/api/machines`; set from the verified
    /// subject at create).
    pub owner: String,
    /// The lifecycle state.
    pub state: MachineState,
    /// The region.
    pub region: String,
    /// The config the machine was created with.
    pub config: MachineConfig,
}

/// The compute backend a create is fulfilled onto — the injected launch seam.
///
/// A create records the [`Machine`], then calls [`MachineLauncher::launch`]; a
/// production launcher drives the workload onto a funded dregg execution-lease and
/// returns the started state. The [`NullLauncher`] admits without launching (dev).
pub trait MachineLauncher: Send + Sync {
    /// Launch (or admit) `machine`; return the state it settled into (or an error
    /// string that becomes a `502`). The default in-process launcher returns
    /// `Started`.
    fn launch(&self, machine: &Machine) -> Result<MachineState, String>;

    /// Reap `machine` (stop the workload). Default: no-op success.
    fn reap(&self, _machine: &Machine) -> Result<(), String> {
        Ok(())
    }
}

/// The in-process launcher: admits a create as `Started` without a real compute
/// backend (the dev / single-box default). The named seam a production launcher fills.
pub struct NullLauncher;

impl MachineLauncher for NullLauncher {
    fn launch(&self, _machine: &Machine) -> Result<MachineState, String> {
        Ok(MachineState::Started)
    }
}

/// The machine store — the fly surface's record plane, owner-scoped.
pub struct MachineStore {
    machines: Mutex<BTreeMap<String, Machine>>,
    next_id: AtomicU64,
}

impl Default for MachineStore {
    fn default() -> MachineStore {
        MachineStore {
            machines: Mutex::new(BTreeMap::new()),
            next_id: AtomicU64::new(1),
        }
    }
}

impl MachineStore {
    /// A fresh, empty store.
    pub fn new() -> MachineStore {
        MachineStore::default()
    }

    fn mint_id(&self) -> String {
        let n = self.next_id.fetch_add(1, Ordering::Relaxed);
        format!("mch_{n:016x}")
    }

    /// Create + fulfill a machine for `app`, owned by `owner`, through `launcher`.
    pub fn create(
        &self,
        app: &str,
        owner: &str,
        req: &CreateMachineRequest,
        launcher: &dyn MachineLauncher,
    ) -> Result<Machine, String> {
        let id = self.mint_id();
        let mut machine = Machine {
            id: id.clone(),
            name: if req.name.is_empty() {
                id.clone()
            } else {
                req.name.clone()
            },
            app: app.to_string(),
            owner: owner.to_string(),
            state: MachineState::Stopped,
            region: req.config.region.clone(),
            config: req.config.clone(),
        };
        machine.state = launcher.launch(&machine)?;
        self.machines
            .lock()
            .expect("machines poisoned")
            .insert(id, machine.clone());
        Ok(machine)
    }

    /// All machines in `app`.
    pub fn list(&self, app: &str) -> Vec<Machine> {
        self.machines
            .lock()
            .expect("machines poisoned")
            .values()
            .filter(|m| m.app == app)
            .cloned()
            .collect()
    }

    /// All machines across all apps (the source for the cap-scoped `/api/machines`).
    pub fn all(&self) -> Vec<Machine> {
        self.machines
            .lock()
            .expect("machines poisoned")
            .values()
            .cloned()
            .collect()
    }

    /// One machine by id (scoped to `app`).
    pub fn get(&self, app: &str, id: &str) -> Option<Machine> {
        self.machines
            .lock()
            .expect("machines poisoned")
            .get(id)
            .filter(|m| m.app == app)
            .cloned()
    }

    /// Set a machine's state (stop / start), returning the updated record.
    pub fn set_state(&self, app: &str, id: &str, state: MachineState) -> Option<Machine> {
        let mut guard = self.machines.lock().expect("machines poisoned");
        let m = guard.get_mut(id).filter(|m| m.app == app)?;
        m.state = state;
        Some(m.clone())
    }

    /// Destroy a machine record.
    pub fn delete(&self, app: &str, id: &str) -> Option<Machine> {
        let mut guard = self.machines.lock().expect("machines poisoned");
        if guard.get(id).map(|m| m.app == app).unwrap_or(false) {
            guard.remove(id)
        } else {
            None
        }
    }
}

/// The fly-machines API handler: classifies with [`crate::route`] and drives the
/// [`MachineStore`] through the injected [`MachineLauncher`]. A create is owner-scoped
/// to the verified `subject` (so `/api/machines` can later scope by owner); a create
/// with no verified subject is refused (`401`).
///
/// The store is shared (`Arc`) so the assembled gateway reads the same records through
/// the cap-scoped `/api/machines` surface.
pub struct MachinesHandler {
    store: Arc<MachineStore>,
    launcher: Box<dyn MachineLauncher>,
}

impl MachinesHandler {
    /// A handler over a fresh store with the in-process [`NullLauncher`].
    pub fn new() -> MachinesHandler {
        MachinesHandler {
            store: Arc::new(MachineStore::new()),
            launcher: Box::new(NullLauncher),
        }
    }

    /// A handler over `store` with a specific launcher (the production compute backend).
    pub fn over(store: Arc<MachineStore>, launcher: Box<dyn MachineLauncher>) -> MachinesHandler {
        MachinesHandler { store, launcher }
    }

    /// A handler with a specific launcher over a fresh store.
    pub fn with_launcher(launcher: Box<dyn MachineLauncher>) -> MachinesHandler {
        MachinesHandler {
            store: Arc::new(MachineStore::new()),
            launcher,
        }
    }

    /// The backing store (the source `/api/machines` reads) — shareable.
    pub fn store(&self) -> &Arc<MachineStore> {
        &self.store
    }

    /// Dispatch a classified request. `subject` is the verified creator (for owner
    /// scoping); a `None` subject on a create is refused (`401`).
    pub fn respond(
        &self,
        method: HttpMethod,
        target: &str,
        body: &[u8],
        subject: Option<&str>,
    ) -> WebResponse {
        match route::parse(method, target) {
            Route::CreateMachine { app } => {
                let Some(owner) = subject.map(str::trim).filter(|s| !s.is_empty()) else {
                    return WebResponse::error(
                        401,
                        "a machine create must carry a verified subject",
                    );
                };
                let req: CreateMachineRequest = match serde_json::from_slice(body) {
                    Ok(r) => r,
                    Err(_) if body.is_empty() => CreateMachineRequest::default(),
                    Err(e) => return WebResponse::error(400, format!("bad create body: {e}")),
                };
                match self.store.create(app, owner, &req, self.launcher.as_ref()) {
                    Ok(m) => machine_json(201, &m),
                    Err(e) => WebResponse::error(502, format!("launch failed: {e}")),
                }
            }
            Route::ListMachines { app } => json_ok(&self.store.list(app)),
            Route::GetMachine { app, id } => match self.store.get(app, id) {
                Some(m) => machine_json(200, &m),
                None => WebResponse::error(404, "no such machine"),
            },
            Route::StopMachine { app, id } => match self.store.get(app, id) {
                Some(m) => {
                    let _ = self.launcher.reap(&m);
                    let updated = self
                        .store
                        .set_state(app, id, MachineState::Stopped)
                        .unwrap_or(m);
                    machine_json(200, &updated)
                }
                None => WebResponse::error(404, "no such machine"),
            },
            Route::StartMachine { app, id } => match self.store.get(app, id) {
                Some(mut m) => match self.launcher.launch(&m) {
                    Ok(state) => {
                        m = self.store.set_state(app, id, state).unwrap_or(m);
                        machine_json(200, &m)
                    }
                    Err(e) => WebResponse::error(502, format!("start failed: {e}")),
                },
                None => WebResponse::error(404, "no such machine"),
            },
            Route::DeleteMachine { app, id } => match self.store.delete(app, id) {
                Some(mut m) => {
                    m.state = MachineState::Destroyed;
                    machine_json(200, &m)
                }
                None => WebResponse::error(404, "no such machine"),
            },
            _ => WebResponse::error(404, "unknown machines surface"),
        }
    }
}

impl Default for MachinesHandler {
    fn default() -> MachinesHandler {
        MachinesHandler::new()
    }
}

fn machine_json(status: u16, machine: &Machine) -> WebResponse {
    let body = serde_json::to_vec(machine).unwrap_or_default();
    WebResponse {
        status,
        content_type: "application/json".to_string(),
        body,
    }
}

fn json_ok<T: Serialize>(value: &T) -> WebResponse {
    WebResponse::json(serde_json::to_vec(value).unwrap_or_default())
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE: &str = "dregg:alice";

    fn create_body() -> Vec<u8> {
        serde_json::to_vec(&CreateMachineRequest {
            name: "web".into(),
            config: MachineConfig {
                guest: GuestConfig {
                    cpus: 1,
                    memory_mb: 256,
                    image: "workload:agent".into(),
                },
                region: "iad".into(),
            },
        })
        .unwrap()
    }

    #[test]
    fn create_list_get_stop_start_delete() {
        let h = MachinesHandler::new();
        // Create (owner-scoped).
        let created = h.respond(
            HttpMethod::Post,
            "/v1/apps/app1/machines",
            &create_body(),
            Some(ALICE),
        );
        assert_eq!(created.status, 201);
        let m: Machine = serde_json::from_slice(&created.body).unwrap();
        assert_eq!(m.app, "app1");
        assert_eq!(m.owner, ALICE);
        assert_eq!(m.state, MachineState::Started);

        // List.
        let listed = h.respond(HttpMethod::Get, "/v1/apps/app1/machines", &[], None);
        let all: Vec<Machine> = serde_json::from_slice(&listed.body).unwrap();
        assert_eq!(all.len(), 1);

        // Get.
        let got = h.respond(
            HttpMethod::Get,
            &format!("/v1/apps/app1/machines/{}", m.id),
            &[],
            None,
        );
        assert_eq!(got.status, 200);

        // Stop -> stopped.
        let stopped = h.respond(
            HttpMethod::Post,
            &format!("/v1/apps/app1/machines/{}/stop", m.id),
            &[],
            None,
        );
        let sm: Machine = serde_json::from_slice(&stopped.body).unwrap();
        assert_eq!(sm.state, MachineState::Stopped);

        // Start -> started.
        let started = h.respond(
            HttpMethod::Post,
            &format!("/v1/apps/app1/machines/{}/start", m.id),
            &[],
            None,
        );
        let stm: Machine = serde_json::from_slice(&started.body).unwrap();
        assert_eq!(stm.state, MachineState::Started);

        // Delete -> destroyed, then gone.
        let del = h.respond(
            HttpMethod::Delete,
            &format!("/v1/apps/app1/machines/{}", m.id),
            &[],
            None,
        );
        let dm: Machine = serde_json::from_slice(&del.body).unwrap();
        assert_eq!(dm.state, MachineState::Destroyed);
        assert_eq!(
            h.respond(
                HttpMethod::Get,
                &format!("/v1/apps/app1/machines/{}", m.id),
                &[],
                None
            )
            .status,
            404
        );
    }

    #[test]
    fn create_without_a_subject_is_refused() {
        let h = MachinesHandler::new();
        let resp = h.respond(
            HttpMethod::Post,
            "/v1/apps/app1/machines",
            &create_body(),
            None,
        );
        assert_eq!(resp.status, 401, "a create must carry a verified subject");
        assert!(
            h.store().all().is_empty(),
            "no machine recorded on a refused create"
        );
    }

    #[test]
    fn a_launcher_failure_is_a_502() {
        struct FailLauncher;
        impl MachineLauncher for FailLauncher {
            fn launch(&self, _m: &Machine) -> Result<MachineState, String> {
                Err("no compute".into())
            }
        }
        let h = MachinesHandler::with_launcher(Box::new(FailLauncher));
        let resp = h.respond(
            HttpMethod::Post,
            "/v1/apps/app1/machines",
            &create_body(),
            Some(ALICE),
        );
        assert_eq!(resp.status, 502);
    }
}
