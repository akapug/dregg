//! The live-cloud transport: a real HTTP client for a remote DreggNet gateway's
//! fly-compatible machines API.
//!
//! When `dregg-cloud` is given `--endpoint <gateway-url>` (or `DREGGNET_ENDPOINT`),
//! the cloud verbs stop routing through the in-process `LocalProvider` and instead
//! make REAL HTTP calls against the gateway (`gateway/`, the ~5K-LOC fly-machines
//! server):
//!
//! ```text
//!   POST   /v1/apps/{app}/machines        create + fulfill a machine
//!   GET    /v1/apps/{app}/machines        list machines
//!   GET    /v1/apps/{app}/machines/{id}   machine status
//!   POST   /v1/apps/{app}/machines/{id}/stop    reap
//!   DELETE /v1/apps/{app}/machines/{id}   destroy
//! ```
//!
//! Auth is the account's `dga1_` credential presented as `Authorization: Bearer
//! <tok>` (the gateway's webauth bearer). The wire bodies mirror the gateway's
//! [`fly types`](../../gateway/src/types.rs) — kept as a small, dependency-light
//! local mirror here (the CLI does not depend on the gateway crate / its server),
//! decoded leniently so a fly client's full record round-trips.
//!
//! The blocking [`reqwest`] call runs on a dedicated OS thread (matching the agent
//! brain's pattern, `dregg-agent::brain`) so the CLI's tokio runtime is never
//! blocked and the client is agnostic to any ambient async runtime.

use std::time::Duration;

use anyhow::{Result, anyhow};
use serde::{Deserialize, Serialize};

/// The guest sizing of a machine (fly's `config.guest`). Mirrors the gateway's
/// `GuestConfig`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GuestConfig {
    pub cpu_kind: String,
    pub cpus: u32,
    pub memory_mb: u32,
}

/// The machine config (fly's `config`). Only the load-bearing subset is modelled;
/// the gateway tolerates the rest.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MachineConfig {
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub image: String,
    pub guest: GuestConfig,
    #[serde(default, skip_serializing_if = "std::collections::BTreeMap::is_empty")]
    pub env: std::collections::BTreeMap<String, String>,
}

/// The body of `POST /v1/apps/{app}/machines` (fly create).
#[derive(Debug, Clone, Serialize)]
pub struct CreateMachineRequest {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub region: Option<String>,
    pub config: MachineConfig,
}

/// The DreggNet-specific dispatch result attached to a [`Machine`] after it runs —
/// the real durable metered outcome (or the lapse/failure reason) the live node
/// returned. Mirrors the gateway's `DispatchReport`.
#[derive(Debug, Clone, Deserialize)]
pub struct DispatchReport {
    pub backend: String,
    #[serde(default)]
    pub node: Option<String>,
    #[serde(default)]
    pub meter_units: Option<i64>,
    #[serde(default)]
    pub outputs: Vec<String>,
    #[serde(default)]
    pub error: Option<String>,
}

/// A machine record, fly-compatible. Decoded leniently (unknown fields ignored) so
/// a fly client's full record round-trips.
#[derive(Debug, Clone, Deserialize)]
pub struct Machine {
    pub id: String,
    #[serde(default)]
    pub name: String,
    pub state: String,
    #[serde(default)]
    pub region: String,
    #[serde(default)]
    pub dregg: Option<DispatchReport>,
}

/// A fly-style error body (`{ "error": "..." }`).
#[derive(Debug, Clone, Deserialize)]
pub struct ApiError {
    pub error: String,
}

/// The outcome of a machines-API call: the HTTP status the gateway returned plus
/// the decoded body. The caller renders the funded/refused story HONESTLY from the
/// status — a 200 carries a [`Machine`]; a 4xx (lease refused / quota / unfunded)
/// carries the gateway's own refusal message.
#[derive(Debug, Clone)]
pub enum MachineOutcome {
    /// `2xx`: the gateway accepted (and, for create against a dispatch-configured
    /// node, ran) the work. Carries the machine record + its metered result.
    Ok(Machine),
    /// A non-2xx refusal/error: the gateway's status + its message, rendered as-is
    /// so the CLI never dresses up a refusal as success.
    Refused { status: u16, message: String },
}

/// A list of machines (`GET /v1/apps/{app}/machines`).
#[derive(Debug, Clone)]
pub enum ListOutcome {
    Ok(Vec<Machine>),
    Refused { status: u16, message: String },
}

/// A real HTTP client to a remote DreggNet gateway's machines API.
pub struct CloudClient {
    /// The gateway base URL (e.g. `https://dreggnet.example.com`), no trailing
    /// slash.
    endpoint: String,
    /// The `dga1_` bearer credential to present, if the account is logged in.
    bearer: Option<String>,
}

impl CloudClient {
    /// Build a client for `endpoint`, presenting `bearer` (the account credential)
    /// when present. The endpoint's trailing slash is trimmed so path joins are clean.
    pub fn new(endpoint: &str, bearer: Option<String>) -> CloudClient {
        CloudClient {
            endpoint: endpoint.trim_end_matches('/').to_string(),
            bearer,
        }
    }

    /// The base URL this client targets (for the honest "→ <endpoint>" banner).
    pub fn endpoint(&self) -> &str {
        &self.endpoint
    }

    /// Whether a bearer credential is being presented.
    pub fn has_bearer(&self) -> bool {
        self.bearer.is_some()
    }

    /// `POST /v1/apps/{app}/machines` — create (and, on a dispatch-configured
    /// gateway, run) a machine. Returns the gateway's funded result or its refusal.
    pub fn create_machine(&self, app: &str, req: &CreateMachineRequest) -> Result<MachineOutcome> {
        let url = format!("{}/v1/apps/{}/machines", self.endpoint, app);
        let body = serde_json::to_string(req)?;
        let (status, text) = self.send(Method::Post, &url, Some(body))?;
        Ok(machine_outcome(status, &text))
    }

    /// `GET /v1/apps/{app}/machines` — list the app's machines.
    pub fn list_machines(&self, app: &str) -> Result<ListOutcome> {
        let url = format!("{}/v1/apps/{}/machines", self.endpoint, app);
        let (status, text) = self.send(Method::Get, &url, None)?;
        if (200..300).contains(&status) {
            let machines: Vec<Machine> = serde_json::from_str(&text)
                .map_err(|e| anyhow!("gateway returned an undecodable machine list: {e}"))?;
            Ok(ListOutcome::Ok(machines))
        } else {
            Ok(ListOutcome::Refused {
                status,
                message: error_message(&text),
            })
        }
    }

    /// `GET /v1/apps/{app}/machines/{id}` — one machine's status.
    pub fn get_machine(&self, app: &str, id: &str) -> Result<MachineOutcome> {
        let url = format!("{}/v1/apps/{}/machines/{}", self.endpoint, app, id);
        let (status, text) = self.send(Method::Get, &url, None)?;
        Ok(machine_outcome(status, &text))
    }

    /// `POST /v1/apps/{app}/machines/{id}/stop` — reap the workload.
    pub fn stop_machine(&self, app: &str, id: &str) -> Result<MachineOutcome> {
        let url = format!("{}/v1/apps/{}/machines/{}/stop", self.endpoint, app, id);
        let (status, text) = self.send(Method::Post, &url, None)?;
        Ok(machine_outcome(status, &text))
    }

    /// `DELETE /v1/apps/{app}/machines/{id}` — destroy the record. Returns whether
    /// the gateway accepted it, plus its message on a refusal.
    pub fn delete_machine(&self, app: &str, id: &str) -> Result<(bool, String)> {
        let url = format!("{}/v1/apps/{}/machines/{}", self.endpoint, app, id);
        let (status, text) = self.send(Method::Delete, &url, None)?;
        if (200..300).contains(&status) {
            Ok((true, text))
        } else {
            Ok((false, error_message(&text)))
        }
    }

    /// Run one blocking HTTP request on a dedicated OS thread (so the CLI's tokio
    /// runtime is never blocked, and `reqwest::blocking` — which panics if dropped
    /// inside an async runtime — runs on its own thread). Returns `(status, body)`.
    fn send(&self, method: Method, url: &str, body: Option<String>) -> Result<(u16, String)> {
        let url = url.to_string();
        let bearer = self.bearer.clone();
        std::thread::scope(|s| {
            s.spawn(move || -> Result<(u16, String)> {
                let client = reqwest::blocking::Client::builder()
                    .timeout(Duration::from_secs(30))
                    .user_agent(concat!("dregg-cloud/", env!("CARGO_PKG_VERSION")))
                    .build()
                    .map_err(|e| anyhow!("build http client: {e}"))?;
                let mut builder = match method {
                    Method::Get => client.get(&url),
                    Method::Post => client.post(&url),
                    Method::Delete => client.delete(&url),
                };
                if let Some(tok) = &bearer {
                    builder = builder.bearer_auth(tok);
                }
                if let Some(body) = body {
                    builder = builder
                        .header(reqwest::header::CONTENT_TYPE, "application/json")
                        .body(body);
                }
                let resp = builder
                    .send()
                    .map_err(|e| anyhow!("request to {url} failed: {e}"))?;
                let status = resp.status().as_u16();
                let text = resp
                    .text()
                    .map_err(|e| anyhow!("read response body: {e}"))?;
                Ok((status, text))
            })
            .join()
            .map_err(|_| anyhow!("http worker thread panicked"))?
        })
    }
}

/// Decode a single-machine response into an outcome by status.
fn machine_outcome(status: u16, text: &str) -> MachineOutcome {
    if (200..300).contains(&status) {
        match serde_json::from_str::<Machine>(text) {
            Ok(m) => MachineOutcome::Ok(m),
            // A 2xx with an undecodable body is itself a refusal-to-trust signal.
            Err(e) => MachineOutcome::Refused {
                status,
                message: format!("gateway returned an undecodable machine record: {e}"),
            },
        }
    } else {
        MachineOutcome::Refused {
            status,
            message: error_message(text),
        }
    }
}

/// Pull the human message out of a gateway error body (`{ "error": "..." }`),
/// falling back to the raw text when it is not the fly error shape.
fn error_message(text: &str) -> String {
    match serde_json::from_str::<ApiError>(text) {
        Ok(e) => e.error,
        Err(_) if text.trim().is_empty() => "(no body)".to_string(),
        Err(_) => text.trim().to_string(),
    }
}

/// The HTTP verbs the machines API uses.
#[derive(Clone, Copy)]
enum Method {
    Get,
    Post,
    Delete,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn error_message_reads_the_fly_shape() {
        assert_eq!(
            error_message(r#"{"error":"lease refused: unfunded"}"#),
            "lease refused: unfunded"
        );
        assert_eq!(error_message("plain text"), "plain text");
        assert_eq!(error_message("   "), "(no body)");
    }

    #[test]
    fn machine_outcome_decodes_a_funded_create() {
        let body = r#"{"id":"abc123","name":"w1","state":"started","region":"local",
            "instance_id":"i-1","private_ip":"",
            "config":{"image":"","guest":{"cpu_kind":"shared","cpus":1,"memory_mb":256},"env":{}},
            "created_at":"now","updated_at":"now",
            "dregg":{"backend":"local","meter_units":3,"outputs":["step1","step2"]}}"#;
        match machine_outcome(200, body) {
            MachineOutcome::Ok(m) => {
                assert_eq!(m.id, "abc123");
                assert_eq!(m.state, "started");
                let d = m.dregg.expect("dispatch report");
                assert_eq!(d.meter_units, Some(3));
                assert_eq!(d.outputs.len(), 2);
            }
            MachineOutcome::Refused { .. } => panic!("expected Ok"),
        }
    }

    #[test]
    fn machine_outcome_renders_a_refusal_honestly() {
        match machine_outcome(422, r#"{"error":"lease refused: over budget"}"#) {
            MachineOutcome::Refused { status, message } => {
                assert_eq!(status, 422);
                assert_eq!(message, "lease refused: over budget");
            }
            MachineOutcome::Ok(_) => panic!("expected Refused"),
        }
    }
}
