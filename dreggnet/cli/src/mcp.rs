//! `dregg-cloud mcp` — the agent-facing twin of the `dregg-cloud` CLI.
//!
//! An MCP (Model Context Protocol) server speaking JSON-RPC 2.0 over stdio, so any
//! MCP client (Claude, an agent runtime, an IDE) can interface with the verifiable
//! cloud through the SAME control plane every CLI verb routes through. Each tool
//! reuses the library this crate's `cmd_*` handlers reuse — `dregg_deploy` calls the
//! real [`DeployEngine`]/`deploy_on_disk`, `dregg_run` the real
//! [`Scheduler`]/`LocalProvider`, `dregg_verify` the real [`verify_site_bundle`],
//! `dregg_agent_*` the real [`AgentCloud`]/`verify_agent_run`, `dregg_status`/
//! `dregg_cell_read` the same persisted state notebook. There is no second object
//! model and no mock — the MCP is a face, not a reimplementation.
//!
//! ## The verifiable-cloud surface (the tools)
//!
//! ```text
//!   dregg_status        the cloud status: account + sites/leases/domains/workloads/agents
//!   dregg_cell_read     read one cloud cell (a site / agent / domain / workload / lease)
//!   dregg_login         connect / mint / show the cap-account (a dga1_ credential)
//!   dregg_deploy        clone→build→publish a site cell (local, or --endpoint live)
//!   dregg_run           run a metered WAT workload (local control plane, or live)
//!   dregg_verify        re-witness a deploy's signed receipt bundle (verify, don't trust)
//!   dregg_agent_deploy  deploy + run a budget-bounded, cap-confined, receipted agent
//!   dregg_agent_verify  re-witness an agent run's receipt chain + that it stayed under bound
//!   dregg_machines      drive the live gateway's fly-compatible machines API (--endpoint)
//! ```
//!
//! Cap-scoping: the account's `dga1_` credential (from `dregg_login`) is presented as
//! the bearer on every `--endpoint` live call, exactly as the CLI does.
//!
//! ## Transport
//!
//! Newline-delimited JSON-RPC 2.0 on stdin/stdout. stdout carries ONLY protocol
//! messages (the tool handlers return structured data; nothing here prints to stdout);
//! all logs go to stderr (see `install_quiet_logging`). The blocking stdin loop runs
//! on a `spawn_blocking` thread so the async library calls (`deploy`, `run`) drive on
//! the CLI's tokio runtime via a captured [`Handle`] without blocking it.

use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::{Result, anyhow, bail};
use serde_json::{Value, json};
use tokio::runtime::Handle;

use dregg_deploy::{DeployEngine, DeploySpec, deploy_on_disk};
use dreggnet_control::{Lease, LocalProvider, MachineSize, Scheduler, WorkloadSource};
use dreggnet_exec::agent::{AgentAction, AgentCloud, AgentSpec, PlannedBrain, verify_agent_run};
use dreggnet_webapp::{SiteRegistry, fetch_site_bundle, hex32, parse_hex32, verify_site_bundle};
use dreggnet_webauth::cred::{PublicKey, RootKey};
use dreggnet_webauth::grant::mint_caps;
use dreggnet_webauth::subject_of;

use crate::cloud::{
    CloudClient, CreateMachineRequest, GuestConfig, ListOutcome, MachineConfig, MachineOutcome,
};
use crate::{
    DeployRecord, IdentityRecord, LeaseRecord, Store, WorkloadRecord, bearer_of, default_site_name,
    grade_str, load_bundle, save_bundle, short, state_label,
};

/// The protocol version this server defaults to when a client does not request one.
const DEFAULT_PROTOCOL_VERSION: &str = "2025-06-18";

/// Entry point for `dregg-cloud mcp`: serve the MCP stdio loop. Called from `main`
/// inside the tokio runtime; the blocking stdin loop is moved to a `spawn_blocking`
/// thread so async library calls can `Handle::block_on` without nesting on a worker.
pub async fn run(state_dir: PathBuf, endpoint: Option<String>) -> Result<()> {
    let handle = Handle::current();
    eprintln!(
        "dregg-cloud mcp: serving the verifiable cloud over JSON-RPC stdio \
         (state {}{})",
        state_dir.display(),
        match &endpoint {
            Some(ep) => format!(", endpoint {ep}"),
            None => String::new(),
        }
    );
    tokio::task::spawn_blocking(move || serve_stdio(&state_dir, endpoint.as_deref(), &handle))
        .await
        .map_err(|e| anyhow!("mcp loop thread panicked: {e}"))?
}

/// The blocking JSON-RPC stdio loop: read a line, dispatch, write the response line.
fn serve_stdio(state_dir: &Path, endpoint: Option<&str>, handle: &Handle) -> Result<()> {
    let stdin = std::io::stdin();
    let mut stdout = std::io::stdout();
    let mut line = String::new();
    loop {
        line.clear();
        let n = stdin.lock().read_line(&mut line)?;
        if n == 0 {
            // EOF — the client closed the pipe.
            return Ok(());
        }
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        let req: Value = match serde_json::from_str(trimmed) {
            Ok(v) => v,
            Err(e) => {
                // A parse error has no id to correlate — emit a null-id JSON-RPC error.
                write_message(
                    &mut stdout,
                    &rpc_error(Value::Null, -32700, &format!("parse error: {e}")),
                )?;
                continue;
            }
        };
        let id = req.get("id").cloned();
        let method = req.get("method").and_then(|m| m.as_str()).unwrap_or("");
        let params = req.get("params").cloned().unwrap_or(Value::Null);

        // Notifications (no id) get no response.
        let is_notification = id.is_none();

        match method {
            "initialize" => {
                let resp = handle_initialize(id.unwrap_or(Value::Null), &params);
                write_message(&mut stdout, &resp)?;
            }
            "notifications/initialized" | "notifications/cancelled" => {
                // Acknowledged by silence (notifications take no response).
            }
            "ping" => {
                if let Some(id) = id {
                    write_message(&mut stdout, &rpc_result(id, json!({})))?;
                }
            }
            "tools/list" => {
                if let Some(id) = id {
                    write_message(
                        &mut stdout,
                        &rpc_result(id, json!({ "tools": tool_specs() })),
                    )?;
                }
            }
            "tools/call" => {
                let id = match id {
                    Some(id) => id,
                    None => continue,
                };
                let resp = handle_tools_call(state_dir, endpoint, handle, id, &params);
                write_message(&mut stdout, &resp)?;
            }
            other => {
                if !is_notification {
                    write_message(
                        &mut stdout,
                        &rpc_error(
                            id.unwrap_or(Value::Null),
                            -32601,
                            &format!("method not found: {other}"),
                        ),
                    )?;
                }
            }
        }
    }
}

/// Write one JSON-RPC message as a single newline-delimited line, then flush.
fn write_message(out: &mut impl Write, msg: &Value) -> Result<()> {
    let line = serde_json::to_string(msg)?;
    out.write_all(line.as_bytes())?;
    out.write_all(b"\n")?;
    out.flush()?;
    Ok(())
}

fn rpc_result(id: Value, result: Value) -> Value {
    json!({ "jsonrpc": "2.0", "id": id, "result": result })
}

fn rpc_error(id: Value, code: i64, message: &str) -> Value {
    json!({ "jsonrpc": "2.0", "id": id, "error": { "code": code, "message": message } })
}

fn handle_initialize(id: Value, params: &Value) -> Value {
    // Echo the client's requested protocol version when present (interop), else default.
    let proto = params
        .get("protocolVersion")
        .and_then(|v| v.as_str())
        .unwrap_or(DEFAULT_PROTOCOL_VERSION)
        .to_string();
    rpc_result(
        id,
        json!({
            "protocolVersion": proto,
            "capabilities": { "tools": { "listChanged": false } },
            "serverInfo": {
                "name": "dregg-cloud",
                "version": env!("CARGO_PKG_VERSION"),
                "title": "dregg-cloud — the verifiable cloud"
            },
            "instructions":
                "The agent face of the dregg verifiable cloud. Deploy/run/verify sites and \
                 budget-bounded agents over a cap-scoped account (dregg_login). Every result is \
                 re-witnessable: dregg_verify re-checks a deploy's signed bytes, dregg_agent_verify \
                 re-checks an agent run's receipt chain + budget bound. Pass `endpoint` (or run with \
                 --endpoint) to act against the LIVE gateway instead of the local in-process cloud."
        }),
    )
}

/// Dispatch a `tools/call`. Tool-level failures are returned as an MCP error RESULT
/// (`isError: true`) rather than a JSON-RPC protocol error, so the client sees them.
fn handle_tools_call(
    state_dir: &Path,
    cli_endpoint: Option<&str>,
    handle: &Handle,
    id: Value,
    params: &Value,
) -> Value {
    let name = params.get("name").and_then(|n| n.as_str()).unwrap_or("");
    let args = params.get("arguments").cloned().unwrap_or(json!({}));

    let outcome = dispatch_tool(state_dir, cli_endpoint, handle, name, &args);
    match outcome {
        Ok(value) => rpc_result(id, tool_text_result(&value, false)),
        Err(e) => rpc_result(
            id,
            tool_text_result(&json!({ "error": e.to_string() }), true),
        ),
    }
}

/// Wrap a structured result value as MCP `tools/call` content (pretty JSON text).
fn tool_text_result(value: &Value, is_error: bool) -> Value {
    let text = serde_json::to_string_pretty(value).unwrap_or_else(|_| value.to_string());
    json!({
        "content": [ { "type": "text", "text": text } ],
        "isError": is_error
    })
}

/// The actual per-tool dispatch. Each arm reuses the same library + state model the
/// `cmd_*` CLI handlers do, returning structured JSON instead of printing.
fn dispatch_tool(
    state_dir: &Path,
    cli_endpoint: Option<&str>,
    handle: &Handle,
    name: &str,
    args: &Value,
) -> Result<Value> {
    // A per-call endpoint overrides the process-wide one (so a single MCP server can
    // serve both the local sim and a live gateway, per call).
    let endpoint = args
        .get("endpoint")
        .and_then(|v| v.as_str())
        .map(str::to_string)
        .or_else(|| cli_endpoint.map(str::to_string));
    let endpoint = endpoint.as_deref();

    match name {
        "dregg_status" => tool_status(state_dir, endpoint),
        "dregg_cell_read" => tool_cell_read(state_dir, args),
        "dregg_login" => tool_login(state_dir, args),
        "dregg_deploy" => handle.block_on(tool_deploy(state_dir, endpoint, args)),
        "dregg_run" => handle.block_on(tool_run(state_dir, endpoint, args)),
        "dregg_verify" => tool_verify(state_dir, args),
        "dregg_agent_deploy" => tool_agent_deploy(state_dir, args),
        "dregg_agent_verify" => tool_agent_verify(state_dir, args),
        "dregg_machines" => tool_machines(state_dir, endpoint, args),
        other => bail!("unknown tool `{other}`"),
    }
}

// ---------------------------------------------------------------------------
// Tools
// ---------------------------------------------------------------------------

/// `dregg_status` — the cloud status: the connected account + every recorded cell
/// (sites, leases, domains, workloads, agents). With an endpoint, also reflect the
/// live machines for an app. Reuses the same persisted notebook as `dregg-cloud ls`.
fn tool_status(state_dir: &Path, endpoint: Option<&str>) -> Result<Value> {
    let store = Store::load(state_dir)?;
    let sites: Vec<Value> = store
        .deploys
        .iter()
        .map(|d| {
            json!({
                "id": d.id, "site": d.site_name, "url": d.url, "owner": d.owner,
                "commit": d.commit, "content_root": d.content_root,
                "verifiable": !d.signer_pubkey.is_empty()
            })
        })
        .collect();
    let leases: Vec<Value> = store
        .leases
        .iter()
        .map(|l| {
            json!({ "id": l.id, "lessee": l.lessee, "cap_grade": l.cap_grade,
                    "asset": l.asset, "budget": l.budget_units, "funded": l.funded })
        })
        .collect();
    let domains: Vec<Value> = store
        .domains
        .iter()
        .map(|b| json!({ "domain": b.domain, "site": b.site, "verified": b.is_verified() }))
        .collect();
    let workloads: Vec<Value> = store
        .workloads
        .iter()
        .map(|w| {
            json!({ "id": w.id, "lease": w.lease_id, "lang": w.lang,
                    "state": w.state, "meter_units": w.meter_units })
        })
        .collect();
    let agents: Vec<Value> = store
        .agents
        .iter()
        .map(|a| {
            json!({ "agent": a.agent, "consumed": a.consumed, "budget": a.budget,
                    "asset": a.asset, "receipts": a.receipts.len() })
        })
        .collect();

    let mut status = json!({
        "account": store.identity.as_ref().map(|i| i.subject.clone()),
        "state_dir": state_dir.display().to_string(),
        "sites": sites,
        "leases": leases,
        "domains": domains,
        "workloads": workloads,
        "agents": agents,
    });

    if let Some(ep) = endpoint {
        status["endpoint"] = json!(ep);
        status["endpoint_note"] = json!(
            "live machines are per-app — read them with dregg_machines {action:'list', app:'<app>'}"
        );
    }
    Ok(status)
}

/// `dregg_cell_read` — read one cloud cell by id/name: a site, agent, domain,
/// workload, or lease. The agent-facing read of a single resource.
fn tool_cell_read(state_dir: &Path, args: &Value) -> Result<Value> {
    let target = arg_str(args, "name")?;
    let store = Store::load(state_dir)?;

    if let Some(d) = store
        .deploys
        .iter()
        .find(|d| d.id.starts_with(&target) || d.site_name == target)
    {
        return Ok(json!({
            "kind": "site", "id": d.id, "site": d.site_name, "repo": d.repo,
            "url": d.url, "owner": d.owner, "commit": d.commit,
            "content_root": d.content_root, "build_plan": d.build_plan,
            "asset_count": d.asset_count, "meter_units": d.meter_units,
            "signer_pubkey": d.signer_pubkey, "verifiable": !d.signer_pubkey.is_empty()
        }));
    }
    if let Some(a) = store
        .agents
        .iter()
        .find(|a| a.agent == target || a.agent.starts_with(&target))
    {
        return Ok(json!({ "kind": "agent", "report": serde_json::to_value(a)? }));
    }
    if let Some(b) = store.domains.iter().find(|b| b.domain == target) {
        return Ok(json!({
            "kind": "domain", "domain": b.domain, "site": b.site,
            "verified": b.is_verified()
        }));
    }
    if let Some(w) = store.workloads.iter().find(|w| w.id.starts_with(&target)) {
        return Ok(json!({
            "kind": "workload", "id": w.id, "lease": w.lease_id, "lang": w.lang,
            "source": w.source, "state": w.state, "machine": w.machine_id,
            "meter_units": w.meter_units
        }));
    }
    if let Some(l) = store.leases.iter().find(|l| l.id.starts_with(&target)) {
        return Ok(json!({
            "kind": "lease", "id": l.id, "lessee": l.lessee, "cap_grade": l.cap_grade,
            "asset": l.asset, "budget": l.budget_units, "funded": l.funded
        }));
    }
    bail!("no cloud cell matching `{target}` (try dregg_status to list cells)")
}

/// `dregg_login` — connect a cap-account: show the current account, bind a wallet
/// `dga1_` credential (+ optional verifying root), or mint a fresh local one. Reuses
/// the same webauth cred core + persisted `IdentityRecord` as `dregg-cloud login`.
fn tool_login(state_dir: &Path, args: &Value) -> Result<Value> {
    let mut store = Store::load(state_dir)?;
    let credential = args.get("credential").and_then(|v| v.as_str());
    let root = args.get("root").and_then(|v| v.as_str());
    let new = args.get("new").and_then(|v| v.as_bool()).unwrap_or(false);
    let show = args
        .get("show_credential")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    // Show the current account (no bind/mint requested).
    if credential.is_none() && !new {
        return match &store.identity {
            Some(id) => Ok(json!({
                "account": id.subject,
                "caps": id.caps,
                "root_pubkey": id.root_pubkey,
                "credential": if show { json!(id.credential) } else { json!("(hidden — pass show_credential:true to reveal this BEARER secret)") }
            })),
            None => bail!(
                "no connected account — call dregg_login with new:true or credential:'dga1_…'"
            ),
        };
    }

    let identity = if let Some(cred) = credential {
        let subject = subject_of(cred)
            .ok_or_else(|| anyhow!("credential did not decode as a dregg `dga1_` credential"))?;
        let root_pubkey = match root {
            Some(hex) => {
                PublicKey::from_hex(hex)
                    .map_err(|e| anyhow!("`root` is not a valid public key hex: {e}"))?;
                hex.to_string()
            }
            None => String::new(),
        };
        IdentityRecord {
            subject,
            credential: cred.to_string(),
            root_pubkey,
            caps: Vec::new(),
        }
    } else {
        // new == true: mint a fresh local cap-account.
        let caps: Vec<String> = args
            .get("caps")
            .and_then(|v| v.as_array())
            .map(|a| {
                a.iter()
                    .filter_map(|c| c.as_str().map(str::to_string))
                    .collect()
            })
            .unwrap_or_else(|| vec!["deploy".to_string(), "domains".to_string()]);
        let root_key = RootKey::generate();
        let cred = mint_caps(&root_key, caps.iter().cloned(), None).encode();
        let subject =
            subject_of(&cred).ok_or_else(|| anyhow!("minted credential did not decode"))?;
        IdentityRecord {
            subject,
            credential: cred,
            root_pubkey: root_key.public().to_hex(),
            caps,
        }
    };

    let result = json!({
        "account": identity.subject,
        "caps": identity.caps,
        "root_pubkey": identity.root_pubkey,
        "credential": if show { json!(identity.credential) } else { json!("(hidden — a dga1_ credential is a BEARER secret; pass show_credential:true to reveal)") },
        "note": "the credential is stored 0600 in the state dir and presented as the bearer on every live (--endpoint) call"
    });
    store.identity = Some(identity);
    store.save(state_dir)?;
    Ok(result)
}

/// `dregg_deploy` — clone→build→publish a repo as a signed, re-witnessable site cell.
/// Local: the real `DeployEngine`/`deploy_on_disk` over an in-process signed
/// `SiteRegistry`, persisting the bundle for `dregg_verify`. Live (`endpoint`): create
/// a machine for the site's app on the gateway's fly-compatible machines API.
async fn tool_deploy(state_dir: &Path, endpoint: Option<&str>, args: &Value) -> Result<Value> {
    let repo = arg_str(args, "repo")?;
    let name = args
        .get("name")
        .and_then(|v| v.as_str())
        .map(str::to_string);
    let git_ref = args.get("ref").and_then(|v| v.as_str()).map(str::to_string);
    let budget = args.get("budget").and_then(|v| v.as_i64()).unwrap_or(100);
    let site_name = name.unwrap_or_else(|| default_site_name(&repo));

    let store_for_owner = Store::load(state_dir)?;
    let owner = args
        .get("owner")
        .and_then(|v| v.as_str())
        .map(str::to_string)
        .unwrap_or_else(|| {
            store_for_owner
                .identity
                .as_ref()
                .map(|i| i.subject.clone())
                .unwrap_or_else(|| "operator".to_string())
        });

    // LIVE PATH: provision on the remote gateway (reuse the same CloudClient the CLI uses).
    if let Some(ep) = endpoint {
        let client = CloudClient::new(ep, bearer_of(&store_for_owner));
        let mut env = std::collections::BTreeMap::new();
        env.insert("DREGG_DEPLOY_REPO".to_string(), repo.clone());
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
        return Ok(machine_outcome_json(
            client.create_machine(&site_name, &req)?,
            ep,
            &site_name,
            "deploy",
        ));
    }

    if budget < 3 {
        bail!("budget must be >= 3 (clone+build+publish each charge 1; got {budget})");
    }

    // LOCAL PATH: the same in-process signed-registry deploy the CLI runs (no serve).
    let id = uuid::Uuid::new_v4().to_string();
    let deploy_root = state_dir.join("deploys");
    let workroot = deploy_root.join("work");
    let db_path = deploy_root.join(format!("{id}.db"));

    let mut seed = [0u8; 32];
    seed[..16].copy_from_slice(uuid::Uuid::new_v4().as_bytes());
    seed[16..].copy_from_slice(uuid::Uuid::new_v4().as_bytes());
    let registry = Arc::new(SiteRegistry::signed(seed));
    let engine = Arc::new(DeployEngine::new(&workroot, registry.clone()));

    let mut spec = DeploySpec::new(&repo, &site_name, &owner);
    spec.git_ref = git_ref;
    spec.budget_units = budget;
    spec.cost_per_step = 1;

    let receipt = deploy_on_disk(engine, &spec, &id, &db_path)
        .await
        .map_err(|e| anyhow!("deploy failed: {e}"))?;

    let bundle = registry.site_bundle(&receipt.site_name);
    let signer_pubkey = bundle
        .as_ref()
        .map(|b| hex32(&b.signer))
        .unwrap_or_default();
    if let Some(bundle) = &bundle {
        save_bundle(state_dir, &id, bundle)?;
    }

    let result = json!({
        "id": id,
        "site": receipt.site_name,
        "url": receipt.url,
        "repo": repo,
        "commit": receipt.commit,
        "build_plan": receipt.build_plan,
        "content_root": receipt.content_root,
        "asset_count": receipt.asset_count,
        "owner": receipt.owner,
        "meter_units": receipt.meter_units,
        "signer_pubkey": signer_pubkey,
        "verifiable": !signer_pubkey.is_empty(),
        "published": "locally (signed bundle persisted); the public edge is the separate gateway-mount step",
        "verify_with": format!("dregg_verify {{ target: '{}' }}", short(&id))
    });

    let mut store = Store::load(state_dir)?;
    store.deploys.push(DeployRecord {
        id,
        repo,
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
    store.save(state_dir)?;
    Ok(result)
}

/// `dregg_run` — run a metered WAT workload. Local: the real `Scheduler`/`LocalProvider`
/// fulfills a funded lease as a durable workflow (auto-opening a sandboxed lease when
/// none is given). Live (`endpoint`): create a machine on the gateway.
async fn tool_run(state_dir: &Path, endpoint: Option<&str>, args: &Value) -> Result<Value> {
    let lang = args.get("lang").and_then(|v| v.as_str()).unwrap_or("wat");
    if lang != "wat" {
        bail!("only lang `wat` is wired at this rung (got `{lang}`)");
    }
    let source_path = args.get("source_path").and_then(|v| v.as_str());
    let inline = args.get("source").and_then(|v| v.as_str());

    let mut store = Store::load(state_dir)?;

    // LIVE PATH: run on the remote cloud by creating a machine under the lease's app.
    if let Some(ep) = endpoint {
        let path = source_path.map(str::to_string).ok_or_else(|| {
            anyhow!("live run needs `source_path` (the gateway resolves the image)")
        })?;
        let lease_id = args.get("lease").and_then(|v| v.as_str());
        let app = match lease_id.and_then(|l| store.lease(l).map(|r| r.lessee.clone())) {
            Some(app) => app,
            None => store
                .identity
                .as_ref()
                .map(|i| i.subject.clone())
                .unwrap_or_else(|| "operator".to_string()),
        };
        let client = CloudClient::new(ep, bearer_of(&store));
        let mut env = std::collections::BTreeMap::new();
        env.insert("DREGG_WORKLOAD_SOURCE".to_string(), path.clone());
        let req = CreateMachineRequest {
            name: None,
            region: None,
            config: MachineConfig {
                image: format!("wat:{path}"),
                guest: GuestConfig {
                    cpu_kind: "shared".to_string(),
                    cpus: 1,
                    memory_mb: 256,
                },
                env,
            },
        };
        return Ok(machine_outcome_json(
            client.create_machine(&app, &req)?,
            ep,
            &app,
            "run",
        ));
    }

    // The WAT source text — inline `source`, else read `source_path`.
    let src = match (inline, source_path) {
        (Some(s), _) => s.to_string(),
        (None, Some(p)) => {
            std::fs::read_to_string(p).map_err(|e| anyhow!("read workload source {p}: {e}"))?
        }
        (None, None) => bail!("provide `source` (inline WAT) or `source_path`"),
    };
    if src.trim().is_empty() {
        bail!("workload source is empty");
    }

    // Resolve the lease: a named one, else auto-open a funded sandboxed lease.
    let lease_id = match args.get("lease").and_then(|v| v.as_str()) {
        Some(l) => {
            if store.lease(l).is_none() {
                bail!("no lease `{l}` (omit `lease` to auto-open one)");
            }
            l.to_string()
        }
        None => auto_open_lease(&mut store, state_dir)?,
    };
    let record = store
        .lease(&lease_id)
        .ok_or_else(|| anyhow!("lease `{lease_id}` vanished"))?
        .clone();

    let workload = WorkloadSource {
        lang: lang.to_string(),
        source: src,
    };
    let scheduler = Scheduler::new(LocalProvider::new(), MachineSize::Small, "local");
    let workload_id = scheduler
        .place_workload(record.lease()?, Some(workload))
        .await
        .map_err(|e| anyhow!("placement failed: {e}"))?;
    let placed = scheduler
        .workload(&workload_id)
        .ok_or_else(|| anyhow!("scheduler lost the placed workload"))?;

    let label = state_label(&placed.state);
    let machine_id = placed.machine.id.to_string();
    let (step1, step2, meter, outputs) = match &placed.output {
        Some(out) => (
            Some(out.step1.clone()),
            Some(out.step2.clone()),
            out.meter_units,
            out.outputs.clone(),
        ),
        None => (None, None, 0, Vec::new()),
    };

    let result = json!({
        "workload": workload_id.to_string(),
        "lease": lease_id,
        "machine": machine_id,
        "lang": lang,
        "state": label,
        "outputs": outputs,
        "meter_units": meter,
        "budget": record.budget_units,
        "lapse_reason": placed.lapse_reason,
    });

    store.workloads.push(WorkloadRecord {
        id: workload_id.to_string(),
        lease_id,
        lessee: record.lessee.clone(),
        cap_grade: record.cap_grade.clone(),
        lang: lang.to_string(),
        source: source_path.unwrap_or("<inline>").to_string(),
        state: label,
        machine_id,
        step1,
        step2,
        meter_units: meter,
    });
    store.save(state_dir)?;
    Ok(result)
}

/// Auto-open a funded sandboxed lease (USD, budget 100, 1/step) when `dregg_run` is
/// called without one, so an agent can run a workload in a single tool call.
fn auto_open_lease(store: &mut Store, state_dir: &Path) -> Result<String> {
    let lessee = store
        .identity
        .as_ref()
        .map(|i| i.subject.clone())
        .unwrap_or_else(|| "operator".to_string());
    let id = uuid::Uuid::new_v4().to_string();
    let record = LeaseRecord {
        id: id.clone(),
        lessee,
        cap_grade: grade_str(dreggnet_control::CapGrade::Sandboxed).to_string(),
        asset: "USD".to_string(),
        budget_units: 100,
        per_period_units: 1,
        funded: true,
    };
    let lease: Lease = record.lease()?;
    if !lease.is_active() {
        bail!("auto-opened lease is not active");
    }
    store.leases.push(record);
    store.save(state_dir)?;
    Ok(id)
}

/// `dregg_verify` — re-witness a deployed site WITHOUT trusting the host: re-check the
/// served bytes against the committed content root + the signed receipt chain. Reuses
/// the real `verify_site_bundle`. `tamper:true` flips one byte to PROVE the check bites.
fn tool_verify(state_dir: &Path, args: &Value) -> Result<Value> {
    let target = arg_str(args, "target")?;
    let url = args.get("url").and_then(|v| v.as_str());
    let tamper = args
        .get("tamper")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    let store = Store::load(state_dir)?;
    let deploy = store
        .deploys
        .iter()
        .find(|d| d.id.starts_with(&target) || d.site_name == target)
        .ok_or_else(|| anyhow!("no deploy matching `{target}` (dregg_status to list sites)"))?;

    if deploy.signer_pubkey.is_empty() {
        bail!(
            "deploy `{}` was recorded without a signed receipt — not re-witnessable",
            short(&deploy.id)
        );
    }
    let expected_signer = parse_hex32(&deploy.signer_pubkey)
        .ok_or_else(|| anyhow!("recorded signer pubkey did not decode as 32-byte hex"))?;

    let mut bundle = match url {
        Some(addr) => {
            let host = format!("{}.example.com", deploy.site_name);
            fetch_site_bundle(addr, &host)
                .map_err(|e| anyhow!("fetch receipt bundle from {addr}: {e}"))?
                .ok_or_else(|| anyhow!("the server at {addr} served no signed receipt"))?
        }
        None => load_bundle(state_dir, &deploy.id)?,
    };

    let mut tampered_path: Option<String> = None;
    if tamper {
        tampered_path = flip_one_served_byte(&mut bundle);
        if tampered_path.is_none() {
            return Ok(json!({
                "verified": null,
                "note": "the bundle has no served bytes to flip; nothing to demonstrate"
            }));
        }
    }

    match verify_site_bundle(&bundle, Some(expected_signer)) {
        Ok(v) => {
            if tamper {
                bail!(
                    "verification PASSED a tampered bundle — the tamper check did not bite (a defect)"
                );
            }
            let commit_match = v.commit.as_ref().map(|c| *c == deploy.commit);
            if commit_match == Some(false) {
                bail!("source-commitment manifest does not match the recorded deploy commit");
            }
            Ok(json!({
                "verified": true,
                "site": v.name,
                "owner": v.owner,
                "content_root": v.content_root,
                "asset_count": v.asset_count,
                "signer": deploy.signer_pubkey,
                "commit": v.commit,
                "commit_matches_deploy": commit_match,
                "summary": "served bytes match the committed root; receipt chain intact"
            }))
        }
        Err(e) => {
            if tamper {
                // The check BIT the flipped byte — exactly what tamper proves.
                return Ok(json!({
                    "verified": false,
                    "tamper_caught": true,
                    "tampered_asset": tampered_path,
                    "mismatch": e.to_string(),
                    "summary": "the tamper was CAUGHT — the served bytes no longer re-witness to the committed root"
                }));
            }
            Ok(json!({
                "verified": false,
                "mismatch": e.to_string(),
                "summary": "verification failed — the served bytes/receipt do not re-witness"
            }))
        }
    }
}

/// Flip one byte of the first served asset (mirrors the CLI's `verify --tamper` self-demo).
fn flip_one_served_byte(bundle: &mut dreggnet_webapp::SiteReceiptBundle) -> Option<String> {
    let (path, asset) = bundle
        .content
        .assets
        .iter_mut()
        .find(|(_, a)| !a.body.is_empty())?;
    asset.body[0] ^= 0x01;
    Some(path.clone())
}

/// `dregg_agent_deploy` — deploy + run a budget-bounded, cap-confined, receipted agent
/// against the self-contained mock-LLM plan (an admitted action, an out-of-bundle
/// refusal, a budget-bound runaway). Reuses the real `AgentCloud`. Persists the report
/// for `dregg_agent_verify`. (Live LLM brains stay a CLI build-feature; the MCP keeps
/// the self-contained, always-buildable path.)
fn tool_agent_deploy(state_dir: &Path, args: &Value) -> Result<Value> {
    let budget = args.get("budget").and_then(|v| v.as_i64()).unwrap_or(50);
    let cost = args.get("cost").and_then(|v| v.as_i64()).unwrap_or(1);
    if budget <= 0 || cost <= 0 {
        bail!("budget and cost must both be > 0 (got budget={budget}, cost={cost})");
    }
    let asset = args
        .get("asset")
        .and_then(|v| v.as_str())
        .unwrap_or("DREGG");
    let services =
        str_list(args, "services").unwrap_or_else(|| vec!["search".into(), "fetch".into()]);
    let cells = str_list(args, "cells").unwrap_or_else(|| vec!["/scratch".into()]);
    let subagent = args
        .get("subagent")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);
    let id = args
        .get("id")
        .and_then(|v| v.as_str())
        .map(str::to_string)
        .unwrap_or_else(|| format!("agent:{}", &uuid::Uuid::new_v4().to_string()[..8]));

    let cloud = AgentCloud::new();
    let mut spec = AgentSpec::new(&id, budget);
    spec.asset = asset.to_string();
    spec.cost_per_action = cost;
    spec.services = services.clone();
    spec.cells = cells.clone();
    let handle = cloud
        .deploy(&spec)
        .map_err(|e| anyhow!("deploy failed: {e}"))?;

    let svc0 = services[0].clone();
    let cell0 = cells[0].clone();
    let mut plan = vec![
        AgentAction::Invoke {
            service: svc0.clone(),
        },
        AgentAction::CellWrite {
            path: cell0,
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
    let report = cloud.run(&handle, &mut PlannedBrain::new(plan));

    let mut store = Store::load(state_dir)?;
    let parent_json = agent_report_json(&report, &handle.caps);
    store.agents.retain(|a| a.agent != report.agent);
    store.agents.push(report);

    let mut sub_json = Value::Null;
    if subagent {
        let child_id = format!("{id}/child");
        let mut child_spec = AgentSpec::new(&child_id, (budget / 2).max(1));
        child_spec.asset = asset.to_string();
        child_spec.cost_per_action = cost;
        child_spec.services = vec![svc0.clone()];
        let child = cloud
            .deploy_subagent(&handle, &child_spec)
            .map_err(|e| anyhow!("sub-agent deploy failed: {e}"))?;
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
        sub_json = agent_report_json(&child_report, &child.caps);
        store.agents.retain(|a| a.agent != child_report.agent);
        store.agents.push(child_report);
    }
    store.save(state_dir)?;

    Ok(json!({
        "agent": parent_json,
        "subagent": sub_json,
        "verify_with": format!("dregg_agent_verify {{ id: '{id}' }}")
    }))
}

/// Render an agent run report (proof + bound) as JSON.
fn agent_report_json(report: &dreggnet_exec::agent::AgentRunReport, caps: &[String]) -> Value {
    let tip = report.tip().map(|h| hex32(&h));
    json!({
        "id": report.agent,
        "cap_bundle": caps,
        "admitted": report.admitted,
        "cap_refused": report.cap_refused,
        "budget_refused": report.budget_refused,
        "proof": {
            "receipts": report.receipts.len(),
            "tip": tip,
            "signer": hex32(&report.signer)
        },
        "bound": {
            "consumed": report.consumed,
            "budget": report.budget,
            "asset": report.asset,
            "headroom": report.headroom
        }
    })
}

/// `dregg_agent_verify` — re-witness a recorded agent run WITHOUT trusting the host:
/// re-verify the receipt chain (signed + unbroken) and that consumed stays under the
/// ceiling. Reuses the real `verify_agent_run`.
fn tool_agent_verify(state_dir: &Path, args: &Value) -> Result<Value> {
    let id = arg_str(args, "id")?;
    let store = Store::load(state_dir)?;
    let report = store
        .agents
        .iter()
        .find(|a| a.agent == id || a.agent.starts_with(&id))
        .ok_or_else(|| anyhow!("no agent run matching `{id}` (dregg_status to list agents)"))?;

    match verify_agent_run(report) {
        Ok(v) => Ok(json!({
            "verified": true,
            "agent": report.agent,
            "actions": v.actions,
            "consumed": v.consumed,
            "budget": v.budget,
            "headroom": v.headroom,
            "asset": report.asset,
            "signer": hex32(&report.signer),
            "summary": "receipt chain intact; consumed stays under the ceiling"
        })),
        Err(e) => Ok(json!({
            "verified": false,
            "agent": report.agent,
            "mismatch": e.to_string(),
            "summary": "agent run did not re-witness — the proof or the bound failed"
        })),
    }
}

/// `dregg_machines` — drive the live gateway's fly-compatible machines API directly
/// (requires an endpoint). Reuses the same `CloudClient` the CLI's `machines` verb uses.
fn tool_machines(state_dir: &Path, endpoint: Option<&str>, args: &Value) -> Result<Value> {
    let ep = endpoint.ok_or_else(|| {
        anyhow!("dregg_machines needs an `endpoint` (or run the server with --endpoint)")
    })?;
    let action = arg_str(args, "action")?;
    let app = arg_str(args, "app")?;
    let store = Store::load(state_dir)?;
    let client = CloudClient::new(ep, bearer_of(&store));

    match action.as_str() {
        "list" => match client.list_machines(&app)? {
            ListOutcome::Ok(machines) => Ok(json!({
                "endpoint": ep, "app": app,
                "machines": machines.iter().map(machine_json).collect::<Vec<_>>()
            })),
            ListOutcome::Refused { status, message } => Ok(json!({
                "refused": true, "status": status, "message": message
            })),
        },
        "create" => {
            let req = CreateMachineRequest {
                name: args
                    .get("name")
                    .and_then(|v| v.as_str())
                    .map(str::to_string),
                region: args
                    .get("region")
                    .and_then(|v| v.as_str())
                    .map(str::to_string),
                config: MachineConfig {
                    image: args
                        .get("image")
                        .and_then(|v| v.as_str())
                        .unwrap_or("")
                        .to_string(),
                    guest: GuestConfig {
                        cpu_kind: args
                            .get("cpu_kind")
                            .and_then(|v| v.as_str())
                            .unwrap_or("shared")
                            .to_string(),
                        cpus: args.get("cpus").and_then(|v| v.as_u64()).unwrap_or(1) as u32,
                        memory_mb: args
                            .get("memory_mb")
                            .and_then(|v| v.as_u64())
                            .unwrap_or(256) as u32,
                    },
                    env: std::collections::BTreeMap::new(),
                },
            };
            Ok(machine_outcome_json(
                client.create_machine(&app, &req)?,
                ep,
                &app,
                "create",
            ))
        }
        "get" => {
            let machine_id = arg_str(args, "id")?;
            Ok(machine_outcome_json(
                client.get_machine(&app, &machine_id)?,
                ep,
                &app,
                "get",
            ))
        }
        "stop" => {
            let machine_id = arg_str(args, "id")?;
            Ok(machine_outcome_json(
                client.stop_machine(&app, &machine_id)?,
                ep,
                &app,
                "stop",
            ))
        }
        "delete" => {
            let machine_id = arg_str(args, "id")?;
            let (ok, msg) = client.delete_machine(&app, &machine_id)?;
            Ok(json!({ "deleted": ok, "message": msg, "app": app, "id": machine_id }))
        }
        other => bail!("unknown machines action `{other}` (list|create|get|stop|delete)"),
    }
}

fn machine_json(m: &crate::cloud::Machine) -> Value {
    json!({
        "id": m.id, "name": m.name, "state": m.state, "region": m.region,
        "dregg": m.dregg.as_ref().map(|d| json!({
            "backend": d.backend, "node": d.node, "meter_units": d.meter_units,
            "outputs": d.outputs, "error": d.error
        }))
    })
}

fn machine_outcome_json(outcome: MachineOutcome, endpoint: &str, app: &str, verb: &str) -> Value {
    match outcome {
        MachineOutcome::Ok(m) => json!({
            "ok": true, "verb": verb, "endpoint": endpoint, "app": app, "machine": machine_json(&m)
        }),
        MachineOutcome::Refused { status, message } => json!({
            "ok": false, "verb": verb, "endpoint": endpoint, "app": app,
            "refused": true, "status": status, "message": message
        }),
    }
}

// ---------------------------------------------------------------------------
// Tool schemas
// ---------------------------------------------------------------------------

/// The MCP `tools/list` payload — every tool with a valid JSON-Schema `inputSchema`.
fn tool_specs() -> Vec<Value> {
    vec![
        json!({
            "name": "dregg_status",
            "description": "The verifiable cloud status: the connected cap-account plus every recorded cell (sites, leases, domains, workloads, agents). With an endpoint, points at the live machines API.",
            "inputSchema": obj_schema(json!({
                "endpoint": str_prop("Optional gateway URL to reflect the live cloud instead of the local notebook.")
            }), &[])
        }),
        json!({
            "name": "dregg_cell_read",
            "description": "Read one cloud cell by id or name — a site, agent, domain, workload, or lease — returning its full recorded state.",
            "inputSchema": obj_schema(json!({
                "name": str_prop("The cell id (a prefix is enough) or name (site name / agent id / domain).")
            }), &["name"])
        }),
        json!({
            "name": "dregg_login",
            "description": "Connect the cap-account: with no args, show the current account; with credential (a dga1_ token, optional root hex), bind a wallet identity; with new:true, mint a fresh local cap-account. The credential is presented as the bearer on every live call.",
            "inputSchema": obj_schema(json!({
                "credential": str_prop("A wallet-held dga1_ credential to bind as the account."),
                "root": str_prop("The verifying root public key (hex) the credential was minted under."),
                "new": bool_prop("Mint a fresh local cap-account (a new root + credential)."),
                "caps": arr_prop("Caps the minted credential grants (with new:true). Default: [deploy, domains]."),
                "show_credential": bool_prop("Reveal the (secret) credential in the result. Off by default.")
            }), &[])
        }),
        json!({
            "name": "dregg_deploy",
            "description": "Clone→build→publish a git repo as a signed, re-witnessable site cell. Local by default (the real DeployEngine over an in-process signed registry, leaving a bundle for dregg_verify); with an endpoint, provisions on the live gateway.",
            "inputSchema": obj_schema(json!({
                "repo": str_prop("The repo to deploy — a git URL, file:// path, or local path."),
                "name": str_prop("The subdomain label to publish under (<name>.example.com). Defaults to the repo basename."),
                "ref": str_prop("The git ref (branch/tag/commit) to pin. Defaults to the remote default branch."),
                "owner": str_prop("The publishing cap holder. Defaults to the logged-in account, else 'operator'."),
                "budget": int_prop("Deploy-lease budget in meter units (>=3; clone+build+publish each charge 1). Default 100."),
                "endpoint": str_prop("Gateway URL for a live deploy instead of the local in-process path.")
            }), &["repo"])
        }),
        json!({
            "name": "dregg_run",
            "description": "Run a metered WAT workload. Local: the real Scheduler/LocalProvider fulfills a funded lease as a durable workflow (a lease is auto-opened when omitted). The module must export a function named 'run'. With an endpoint, runs on the live gateway.",
            "inputSchema": obj_schema(json!({
                "source": str_prop("Inline WAT source text (the program to run)."),
                "source_path": str_prop("Path to a WAT source file (required for a live run; the gateway resolves the image)."),
                "lang": str_prop("Workload language. Only 'wat' is wired. Default 'wat'."),
                "lease": str_prop("An existing lease id. Omit (local) to auto-open a funded sandboxed lease."),
                "endpoint": str_prop("Gateway URL for a live run instead of the local control plane.")
            }), &[])
        }),
        json!({
            "name": "dregg_verify",
            "description": "Re-witness a deployed site WITHOUT trusting the host: re-check the served bytes against the committed content root and the signed receipt chain. With tamper:true, flips one byte to PROVE the check bites. The 'you verify, you don't trust' check.",
            "inputSchema": obj_schema(json!({
                "target": str_prop("The deploy id (a prefix is enough) or the site name to verify."),
                "url": str_prop("Fetch the receipt bundle from a running server over HTTP (e.g. 127.0.0.1:8080) instead of the local bundle."),
                "tamper": bool_prop("Self-demo: flip one served byte before re-witnessing; the verify must then report the tamper was caught.")
            }), &["target"])
        }),
        json!({
            "name": "dregg_agent_deploy",
            "description": "Deploy + run a budget-bounded, cap-confined, receipted agent against the self-contained mock-LLM plan (an admitted action, an out-of-bundle cap refusal, a budget-bound runaway). Returns the proof (receipt chain) + the bound (budget ceiling). Optionally also runs an attenuated sub-agent.",
            "inputSchema": obj_schema(json!({
                "id": str_prop("The agent id (meter subject + receipt identity). Defaults to a fresh id."),
                "budget": int_prop("The spend ceiling in budget units (>0). Default 50."),
                "cost": int_prop("The budget cost charged per action (>0). Default 1."),
                "services": arr_prop("Services the agent may invoke. Default [search, fetch]."),
                "cells": arr_prop("Cells the agent may read+write. Default [/scratch]."),
                "asset": str_prop("The asset the budget is denominated in. Default DREGG."),
                "subagent": bool_prop("Also deploy + run an attenuated sub-agent (half budget, first service only).")
            }), &[])
        }),
        json!({
            "name": "dregg_agent_verify",
            "description": "Re-witness a recorded agent run WITHOUT trusting the host: re-verify the receipt chain (signed + unbroken) and that consumed stays under the budget ceiling.",
            "inputSchema": obj_schema(json!({
                "id": str_prop("The agent id (a prefix is enough).")
            }), &["id"])
        }),
        json!({
            "name": "dregg_machines",
            "description": "Drive the live gateway's fly-compatible machines API directly (requires an endpoint): list/create/get/stop/delete machines on a remote DreggNet gateway — funded, metered, and receipted by the live node, cap-scoped by the account credential.",
            "inputSchema": obj_schema(json!({
                "action": str_prop("One of: list, create, get, stop, delete."),
                "app": str_prop("The app (tenant) the machine lives under."),
                "id": str_prop("The machine id (for get/stop/delete)."),
                "name": str_prop("An optional machine name (for create)."),
                "image": str_prop("The workload image/artifact reference (for create)."),
                "cpu_kind": str_prop("Guest CPU class: shared or performance (for create)."),
                "cpus": int_prop("Number of vCPUs (for create)."),
                "memory_mb": int_prop("Memory in MiB (for create)."),
                "region": str_prop("Region placement hint (for create)."),
                "endpoint": str_prop("Gateway URL (overrides the server's --endpoint).")
            }), &["action", "app"])
        }),
    ]
}

fn obj_schema(properties: Value, required: &[&str]) -> Value {
    json!({
        "type": "object",
        "properties": properties,
        "required": required,
        "additionalProperties": false
    })
}

fn str_prop(desc: &str) -> Value {
    json!({ "type": "string", "description": desc })
}
fn bool_prop(desc: &str) -> Value {
    json!({ "type": "boolean", "description": desc })
}
fn int_prop(desc: &str) -> Value {
    json!({ "type": "integer", "description": desc })
}
fn arr_prop(desc: &str) -> Value {
    json!({ "type": "array", "items": { "type": "string" }, "description": desc })
}

// ---------------------------------------------------------------------------
// Arg helpers
// ---------------------------------------------------------------------------

fn arg_str(args: &Value, key: &str) -> Result<String> {
    args.get(key)
        .and_then(|v| v.as_str())
        .map(str::to_string)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| anyhow!("missing required string argument `{key}`"))
}

fn str_list(args: &Value, key: &str) -> Option<Vec<String>> {
    let arr = args.get(key).and_then(|v| v.as_array())?;
    let list: Vec<String> = arr
        .iter()
        .filter_map(|v| v.as_str().map(str::to_string))
        .collect();
    if list.is_empty() { None } else { Some(list) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tool_specs_are_well_formed() {
        let specs = tool_specs();
        assert_eq!(specs.len(), 9, "the verifiable-cloud tool surface");
        for spec in &specs {
            let name = spec.get("name").and_then(|n| n.as_str()).expect("name");
            assert!(
                name.starts_with("dregg_"),
                "{name} should be dregg_-prefixed"
            );
            assert!(
                spec.get("description").and_then(|d| d.as_str()).is_some(),
                "{name} description"
            );
            let schema = spec.get("inputSchema").expect("inputSchema");
            assert_eq!(schema["type"], "object", "{name} schema is an object");
            assert!(schema.get("properties").is_some(), "{name} properties");
            assert!(schema.get("required").is_some(), "{name} required");
        }
    }

    #[test]
    fn initialize_echoes_protocol_version() {
        let resp = handle_initialize(json!(1), &json!({ "protocolVersion": "2024-11-05" }));
        assert_eq!(resp["result"]["protocolVersion"], "2024-11-05");
        assert_eq!(resp["result"]["serverInfo"]["name"], "dregg-cloud");
        assert!(resp["result"]["capabilities"]["tools"].is_object());
    }

    #[test]
    fn initialize_defaults_protocol_version() {
        let resp = handle_initialize(json!(1), &json!({}));
        assert_eq!(resp["result"]["protocolVersion"], DEFAULT_PROTOCOL_VERSION);
    }

    #[test]
    fn tool_text_result_wraps_content() {
        let r = tool_text_result(&json!({ "verified": true }), false);
        assert_eq!(r["isError"], false);
        assert_eq!(r["content"][0]["type"], "text");
        assert!(
            r["content"][0]["text"]
                .as_str()
                .unwrap()
                .contains("verified")
        );
    }
}
