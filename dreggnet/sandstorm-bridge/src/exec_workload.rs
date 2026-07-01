//! **A grain workload, welded onto the real `dreggnet-exec` compute tier.**
//!
//! The prototype's [`crate::bridge::GrainWorkload`] runs in-process (the [`NotesApp`]
//! stub). The **deployed** path runs a grain's request handler through the *real*
//! DreggNet compute tier — [`dreggnet_exec::run_workload_with_input`] — at the grain's
//! demanded [`SandboxTier`], mapped to the real [`dreggnet_exec::CapTier`]:
//!
//! - [`SandboxTier::Caged`] → [`CapTier::Caged`]: a real OS-sandboxed native process
//!   (seccomp-bpf + Landlock on Linux). An http-bridge app routes here.
//! - [`SandboxTier::MicroVm`] → [`CapTier::MicroVm`]: a per-grain Firecracker microVM
//!   behind the KVM boundary (refuses cleanly where `/dev/kvm`/firecracker are absent
//!   — never a silent downgrade).
//!
//! and **never weaker** — the `dreggnet-exec` `check_floor` rule is the production
//! backstop, so a grain can never be silently run below the isolation Sandstorm
//! assumes.
//!
//! The grain's request handler is run as a real workload: the bridged request (method,
//! path, body, the cap-derived `X-Sandstorm-Permissions`) and the grain's `/var` (the
//! cell umem heap) are marshalled in as the workload's input, and the workload returns
//! the HTTP response plus the new `/var`. [`ExecGrainWorkload`] carries a
//! representative permissioned-notes handler (the Etherpad/Davros shape) **as the
//! in-sandbox app**, so the catalog-app contract (verbs · permission gating ·
//! persistence) runs end-to-end through the real tier. Executing an *arbitrary
//! untrusted `.spk` chroot* on the live tier is the REVIEWED-GO devnet step (the
//! Firecracker microVM + the SBX deny-default make it the safe path); this module is
//! the real-tier dispatch path that step plugs into.

use std::sync::Mutex;

use dreggnet_exec::{run_workload_with_input, CapTier, ExecError, Input};
use serde_json::json;

use crate::bridge::{BridgedRequest, GrainWorkload, HttpResponse, Method};
use crate::cell::Umem;
use crate::grain::SandboxTier;

/// Map a grain's demanded [`SandboxTier`] onto the real [`CapTier`]. A grain never
/// maps below `Caged` — the wasm tiers are deliberately unreachable (they would be a
/// silent isolation downgrade below what the Sandstorm supervisor assumes).
pub fn cap_tier_for(tier: SandboxTier) -> CapTier {
    match tier {
        SandboxTier::Caged => CapTier::Caged,
        SandboxTier::MicroVm => CapTier::MicroVm,
    }
}

/// The language the in-sandbox handler runs as. The representative handler is Python
/// (the native CPython tier — `dreggnet-exec`'s default-on `python` feature), a real
/// `python3` subprocess speaking the polyana newline-JSON wire. A real catalog grain
/// runs whatever its `.spk` chroot `continueCommand` launches (the reviewed-go step).
const HANDLER_LANG: &str = "python";

/// A representative permissioned-notes http-bridge app, **as a real workload**. It is
/// the same contract as [`crate::bridge::NotesApp`] (read needs `view`, write needs
/// `edit`, state persists in `/var`), but it runs as a genuine `python3` subprocess
/// through the real `dreggnet-exec` tier rather than in-process. It reads one request
/// envelope `{grain request + permissions + /var}` from the polyana wire and returns
/// `{status, body, var}`.
const NOTES_HANDLER_PY: &str = r#"import sys, json

def handle(env):
    method = env["method"]
    path = env["path"]
    perms = set(env.get("permissions", []))
    var = dict(env.get("var", {}))
    key = "notes" + path
    if method == "GET":
        if "view" not in perms:
            return {"status": 403, "body": "forbidden", "var": var}
        if key in var:
            return {"status": 200, "body": var[key], "var": var}
        return {"status": 404, "body": "not found", "var": var}
    if method in ("POST", "PUT"):
        if "edit" not in perms:
            return {"status": 403, "body": "forbidden", "var": var}
        var[key] = env.get("body", "")
        return {"status": 200, "body": "stored", "var": var}
    if method == "DELETE":
        if "edit" not in perms:
            return {"status": 403, "body": "forbidden", "var": var}
        existed = key in var
        var.pop(key, None)
        return {"status": 200, "body": ("deleted" if existed else "absent"), "var": var}
    return {"status": 405, "body": "method not allowed", "var": var}

for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    req = json.loads(line)
    args = req.get("args", [])
    env = args[0] if args else {}
    out = handle(env)
    print(json.dumps({"ok": [json.dumps(out)]}), flush=True)
"#;

/// The result of running a grain request through the real tier: the HTTP response and
/// the enforcement level the tier actually achieved (surfaced, never hidden — a
/// downgrade is loud).
#[derive(Clone, Debug)]
pub struct GrainRun {
    pub response: HttpResponse,
    /// The polyana `EnforcementLevel` the run achieved (`"OsSandbox"` on a Linux
    /// Caged host, `"Container"` on a KVM MicroVm host, `"None"` where the OS cannot
    /// cage — surfaced so the operator sees the real posture).
    pub enforcement: String,
}

/// A grain workload backed by the **real** `dreggnet-exec` compute tier. Implements
/// [`GrainWorkload`] so it drops straight into [`crate::bridge::HttpBridge::serve`],
/// and additionally exposes [`run`](Self::run) for the surfaced enforcement level.
pub struct ExecGrainWorkload {
    tier: CapTier,
    handler_lang: String,
    handler_src: String,
    last_enforcement: Mutex<Option<String>>,
}

impl ExecGrainWorkload {
    /// A grain workload at the given sandbox tier running the representative notes
    /// handler. A real catalog grain swaps `handler_src` for its `.spk` chroot
    /// entrypoint (the reviewed-go untrusted-code step).
    pub fn notes(tier: SandboxTier) -> Self {
        ExecGrainWorkload {
            tier: cap_tier_for(tier),
            handler_lang: HANDLER_LANG.to_string(),
            handler_src: NOTES_HANDLER_PY.to_string(),
            last_enforcement: Mutex::new(None),
        }
    }

    /// A grain workload running a caller-supplied handler program at `tier`.
    pub fn with_handler(
        tier: SandboxTier,
        lang: impl Into<String>,
        src: impl Into<String>,
    ) -> Self {
        ExecGrainWorkload {
            tier: cap_tier_for(tier),
            handler_lang: lang.into(),
            handler_src: src.into(),
            last_enforcement: Mutex::new(None),
        }
    }

    /// The enforcement level the most recent [`run`](Self::run) / serve achieved.
    pub fn last_enforcement(&self) -> Option<String> {
        self.last_enforcement.lock().unwrap().clone()
    }

    /// Run one grain request through the real `dreggnet-exec` tier. Marshals the
    /// request + `/var` into the workload input, runs it at the grain's [`CapTier`],
    /// applies the returned `/var` back into the cell umem, and surfaces the
    /// enforcement level. A tier that cannot run the grain (no `python3`; or a MicroVm
    /// host with no KVM) returns a `503` with the refusal surfaced — fail-closed,
    /// never a silent unsandboxed run.
    pub fn run(&self, req: &BridgedRequest, var: &mut Umem) -> GrainRun {
        let envelope = json!({
            "method": method_str(req.method),
            "path": req.path,
            "body": String::from_utf8_lossy(&req.body),
            "permissions": req.permissions(),
            "var": var_to_json(var),
        });

        match run_workload_with_input(
            &self.handler_lang,
            &self.handler_src,
            self.tier,
            &[Input::Json(envelope)],
        ) {
            Ok(out) => {
                *self.last_enforcement.lock().unwrap() = Some(out.enforcement.clone());
                match out.values.first().and_then(|v| parse_handler_output(v)) {
                    Some((status, body, new_var)) => {
                        apply_var(var, new_var);
                        GrainRun {
                            response: HttpResponse {
                                status,
                                body: body.into_bytes(),
                            },
                            enforcement: out.enforcement,
                        }
                    }
                    None => GrainRun {
                        response: HttpResponse {
                            status: 502,
                            body: b"grain handler produced no parseable response".to_vec(),
                        },
                        enforcement: out.enforcement,
                    },
                }
            }
            Err(e) => {
                let reason = exec_refusal(&e);
                *self.last_enforcement.lock().unwrap() = Some("refused".to_string());
                GrainRun {
                    response: HttpResponse {
                        status: 503,
                        body: format!("grain tier refused: {reason}").into_bytes(),
                    },
                    enforcement: "refused".to_string(),
                }
            }
        }
    }
}

impl GrainWorkload for ExecGrainWorkload {
    fn serve(&self, req: &BridgedRequest, var: &mut Umem) -> HttpResponse {
        self.run(req, var).response
    }
}

fn method_str(m: Method) -> &'static str {
    match m {
        Method::Get => "GET",
        Method::Post => "POST",
        Method::Put => "PUT",
        Method::Delete => "DELETE",
    }
}

/// The grain `/var` as a JSON object of `key -> utf8-string` for the handler. The
/// representative notes app stores text; a real grain's `/var` carries arbitrary
/// bytes (production marshals binary values as base64 — the same envelope shape).
fn var_to_json(var: &Umem) -> serde_json::Value {
    let mut map = serde_json::Map::new();
    for (k, v) in var.iter() {
        map.insert(k.to_string(), json!(String::from_utf8_lossy(v).to_string()));
    }
    serde_json::Value::Object(map)
}

/// Apply the handler's returned `/var` back into the cell umem, replacing it (the
/// handler owns its `/var` for the request). The committed `data_root` then reflects
/// exactly what the workload wrote — the witnessed state change.
fn apply_var(var: &mut Umem, new_var: serde_json::Map<String, serde_json::Value>) {
    var.clear();
    for (k, v) in new_var {
        if let Some(s) = v.as_str() {
            var.put(k, s.as_bytes().to_vec());
        }
    }
}

fn parse_handler_output(
    s: &str,
) -> Option<(u16, String, serde_json::Map<String, serde_json::Value>)> {
    let v: serde_json::Value = serde_json::from_str(s).ok()?;
    let status = v.get("status")?.as_u64()? as u16;
    let body = v.get("body")?.as_str()?.to_string();
    let var = v
        .get("var")
        .and_then(|x| x.as_object())
        .cloned()
        .unwrap_or_default();
    Some((status, body, var))
}

fn exec_refusal(e: &ExecError) -> String {
    e.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bridge::BridgedRequest;
    use std::collections::BTreeMap;

    fn python3_available() -> bool {
        std::process::Command::new("python3")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    fn bridged(method: Method, path: &str, body: &[u8], perms: &[&str]) -> BridgedRequest {
        let mut headers = BTreeMap::new();
        headers.insert("X-Sandstorm-Permissions".to_string(), perms.join(","));
        BridgedRequest {
            method,
            path: path.to_string(),
            body: body.to_vec(),
            headers,
        }
    }

    #[test]
    fn the_grain_tier_maps_never_weaker_than_caged() {
        assert_eq!(cap_tier_for(SandboxTier::Caged), CapTier::Caged);
        assert_eq!(cap_tier_for(SandboxTier::MicroVm), CapTier::MicroVm);
        // The mapping has no wasm route — a grain cannot be silently downgraded.
    }

    #[test]
    fn a_grain_request_runs_through_the_real_exec_tier() {
        if !python3_available() {
            eprintln!("skip: no python3 on PATH");
            return;
        }
        let w = ExecGrainWorkload::notes(SandboxTier::Caged);
        let mut var = Umem::new();
        // An editor writes a note — runs as a real python3 workload at CapTier::Caged.
        let post = w.run(
            &bridged(Method::Post, "/welcome", b"hello dregg", &["view", "edit"]),
            &mut var,
        );
        assert_eq!(post.response.status, 200);
        // The enforcement level is surfaced (OsSandbox on Linux, None where the OS
        // cannot cage — never hidden).
        assert!(!post.enforcement.is_empty());
        // The write persisted into the cell umem.
        let get = w.run(&bridged(Method::Get, "/welcome", b"", &["view"]), &mut var);
        assert_eq!(get.response.status, 200);
        assert_eq!(get.response.body, b"hello dregg");
    }

    #[test]
    fn the_real_tier_enforces_the_cap_derived_permissions() {
        if !python3_available() {
            eprintln!("skip: no python3 on PATH");
            return;
        }
        let w = ExecGrainWorkload::notes(SandboxTier::Caged);
        let mut var = Umem::new();
        // A viewer (no `edit`) cannot write — the real workload reads the permission
        // header and refuses.
        let r = w.run(&bridged(Method::Post, "/x", b"nope", &["view"]), &mut var);
        assert_eq!(r.response.status, 403);
        assert!(var.is_empty());
    }
}
