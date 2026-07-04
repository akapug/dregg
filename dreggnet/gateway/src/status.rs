//! The friendly gateway root: a landing page + status JSON + liveness.
//!
//! Where the `/v1/apps/...` surface is the fly-machines control plane, this module
//! is the *front door a human (or a probe) sees* when they hit the gateway root.
//! A bare `GET /` used to fall through to the fly-shaped `{"error":"machine not
//! found"}` 404; instead it now answers with a small status page:
//!
//! - `GET /` → an HTML landing page ("DreggNet gateway — alive, N machines,
//!   federation healthy, see portal.example.com");
//! - `GET /status` (or `/v1`) → the same status as JSON;
//! - `GET /healthz` (or `/health`) → a minimal liveness JSON.
//!
//! The status is assembled from the live gateway (machine count, the configured
//! compute backend) plus a [`GatewayInfo`] (the name / portal pointer / the dregg
//! node health URL). The federation health is a best-effort, short-timeout probe of
//! the node's health endpoint — it never fails the page.

use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::Duration;

use serde::Serialize;

use crate::gateway::MachineGateway;

/// Static, operator-set facts about this gateway deployment — the bits the live
/// gateway state doesn't carry. Defaults are sensible for the live edge.
#[derive(Debug, Clone)]
pub struct GatewayInfo {
    /// The human name shown on the landing page.
    pub name: String,
    /// The public visual portal to point people at.
    pub portal_url: String,
    /// The machines-API base path (the fly surface).
    pub api_base: String,
    /// The dregg node's health endpoint to probe for federation health, if any
    /// (e.g. `http://dregg-node:8420/health`). `None` → federation health unknown.
    pub node_health_url: Option<String>,
    /// How long to wait on the node health probe before giving up.
    pub health_timeout: Duration,
}

impl Default for GatewayInfo {
    fn default() -> Self {
        GatewayInfo {
            name: "DreggNet gateway".to_string(),
            portal_url: "https://portal.example.com".to_string(),
            api_base: "/v1/apps/{app}/machines".to_string(),
            node_health_url: None,
            health_timeout: Duration::from_millis(800),
        }
    }
}

/// How a machine's workload is run.
#[derive(Debug, Clone, Serialize)]
pub struct ComputeStatus {
    /// Whether a created machine's workload is dispatched to a remote compute node.
    pub dispatch: bool,
    /// The mesh backend (`"tailscale"` / `"stub"`), or `"local"` for in-process.
    pub backend: String,
    /// The compute node target (e.g. `"100.64.0.2:8021"`), when dispatching.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub node: Option<String>,
}

/// The federation/node health, as observed by a best-effort probe.
#[derive(Debug, Clone, Serialize)]
pub struct FederationStatus {
    /// `"healthy"` (node answered 2xx) / `"reachable"` (answered, non-2xx) /
    /// `"unreachable"` (could not connect) / `"unknown"` (no health URL configured).
    pub health: String,
    /// The health endpoint that was probed, if configured.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub node: Option<String>,
}

/// The assembled gateway status — the body of `GET /status` and the source of the
/// landing page.
#[derive(Debug, Clone, Serialize)]
pub struct GatewayStatus {
    /// The gateway name.
    pub service: String,
    /// `"alive"` — the gateway is serving.
    pub status: String,
    /// The number of machine records the gateway holds.
    pub machines: usize,
    /// Where created-machine workloads run.
    pub compute: ComputeStatus,
    /// The federation/node health.
    pub federation: FederationStatus,
    /// The public visual portal.
    pub portal: String,
    /// The machines-API base path.
    pub api_base: String,
}

impl GatewayStatus {
    /// Assemble the live status from the gateway + the operator info. This probes
    /// the node health endpoint (best-effort, short timeout).
    pub fn assemble(gateway: &MachineGateway, info: &GatewayInfo) -> GatewayStatus {
        let compute = match gateway.compute() {
            Some(backend) => ComputeStatus {
                dispatch: true,
                backend: backend.backend().to_string(),
                node: Some(backend.target()),
            },
            None => ComputeStatus {
                dispatch: false,
                backend: "local".to_string(),
                node: None,
            },
        };

        let federation = match &info.node_health_url {
            Some(url) => FederationStatus {
                health: probe_health(url, info.health_timeout).to_string(),
                node: Some(url.clone()),
            },
            None => FederationStatus {
                health: "unknown".to_string(),
                node: None,
            },
        };

        GatewayStatus {
            service: info.name.clone(),
            status: "alive".to_string(),
            machines: gateway.count(),
            compute,
            federation,
            portal: info.portal_url.clone(),
            api_base: info.api_base.clone(),
        }
    }

    /// A one-line human summary (the headline of the landing page).
    pub fn headline(&self) -> String {
        format!(
            "{} — alive, {} machine{}, federation {}",
            self.service,
            self.machines,
            if self.machines == 1 { "" } else { "s" },
            self.federation.health,
        )
    }

    /// Render the landing page as a small self-contained HTML document.
    pub fn render_html(&self) -> String {
        let dispatch_line = if self.compute.dispatch {
            format!(
                "dispatches workloads to <code>{}</code> over the <code>{}</code> overlay",
                esc(self.compute.node.as_deref().unwrap_or("")),
                esc(&self.compute.backend),
            )
        } else {
            "runs workloads in-process (single-box / dev mode)".to_string()
        };
        format!(
            "<!doctype html>\n\
<html lang=\"en\"><head><meta charset=\"utf-8\">\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\
<title>{title}</title>\
<style>\
body{{font:16px/1.6 -apple-system,system-ui,sans-serif;max-width:42rem;margin:4rem auto;padding:0 1.25rem;color:#1a1a1a;background:#fafafa}}\
h1{{font-size:1.4rem;margin:0 0 .25rem}}\
.dot{{color:#1a8a3a}}\
code{{background:#eee;padding:.1rem .35rem;border-radius:.25rem}}\
ul{{padding-left:1.1rem}} a{{color:#2456c8}}\
.muted{{color:#666;font-size:.9rem}}\
</style></head><body>\
<h1><span class=\"dot\">●</span> {title}</h1>\
<p>{headline}.</p>\
<ul>\
<li><strong>{machines}</strong> machine{plural} known to this gateway</li>\
<li>Compute: {dispatch_line}</li>\
<li>Federation: <strong>{fed}</strong>{fed_node}</li>\
<li>API base: <code>{api}</code> (fly-compatible machines API)</li>\
</ul>\
<p>Visual portal: <a href=\"{portal}\">{portal}</a></p>\
<p class=\"muted\">A <code>POST {api}</code> creates a machine: the gateway maps it to a funded \
dregg execution-lease and {dispatch_verb} a real durable metered workload.</p>\
</body></html>\n",
            title = esc(&self.service),
            headline = esc(&self.headline()),
            machines = self.machines,
            plural = if self.machines == 1 { "" } else { "s" },
            dispatch_line = dispatch_line,
            fed = esc(&self.federation.health),
            fed_node = self
                .federation
                .node
                .as_deref()
                .map(|n| format!(" (<code>{}</code>)", esc(n)))
                .unwrap_or_default(),
            api = esc(&self.api_base),
            portal = esc(&self.portal),
            dispatch_verb = if self.compute.dispatch {
                "dispatches it to a compute node to run"
            } else {
                "runs it in-process"
            },
        )
    }
}

/// The result of a node health probe.
enum Health {
    Healthy,
    Reachable,
    Unreachable,
}

impl Health {
    fn to_string(&self) -> String {
        match self {
            Health::Healthy => "healthy",
            Health::Reachable => "reachable",
            Health::Unreachable => "unreachable",
        }
        .to_string()
    }
}

/// Best-effort liveness probe of a node `http://host:port/path` health URL: a
/// blocking `GET` with `timeout`. A 2xx → healthy; a connection that answers
/// non-2xx → reachable; a failure to connect/read → unreachable. Never panics.
fn probe_health(url: &str, timeout: Duration) -> Health {
    let Some((host, port, path)) = parse_http_url(url) else {
        return Health::Unreachable;
    };
    let Ok(mut addrs) = (host.as_str(), port).to_socket_addrs() else {
        return Health::Unreachable;
    };
    let Some(addr) = addrs.next() else {
        return Health::Unreachable;
    };
    let Ok(mut stream) = TcpStream::connect_timeout(&addr, timeout) else {
        return Health::Unreachable;
    };
    let _ = stream.set_read_timeout(Some(timeout));
    let _ = stream.set_write_timeout(Some(timeout));
    let req =
        format!("GET {path} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\nAccept: */*\r\n\r\n");
    if stream.write_all(req.as_bytes()).is_err() {
        return Health::Reachable; // connected but the write faulted
    }
    let mut buf = [0u8; 256];
    match stream.read(&mut buf) {
        Ok(n) if n > 0 => {
            // Status line: `HTTP/1.1 200 OK`.
            let line = String::from_utf8_lossy(&buf[..n]);
            let code = line
                .split_whitespace()
                .nth(1)
                .and_then(|c| c.parse::<u16>().ok());
            match code {
                Some(c) if (200..300).contains(&c) => Health::Healthy,
                _ => Health::Reachable,
            }
        }
        // Connected (TCP) but no HTTP body — still a live socket.
        _ => Health::Reachable,
    }
}

/// Split `http://host[:port][/path]` into `(host, port, path)`. Only plain `http`
/// is supported (the gateway probes its compose-internal node); `https` and other
/// schemes return `None`. Defaults: port 80, path `/`.
fn parse_http_url(url: &str) -> Option<(String, u16, String)> {
    let rest = url.strip_prefix("http://")?;
    let (authority, path) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i..]),
        None => (rest, "/"),
    };
    let (host, port) = match authority.rsplit_once(':') {
        Some((h, p)) => (h.to_string(), p.parse().ok()?),
        None => (authority.to_string(), 80),
    };
    if host.is_empty() {
        return None;
    }
    Some((host, port, path.to_string()))
}

/// Minimal HTML escaping for the few interpolated strings (names / URLs / targets).
fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_url_variants() {
        assert_eq!(
            parse_http_url("http://dregg-node:8420/health"),
            Some(("dregg-node".into(), 8420, "/health".into()))
        );
        assert_eq!(
            parse_http_url("http://host"),
            Some(("host".into(), 80, "/".into()))
        );
        assert_eq!(parse_http_url("https://x/health"), None);
        assert_eq!(parse_http_url("not a url"), None);
    }

    #[test]
    fn status_of_a_plain_gateway_is_alive_local_unknown() {
        let gw = MachineGateway::new();
        let status = GatewayStatus::assemble(&gw, &GatewayInfo::default());
        assert_eq!(status.status, "alive");
        assert_eq!(status.machines, 0);
        assert!(!status.compute.dispatch);
        assert_eq!(status.federation.health, "unknown");
        // The HTML page mentions the portal + the headline.
        let html = status.render_html();
        assert!(html.contains("portal.example.com"));
        assert!(html.contains("DreggNet gateway"));
        assert!(html.contains("alive"));
    }

    #[test]
    fn unreachable_node_health_is_reported_not_fatal() {
        let info = GatewayInfo {
            // A port that nothing is listening on → unreachable, but the page renders.
            node_health_url: Some("http://127.0.0.1:1/health".into()),
            health_timeout: Duration::from_millis(150),
            ..GatewayInfo::default()
        };
        let status = GatewayStatus::assemble(&MachineGateway::new(), &info);
        assert_eq!(status.federation.health, "unreachable");
    }
}
