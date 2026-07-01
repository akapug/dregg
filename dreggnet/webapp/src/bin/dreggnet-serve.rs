//! `dreggnet-serve` — serve an agent-assembled [`WebApp`] over real HTTP.
//!
//! A portable (std `TcpListener`, cross-platform) serving binary: it binds a
//! listener and serves a [`WebApp`]'s routes over a small HTTP/1.1 loop, routing
//! each inbound request to its polyana handler via
//! [`dreggnet_webapp::Router`]. This is the any-host realization of "the gateway
//! routes inbound HTTP to a leased polyana workload" — the Linux-only `httpe`
//! gateway adopts the same `Router`.
//!
//! ```sh
//! dreggnet-serve --port 8787
//! # the agent's assembled demo app is served:
//! curl -s localhost:8787/hello
//! curl -s 'localhost:8787/add?a=40&b=2'   # -> {"result":42}, computed in the sandbox
//! ```
//!
//! With `--lease-budget N`, the app is served through a [`LeasedRouter`] metered
//! against a funded dregg execution-lease of `N` units (1 unit/request); once the
//! budget is spent, further requests get `402 Payment Required` — no unpaid work.
//!
//! [`WebApp`]: dreggnet_webapp::WebApp
//! [`LeasedRouter`]: dreggnet_webapp::LeasedRouter

use std::sync::Arc;

use dreggnet_bridge::{CapGrade, Lease};
use dreggnet_webapp::{LeasedRouter, Router, ServeRequest, WebRequest, WebResponse, serve_http};

/// Either an unmetered router or a lease-metered one.
enum Serving {
    Plain(Router),
    Leased(LeasedRouter),
}

impl Serving {
    fn serve(&self, req: &WebRequest) -> WebResponse {
        match self {
            Serving::Plain(r) => r.serve(req),
            Serving::Leased(r) => {
                let (resp, meter) = r.serve(req);
                eprintln!(
                    "dreggnet-serve: metered {} {} -> {} (lease {}/{} units, {} reqs)",
                    req.method, req.path, resp.status, meter.charged, meter.budget, meter.requests
                );
                resp
            }
        }
    }
}

fn main() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let (bind, lease_budget) = parse_args(&args);

    // The agent's assembled app (the demo: /hello + /add). A real deployment
    // loads the WebApp the agent declared (JSON), here we serve the builtin demo.
    let app = dreggnet_webapp::assemble::demo_app("dreggnet-serve");

    let serving = match lease_budget {
        Some(budget) => {
            let lease = Lease::funded(
                "dreggnet-serve",
                CapGrade::Sandboxed,
                "dreggnet/serve-demo",
                budget,
                1,
            );
            match LeasedRouter::new(app, lease) {
                Ok(r) => Serving::Leased(r),
                Err(e) => {
                    eprintln!("dreggnet-serve: lease refused: {e}");
                    std::process::exit(1);
                }
            }
        }
        None => Serving::Plain(Router::new(app)),
    };
    let serving = Arc::new(serving);

    eprintln!("dreggnet-serve: serving an agent-assembled web app on http://{bind}");
    for route in &serving_app(&serving).routes {
        eprintln!("  {} {}", route.method, route.path);
    }
    eprintln!("  try: curl -s 'http://{bind}/add?a=40&b=2'");
    if lease_budget.is_some() {
        eprintln!("  (metered: {} units, 1/request)", lease_budget.unwrap());
    }

    // The shared portable serving loop (`webapp/src/serve.rs`, also driving the
    // static `dreggnet-host` path) — this dynamic front-end just supplies the
    // per-request handler, routing the parsed request through the polyana `Router`.
    serve_http(&bind, move |req: &ServeRequest| {
        serving.serve(&WebRequest::new(req.method, &req.target, req.body.clone()))
    })
}

fn serving_app(s: &Serving) -> &dreggnet_webapp::WebApp {
    match s {
        Serving::Plain(r) => r.app(),
        Serving::Leased(r) => r.app(),
    }
}

/// Parse `--port`/`-p` (default 8787), `--bind`/`-b` host (default `0.0.0.0`),
/// and optional `--lease-budget N`.
fn parse_args(args: &[String]) -> (String, Option<i64>) {
    let mut port: u16 = 8787;
    let mut host = String::from("0.0.0.0");
    let mut lease_budget: Option<i64> = None;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--port" | "-p" => {
                if let Some(v) = args.get(i + 1).and_then(|s| s.parse().ok()) {
                    port = v;
                }
                i += 2;
            }
            "--bind" | "-b" => {
                if let Some(v) = args.get(i + 1) {
                    host = v.clone();
                }
                i += 2;
            }
            "--lease-budget" => {
                lease_budget = args.get(i + 1).and_then(|s| s.parse().ok());
                i += 2;
            }
            _ => i += 1,
        }
    }
    (format!("{host}:{port}"), lease_budget)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_args_defaults_and_overrides() {
        assert_eq!(
            parse_args(&["x".into()]),
            ("0.0.0.0:8787".to_string(), None)
        );
        assert_eq!(
            parse_args(&[
                "x".into(),
                "--port".into(),
                "9000".into(),
                "--lease-budget".into(),
                "5".into()
            ]),
            ("0.0.0.0:9000".to_string(), Some(5))
        );
    }
}
