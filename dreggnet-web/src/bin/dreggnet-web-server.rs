//! # `dreggnet-web-server` — the public-demo server entrypoint.
//!
//! The ~15-line-core unblocker to a public demo at `demo.dregg.net`: it takes the merged
//! [`dreggnet_web::make_app`] app (the games + feature-surface catalog + the seeded no-cheat
//! Descent leaderboard) and SERVES it — binds a `TcpListener`, `axum::serve`s, and shuts down
//! gracefully on ctrl-c. A stranger opens the URL and plays the games + independently re-verifies
//! the leaderboard by replay — no node, no testnet, no 45-min prover.
//!
//! ## Configuration
//! - bind address: `--bind <addr>` flag, else `DREGGNET_WEB_BIND` env, else `127.0.0.1:8787`;
//! - persistence: `DATABASE_URL` env (a sqlite path / `sqlite:` url) makes the Descent leaderboard
//!   durable — submitted runs survive a restart, re-verified by replay on boot; unset → in-RAM;
//! - log level: the standard `RUST_LOG` env (`tracing_subscriber` env-filter), default `info`.
//!
//! ## Honest scope (the deploy scout's Phase-0)
//! DEMO-READY here: the standalone web server — the games, the do-once feature surfaces, and the
//! no-cheat-by-REPLAY Descent leaderboard + stranger-run verify + an HTTP run-ingest
//! (`POST /descent/submit`), all node-free (verification is in-process re-execution). The Descent
//! leaderboard is DURABLE over sqlite (`DATABASE_URL`), re-verified on boot. STILL EPHEMERAL: the
//! live game sessions (a restart drops in-progress sessions). NAMED (ops / ember-gated): a fronting
//! Caddy for TLS / rate-limit / CORS (external); the unsigned `dregg_user` cookie for identity
//! (auth). See [`dreggnet_web::make_app`].

use std::net::SocketAddr;

use dreggnet_web::make_app;
use tracing_subscriber::EnvFilter;

/// The bind address the demo server listens on when nothing else is configured.
const DEFAULT_BIND: &str = "127.0.0.1:8787";

#[tokio::main]
async fn main() {
    // Structured logging — `RUST_LOG` selects the level (default `info`).
    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info")),
        )
        .init();

    let bind = resolve_bind();
    let addr: SocketAddr = match bind.parse() {
        Ok(a) => a,
        Err(e) => {
            tracing::error!(%bind, error = %e, "invalid bind address");
            std::process::exit(2);
        }
    };

    // The merged public-demo app: games + feature surfaces + the seeded no-cheat leaderboard.
    let app = make_app();

    let listener = match tokio::net::TcpListener::bind(addr).await {
        Ok(l) => l,
        Err(e) => {
            tracing::error!(%addr, error = %e, "failed to bind — is the port in use?");
            std::process::exit(1);
        }
    };

    tracing::info!(
        %addr,
        "DreggNet Cloud demo server up — GET / (landing) · /offerings (catalog) · \
         /descent/leaderboard (no-cheat board) · /health"
    );

    if let Err(e) = axum::serve(listener, app)
        .with_graceful_shutdown(shutdown_signal())
        .await
    {
        tracing::error!(error = %e, "server error");
        std::process::exit(1);
    }
    tracing::info!("server shut down gracefully");
}

/// Resolve the bind address: `--bind <addr>` flag > `DREGGNET_WEB_BIND` env > [`DEFAULT_BIND`].
fn resolve_bind() -> String {
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--bind" => {
                if let Some(v) = args.next() {
                    return v;
                }
            }
            other => {
                if let Some(v) = other.strip_prefix("--bind=") {
                    return v.to_string();
                }
            }
        }
    }
    std::env::var("DREGGNET_WEB_BIND").unwrap_or_else(|_| DEFAULT_BIND.to_string())
}

/// Complete on ctrl-c — hands `axum::serve` its graceful-shutdown trigger.
async fn shutdown_signal() {
    let _ = tokio::signal::ctrl_c().await;
    tracing::info!("received ctrl-c — shutting down");
}
