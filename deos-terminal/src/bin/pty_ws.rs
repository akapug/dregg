//! `deos-terminal-pty-ws` — the PTY-over-WebSocket dev backend.
//!
//! A browser tab has no PTY, so the in-browser terminal grid drives a real shell
//! through this server. The server and its gate live in
//! [`deos_terminal::pty_server`]; this bin configures and runs it.
//!
//! Usage:  `deos-terminal-pty-ws [BIND_ADDR]`   (default `127.0.0.1:7717`)
//!
//! - `DEOS_TERMINAL_TOKEN` — the session token the launcher minted (≥ 32 visible
//!   ASCII chars). If unset, the server mints one and prints
//!   `DEOS_TERMINAL_TOKEN=<hex>` as its first stdout line for the launcher to
//!   read. Every client must present it (header or first frame) before a PTY is
//!   opened.
//! - `DEOS_TERMINAL_ALLOWED_ORIGINS` — comma-separated exact origins; default
//!   loopback `http(s)` origins only.
//! - `DEOS_TERMINAL_ALLOW_NON_LOOPBACK=1` — required to bind a non-loopback
//!   address.
//! - `DEOS_TERMINAL_SHELL` — the shell (else `$SHELL`, else `/bin/sh`).

#[cfg(target_arch = "wasm32")]
fn main() {}

#[cfg(not(target_arch = "wasm32"))]
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    use deos_terminal::pty_server::{self, ServerConfig, Spawn};

    let bind = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "127.0.0.1:7717".to_string());
    let (config, minted) = ServerConfig::from_env(Spawn::Shell)?;
    let listener = pty_server::bind(&bind, pty_server::non_loopback_allowed_from_env()).await?;
    let local = listener.local_addr()?;
    if minted {
        use std::io::Write as _;
        let mut out = std::io::stdout().lock();
        writeln!(out, "{}={}", pty_server::TOKEN_VAR, config.token.expose())?;
        out.flush()?;
    }
    log::info!("deos-terminal-pty-ws listening on ws://{local}");
    eprintln!("deos-terminal-pty-ws listening on ws://{local}");
    pty_server::serve(listener, config).await
}
