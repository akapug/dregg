//! The PTY-over-WebSocket server: one gated WS listener, one PTY per
//! authenticated connection.
//!
//! A browser tab has no PTY, so the in-browser terminal grid drives a real shell
//! through this server. The wire (see [`crate::transport`]):
//!
//! - PTY output bytes  → **binary** WS frames
//! - client **binary** frames → PTY stdin
//! - client **text** frames → a JSON [`WireMsg`] control message (resize)
//! - child exit → a `WireMsg::Exit` text frame, then close
//!
//! ## The gate — nothing is spawned for a connection that has not passed it
//!
//! Browsers do not apply the same-origin policy to WebSocket connects, so any
//! page open on the machine can dial a loopback listener. A shell is therefore
//! behind three checks, all before `openpty`:
//!
//! 1. **Bind.** [`bind`] refuses a non-loopback address unless the operator
//!    passed `allow_non_loopback` (`DEOS_TERMINAL_ALLOW_NON_LOOPBACK=1` for the
//!    bins). Both the resolved addresses and the bound socket are checked.
//! 2. **Origin.** The handshake callback rejects (HTTP 403) any `Origin` the
//!    [`OriginPolicy`] does not admit. The default admits only loopback
//!    `http(s)` origins (`localhost`, `127.0.0.1`, `[::1]`, any port);
//!    `DEOS_TERMINAL_ALLOWED_ORIGINS` replaces it with an exact list. A request
//!    with no `Origin` header is not from a browser page and passes this check —
//!    it still needs the token.
//! 3. **Token.** A per-server [`SessionToken`] the launcher mints (or the server
//!    mints and prints for its launcher). The client presents it either as an
//!    `Authorization: Bearer <token>` request header (checked in the handshake;
//!    a wrong one is HTTP 401) or — because a browser `WebSocket` cannot set
//!    headers — as its FIRST frame, a [`WireMsg::Auth`] text frame, within
//!    [`AUTH_TIMEOUT`]. Anything else as the first frame, or nothing, closes the
//!    socket with a policy-violation close frame. Only then is a PTY opened.
//!
//! The shell's environment is [`crate::shell_env::minimal_shell_env`], applied
//! after `env_clear` — not this server's environment, which holds the token.

use std::io::{Read, Write};
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;

use anyhow::Context as _;
use futures_util::{SinkExt, StreamExt};
use portable_pty::{CommandBuilder, NativePtySystem, PtySize, PtySystem};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::mpsc;
use tokio_tungstenite::tungstenite::handshake::server::{ErrorResponse, Request, Response};
use tokio_tungstenite::tungstenite::http::{header, StatusCode};
use tokio_tungstenite::tungstenite::protocol::frame::coding::CloseCode;
use tokio_tungstenite::tungstenite::protocol::CloseFrame;
use tokio_tungstenite::tungstenite::Message;

use crate::transport::WireMsg;

/// How long a connection that did not authenticate in its handshake has to send
/// its [`WireMsg::Auth`] frame.
pub const AUTH_TIMEOUT: Duration = Duration::from_secs(10);

/// The launcher-minted token, read by the bins.
pub const TOKEN_VAR: &str = "DEOS_TERMINAL_TOKEN";
/// Comma-separated exact origins replacing the loopback default.
pub const ALLOWED_ORIGINS_VAR: &str = "DEOS_TERMINAL_ALLOWED_ORIGINS";
/// `1` to permit binding a non-loopback address.
pub const ALLOW_NON_LOOPBACK_VAR: &str = "DEOS_TERMINAL_ALLOW_NON_LOOPBACK";

/// The shortest launcher-supplied token accepted (hex chars ⇒ 128 bits).
pub const MIN_TOKEN_LEN: usize = 32;

/// The per-server session token. `Debug` is redacted; comparison is
/// constant-time in the token's length.
#[derive(Clone)]
pub struct SessionToken(String);

impl std::fmt::Debug for SessionToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("SessionToken(<redacted>)")
    }
}

impl SessionToken {
    /// 32 bytes from the OS RNG, hex-encoded.
    pub fn mint() -> anyhow::Result<Self> {
        let mut bytes = [0u8; 32];
        getrandom::fill(&mut bytes).map_err(|e| anyhow::anyhow!("OS RNG: {e}"))?;
        Ok(Self(bytes.iter().map(|b| format!("{b:02x}")).collect()))
    }

    /// A token the launcher minted. Refuses anything shorter than
    /// [`MIN_TOKEN_LEN`] or outside visible ASCII (it has to survive a header and
    /// a JSON string unchanged).
    pub fn from_launcher(token: &str) -> anyhow::Result<Self> {
        if token.len() < MIN_TOKEN_LEN {
            anyhow::bail!("session token shorter than {MIN_TOKEN_LEN} characters");
        }
        if !token.bytes().all(|b| b.is_ascii_graphic()) {
            anyhow::bail!("session token must be visible ASCII");
        }
        Ok(Self(token.to_string()))
    }

    /// The token itself, for the launcher to hand to its client.
    pub fn expose(&self) -> &str {
        &self.0
    }

    /// Whether `presented` is this token.
    pub fn matches(&self, presented: &str) -> bool {
        let (a, b) = (self.0.as_bytes(), presented.as_bytes());
        if a.len() != b.len() {
            return false;
        }
        a.iter().zip(b).fold(0u8, |acc, (x, y)| acc | (x ^ y)) == 0
    }
}

/// Which `Origin` header values the handshake admits.
#[derive(Clone, Debug)]
pub enum OriginPolicy {
    /// `http://` or `https://` + `localhost` / `127.0.0.1` / `[::1]`, optional
    /// port, nothing else.
    Loopback,
    /// Exactly these origins (ASCII case-insensitive).
    Exact(Vec<String>),
}

impl OriginPolicy {
    /// `Exact` from a comma-separated list; `Loopback` when the list is empty.
    pub fn from_list(list: &str) -> Self {
        let origins: Vec<String> = list
            .split(',')
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(str::to_string)
            .collect();
        if origins.is_empty() {
            OriginPolicy::Loopback
        } else {
            OriginPolicy::Exact(origins)
        }
    }

    /// Whether a request carrying `origin` passes. `None` (no header: not a
    /// browser page) passes; the token check still applies.
    pub fn admits(&self, origin: Option<&str>) -> bool {
        let Some(origin) = origin else { return true };
        match self {
            OriginPolicy::Loopback => is_loopback_origin(origin),
            OriginPolicy::Exact(list) => list.iter().any(|a| a.eq_ignore_ascii_case(origin)),
        }
    }
}

fn is_loopback_origin(origin: &str) -> bool {
    let lower = origin.to_ascii_lowercase();
    let Some(rest) = lower
        .strip_prefix("http://")
        .or_else(|| lower.strip_prefix("https://"))
    else {
        return false;
    };
    let (host, port) = if let Some(v6) = rest.strip_prefix("[::1]") {
        ("[::1]", v6)
    } else {
        match rest.find(':') {
            Some(i) => (&rest[..i], &rest[i..]),
            None => (rest, ""),
        }
    };
    let port_ok = port.is_empty()
        || (port.len() > 1 && port.len() <= 6 && port[1..].bytes().all(|b| b.is_ascii_digit()) && port.starts_with(':'));
    matches!(host, "localhost" | "127.0.0.1" | "[::1]") && port_ok
}

/// What a connection runs.
#[derive(Clone, Debug)]
pub enum Spawn {
    /// `$DEOS_TERMINAL_SHELL` / `$SHELL` / `/bin/sh`, interactive.
    Shell,
    /// A specific program + args.
    Command(String, Vec<String>),
}

/// Everything a server needs to decide whether to open a PTY, and what to run.
#[derive(Clone, Debug)]
pub struct ServerConfig {
    pub token: SessionToken,
    pub origins: OriginPolicy,
    pub spawn: Spawn,
}

impl ServerConfig {
    /// The bins' configuration: the token from [`TOKEN_VAR`] (validated) or a
    /// freshly minted one, the origin policy from [`ALLOWED_ORIGINS_VAR`].
    /// Returns whether the token was minted here (the bin then prints it for its
    /// launcher). [`TOKEN_VAR`] is removed from this process's environment.
    pub fn from_env(spawn: Spawn) -> anyhow::Result<(Self, bool)> {
        let (token, minted) = match std::env::var(TOKEN_VAR) {
            Ok(t) => (SessionToken::from_launcher(&t)?, false),
            Err(_) => (SessionToken::mint()?, true),
        };
        std::env::remove_var(TOKEN_VAR);
        let origins = OriginPolicy::from_list(&std::env::var(ALLOWED_ORIGINS_VAR).unwrap_or_default());
        Ok((
            Self {
                token,
                origins,
                spawn,
            },
            minted,
        ))
    }
}

/// Whether [`ALLOW_NON_LOOPBACK_VAR`] is `1`.
pub fn non_loopback_allowed_from_env() -> bool {
    std::env::var(ALLOW_NON_LOOPBACK_VAR).as_deref() == Ok("1")
}

/// Bind `addr`, refusing a non-loopback address unless `allow_non_loopback`.
pub async fn bind(addr: &str, allow_non_loopback: bool) -> anyhow::Result<TcpListener> {
    if !allow_non_loopback {
        let resolved: Vec<SocketAddr> = tokio::net::lookup_host(addr)
            .await
            .with_context(|| format!("resolving {addr}"))?
            .collect();
        if resolved.is_empty() || resolved.iter().any(|a| !a.ip().is_loopback()) {
            anyhow::bail!(
                "refusing to bind {addr}: not loopback-only ({resolved:?}); \
                 set {ALLOW_NON_LOOPBACK_VAR}=1 to expose a shell beyond this host"
            );
        }
    }
    let listener = TcpListener::bind(addr)
        .await
        .with_context(|| format!("binding {addr}"))?;
    let local = listener.local_addr()?;
    if !allow_non_loopback && !local.ip().is_loopback() {
        anyhow::bail!("refusing to serve on {local}: not loopback");
    }
    Ok(listener)
}

/// Serve connections on `listener` forever.
pub async fn serve(listener: TcpListener, config: ServerConfig) -> anyhow::Result<()> {
    let config = Arc::new(config);
    loop {
        let (stream, peer) = listener.accept().await?;
        let config = config.clone();
        tokio::spawn(async move {
            if let Err(e) = serve_connection(stream, &config).await {
                log::warn!("pty-ws connection {peer} ended: {e:#}");
            }
        });
    }
}

/// Bind (see [`bind`]) and return the bound address plus the serving future.
pub async fn bind_serve(
    addr: &str,
    allow_non_loopback: bool,
    config: ServerConfig,
) -> anyhow::Result<(SocketAddr, impl std::future::Future<Output = anyhow::Result<()>>)> {
    let listener = bind(addr, allow_non_loopback).await?;
    let local = listener.local_addr()?;
    Ok((local, serve(listener, config)))
}

fn reject(status: StatusCode, why: &str) -> ErrorResponse {
    let mut resp = ErrorResponse::new(Some(why.to_string()));
    *resp.status_mut() = status;
    resp
}

/// The gate, then one WS connection ↔ one PTY-hosted process.
async fn serve_connection(stream: TcpStream, config: &ServerConfig) -> anyhow::Result<()> {
    let mut header_authenticated = false;
    let ws = tokio_tungstenite::accept_hdr_async(stream, |req: &Request, resp: Response| {
        let origin = match req.headers().get(header::ORIGIN) {
            None => None,
            Some(v) => match v.to_str() {
                Ok(s) => Some(s),
                Err(_) => return Err(reject(StatusCode::FORBIDDEN, "origin not allowed")),
            },
        };
        if !config.origins.admits(origin) {
            return Err(reject(StatusCode::FORBIDDEN, "origin not allowed"));
        }
        if let Some(auth) = req.headers().get(header::AUTHORIZATION) {
            match auth.to_str().ok().and_then(|v| v.strip_prefix("Bearer ")) {
                Some(t) if config.token.matches(t) => header_authenticated = true,
                _ => return Err(reject(StatusCode::UNAUTHORIZED, "bad session token")),
            }
        }
        Ok(resp)
    })
    .await
    .context("websocket handshake")?;
    let (mut ws_tx, mut ws_rx) = ws.split();

    if !header_authenticated {
        let first = tokio::time::timeout(AUTH_TIMEOUT, ws_rx.next()).await;
        let ok = match &first {
            Ok(Some(Ok(Message::Text(text)))) => matches!(
                WireMsg::from_text(text),
                Some(WireMsg::Auth { token }) if config.token.matches(&token)
            ),
            _ => false,
        };
        if !ok {
            let _ = ws_tx
                .send(Message::Close(Some(CloseFrame {
                    code: CloseCode::Policy,
                    reason: "unauthenticated".into(),
                })))
                .await;
            anyhow::bail!("unauthenticated connection closed before any PTY was opened");
        }
    }

    let pty_system = NativePtySystem::default();
    let pair = pty_system
        .openpty(PtySize {
            rows: 24,
            cols: 80,
            pixel_width: 0,
            pixel_height: 0,
        })
        .context("openpty")?;

    let cmd = build_command(&config.spawn);
    let mut child = pair.slave.spawn_command(cmd).context("spawn process")?;
    // The session ends when EITHER side does: a client that goes away must not
    // leave its shell running (the reader thread would then wait forever for a
    // PTY EOF that only the child's exit produces).
    let mut killer = child.clone_killer();
    // Drop the slave once the child holds it, so EOF propagates on child exit.
    drop(pair.slave);

    let mut reader = pair.master.try_clone_reader().context("clone reader")?;
    let mut writer = pair.master.take_writer().context("take writer")?;
    let master = pair.master; // kept here for the resize control path.

    // PTY output → an mpsc the async side forwards as binary WS frames. The PTY
    // read is blocking, so it lives on a blocking thread.
    let (out_tx, mut out_rx) = mpsc::channel::<Vec<u8>>(64);
    let reader_handle = std::thread::spawn(move || {
        let mut buf = [0u8; 8192];
        loop {
            match reader.read(&mut buf) {
                Ok(0) => break,
                Ok(n) => {
                    if out_tx.blocking_send(buf[..n].to_vec()).is_err() {
                        break;
                    }
                }
                Err(_) => break,
            }
        }
    });

    let (exit_tx, mut exit_rx) = mpsc::channel::<Option<i32>>(1);
    let exit_handle = std::thread::spawn(move || {
        let code = child.wait().ok().map(|s| s.exit_code() as i32);
        let _ = exit_tx.blocking_send(code);
    });

    loop {
        tokio::select! {
            maybe_out = out_rx.recv() => {
                match maybe_out {
                    Some(bytes) => {
                        if ws_tx.send(Message::Binary(bytes.into())).await.is_err() {
                            break;
                        }
                    }
                    None => break,
                }
            }
            code = exit_rx.recv() => {
                let code = code.flatten();
                let _ = ws_tx
                    .send(Message::Text(WireMsg::Exit { code }.to_text().into()))
                    .await;
                let _ = ws_tx.send(Message::Close(None)).await;
                break;
            }
            msg = ws_rx.next() => {
                match msg {
                    Some(Ok(Message::Binary(bytes))) => {
                        if writer.write_all(&bytes).is_err() {
                            break;
                        }
                        let _ = writer.flush();
                    }
                    Some(Ok(Message::Text(text))) => {
                        if let Some(WireMsg::Resize { cols, rows }) = WireMsg::from_text(&text) {
                            let _ = master.resize(PtySize {
                                rows,
                                cols,
                                pixel_width: 0,
                                pixel_height: 0,
                            });
                        }
                    }
                    Some(Ok(Message::Close(_))) | None => break,
                    Some(Ok(_)) => {}
                    Some(Err(_)) => break,
                }
            }
        }
    }

    // Kill the child (a no-op if it already exited), release the PTY master,
    // and reap the helper threads off the async workers.
    let _ = killer.kill();
    drop(writer);
    drop(master);
    let _ = tokio::task::spawn_blocking(move || {
        let _ = reader_handle.join();
        let _ = exit_handle.join();
    })
    .await;
    Ok(())
}

/// The child command, with the minimal environment in place of this process's.
fn build_command(spawn: &Spawn) -> CommandBuilder {
    let mut cmd = match spawn {
        Spawn::Shell => {
            let shell = std::env::var("DEOS_TERMINAL_SHELL")
                .or_else(|_| std::env::var("SHELL"))
                .unwrap_or_else(|_| "/bin/sh".to_string());
            let mut cmd = CommandBuilder::new(shell);
            cmd.arg("-i");
            cmd
        }
        Spawn::Command(prog, args) => {
            let mut cmd = CommandBuilder::new(prog);
            for a in args {
                cmd.arg(a);
            }
            cmd
        }
    };
    cmd.env_clear();
    for (k, v) in crate::shell_env::minimal_shell_env() {
        cmd.env(k, v);
    }
    if matches!(spawn, Spawn::Shell) {
        // A trivial, predictable prompt keeps the wire deterministic.
        cmd.env("PS1", "$ ");
    }
    if let Ok(cwd) = std::env::current_dir() {
        cmd.cwd(cwd);
    }
    cmd
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn loopback_policy_admits_only_loopback_http_origins() {
        let p = OriginPolicy::Loopback;
        for ok in [
            "http://localhost",
            "http://localhost:8080",
            "https://127.0.0.1:3000",
            "http://[::1]:5173",
            "HTTP://LOCALHOST:1",
        ] {
            assert!(p.admits(Some(ok)), "{ok} should pass");
        }
        for bad in [
            "https://evil.example",
            "http://localhost.evil.example",
            "http://127.0.0.1.evil.example",
            "http://localhost:80/path",
            "http://localhost:",
            "http://localhost@evil.example",
            "null",
            "file://",
            "ws://localhost",
            "http://[::1].evil",
        ] {
            assert!(!p.admits(Some(bad)), "{bad} should be refused");
        }
        assert!(p.admits(None), "a non-browser client (no Origin) reaches the token check");
    }

    #[test]
    fn exact_policy_replaces_the_default() {
        let p = OriginPolicy::from_list(" https://cockpit.example , ");
        assert!(p.admits(Some("https://cockpit.example")));
        assert!(!p.admits(Some("http://localhost")));
        assert!(matches!(OriginPolicy::from_list(" , "), OriginPolicy::Loopback));
    }

    #[test]
    fn tokens_mint_distinct_and_match_exactly() {
        let a = SessionToken::mint().unwrap();
        let b = SessionToken::mint().unwrap();
        assert_ne!(a.expose(), b.expose());
        assert_eq!(a.expose().len(), 64);
        assert!(a.matches(a.expose()));
        assert!(!a.matches(b.expose()));
        assert!(!a.matches(&a.expose()[..63]));
        assert!(!a.matches(""));
        assert!(!format!("{a:?}").contains(a.expose()));
    }

    #[test]
    fn short_or_odd_launcher_tokens_are_refused() {
        assert!(SessionToken::from_launcher("short").is_err());
        assert!(SessionToken::from_launcher(&"a b".repeat(20)).is_err());
        assert!(SessionToken::from_launcher(&"x".repeat(32)).is_ok());
    }

    #[tokio::test]
    async fn non_loopback_bind_is_refused_by_default() {
        let err = bind("0.0.0.0:0", false).await.unwrap_err();
        assert!(format!("{err:#}").contains("not loopback"), "{err:#}");
        assert!(bind("127.0.0.1:0", false).await.is_ok());
    }
}
