//! End-to-end proof of the PTY-over-WebSocket bridge AND its gate (D1).
//!
//! Each server runs a tiny shell script as its PTY child. The script's first act
//! is to create a marker file, so "was a PTY child spawned for this connection?"
//! is a filesystem fact the test reads, not something the server reports about
//! itself. Every refusal test ends with an authenticated connection to the SAME
//! server that does create the marker — so an absent marker means the gate held,
//! not that the probe was broken.

#![cfg(not(target_arch = "wasm32"))]

use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::Duration;

use deos_terminal::pty_server::{self, OriginPolicy, ServerConfig, SessionToken, Spawn};
use deos_terminal::WireMsg;
use futures_util::{SinkExt, StreamExt};
use tokio_tungstenite::tungstenite::client::IntoClientRequest;
use tokio_tungstenite::tungstenite::http::HeaderValue;
use tokio_tungstenite::tungstenite::protocol::frame::coding::CloseCode;
use tokio_tungstenite::tungstenite::{Error as WsError, Message};

type Ws =
    tokio_tungstenite::WebSocketStream<tokio_tungstenite::MaybeTlsStream<tokio::net::TcpStream>>;

/// A scratch dir holding the spawn-marker script and the marker it writes.
struct Probe {
    dir: PathBuf,
}

impl Probe {
    fn new(name: &str) -> Self {
        let dir = std::env::temp_dir().join(format!("deos-pty-ws-{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let script = dir.join("shell.sh");
        std::fs::write(
            &script,
            format!(
                "#!/bin/sh\necho $$ > '{}'\nPS1='$ ' exec /bin/sh -i\n",
                dir.join("spawned").display()
            ),
        )
        .unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        Self { dir }
    }
    fn script(&self) -> String {
        self.dir.join("shell.sh").display().to_string()
    }
    fn spawned(&self) -> bool {
        self.dir.join("spawned").exists()
    }
    /// The PID the probe script wrote (the `exec`'d shell keeps it).
    fn shell_pid(&self) -> String {
        std::fs::read_to_string(self.dir.join("spawned"))
            .unwrap()
            .trim()
            .to_string()
    }
}

impl Drop for Probe {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// An in-process gated server running the probe script; returns its URL + token.
async fn server(probe: &Probe) -> (String, SessionToken) {
    let token = SessionToken::mint().unwrap();
    let config = ServerConfig {
        token: token.clone(),
        origins: OriginPolicy::Loopback,
        spawn: Spawn::Command(probe.script(), vec![]),
    };
    let (addr, fut) = pty_server::bind_serve("127.0.0.1:0", false, config)
        .await
        .expect("bind pty-ws server");
    tokio::spawn(fut);
    (format!("ws://{addr}"), token)
}

async fn dial(url: &str, origin: Option<&str>, bearer: Option<&str>) -> Result<Ws, WsError> {
    let mut req = url.into_client_request().unwrap();
    if let Some(o) = origin {
        req.headers_mut()
            .insert("Origin", HeaderValue::from_str(o).unwrap());
    }
    if let Some(t) = bearer {
        req.headers_mut().insert(
            "Authorization",
            HeaderValue::from_str(&format!("Bearer {t}")).unwrap(),
        );
    }
    tokio_tungstenite::connect_async(req)
        .await
        .map(|(ws, _)| ws)
}

fn auth_frame(token: &str) -> Message {
    Message::Text(
        WireMsg::Auth {
            token: token.to_string(),
        }
        .to_text()
        .into(),
    )
}

/// Have the shell print `<marker>_42` and read PTY output until it appears.
/// The command is typed as `echo <marker>_$((40+2))`: the PTY's line discipline
/// echoes typed input back on its own, so only a shell that actually RAN the
/// command produces the `_42` form.
async fn shell_echoes(ws: &mut Ws, marker: &str) -> (bool, String) {
    ws.send(Message::Binary(
        format!("echo {marker}_$((40+2))\n").into_bytes().into(),
    ))
    .await
    .expect("send keystrokes");
    let marker = format!("{marker}_42");
    let marker = marker.as_str();
    let mut seen = String::new();
    let deadline = tokio::time::Instant::now() + Duration::from_secs(10);
    let found = loop {
        let remaining = deadline.saturating_duration_since(tokio::time::Instant::now());
        if remaining.is_zero() {
            break false;
        }
        match tokio::time::timeout(remaining, ws.next()).await {
            Ok(Some(Ok(Message::Binary(bytes)))) => {
                seen.push_str(&String::from_utf8_lossy(&bytes));
                if seen.contains(marker) {
                    break true;
                }
            }
            Ok(Some(Ok(Message::Close(_)))) | Ok(None) => break false,
            Ok(Some(Ok(_))) => {}
            Ok(Some(Err(_))) | Err(_) => break false,
        }
    };
    (found, seen)
}

/// Read until the server closes; returns the close code if a close frame came,
/// and any PTY output seen (there must be none).
async fn await_close(ws: &mut Ws) -> (Option<CloseCode>, String) {
    let mut output = String::new();
    let deadline = tokio::time::Instant::now() + Duration::from_secs(5);
    loop {
        let remaining = deadline.saturating_duration_since(tokio::time::Instant::now());
        assert!(
            !remaining.is_zero(),
            "server did not close an unauthenticated socket"
        );
        match tokio::time::timeout(remaining, ws.next()).await {
            Ok(Some(Ok(Message::Close(frame)))) => return (frame.map(|f| f.code), output),
            Ok(Some(Ok(Message::Binary(b)))) => output.push_str(&String::from_utf8_lossy(&b)),
            Ok(Some(Ok(_))) => {}
            Ok(None) | Ok(Some(Err(_))) => return (None, output),
            Err(_) => panic!("server did not close an unauthenticated socket"),
        }
    }
}

/// The control half of every refusal test: the same server DOES spawn for an
/// authenticated client, so the absent marker above was the gate.
async fn authenticated_client_spawns(url: &str, token: &SessionToken, probe: &Probe) {
    let mut ws = dial(url, Some("http://localhost:5173"), None)
        .await
        .expect("dial");
    ws.send(auth_frame(token.expose())).await.unwrap();
    let (found, seen) = shell_echoes(&mut ws, "DEOS_GATE_CONTROL_77").await;
    assert!(found, "authenticated shell did not echo. Bytes:\n{seen}");
    assert!(probe.spawned(), "the probe script did not mark its spawn");
}

async fn settle() {
    tokio::time::sleep(Duration::from_millis(400)).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn first_frame_token_drives_a_shell() {
    let probe = Probe::new("first-frame");
    let (url, token) = server(&probe).await;
    let mut ws = dial(&url, Some("http://127.0.0.1:8080"), None)
        .await
        .expect("dial");
    ws.send(auth_frame(token.expose())).await.unwrap();
    let (found, seen) = shell_echoes(&mut ws, "DEOS_WS_OK_5151").await;
    assert!(
        found,
        "shell did not echo over the WebSocket. Bytes:\n{seen}"
    );
    assert!(probe.spawned());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn header_token_drives_a_shell() {
    let probe = Probe::new("header");
    let (url, token) = server(&probe).await;
    let mut ws = dial(&url, None, Some(token.expose())).await.expect("dial");
    let (found, seen) = shell_echoes(&mut ws, "DEOS_WS_HDR_6262").await;
    assert!(
        found,
        "shell did not echo over the WebSocket. Bytes:\n{seen}"
    );
    assert!(probe.spawned());
}

/// D1: a client that never presents the token — its first frame is keystrokes —
/// is closed with a policy-violation frame, and no PTY child ever ran.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn no_token_is_closed_before_any_pty_is_spawned() {
    let probe = Probe::new("no-token");
    let (url, token) = server(&probe).await;
    let mut ws = dial(&url, Some("http://localhost:3000"), None)
        .await
        .expect("dial");
    ws.send(Message::Binary(b"echo PWNED_NO_TOKEN\n".to_vec().into()))
        .await
        .unwrap();
    let (code, output) = await_close(&mut ws).await;
    assert_eq!(
        code,
        Some(CloseCode::Policy),
        "closed as a policy violation"
    );
    assert!(
        output.is_empty(),
        "PTY output reached an unauthenticated client: {output}"
    );
    settle().await;
    assert!(
        !probe.spawned(),
        "a PTY child ran for an unauthenticated connection"
    );

    authenticated_client_spawns(&url, &token, &probe).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn wrong_first_frame_token_is_closed_before_any_pty_is_spawned() {
    let probe = Probe::new("wrong-token");
    let (url, token) = server(&probe).await;
    let other = SessionToken::mint().unwrap();
    let mut ws = dial(&url, None, None).await.expect("dial");
    ws.send(auth_frame(other.expose())).await.unwrap();
    let (code, output) = await_close(&mut ws).await;
    assert_eq!(code, Some(CloseCode::Policy));
    assert!(output.is_empty());
    settle().await;
    assert!(!probe.spawned(), "a PTY child ran for a wrong token");

    authenticated_client_spawns(&url, &token, &probe).await;
}

/// A page on a foreign origin is refused at the HTTP handshake (403) even when
/// it somehow holds the token.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn foreign_origin_is_refused_at_the_handshake() {
    let probe = Probe::new("origin");
    let (url, token) = server(&probe).await;
    match dial(&url, Some("https://evil.example"), Some(token.expose())).await {
        Err(WsError::Http(resp)) => assert_eq!(resp.status(), 403),
        Err(e) => panic!("expected an HTTP 403 refusal, got {e}"),
        Ok(_) => panic!("a foreign origin completed the handshake"),
    }
    settle().await;
    assert!(!probe.spawned());

    authenticated_client_spawns(&url, &token, &probe).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn wrong_header_token_is_refused_at_the_handshake() {
    let probe = Probe::new("bad-bearer");
    let (url, token) = server(&probe).await;
    let other = SessionToken::mint().unwrap();
    match dial(&url, None, Some(other.expose())).await {
        Err(WsError::Http(resp)) => assert_eq!(resp.status(), 401),
        Err(e) => panic!("expected an HTTP 401 refusal, got {e}"),
        Ok(_) => panic!("a wrong bearer token completed the handshake"),
    }
    settle().await;
    assert!(!probe.spawned());

    authenticated_client_spawns(&url, &token, &probe).await;
}

fn alive(pid: &str) -> bool {
    Command::new("kill")
        .args(["-0", pid])
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// A client that goes away takes its shell with it: the server kills the PTY
/// child instead of leaving it running behind a dead socket.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn disconnect_kills_the_shell() {
    let probe = Probe::new("disconnect");
    let (url, token) = server(&probe).await;
    let mut ws = dial(&url, None, Some(token.expose())).await.expect("dial");
    let (found, seen) = shell_echoes(&mut ws, "DEOS_WS_DISC_9191").await;
    assert!(found, "shell did not run the command. Bytes:\n{seen}");
    let pid = probe.shell_pid();
    assert!(
        alive(&pid),
        "the shell {pid} should be running while connected"
    );

    ws.close(None).await.unwrap();
    drop(ws);
    let deadline = std::time::Instant::now() + Duration::from_secs(5);
    while alive(&pid) && std::time::Instant::now() < deadline {
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    assert!(!alive(&pid), "the shell {pid} outlived its connection");
}

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_deos-terminal-pty-ws")
}

/// The bin refuses a non-loopback bind unless explicitly configured.
#[test]
fn bin_refuses_a_non_loopback_bind() {
    let out = Command::new(bin())
        .arg("0.0.0.0:0")
        .env_remove(pty_server::ALLOW_NON_LOOPBACK_VAR)
        .env(pty_server::TOKEN_VAR, "x".repeat(40))
        .output()
        .expect("run bin");
    assert!(!out.status.success(), "the bin served on 0.0.0.0");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("not loopback"), "stderr: {stderr}");
}

/// With no launcher token the bin mints one, prints it on stdout for its
/// launcher, and requires it.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn bin_mints_prints_and_requires_its_token() {
    use tokio::io::AsyncBufReadExt;

    let probe = Probe::new("bin");
    let mut child = tokio::process::Command::new(bin())
        .arg("127.0.0.1:0")
        .env_remove(pty_server::TOKEN_VAR)
        .env("DEOS_TERMINAL_SHELL", probe.script())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true)
        .spawn()
        .expect("spawn bin");
    let mut stdout = tokio::io::BufReader::new(child.stdout.take().unwrap()).lines();
    let mut stderr = tokio::io::BufReader::new(child.stderr.take().unwrap()).lines();

    let token_line = tokio::time::timeout(Duration::from_secs(10), stdout.next_line())
        .await
        .expect("token line in time")
        .unwrap()
        .expect("a token line");
    let token = token_line
        .strip_prefix(&format!("{}=", pty_server::TOKEN_VAR))
        .expect("DEOS_TERMINAL_TOKEN=<hex>")
        .to_string();
    assert_eq!(token.len(), 64);
    let url = loop {
        let line = tokio::time::timeout(Duration::from_secs(10), stderr.next_line())
            .await
            .expect("listen line in time")
            .unwrap()
            .expect("a listen line");
        if let Some(i) = line.find("ws://") {
            break line[i..].trim().to_string();
        }
    };

    let mut ws = dial(&url, None, None).await.expect("dial");
    ws.send(Message::Binary(b"echo PWNED_BIN\n".to_vec().into()))
        .await
        .unwrap();
    let (code, _) = await_close(&mut ws).await;
    assert_eq!(code, Some(CloseCode::Policy));
    settle().await;
    assert!(
        !probe.spawned(),
        "the bin spawned a shell without its token"
    );

    let mut ws = dial(&url, None, Some(&token))
        .await
        .expect("dial with token");
    let (found, seen) = shell_echoes(&mut ws, "DEOS_BIN_OK_8383").await;
    assert!(found, "bin shell did not echo. Bytes:\n{seen}");
    assert!(probe.spawned());
    let _ = child.kill().await;
}
