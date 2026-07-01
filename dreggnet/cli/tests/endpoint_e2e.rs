//! `--endpoint` proof: the CLI is a REAL client to a live cloud.
//!
//! These tests stand up a tiny stub HTTP gateway (a `std::net::TcpListener` that
//! speaks just enough of the fly-machines API) and drive the `dregg-cloud` binary
//! with `--endpoint http://127.0.0.1:<port>`. They prove that:
//!
//! - `machines create` / `deploy` / `run` make a REAL `POST /v1/apps/{app}/machines`
//!   over the wire (the stub records the method + path + body it received),
//! - the account's `dga1_` credential is presented as `Authorization: Bearer …`,
//! - a funded 200 renders the live node's metered result, and
//! - a gateway refusal (a 4xx) is rendered HONESTLY and exits non-zero.
//!
//! This is the "interface with the live cloud" story made real and testable without
//! a live node: the same code path points at `https://dreggnet.example.com`.

use std::io::{Read, Write};
use std::net::TcpListener;
use std::process::Command;
use std::sync::{Arc, Mutex};
use std::thread;

/// One request the stub gateway received — enough to assert the CLI made the real call.
#[derive(Clone, Default)]
struct Recorded {
    method: String,
    path: String,
    authorization: Option<String>,
    body: String,
}

/// How the stub should answer a request (matched by path substring).
#[derive(Clone)]
struct Canned {
    status_line: &'static str,
    body: String,
}

/// A stub fly-machines gateway: it records every request and answers by path.
struct StubGateway {
    addr: String,
    recorded: Arc<Mutex<Vec<Recorded>>>,
}

impl StubGateway {
    /// Bind a stub on an ephemeral port. `responder` maps `(method, path)` to a
    /// canned response; the connection loop runs on a background thread.
    fn start(responder: impl Fn(&str, &str) -> Canned + Send + Sync + 'static) -> StubGateway {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind stub");
        let addr = format!("http://{}", listener.local_addr().unwrap());
        let recorded = Arc::new(Mutex::new(Vec::new()));
        let rec = recorded.clone();
        let responder = Arc::new(responder);
        thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(mut stream) = stream else { continue };
                let req = read_request(&mut stream);
                rec.lock().unwrap().push(req.clone());
                let canned = responder(&req.method, &req.path);
                let resp = format!(
                    "{}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
                    canned.status_line,
                    canned.body.len(),
                    canned.body
                );
                let _ = stream.write_all(resp.as_bytes());
                let _ = stream.flush();
            }
        });
        StubGateway { addr, recorded }
    }

    fn requests(&self) -> Vec<Recorded> {
        self.recorded.lock().unwrap().clone()
    }
}

/// Read one HTTP request off the stream: the request line, the headers we care
/// about (Authorization, Content-Length), and a Content-Length-sized body.
fn read_request(stream: &mut std::net::TcpStream) -> Recorded {
    let mut buf = Vec::new();
    let mut tmp = [0u8; 1024];
    // Read until the header terminator is present.
    loop {
        let n = stream.read(&mut tmp).unwrap_or(0);
        if n == 0 {
            break;
        }
        buf.extend_from_slice(&tmp[..n]);
        if let Some(pos) = find_header_end(&buf) {
            // Ensure we have the full body (Content-Length) too.
            let head = String::from_utf8_lossy(&buf[..pos]).to_string();
            let content_len = content_length(&head);
            let body_start = pos + 4;
            while buf.len() < body_start + content_len {
                let n = stream.read(&mut tmp).unwrap_or(0);
                if n == 0 {
                    break;
                }
                buf.extend_from_slice(&tmp[..n]);
            }
            let head_lines: Vec<&str> = head.lines().collect();
            let mut parts = head_lines.first().unwrap_or(&"").split_whitespace();
            let method = parts.next().unwrap_or("").to_string();
            let path = parts.next().unwrap_or("").to_string();
            let authorization = head_lines
                .iter()
                .find(|l| l.to_ascii_lowercase().starts_with("authorization:"))
                .map(|l| l.splitn(2, ':').nth(1).unwrap_or("").trim().to_string());
            let body = String::from_utf8_lossy(
                &buf[body_start..(body_start + content_len).min(buf.len())],
            )
            .to_string();
            return Recorded {
                method,
                path,
                authorization,
                body,
            };
        }
    }
    Recorded::default()
}

fn find_header_end(buf: &[u8]) -> Option<usize> {
    buf.windows(4).position(|w| w == b"\r\n\r\n")
}

fn content_length(head: &str) -> usize {
    head.lines()
        .find(|l| l.to_ascii_lowercase().starts_with("content-length:"))
        .and_then(|l| l.splitn(2, ':').nth(1))
        .and_then(|v| v.trim().parse().ok())
        .unwrap_or(0)
}

const FUNDED_MACHINE: &str = r#"{"id":"d891f2","name":"funded","state":"started","region":"local","instance_id":"i-1","private_ip":"","config":{"image":"","guest":{"cpu_kind":"shared","cpus":1,"memory_mb":256},"env":{}},"created_at":"now","updated_at":"now","dregg":{"backend":"local","meter_units":3,"outputs":["clone","build","publish"]}}"#;

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_dregg-cloud")
}

/// `machines create --endpoint` makes the real POST and renders the funded result;
/// the logged-in `dga1_` credential is presented as the bearer.
#[test]
fn endpoint_machines_create_renders_funded_result() {
    let stub = StubGateway::start(|_m, path| {
        if path.contains("/machines") {
            Canned {
                status_line: "HTTP/1.1 200 OK",
                body: FUNDED_MACHINE.to_string(),
            }
        } else {
            Canned {
                status_line: "HTTP/1.1 404 Not Found",
                body: r#"{"error":"not found"}"#.to_string(),
            }
        }
    });

    let dir = tempfile::tempdir().unwrap();
    let state_dir = dir.path();

    // Log in so the CLI has a `dga1_` credential to present as the bearer.
    let login = Command::new(bin())
        .args(["--state-dir"])
        .arg(state_dir)
        .args(["login", "--new"])
        .output()
        .expect("login");
    assert!(login.status.success());

    let out = Command::new(bin())
        .args(["--state-dir"])
        .arg(state_dir)
        .args(["--endpoint", &stub.addr, "machines", "create", "funded"])
        .output()
        .expect("machines create");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "create failed: {stdout}\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        stdout.contains("✓ machine d891f2"),
        "missing machine id:\n{stdout}"
    );
    assert!(
        stdout.contains("state     started"),
        "missing state:\n{stdout}"
    );
    assert!(
        stdout.contains("3 units charged by the live node"),
        "missing meter:\n{stdout}"
    );
    assert!(
        stdout.contains("output[0] clone"),
        "missing outputs:\n{stdout}"
    );

    // The REAL wire call happened, with the bearer + a JSON create body.
    let reqs = stub.requests();
    let create = reqs
        .iter()
        .find(|r| r.method == "POST" && r.path == "/v1/apps/funded/machines")
        .expect("a real POST to the machines API");
    assert!(
        create
            .authorization
            .as_deref()
            .is_some_and(|a| a.starts_with("Bearer dga1_")),
        "the dga1_ credential must be presented as the bearer, got {:?}",
        create.authorization
    );
    assert!(
        create.body.contains("\"guest\""),
        "create body should be the fly config: {}",
        create.body
    );
}

/// A gateway refusal (a 4xx) is rendered honestly and the CLI exits non-zero.
#[test]
fn endpoint_create_renders_refusal_honestly() {
    let stub = StubGateway::start(|_m, _path| Canned {
        status_line: "HTTP/1.1 422 Unprocessable Entity",
        body: r#"{"error":"lease refused: app is unfunded"}"#.to_string(),
    });

    let dir = tempfile::tempdir().unwrap();
    let out = Command::new(bin())
        .args(["--state-dir"])
        .arg(dir.path())
        .args(["--endpoint", &stub.addr, "machines", "create", "broke"])
        .output()
        .expect("machines create");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        !out.status.success(),
        "a refusal must exit non-zero:\n{stdout}"
    );
    assert!(
        stdout.contains("refused the create (HTTP 422)"),
        "missing honest refusal:\n{stdout}"
    );
    assert!(
        stdout.contains("lease refused: app is unfunded"),
        "missing gateway message:\n{stdout}"
    );
}

/// `deploy --endpoint` provisions on the live cloud via the same machines API.
#[test]
fn endpoint_deploy_hits_the_wire() {
    let stub = StubGateway::start(|_m, _path| Canned {
        status_line: "HTTP/1.1 200 OK",
        body: FUNDED_MACHINE.to_string(),
    });

    let dir = tempfile::tempdir().unwrap();
    let out = Command::new(bin())
        .args(["--state-dir"])
        .arg(dir.path())
        .args([
            "--endpoint",
            &stub.addr,
            "deploy",
            "https://example.com/me/site.git",
            "--name",
            "funded",
        ])
        .output()
        .expect("deploy");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "deploy failed:\n{stdout}\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        stdout.contains("deploying") && stdout.contains("LIVE cloud"),
        "missing live banner:\n{stdout}"
    );
    assert!(
        stdout.contains("✓ machine"),
        "missing machine render:\n{stdout}"
    );

    let reqs = stub.requests();
    assert!(
        reqs.iter()
            .any(|r| r.method == "POST" && r.path == "/v1/apps/funded/machines"),
        "deploy must POST the machines API: {:?}",
        reqs.iter()
            .map(|r| format!("{} {}", r.method, r.path))
            .collect::<Vec<_>>()
    );
}

/// `machines list --endpoint` makes a real GET and renders the records.
#[test]
fn endpoint_machines_list() {
    let stub = StubGateway::start(|m, _path| {
        if m == "GET" {
            Canned {
                status_line: "HTTP/1.1 200 OK",
                body: format!("[{FUNDED_MACHINE}]"),
            }
        } else {
            Canned {
                status_line: "HTTP/1.1 200 OK",
                body: FUNDED_MACHINE.to_string(),
            }
        }
    });

    let dir = tempfile::tempdir().unwrap();
    let out = Command::new(bin())
        .args(["--state-dir"])
        .arg(dir.path())
        .args(["--endpoint", &stub.addr, "machines", "list", "funded"])
        .output()
        .expect("machines list");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "list failed:\n{stdout}");
    assert!(
        stdout.contains("1 machine(s) for app `funded`"),
        "missing list header:\n{stdout}"
    );
    assert!(
        stdout.contains("✓ machine d891f2"),
        "missing machine in list:\n{stdout}"
    );

    let reqs = stub.requests();
    assert!(
        reqs.iter()
            .any(|r| r.method == "GET" && r.path == "/v1/apps/funded/machines"),
        "list must GET the machines API"
    );
}

/// `machines` without `--endpoint` is a clean error (it is a live-only verb).
#[test]
fn machines_without_endpoint_errors() {
    let dir = tempfile::tempdir().unwrap();
    let out = Command::new(bin())
        .args(["--state-dir"])
        .arg(dir.path())
        .args(["machines", "list", "anything"])
        .output()
        .expect("machines list");
    assert!(!out.status.success());
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("--endpoint"),
        "should point at --endpoint"
    );
}
