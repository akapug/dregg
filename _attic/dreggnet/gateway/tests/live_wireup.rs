//! W1 + W4 — the trust rail is LIVE in the SHIPPED `dreggnet-gateway` binary, not
//! just in the library unit tests.
//!
//! `gateway/tests/no_free_compute.rs` proves the LEASE-1a funding gate at the
//! library level (`MachineGateway::create`). This test proves the gate is actually
//! WIRED into the running serving binary: it spawns the real `dreggnet-gateway`
//! process, points it at a stub dregg node over `DREGGNET_NODE_URL`, and drives the
//! fly machines API over a real TCP socket. It demonstrates, end-to-end through the
//! binary the staging stack ships:
//!
//! 1. **admit-funded** — a `POST .../machines` for an app the (stub) chain funds is
//!    admitted (200) against the REAL on-chain reserve;
//! 2. **refuse-unfunded** — a create for an app the chain does NOT fund is refused
//!    (no 200, no machine) — the LEASE-1a gate bites in the shipped binary;
//! 3. **guard bites** — with `DREGGNET_GUARD=on`, once the per-account server quota
//!    is exhausted a further funded create is refused in-band (402);
//! 4. **fail-closed** — with `DREGGNET_NODE_URL` UNSET the binary admits nothing
//!    (no funding source ⇒ refuse), the warned default the env wires away.
//!
//! The stub node speaks the node cell API the default-build funding source reads
//! (`GET /api/cells` + `GET /api/cell/{id}`), so no live node is required. The
//! light-client-VERIFIED read (`--features dregg-verify`) is the same wire with a
//! receipt-log certificate on top, exercised by `no_free_compute.rs`'s verified case.

use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::process::{Child, Command};
use std::time::{Duration, Instant};

/// A 64-char hex dregg cell id (every byte = `b`). The decoded lease's lessee IS
/// this cell id, so the funded app the gateway admits is exactly this string.
fn cell_id(b: u8) -> String {
    std::iter::repeat_n(format!("{b:02x}"), 32).collect()
}

/// A 64-char field-element hex holding `v` as a little-endian i64 in the low 8
/// bytes (matching `node_api::decode_i64_slot`).
fn i64_field(v: i64) -> String {
    let mut bytes = [0u8; 32];
    bytes[..8].copy_from_slice(&v.to_le_bytes());
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The 16-slot `fields` of a funded, active execution-lease cell:
/// rent>0 (slot 4), period>0 (slot 5), not lapsed (slot 2 = 0), a real provider
/// (slot 6 nonzero).
fn lease_fields() -> Vec<String> {
    let zero = "0".repeat(64);
    let mut f = vec![zero; 16];
    f[2] = i64_field(0); // LAPSED — live
    f[4] = i64_field(1); // RENT per period
    f[5] = i64_field(1); // PERIOD length
    f[6] = "ff".repeat(32); // PROVIDER — nonzero
    f
}

/// Spawn a stub dregg node serving the cell API a funded lease decode reads. It
/// holds ONE funded lease cell (`funded_cell`); every other app is unfunded.
/// Returns the bound address; the server thread lives for the test's duration.
fn spawn_stub_node(funded_cell: String) -> SocketAddr {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    let cells_body =
        format!(r#"[{{"id":"{funded_cell}","balance":1000000,"nonce":0,"has_program":true}}]"#);
    let detail_body = format!(
        r#"{{"id":"{funded_cell}","found":true,"balance":1000000,"has_program":true,"token_id":"","fields":{}}}"#,
        serde_json::to_string(&lease_fields()).unwrap()
    );
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { continue };
            let mut buf = [0u8; 8192];
            let n = stream.read(&mut buf).unwrap_or(0);
            let req = String::from_utf8_lossy(&buf[..n]);
            let first = req.lines().next().unwrap_or("");
            let body = if first.starts_with("GET /api/cells") {
                cells_body.clone()
            } else if first.starts_with(&format!("GET /api/cell/{funded_cell}")) {
                detail_body.clone()
            } else {
                "{}".to_string()
            };
            let resp = format!(
                "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\
                 Content-Length: {}\r\nConnection: close\r\n\r\n{body}",
                body.len()
            );
            let _ = stream.write_all(resp.as_bytes());
            let _ = stream.flush();
        }
    });
    addr
}

/// Grab a free TCP port (bind :0, read the port, drop the listener so the gateway
/// can bind it).
fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port()
}

/// A spawned gateway process that is killed on drop (so a panicking assertion never
/// leaks the child).
struct GatewayProc(Child);
impl Drop for GatewayProc {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// Spawn the real `dreggnet-gateway` binary on `port` with the given env, and wait
/// until it accepts connections.
fn spawn_gateway(port: u16, envs: &[(&str, &str)]) -> GatewayProc {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_dreggnet-gateway"));
    cmd.args(["--bind", "127.0.0.1", "--port", &port.to_string()]);
    // A bare binary with no env beyond what the test sets: no dispatch (in-process
    // create), no sites dir, no storage root.
    cmd.env("DREGGNET_DISPATCH", "local");
    cmd.env("DREGGNET_SITES_DIR", "/nonexistent-sites");
    cmd.env("RUST_LOG", "warn");
    for (k, v) in envs {
        cmd.env(k, v);
    }
    let child = cmd.spawn().expect("spawn dreggnet-gateway");
    let addr: SocketAddr = format!("127.0.0.1:{port}").parse().unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    while Instant::now() < deadline {
        if TcpStream::connect_timeout(&addr, Duration::from_millis(200)).is_ok() {
            return GatewayProc(child);
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    panic!("gateway did not come up on {addr}");
}

/// `POST /v1/apps/{app}/machines` with an empty (default-machine) body. Returns
/// `(status_code, body)`.
fn create_machine(port: u16, app: &str) -> (u16, String) {
    let addr: SocketAddr = format!("127.0.0.1:{port}").parse().unwrap();
    let mut conn = TcpStream::connect(addr).unwrap();
    conn.set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    let req = format!(
        "POST /v1/apps/{app}/machines HTTP/1.1\r\nHost: localhost\r\n\
         Content-Length: 0\r\nConnection: close\r\n\r\n"
    );
    conn.write_all(req.as_bytes()).unwrap();
    conn.flush().unwrap();
    let mut raw = Vec::new();
    conn.read_to_end(&mut raw).unwrap();
    let text = String::from_utf8_lossy(&raw);
    let status = text
        .lines()
        .next()
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|s| s.parse::<u16>().ok())
        .unwrap_or(0);
    let body = text.split("\r\n\r\n").nth(1).unwrap_or("").to_string();
    (status, body)
}

#[test]
fn shipped_binary_admits_funded_refuses_unfunded_and_the_guard_bites() {
    let funded = cell_id(0x42);
    let node = spawn_stub_node(funded.clone());
    let node_url = format!("http://127.0.0.1:{}", node.port());
    let port = free_port();
    // The staging default: a funding source attached (DREGGNET_NODE_URL) + the
    // abuse guard on.
    let _gw = spawn_gateway(
        port,
        &[("DREGGNET_NODE_URL", &node_url), ("DREGGNET_GUARD", "on")],
    );

    // 1. admit-funded — the chain funds this app (the lease cell id), so the create
    //    is admitted (200) against the real on-chain reserve.
    let (status, body) = create_machine(port, &funded);
    assert_eq!(
        status, 200,
        "funded create should be admitted; body: {body}"
    );
    assert!(
        body.contains("\"state\":\"created\""),
        "expected a created machine; body: {body}"
    );

    // 2. refuse-unfunded — an app the chain does NOT fund is refused: the LEASE-1a
    //    gate bites in the SHIPPED binary (no 200, the funding error is surfaced).
    let (status, body) = create_machine(port, "totally-unfunded-app");
    assert_ne!(status, 200, "an unfunded create must NOT be admitted");
    assert!(
        body.contains("funded lease") || body.contains("funding"),
        "expected an unfunded/funding refusal; status {status}, body: {body}"
    );

    // 3. guard bites — the default good-tier server quota is 2. One funded machine
    //    is already live (#1), so a 2nd is admitted and the 3rd hits the per-account
    //    quota ceiling (402) — the abuse guard, live in-band.
    let (status, _) = create_machine(port, &funded);
    assert_eq!(
        status, 200,
        "the 2nd funded create (within quota) is admitted"
    );
    let (status, body) = create_machine(port, &funded);
    assert_eq!(
        status, 402,
        "the 3rd funded create should hit the per-account quota (guard bites); body: {body}"
    );
}

#[test]
fn shipped_binary_fails_closed_with_no_funding_source() {
    // No DREGGNET_NODE_URL: the binary has no way to confirm on-chain funding, so it
    // fails CLOSED — every create is refused (the loud-warned default the staging
    // env wires away by setting DREGGNET_NODE_URL).
    let port = free_port();
    let _gw = spawn_gateway(port, &[]);
    let (status, body) = create_machine(port, "any-app");
    assert_ne!(
        status, 200,
        "with no funding source the gateway must admit nothing; body: {body}"
    );
}
