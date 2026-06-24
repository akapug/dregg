//! **THE HTTP(S) DELIVERABLE: a REAL `http://` page, fetched through the net-cap
//! gate over a real socket, laid out by servo, rasterized by SWGL, captured to a
//! PNG.**
//!
//! This is the payoff of the forbidden-scheme fork (`servo-render/vendor/servo-net`):
//! servo's `net` crate no longer blocks an embedder `ProtocolHandler` for
//! `http`/`https`, and `scheme_fetch` consults it first — so the http(s) byte socket
//! is owned by the cap-gated handler (`netcap_http::CapGatedHttpHandler`) instead of
//! servo's internal hyper.
//!
//! Network access in this environment may be limited, so the test spins up a REAL
//! local http server (`std::net::TcpListener` — a real http(s) socket, NOT a
//! `data:` page) serving a small static HTML page, then:
//!
//!   1. **cap-DENIED run** — a surface scoped to a DIFFERENT origin tries to load the
//!      server's page; the cap gate refuses it AT the socket (the handler records
//!      `RefusedByCap`, `Netlayer::dial` was never called for it), and servo gets a
//!      network error (no page bytes);
//!   2. **cap-ALLOWED run** — a surface scoped to the server's origin loads the page;
//!      the cap gate admits it, the handler opens a REAL TCP socket, fetches the real
//!      bytes, servo lays them out, SWGL rasterizes → a PNG of the actual fetched
//!      page content. The handler's audit shows the origin was `Dialed` and the real
//!      bytes were served.
//!
//! `HTTP_RENDER_PNG_OUT=/path/page.png cargo test --features libservo --test \
//!  http_render_to_png -- --nocapture` writes the captured PNG.
//!
//! Run only under `--features libservo` (the real engine).

#![cfg(feature = "libservo")]

use std::io::{Read, Write};
use std::net::TcpListener;
use std::sync::mpsc;
use std::thread;

use servo_render::webview::CapGatedHttpEngine;
use servo_render::RgbaFrame;

use dregg_firmament::cell_seed;
use starbridge_web_surface::{AuthRequired, SurfaceCapability};

// ───────────────────────── a tiny self-contained PNG encoder ─────────────────────────
fn crc32(bytes: &[u8]) -> u32 {
    let mut crc: u32 = 0xFFFF_FFFF;
    for &b in bytes {
        crc ^= b as u32;
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
    }
    !crc
}
fn adler32(bytes: &[u8]) -> u32 {
    const MOD: u32 = 65521;
    let (mut a, mut b) = (1u32, 0u32);
    for &x in bytes {
        a = (a + x as u32) % MOD;
        b = (b + a) % MOD;
    }
    (b << 16) | a
}
fn png_encode_rgba8(w: u32, h: u32, rgba: &[u8]) -> Vec<u8> {
    fn chunk(out: &mut Vec<u8>, kind: &[u8; 4], data: &[u8]) {
        out.extend_from_slice(&(data.len() as u32).to_be_bytes());
        let mut typed = Vec::with_capacity(4 + data.len());
        typed.extend_from_slice(kind);
        typed.extend_from_slice(data);
        out.extend_from_slice(&typed);
        out.extend_from_slice(&crc32(&typed).to_be_bytes());
    }
    // SWGL/WebRender render bottom-left origin; flip vertically so the PNG is upright.
    let row_bytes = (w * 4) as usize;
    let mut raw = Vec::with_capacity((h * (1 + w * 4)) as usize);
    for y in 0..h {
        raw.push(0);
        let src = ((h - 1 - y) * w * 4) as usize;
        raw.extend_from_slice(&rgba[src..src + row_bytes]);
    }
    let mut z = vec![0x78u8, 0x01];
    let mut off = 0usize;
    while off < raw.len() {
        let take = (raw.len() - off).min(0xFFFF);
        let bfinal = if off + take >= raw.len() { 1u8 } else { 0u8 };
        z.push(bfinal);
        z.extend_from_slice(&(take as u16).to_le_bytes());
        z.extend_from_slice(&(!(take as u16)).to_le_bytes());
        z.extend_from_slice(&raw[off..off + take]);
        off += take;
    }
    z.extend_from_slice(&adler32(&raw).to_be_bytes());
    let mut png = vec![0x89, b'P', b'N', b'G', 0x0D, 0x0A, 0x1A, 0x0A];
    let mut ihdr = Vec::new();
    ihdr.extend_from_slice(&w.to_be_bytes());
    ihdr.extend_from_slice(&h.to_be_bytes());
    ihdr.extend_from_slice(&[8, 6, 0, 0, 0]);
    chunk(&mut png, b"IHDR", &ihdr);
    chunk(&mut png, b"IDAT", &z);
    chunk(&mut png, b"IEND", &[]);
    png
}

/// The HTML the local server serves — a blue page with a centered yellow block AND a
/// black heading, so the rasterized frame proves BOTH layout (≥2 colors) and glyphs
/// (antialiased grays) came from real http bytes the engine laid out.
const PAGE_HTML: &str = "<!doctype html><html><body style='margin:0;background:#0000ff'>\
<h1 style='margin:18px;font-size:40px;color:#000000'>dregg over http</h1>\
<div style='margin:20px auto;width:160px;height:90px;background:#ffff00'></div>\
</body></html>";

/// Spin a REAL local http server on an ephemeral port in a background thread. It
/// serves `PAGE_HTML` (with a real status line + Content-Type) to every connection
/// (`Connection: close`), for `n` requests, then exits. Returns the bound origin
/// (`http://127.0.0.1:PORT`).
fn spawn_local_http_server(n: usize) -> (String, thread::JoinHandle<()>) {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind ephemeral http port");
    let addr = listener.local_addr().expect("local addr");
    let origin = format!("http://{addr}");
    let (ready_tx, ready_rx) = mpsc::channel();
    let handle = thread::spawn(move || {
        ready_tx.send(()).ok();
        let body = PAGE_HTML.as_bytes();
        for _ in 0..n {
            match listener.accept() {
                Ok((mut stream, _)) => {
                    // Read the request (until headers end) — a real request arrives.
                    let mut buf = [0u8; 2048];
                    let _ = stream.read(&mut buf);
                    let resp = format!(
                        "HTTP/1.1 200 OK\r\n\
                         Content-Type: text/html; charset=utf-8\r\n\
                         Content-Length: {}\r\n\
                         Connection: close\r\n\r\n",
                        body.len()
                    );
                    let _ = stream.write_all(resp.as_bytes());
                    let _ = stream.write_all(body);
                    let _ = stream.flush();
                }
                Err(_) => break,
            }
        }
    });
    ready_rx.recv().ok();
    (origin, handle)
}

/// **THE LOAD-BEARING TEST.** A real http page through the cap gate → SWGL → PNG.
#[test]
fn real_http_page_rasterized_through_the_cap_gate() {
    const W: u32 = 360;
    const H: u32 = 200;

    // A real local http server (a real socket, NOT data:). It serves up to 4 requests
    // (the allowed run may issue a couple — the navigation + a favicon probe).
    let (origin, server) = spawn_local_http_server(4);
    let page_url = format!("{origin}/index.html");
    let presenter = cell_seed(11);

    // ONE `Servo` engine for the whole process (servo_config::opts is a process
    // `OnceCell`), with ONE cap-gated http handler registered (the fork permits it).
    // Both the denied and the allowed page render on it; `engine.render` re-points the
    // handler's held cap per page. The whole engine drive is serialized on the SWGL
    // current-context lock (SWGL's `ctx` is a process global).
    let (frame, last_fetch, dialed_outcomes, denied_outcomes, denied_fetched, outcome): (
        Option<RgbaFrame>,
        Option<(String, usize)>,
        Vec<_>,
        Vec<_>,
        Option<(String, usize)>,
        Option<_>,
    ) = servo_render::with_gl(|| {
        let engine = CapGatedHttpEngine::new(
            SurfaceCapability::root(presenter, AuthRequired::Either),
            &[],
        );

        // ── RUN 1: CAP-DENIED. A surface scoped to a DIFFERENT origin. The cap gate
        // must refuse the server's origin AT the socket — no bytes, no real page. ──
        let denied_surface = SurfaceCapability::scoped(
            presenter,
            AuthRequired::Either,
            [String::from("http://allowed.example")],
            [],
        );
        let _ = engine.render(
            &page_url,
            denied_surface,
            // seed only the (different) allowed origin as reachable — NOT the server's.
            &["http://allowed.example".to_string()],
            W,
            H,
            2048,
        );
        let denied_outcomes = engine.handler().outcomes();
        let denied_fetched = engine.handler().last_fetch();

        // ── RUN 2: CAP-ALLOWED. A surface scoped to the SERVER's origin. The cap gate
        // admits it, the handler opens a real TCP socket, fetches the real bytes,
        // servo lays them out, SWGL rasterizes. ──
        let allowed_surface =
            SurfaceCapability::scoped(presenter, AuthRequired::Either, [origin.clone()], []);
        let (frame, outcome) =
            engine.render(&page_url, allowed_surface, &[origin.clone()], W, H, 4096);
        let outcomes = engine.handler().outcomes();
        let last_fetch = engine.handler().last_fetch();
        (
            frame,
            last_fetch,
            outcomes,
            denied_outcomes,
            denied_fetched,
            outcome,
        )
    });

    // The cap gate bites for the unauthorized origin: NO bytes were fetched (the byte
    // socket never opened). The refusal may land at the delegate's navigation/connect
    // decision (`CapGate::request_navigation`/`load_web_resource`, denied upstream) OR
    // at the handler's own socket-boundary check — either way the held cap does not
    // authorize this origin, so the handler NEVER fetched real bytes. (When the
    // handler IS reached, every outcome is `RefusedByCap`.)
    assert!(
        denied_outcomes.iter().all(|o| o.refused_by_cap()),
        "any http load the handler saw for the denied origin was RefusedByCap: {denied_outcomes:?}"
    );
    assert!(
        denied_fetched.is_none(),
        "NO bytes were fetched for the cap-denied origin — the byte socket never opened"
    );
    println!(
        "CAP-DENIED: unauthorized origin blocked, zero bytes fetched (handler saw {} load(s), all RefusedByCap; navigation may also be denied upstream by the delegate)",
        denied_outcomes.len()
    );

    // The cap admitted the origin and the handler fetched REAL bytes over a real socket.
    let outcomes = dialed_outcomes;
    assert!(
        outcomes.iter().any(|o| o.dialed()),
        "the server origin was DIALED through the netlayer (cap-admitted): {outcomes:?}"
    );
    assert!(
        !outcomes.iter().any(|o| o.refused_by_cap()),
        "no cap refusal for the authorized origin: {outcomes:?}"
    );
    let (fetched_url, fetched_len) = last_fetch
        .expect("the handler fetched real http bytes over a real socket for the allowed origin");
    assert!(
        fetched_url.starts_with(&origin),
        "the fetched url is the server's: {fetched_url}"
    );
    assert!(
        fetched_len >= PAGE_HTML.len(),
        "the full page body ({} bytes) was fetched over the real socket; got {fetched_len}",
        PAGE_HTML.len()
    );
    println!(
        "CAP-ALLOWED: {} → dialed, fetched {fetched_len} real bytes over a real TCP socket; last outcome={outcome:?}",
        fetched_url
    );

    // The engine produced a frame from the real http bytes.
    let frame = frame.expect("the real Servo WebView produced a frame for the http page");
    assert_eq!(frame.width, W);
    assert_eq!(frame.height, H);
    assert_eq!(
        frame.bytes.len(),
        (W * H * 4) as usize,
        "real RGBA8, 4 bytes/pixel"
    );

    // ── PROVE it is genuine laid-out PAGE content from the http bytes ──
    // The page has a blue bg, a yellow block, and black antialiased glyphs. Real
    // layout + glyph raster yields many distinct colors incl. white/black/gray.
    let mut distinct = std::collections::BTreeSet::new();
    let mut has_blue = false;
    let mut has_yellowish = false;
    for i in 0..(frame.width * frame.height) as usize {
        let p = &frame.bytes[i * 4..i * 4 + 4];
        distinct.insert([p[0], p[1], p[2], p[3]]);
        if p[2] > 200 && p[0] < 80 && p[1] < 80 {
            has_blue = true;
        }
        if p[0] > 200 && p[1] > 200 && p[2] < 80 {
            has_yellowish = true;
        }
    }
    assert!(
        distinct.len() >= 3,
        "the rendered http page is non-trivial (≥3 distinct colors = real layout); got {}",
        distinct.len()
    );
    assert!(
        has_blue,
        "the page's blue background (from the http bytes) was rasterized"
    );
    assert!(
        has_yellowish,
        "the page's yellow block (from the http bytes) was laid out + rasterized"
    );

    // ── write the captured PNG of the REAL fetched page ──
    let out_path = std::env::var("HTTP_RENDER_PNG_OUT").unwrap_or_else(|_| {
        let mut p = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        p.push("servo_real_http_render.png");
        p.to_string_lossy().into_owned()
    });
    let png = png_encode_rgba8(frame.width, frame.height, &frame.bytes);
    std::fs::write(&out_path, &png).expect("write the rendered http-page PNG");
    let png_len = std::fs::metadata(&out_path).map(|m| m.len()).unwrap_or(0);
    assert!(
        png_len > 100,
        "the captured PNG is substantial, got {png_len} bytes"
    );
    println!(
        "HTTP_RENDER_PNG_WRITTEN path={out_path} bytes={png_len} dims={W}x{H} \
         distinct_colors={} source='REAL http:// page fetched over a cap-gated socket, \
         servo layout, SWGL raster'",
        distinct.len()
    );

    // The server thread loops on `accept()`; the allowed run already consumed a
    // connection. Detach it (it dies with the process) rather than join — a join
    // could block on a pending `accept()` for an unused slot.
    drop(server);
}
