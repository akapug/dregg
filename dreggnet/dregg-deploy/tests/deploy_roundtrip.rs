//! The auto-deploy round-trip, proven end to end through the local / in-process path.
//!
//! Builds a real local git repo fixture, deploys it (clone → detect → build → publish) as a
//! durable workflow, and asserts:
//!   - the built site is served over real TCP, and the receipt carries the source commit;
//!   - the commit is folded into the published cell (the `/.well-known/dregg-deploy.json`
//!     manifest is served and re-witnesses the commit);
//!   - the build runs in the cap-bounded exec tier (a `compute` deploy);
//!   - a deploy that crashes mid-build resumes exactly-once (clone/build replayed, never
//!     re-run; meter never doubled; the site still goes live);
//!   - an under-funded deploy budget reaps the deploy before it publishes.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::process::Command;
use std::sync::Arc;
use std::thread;

use dregg_deploy::workflow::{DeployStage, build_deploy_registries};
use dregg_deploy::{
    BuildPlan, BuildTier, DEPLOY_MANIFEST_PATH, DeployEngine, DeployReceipt, DeploySpec,
    deploy_in_memory_blocking, meter,
};
use dreggnet_webapp::hosting::SiteRegistry;
use dreggnet_webapp::{HttpMethod, WebRequest, WebResponse};

// ---------------------------------------------------------------------------
// Fixtures + a local gateway (the portable stand-in for the example.com edge).
// ---------------------------------------------------------------------------

/// Build a tiny local git repo with one commit; return (dir, commit).
fn fixture_repo(files: &[(&str, &str)]) -> (tempfile::TempDir, String) {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path();
    let run = |args: &[&str]| {
        let ok = Command::new("git")
            .arg("-C")
            .arg(p)
            .args(args)
            .output()
            .unwrap()
            .status
            .success();
        assert!(ok, "git {args:?}");
    };
    run(&["init", "-q"]);
    run(&["config", "user.email", "t@dregg.test"]);
    run(&["config", "user.name", "dregg test"]);
    run(&["config", "commit.gpgsign", "false"]);
    for (path, body) in files {
        let fp = p.join(path);
        if let Some(parent) = fp.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(fp, body).unwrap();
    }
    run(&["add", "-A"]);
    run(&["commit", "-q", "-m", "fixture"]);
    let out = Command::new("git")
        .arg("-C")
        .arg(p)
        .args(["rev-parse", "HEAD"])
        .output()
        .unwrap();
    let commit = String::from_utf8_lossy(&out.stdout).trim().to_string();
    (dir, commit)
}

/// Serve one HTTP request against a registry (the local gateway stand-in).
fn serve_one(stream: &mut TcpStream, registry: &SiteRegistry) -> std::io::Result<()> {
    let mut buf = Vec::new();
    let mut tmp = [0u8; 1024];
    let header_end = loop {
        if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
            break pos + 4;
        }
        let n = stream.read(&mut tmp)?;
        if n == 0 {
            return Ok(());
        }
        buf.extend_from_slice(&tmp[..n]);
    };
    let header_block = String::from_utf8_lossy(&buf[..header_end]).to_string();
    let mut lines = header_block.split("\r\n");
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("");
    let target = parts.next().unwrap_or("/");
    let host = lines
        .find_map(|l| {
            let (n, v) = l.split_once(':')?;
            n.trim()
                .eq_ignore_ascii_case("host")
                .then(|| v.trim().to_string())
        })
        .unwrap_or_default();
    let resp = match HttpMethod::parse(method) {
        Some(m) => registry.resolve(&host, &WebRequest::new(m, target, Vec::new())),
        None => WebResponse::error(405, "unsupported method"),
    };
    let head = format!(
        "HTTP/1.1 {} OK\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        resp.status,
        resp.content_type,
        resp.body.len(),
    );
    stream.write_all(head.as_bytes())?;
    stream.write_all(&resp.body)?;
    stream.flush()
}

fn http_get(addr: &str, host: &str, target: &str) -> String {
    let mut stream = TcpStream::connect(addr).expect("connect");
    let req = format!("GET {target} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\n\r\n");
    stream.write_all(req.as_bytes()).expect("write");
    let mut out = String::new();
    stream.read_to_string(&mut out).expect("read");
    out
}

// ---------------------------------------------------------------------------
// 1. The full round-trip: clone → detect(static) → build → publish → serve.
// ---------------------------------------------------------------------------

/// The deploy receipt is a typed VIEW over the publish turn receipt: a deploy
/// IS a publish turn, so the kernel receipt is already the receipt. When the
/// deploy engine's `SiteRegistry` is signed, the `DeployReceipt.turn_receipt_hash`
/// equals the hash of the publish turn receipt the registry sealed — re-witnessable
/// against that signed publish chain, not a parallel "deploy receipt" notion.
#[test]
fn signed_deploy_receipt_views_the_publish_turn_receipt() {
    use dreggnet_webapp::hosting::PublishReceipt;
    use dreggnet_webapp::receipt::{ReceiptBody, receipt_hash};

    const SEED: [u8; 32] = [77u8; 32];
    let (src, _commit) = fixture_repo(&[("index.html", "<h1>signed</h1>")]);

    // A SIGNED registry: the publish inside the deploy is sealed into its chain.
    let registry = Arc::new(SiteRegistry::signed(SEED));
    let workroot = tempfile::tempdir().unwrap();
    let engine = Arc::new(DeployEngine::new(workroot.path(), registry.clone()));

    let spec = DeploySpec::new(src.path().to_str().unwrap(), "blog", "agent:ember");
    let receipt: DeployReceipt =
        deploy_in_memory_blocking(engine, &spec, "deploy-signed-1").expect("deploy");

    // The deploy receipt carries the publish turn-receipt hash (it is a view).
    let turn_hash = receipt
        .turn_receipt_hash
        .expect("a signed deploy views a turn receipt");

    // Re-witness: reconstruct the publish turn receipt from the deploy's fields
    // (the publish was the genesis of the registry's chain → prev = None) and
    // confirm its hash is exactly what the deploy receipt views.
    let publish = PublishReceipt {
        seq: receipt.publish_seq,
        name: receipt.site_name.clone(),
        owner: receipt.owner.clone(),
        content_root: receipt.content_root.clone(),
        asset_count: receipt.asset_count,
        attest: None,
    };
    let expected = receipt_hash(&publish.body_hash(), publish.seq(), None, None);
    assert_eq!(
        turn_hash, expected,
        "deploy receipt views the real publish turn receipt"
    );

    // The unsigned local default carries no turn-receipt view.
    let (src2, _) = fixture_repo(&[("index.html", "<h1>plain</h1>")]);
    let plain_reg = Arc::new(SiteRegistry::new());
    let workroot2 = tempfile::tempdir().unwrap();
    let plain_engine = Arc::new(DeployEngine::new(workroot2.path(), plain_reg));
    let plain_spec = DeploySpec::new(src2.path().to_str().unwrap(), "plain", "agent:ember");
    let plain: DeployReceipt =
        deploy_in_memory_blocking(plain_engine, &plain_spec, "deploy-plain-1").expect("deploy");
    assert!(plain.turn_receipt_hash.is_none());
}

#[test]
fn static_deploy_round_trip_serves_with_commit_in_receipt_and_cell() {
    let (src, commit) = fixture_repo(&[
        ("index.html", "<!doctype html><h1>deployed from git</h1>"),
        ("style.css", "h1{color:rebeccapurple}"),
    ]);

    let registry = Arc::new(SiteRegistry::new());
    let workroot = tempfile::tempdir().unwrap();
    let engine = Arc::new(DeployEngine::new(workroot.path(), registry.clone()));

    let spec = DeploySpec::new(src.path().to_str().unwrap(), "blog", "agent:ember");
    let receipt: DeployReceipt =
        deploy_in_memory_blocking(engine, &spec, "deploy-static-1").expect("deploy");

    // The receipt carries the SOURCE COMMITMENT.
    assert_eq!(
        receipt.commit, commit,
        "the receipt carries the cloned commit"
    );
    assert_eq!(receipt.build_plan, "static");
    assert_eq!(receipt.site_name, "blog");
    assert!(!receipt.content_root.is_empty());
    assert_eq!(
        receipt.meter_units, 3,
        "clone+build+publish each metered once"
    );
    // index.html + style.css + the injected deploy manifest = 3 assets.
    assert_eq!(receipt.asset_count, 3);

    // Serve the published cell over real TCP.
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap().to_string();
    let reg = Arc::clone(&registry);
    let server = thread::spawn(move || {
        for _ in 0..3 {
            let (mut stream, _) = listener.accept().unwrap();
            let _ = serve_one(&mut stream, &reg);
        }
    });

    // The built site is live.
    let index = http_get(&addr, "blog.example.com", "/");
    assert!(index.contains("200 OK"), "index: {index}");
    assert!(index.contains("deployed from git"), "index body: {index}");

    // The commit is re-witnessable from the served cell itself.
    let manifest = http_get(&addr, "blog.example.com", DEPLOY_MANIFEST_PATH);
    assert!(manifest.contains("200 OK"), "manifest: {manifest}");
    assert!(
        manifest.contains(&commit),
        "the served deploy manifest carries the commit"
    );

    let css = http_get(&addr, "blog.example.com", "/style.css");
    assert!(css.contains("text/css"), "css content-type: {css}");

    server.join().unwrap();
}

// ---------------------------------------------------------------------------
// 2. The build runs in the cap-bounded exec tier (a compute deploy).
// ---------------------------------------------------------------------------

#[test]
fn compute_deploy_builds_in_the_exec_tier() {
    // A repo whose dregg.toml declares a wasm compute build run through the exec tier.
    let manifest = "[site]\nname = \"calc\"\n\
        [build]\nkind = \"compute\"\nlang = \"wat\"\ntier = \"sandboxed\"\nartifact = \"index.html\"\n\
        source = \"(module (func (export \\\"run\\\") (result i32) (i32.const 42)))\"\n";
    let (src, commit) = fixture_repo(&[("dregg.toml", manifest)]);

    let registry = Arc::new(SiteRegistry::new());
    let workroot = tempfile::tempdir().unwrap();
    let engine = Arc::new(DeployEngine::new(workroot.path(), registry.clone()));

    let spec = DeploySpec::new(src.path().to_str().unwrap(), "calc", "agent:ember");
    let receipt = deploy_in_memory_blocking(engine, &spec, "deploy-compute-1").expect("deploy");

    assert_eq!(receipt.build_plan, "compute");
    assert_eq!(receipt.commit, commit);

    // The exec-tier build output (42) is the served page.
    let resp = registry.resolve("calc.example.com", &WebRequest::get("/"));
    assert_eq!(resp.status, 200);
    assert_eq!(
        resp.body_str().trim(),
        "42",
        "the wasm-tier build output is served"
    );
}

// ---------------------------------------------------------------------------
// 3. Crash mid-deploy resumes exactly-once (clone/build replayed, site still goes live).
// ---------------------------------------------------------------------------

#[tokio::test]
async fn crash_mid_deploy_resumes_exactly_once() {
    use duroxide::providers::sqlite::SqliteProvider;
    use duroxide::runtime::Runtime;
    use duroxide::{Client, OrchestrationStatus};
    use std::time::Duration;

    let (src, commit) = fixture_repo(&[("index.html", "<h1>resumed</h1>")]);

    let dir = tempfile::tempdir().unwrap();
    let db_path = dir.path().join("deploy.db");
    let db_url = format!("sqlite:{}?mode=rwc", db_path.display());
    let workroot = tempfile::tempdir().unwrap();
    let registry = Arc::new(SiteRegistry::new());
    // ONE engine, shared across both runtimes (same workroot + registry) — the resume path.
    let engine = Arc::new(DeployEngine::new(workroot.path(), registry.clone()));

    let instance = "deploy-crash-1";
    let mut spec = DeploySpec::new(src.path().to_str().unwrap(), "blog", "agent:ember");
    // Park after BUILD: clone + build are checkpointed + metered; publish has NOT run.
    spec.pause_after = Some(DeployStage::Build);
    spec.pause_event = Some("Resume".to_string());
    let input = serde_json::to_string(&spec).unwrap();

    let open_store = |url: String| async move {
        Arc::new(SqliteProvider::new(&url, None).await.expect("open store"))
    };

    // ===== Runtime #1: run to the post-build checkpoint, then "crash". =====
    {
        let store = open_store(db_url.clone()).await;
        let (a, o) = build_deploy_registries(engine.clone());
        let rt = Runtime::start_with_store(store.clone(), a, o).await;
        let client = Client::new(store.clone());
        client
            .start_orchestration(instance, dregg_deploy::ORCH_DEPLOY, input.clone())
            .await
            .expect("start");

        let mut parked = false;
        for _ in 0..400 {
            let built = meter::run_calls(instance, "build") >= 1;
            let status = client.get_orchestration_status(instance).await.unwrap();
            if built && matches!(status, OrchestrationStatus::Running { .. }) {
                parked = true;
                break;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
        assert!(parked, "deploy did not reach the post-build checkpoint");
        tokio::time::sleep(Duration::from_millis(200)).await;

        assert_eq!(meter::run_calls(instance, "clone"), 1, "clone ran once");
        assert_eq!(meter::run_calls(instance, "build"), 1, "build ran once");
        assert_eq!(
            meter::run_calls(instance, "publish"),
            0,
            "publish has NOT run"
        );
        assert_eq!(meter::units(instance), 2, "two metered steps so far");

        rt.shutdown(None).await; // 💥 crash
    }

    // ===== Runtime #2: resume over the SAME on-disk store + workroot + registry. =====
    {
        let store = open_store(db_url.clone()).await;
        let (a, o) = build_deploy_registries(engine.clone());
        let rt = Runtime::start_with_store(store.clone(), a, o).await;
        let client = Client::new(store.clone());

        // The resumed orchestration replays clone+build from history, then re-subscribes to
        // the `Resume` wait. Raising before that subscription exists drops the event, so
        // poll-raise until the deploy completes (extra raises stay in history, harmless).
        let mut completed = false;
        for _ in 0..120 {
            let _ = client.raise_event(instance, "Resume", "").await;
            if matches!(
                client.get_orchestration_status(instance).await,
                Ok(OrchestrationStatus::Completed { .. })
            ) {
                completed = true;
                break;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
        assert!(
            completed,
            "resumed deploy did not complete after re-raising Resume"
        );

        let status = client
            .wait_for_orchestration(instance, Duration::from_secs(60))
            .await
            .expect("wait");
        let output = match status {
            OrchestrationStatus::Completed { output, .. } => output,
            other => panic!("deploy did not complete: {other:?}"),
        };
        let receipt: DeployReceipt = serde_json::from_str(&output).unwrap();

        assert_eq!(receipt.commit, commit, "commit preserved across the crash");
        assert_eq!(receipt.meter_units, 3, "three metered steps total");

        // EXACTLY-ONCE: clone + build were replayed from the checkpoint, never re-run.
        assert_eq!(meter::run_calls(instance, "clone"), 1, "clone never re-run");
        assert_eq!(meter::run_calls(instance, "build"), 1, "build never re-run");
        assert_eq!(
            meter::run_calls(instance, "publish"),
            1,
            "publish ran once, post-resume"
        );
        assert_eq!(
            meter::units(instance),
            3,
            "meter charged exactly three times"
        );

        // The site is live after the resume.
        let resp = registry.resolve("blog.example.com", &WebRequest::get("/"));
        assert_eq!(resp.status, 200);
        assert!(resp.body_str().contains("resumed"));

        rt.shutdown(None).await;
    }
}

// ---------------------------------------------------------------------------
// 4. An under-funded deploy budget reaps the deploy before publish.
// ---------------------------------------------------------------------------

#[test]
fn underfunded_budget_reaps_the_deploy() {
    let (src, _commit) = fixture_repo(&[("index.html", "<h1>x</h1>")]);
    let registry = Arc::new(SiteRegistry::new());
    let workroot = tempfile::tempdir().unwrap();
    let engine = Arc::new(DeployEngine::new(workroot.path(), registry.clone()));

    // Budget 2, cost 1/step: clone + build fit (totals 1, 2), publish's tick (total 3) lapses.
    let mut spec = DeploySpec::new(src.path().to_str().unwrap(), "blog", "agent:ember");
    spec.budget_units = 2;
    spec.cost_per_step = 1;

    let err = deploy_in_memory_blocking(engine, &spec, "deploy-broke-1").unwrap_err();
    assert!(
        err.contains("deploy-lease exhausted"),
        "expected lapse, got: {err}"
    );
    // The deploy never published — the site is not live.
    assert!(
        registry.get("blog").is_none(),
        "an exhausted deploy publishes nothing"
    );
}

// ---------------------------------------------------------------------------
// 5. An explicit build override drives the workflow (the API the CLI uses).
// ---------------------------------------------------------------------------

#[test]
fn explicit_build_override_drives_the_deploy() {
    let (src, _commit) = fixture_repo(&[("public/index.html", "<h1>from public/</h1>")]);
    let registry = Arc::new(SiteRegistry::new());
    let workroot = tempfile::tempdir().unwrap();
    let engine = Arc::new(DeployEngine::new(workroot.path(), registry.clone()));

    let mut spec = DeploySpec::new(src.path().to_str().unwrap(), "site", "agent:ember");
    spec.build_override = Some(BuildPlan::Static {
        publish_dir: "public".to_string(),
    });
    let _ = BuildTier::default(); // (the override path is tier-agnostic for static)

    let receipt = deploy_in_memory_blocking(engine, &spec, "deploy-override-1").expect("deploy");
    assert_eq!(receipt.build_plan, "static");
    let resp = registry.resolve("site.example.com", &WebRequest::get("/"));
    assert!(resp.body_str().contains("from public/"));
}
