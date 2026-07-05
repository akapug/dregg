//! **The prototype→devnet end-to-end proof: a real grain, on the real surfaces.**
//!
//! This drives the whole welded path with NO in-process stubs for the load-bearing
//! parts:
//!
//! 1. a **real signed `.spk`** is parsed + Ed25519-verified (App ID = the signing
//!    key), its manifest decoded, its grain spec derived;
//! 2. the grain is a **dregg cell** with a lifecycle (create → wake under a funded
//!    lease → sleep/checkpoint → wake), its `/var` a committed umem heap;
//! 3. its powerbox capability is a **real `dreggnet-webauth` `dga1_` credential**
//!    (ed25519 caveat-chain, host-rooted, attenuating-only);
//! 4. each request is served through the **real `dreggnet-webapp` site surface**
//!    (`WebRequest`/`WebResponse`, the `<name>.example.com` wildcard routing the
//!    httpe `dreggnet-gateway` adopts), with `X-Sandstorm-Permissions` derived from
//!    the cap;
//! 5. the grain handler **runs on the real `dreggnet-exec` compute tier**
//!    (`CapTier::Caged` — a real `python3` subprocess; the enforcement level is
//!    surfaced);
//! 6. the served snapshot is **published + re-witnessed** through the real, cap-gated
//!    `SiteRegistry::publish` turn.
//!
//! Executing an *arbitrary untrusted `.spk` chroot* on the live tier is the
//! REVIEWED-GO devnet step (the Firecracker microVM + SBX deny-default make it safe);
//! this proof runs the representative permissioned-notes app as the in-sandbox handler
//! through the same real-tier dispatch that step plugs into. The test skips cleanly
//! where `python3` is not on PATH (the real tier needs it).

use ed25519_dalek::SigningKey;

use dreggnet_webapp::{HttpMethod, SiteRegistry, WebRequest};

use sandstorm_bridge::cell::Umem;
use sandstorm_bridge::exec_workload::ExecGrainWorkload;
use sandstorm_bridge::grain::{GrainCell, GrainState, SandboxTier};
use sandstorm_bridge::manifest::SpkManifest;
use sandstorm_bridge::serving::{publish_grain_snapshot, serve_grain, GrainSession};
use sandstorm_bridge::spk::{File, Spk, SpkBuilder};
use sandstorm_bridge::webauth_rail::HostAuthority;

fn python3_available() -> bool {
    std::process::Command::new("python3")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// A genuinely-signed Etherpad-shape `.spk` (real Ed25519 signature; the App ID is
/// the signing key). The reader/manifest/grain path runs against the real format.
fn etherpad_spk() -> Vec<u8> {
    let manifest = r#"{
      "app_id": "overridden-by-the-signing-key",
      "app_title": "Etherpad",
      "app_version": 33,
      "marketing_version": "1.8.18",
      "continue_command": { "argv": ["/sandstorm-http-bridge", "8000", "--", "/start.sh"] },
      "bridge_config": {
        "api_port": 8000,
        "permissions": ["view", "edit"],
        "roles": [
          { "title": "editor", "permissions": ["view", "edit"] },
          { "title": "viewer", "permissions": ["view"] }
        ]
      }
    }"#;
    SpkBuilder::new()
        .manifest_json(manifest)
        .file(File::executable("start.sh", b"#!/bin/sh\n".to_vec()))
        .pack(&SigningKey::from_bytes(&[7u8; 32]))
}

#[test]
fn a_real_grain_runs_end_to_end_on_the_real_surfaces() {
    if !python3_available() {
        eprintln!("skip: no python3 on PATH (the real exec tier needs it)");
        return;
    }

    // (1) Parse + verify the real signed .spk; derive the grain spec.
    let spk = Spk::parse(&etherpad_spk()).expect("verified .spk");
    let manifest = SpkManifest::from_spk(&spk).expect("manifest from .spk");
    assert_eq!(manifest.app_title, "Etherpad");
    assert_eq!(manifest.app_id, spk.app_id(), "App ID is the signing key");
    let spec = manifest.grain_spec();
    assert_eq!(
        spec.tier,
        SandboxTier::Caged,
        "an http-bridge app routes to Caged"
    );
    let declared = spec.declared_permissions.clone();
    assert_eq!(declared, vec!["view".to_string(), "edit".to_string()]);

    // (2) The grain is a dregg cell with a funded lifecycle.
    let grain_id = "cell:etherpad";
    let mut grain = GrainCell::create(grain_id, "u:alice", spec);
    assert_eq!(grain.state, GrainState::Created);
    grain.wake(true).expect("funded wake");
    assert_eq!(grain.state, GrainState::Running);

    // (3) Powerbox: a real dga1_ capability, host-rooted, sealed to alice.
    let host = HostAuthority::from_seed([42u8; 32]);
    let alice_token = host
        .mint_grain_cap(grain_id, "u:alice", &["view", "edit"], None)
        .encode();
    assert!(alice_token.starts_with("dga1_"), "the real cap wire");

    // (5) The grain handler on the real exec tier.
    let workload = ExecGrainWorkload::notes(SandboxTier::Caged);
    let mut var = Umem::new();

    // (4)+(5) Serve a write through the real webapp surface → real exec tier.
    let alice = GrainSession {
        user_id: "u:alice",
        username: "Alice",
        session_id: "s:1",
        presenter_subject: "u:alice",
        token: &alice_token,
    };
    let post = serve_grain(
        "etherpad.example.com",
        &WebRequest::new(HttpMethod::Post, "/pad/welcome", b"hello dregg".to_vec()),
        grain_id,
        &declared,
        &alice,
        &host.public(),
        &workload,
        &mut var,
        1000,
    );
    assert_eq!(post.status, 200, "the write was served");
    // The enforcement level the real tier achieved is surfaced (never hidden).
    let enforcement = workload.last_enforcement().expect("an enforcement level");
    assert!(!enforcement.is_empty());

    // The grain's /var (the cell umem) carries the write; checkpoint it (sleep).
    let checkpoint = var.commit();
    grain.meter_period(1).expect("metered uptime");
    grain
        .sleep(checkpoint.0.clone())
        .expect("sleep checkpoints the umem");
    assert_eq!(grain.state, GrainState::Sleeping);

    // (2) Wake again; the data survived the checkpoint (same committed root).
    grain.wake(true).expect("re-wake");
    assert_eq!(grain.data_root.as_deref(), Some(checkpoint.0.as_str()));

    // (3) A viewer holds a real attenuated dga1_ cap (view-only).
    let bob_token = host
        .mint_grain_cap(grain_id, "u:bob", &["view"], None)
        .encode();
    let bob = GrainSession {
        user_id: "u:bob",
        username: "bob",
        session_id: "s:2",
        presenter_subject: "u:bob",
        token: &bob_token,
    };
    // (4)+(5) The viewer reads the note back through the whole real path.
    let get = serve_grain(
        "etherpad.example.com",
        &WebRequest::new(HttpMethod::Get, "/pad/welcome", Vec::new()),
        grain_id,
        &declared,
        &bob,
        &host.public(),
        &workload,
        &mut var,
        1000,
    );
    assert_eq!(get.status, 200);
    assert_eq!(
        get.body, b"hello dregg",
        "the grain state survived sleep/wake"
    );

    // The viewer cannot write (no `edit` facet on the real cap rail) → 403.
    let denied = serve_grain(
        "etherpad.example.com",
        &WebRequest::new(HttpMethod::Post, "/pad/welcome", b"tamper".to_vec()),
        grain_id,
        &declared,
        &bob,
        &host.public(),
        &workload,
        &mut var,
        1000,
    );
    assert_eq!(denied.status, 403);

    // (6) Verifiable serving: publish the grain's served bytes as a hosted cell
    // through the real, cap-gated, receipted publish turn, and re-witness it.
    let registry = SiteRegistry::new();
    let body = get.body.clone();
    let receipt = publish_grain_snapshot(&registry, "u:alice", "etherpad", "/pad/welcome", body)
        .expect("publish the served snapshot");
    assert_eq!(receipt.owner, "u:alice");
    let rewitnessed = registry.serve_site(
        "etherpad",
        &WebRequest::new(HttpMethod::Get, "/pad/welcome", Vec::new()),
    );
    assert_eq!(rewitnessed.status, 200);
    assert_eq!(rewitnessed.body, b"hello dregg");
}

/// **The real catalog `.spk`, installed and served through the real surfaces.**
///
/// Uses the real `fixtures/sample.spk` ("Simple Todos", a Meteor http-bridge app):
/// parse + Ed25519/SHA-512 verify → decode the real capnp manifest → derive the grain
/// spec (Caged tier, ingress 8000) → create a grain cell → serve a request through the
/// real `dreggnet-webapp` surface on the real `dreggnet-exec` Caged tier, with a real
/// `dga1_` powerbox cap gating access (a forged cap is refused).
///
/// Honest scope: executing the package's *own* untrusted Meteor chroot on the live tier
/// is the REVIEWED-GO devnet step (the Firecracker microVM + SBX deny-default make it
/// safe). This proof runs the representative permissioned-notes handler **as** the
/// in-sandbox app through the same real-tier dispatch that step plugs into, driven by the
/// real package's verified identity and spec. The package declares its permission model
/// via its (default here) `sandstorm-http-bridge-config` + the bridge's implicit
/// defaults; we serve with a representative facet set.
#[test]
fn a_real_catalog_spk_installs_and_serves_through_the_real_surfaces() {
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("sample.spk");
    let bytes = match std::fs::read(&path) {
        Ok(b) => b,
        Err(_) => {
            eprintln!("skip: no real fixture at {}", path.display());
            return;
        }
    };
    if !python3_available() {
        eprintln!("skip: no python3 on PATH (the real exec tier needs it)");
        return;
    }

    // (1) Install: parse + verify the REAL package, decode its real capnp manifest.
    let spk = Spk::parse(&bytes).expect("the real catalog .spk verifies");
    let manifest = SpkManifest::from_spk(&spk).expect("decode the real capnp manifest");
    assert_eq!(manifest.app_title, "Simple Todos");
    assert_eq!(manifest.app_id, spk.app_id());
    let spec = manifest.grain_spec();
    // A real http-bridge app routes to the Caged jail with its recovered ingress port.
    assert_eq!(spec.tier, SandboxTier::Caged);
    assert_eq!(spec.ingress_port, Some(8000));

    // (2) Create the grain cell for this real app.
    let grain_id = "cell:simple-todos";
    let mut grain = GrainCell::create(grain_id, "u:alice", spec);
    grain.wake(true).expect("funded wake");
    assert_eq!(grain.state, GrainState::Running);

    // (3) A real dga1_ powerbox cap, host-rooted, sealed to alice. The representative
    //     handler declares view/edit; the real cap gates which the presenter exercises.
    let host = HostAuthority::from_seed([77u8; 32]);
    let declared = vec!["view".to_string(), "edit".to_string()];
    let alice_token = host
        .mint_grain_cap(grain_id, "u:alice", &["view", "edit"], None)
        .encode();
    let alice = GrainSession {
        user_id: "u:alice",
        username: "Alice",
        session_id: "s:1",
        presenter_subject: "u:alice",
        token: &alice_token,
    };
    let workload = ExecGrainWorkload::notes(SandboxTier::Caged);
    let mut var = Umem::new();

    // (4)+(5) Serve a write through the real webapp surface → real exec Caged tier.
    let post = serve_grain(
        "simple-todos.example.com",
        &WebRequest::new(HttpMethod::Post, "/todo/1", b"buy milk".to_vec()),
        grain_id,
        &declared,
        &alice,
        &host.public(),
        &workload,
        &mut var,
        1000,
    );
    assert_eq!(post.status, 200, "the real-tier serve succeeded");
    assert!(!workload.last_enforcement().unwrap_or_default().is_empty());
    grain.touch(1000);

    // Read it back through the whole real path.
    let get = serve_grain(
        "simple-todos.example.com",
        &WebRequest::new(HttpMethod::Get, "/todo/1", Vec::new()),
        grain_id,
        &declared,
        &alice,
        &host.public(),
        &workload,
        &mut var,
        1000,
    );
    assert_eq!(get.status, 200);
    assert_eq!(get.body, b"buy milk");

    // (powerbox) A forged cap (not host-rooted) gates access shut → 403.
    let attacker = HostAuthority::from_seed([211u8; 32]);
    let forged = attacker
        .mint_grain_cap(grain_id, "u:mallory", &["view", "edit"], None)
        .encode();
    let mallory = GrainSession {
        user_id: "u:mallory",
        username: "mallory",
        session_id: "s:x",
        presenter_subject: "u:mallory",
        token: &forged,
    };
    let denied = serve_grain(
        "simple-todos.example.com",
        &WebRequest::new(HttpMethod::Post, "/todo/pwn", b"x".to_vec()),
        grain_id,
        &declared,
        &mallory,
        &host.public(),
        &workload,
        &mut var,
        1000,
    );
    assert_eq!(denied.status, 403, "the forged powerbox cap is refused");

    // (6) Publish the served snapshot as a re-witnessable hosted cell.
    let registry = SiteRegistry::new();
    let receipt = publish_grain_snapshot(
        &registry,
        "u:alice",
        "simple-todos",
        "/todo/1",
        get.body.clone(),
    )
    .expect("publish the served snapshot");
    assert_eq!(receipt.owner, "u:alice");
}

/// **Multi-grain isolation:** two grains of the *same* app are independent cells with
/// independent `/var` heaps, and a powerbox cap minted for one grain is inert at the
/// other (the `grain` caveat fails) — no cross-grain read.
#[test]
fn two_grains_of_the_same_app_are_isolated() {
    if !python3_available() {
        eprintln!("skip: no python3 on PATH (the real exec tier needs it)");
        return;
    }
    // Both grains run the same app (same verified spec); they differ only by cell id.
    let spec = SpkManifest::from_spk(&Spk::parse(&etherpad_spk()).unwrap())
        .unwrap()
        .grain_spec();
    assert_eq!(spec.tier, SandboxTier::Caged);
    let host = HostAuthority::from_seed([88u8; 32]);
    let declared = vec!["view".to_string(), "edit".to_string()];
    let workload = ExecGrainWorkload::notes(SandboxTier::Caged);

    let grain_a = "cell:todos-a";
    let grain_b = "cell:todos-b";
    let mut var_a = Umem::new();
    let mut var_b = Umem::new();

    // Alice owns grain A; Bob owns grain B (same app, distinct cells).
    let a_token = host
        .mint_grain_cap(grain_a, "u:alice", &["view", "edit"], None)
        .encode();
    let a_session = GrainSession {
        user_id: "u:alice",
        username: "Alice",
        session_id: "s:a",
        presenter_subject: "u:alice",
        token: &a_token,
    };

    // Alice writes a secret into grain A's /var.
    let w = serve_grain(
        "todos-a.example.com",
        &WebRequest::new(HttpMethod::Post, "/secret", b"alice-private".to_vec()),
        grain_a,
        &declared,
        &a_session,
        &host.public(),
        &workload,
        &mut var_a,
        1000,
    );
    assert_eq!(w.status, 200);

    // grain B's /var never saw it — the heaps are independent cells.
    assert!(var_b.is_empty());
    assert_eq!(var_a.get("notes/secret"), Some(&b"alice-private"[..]));

    // Alice's grain-A cap is inert at grain B (the `grain` caveat fails) → 403.
    let cross = serve_grain(
        "todos-b.example.com",
        &WebRequest::new(HttpMethod::Get, "/secret", Vec::new()),
        grain_b,
        &declared,
        &a_session, // alice's cap is bound to grain A
        &host.public(),
        &workload,
        &mut var_b,
        1000,
    );
    assert_eq!(
        cross.status, 403,
        "a cap for grain A grants nothing at grain B"
    );
    assert!(var_b.is_empty());
}
