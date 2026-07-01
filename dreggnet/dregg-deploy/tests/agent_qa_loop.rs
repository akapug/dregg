//! The **self-verifying coding/ops agent loop**, end to end through real pieces.
//!
//! This proves the AGENT TOOLKIT closes the loop: an agent deployed with a
//! `{run_tests, verify_deploy, check_health}` cap bundle
//!   1. has a real artifact to QA — a site deployed (clone → build → publish) into
//!      a signed registry, yielding a re-witnessable [`SiteReceiptBundle`];
//!   2. **runs the tests** in a cap-bounded compute tier (the `run_tests` tool over
//!      the `dreggnet-exec` wasm sandbox) and gets a real pass/fail;
//!   3. **verifies the deploy** with the REAL `dreggnet_webapp::verify_site_bundle`
//!      (the served bytes re-hash to the committed root + the receipt chain is
//!      intact), wired behind the cap-gated `invoke` rail as the `verify_deploy`
//!      tool;
//!   4. **checks health** (the monitoring tool);
//! and the WHOLE QA/ops sequence — every verdict bound into a receipt — re-witnesses
//! with `verify_agent_run`, without trusting the host.
//!
//! Teeth: a tool not in the bundle is refused; a deploy whose served bytes were
//! tampered makes `verify_deploy` return a real (receipted) FAIL.

use std::process::Command;
use std::sync::Arc;

use dregg_deploy::{DeployEngine, DeploySpec, deploy_in_memory_blocking};
use dreggnet_exec::CapTier;
use dreggnet_exec::agent::{AgentAction, AgentCloud, AgentSpec, PlannedBrain, verify_agent_run};
use dreggnet_exec::agent_toolkit::{HealthSnapshot, PolyanaToolkit, Toolkit};
use dreggnet_webapp::hosting::SiteRegistry;
use dreggnet_webapp::verify::{SiteReceiptBundle, verify_site_bundle};

/// Build a tiny local git repo with one commit (the deploy source).
fn fixture_repo(files: &[(&str, &str)]) -> tempfile::TempDir {
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
        std::fs::write(p.join(path), body).unwrap();
    }
    run(&["add", "-A"]);
    run(&["commit", "-q", "-m", "fixture"]);
    dir
}

/// Deploy a fixture site into a signed registry and return (bundle, owner_key).
fn deploy_signed_site(seed: [u8; 32], name: &str) -> (SiteReceiptBundle, [u8; 32]) {
    let src = fixture_repo(&[("index.html", "<!doctype html><h1>deployed + verified</h1>")]);
    let registry = Arc::new(SiteRegistry::signed(seed));
    let workroot = tempfile::tempdir().unwrap();
    let engine = Arc::new(DeployEngine::new(workroot.path(), registry.clone()));
    let spec = DeploySpec::new(src.path().to_str().unwrap(), name, "agent:ember");
    deploy_in_memory_blocking(engine, &spec, "deploy-qa-1").expect("deploy");
    let bundle = registry
        .site_bundle(name)
        .expect("a signed registry yields a bundle");
    let owner_key = registry
        .receipt_signer()
        .expect("signed registry has a signer");
    (bundle, owner_key)
}

/// A spec granting the QA/ops tools + the agent's own /deploy cell.
fn qa_spec(id: &str, budget: i64, services: &[&str]) -> AgentSpec {
    let mut s = AgentSpec::new(id, budget);
    s.services = services.iter().map(|s| s.to_string()).collect();
    s.cells = vec!["/deploy".to_string()];
    s
}

/// A green test suite (0 failures) as a core-module WAT for the `run_tests` tool.
const GREEN_SUITE: &str = "(module (func (export \"run\") (result i32) (i32.const 0)))";

#[test]
fn self_verifying_agent_qa_loop_over_a_real_deploy() {
    // A real deploy → a re-witnessable bundle + the owner key (the trust anchor).
    let (bundle, owner_key) = deploy_signed_site([55u8; 32], "blog");

    // The toolkit wires DreggNet's existing pieces as invoke-able tools:
    //  · run_tests   → the dreggnet-exec compute tier (real sandboxed run);
    //  · verify_deploy → the REAL dreggnet_webapp::verify_site_bundle (no re-impl);
    //  · check_health → a monitoring probe.
    let verify_bundle = bundle.clone();
    let toolkit = Toolkit::new()
        .with_run_tests_in("run_tests", "wat", GREEN_SUITE, CapTier::Sandboxed)
        .with_verify_deploy("verify_deploy", move || {
            verify_site_bundle(&verify_bundle, Some(owner_key))
                .map(|v| {
                    format!(
                        "{} ({} assets) @root {}",
                        v.name, v.asset_count, v.content_root
                    )
                })
                .map_err(|e| e.to_string())
        })
        .with_check_health("check_health", || {
            HealthSnapshot::healthy("node up · 0 divergence · Σδ=0")
        });

    // Deploy the agent with the full QA/ops bundle and run: deploy → test →
    // verify → monitor.
    let cloud = AgentCloud::from_seed([66u8; 32]);
    let handle = cloud
        .deploy(&qa_spec(
            "agent:devops",
            20,
            &["run_tests", "verify_deploy", "check_health"],
        ))
        .unwrap();
    let plan = vec![
        AgentAction::CellWrite {
            path: "/deploy".into(),
            value: "site:blog".into(),
        },
        AgentAction::Invoke {
            service: "run_tests".into(),
        },
        AgentAction::Invoke {
            service: "verify_deploy".into(),
        },
        AgentAction::Invoke {
            service: "check_health".into(),
        },
    ];
    let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);

    // The whole QA/ops sequence ran, was metered, and is receipted.
    assert_eq!(report.admitted, 4, "deploy + 3 QA/ops calls");
    assert_eq!(report.consumed, 4);
    assert_eq!(report.receipts.len(), 4);

    // Every verdict — including the REAL deploy verification — passed.
    let results = report.tool_results();
    assert_eq!(results.len(), 3);
    assert!(report.all_tools_passed(), "QA/ops all green: {results:?}");
    let (_, verify_ok, verify_msg) = results
        .iter()
        .find(|(a, ..)| a == "invoke:verify_deploy")
        .expect("verify_deploy ran");
    assert!(
        verify_ok,
        "the real deploy verification passed: {verify_msg}"
    );
    assert!(
        verify_msg.contains("blog"),
        "the verdict names the verified site: {verify_msg}"
    );

    // The whole self-verifying loop re-witnesses without trusting the host.
    let v = verify_agent_run(&report).expect("the self-QA loop re-witnesses");
    assert_eq!(v.actions, 4);
}

#[test]
fn verify_deploy_tool_catches_a_tampered_deploy() {
    let (mut bundle, owner_key) = deploy_signed_site([77u8; 32], "blog");
    // A lying host serves a tampered index.html — the recomputed content root
    // moves away from the signed one, so the REAL verifier refuses it.
    let asset = bundle.content.assets.get_mut("/index.html").unwrap();
    asset.body = b"<h1>OWNED BY THE HOST</h1>".to_vec();

    let verify_bundle = bundle.clone();
    let toolkit = Toolkit::new().with_verify_deploy("verify_deploy", move || {
        verify_site_bundle(&verify_bundle, Some(owner_key))
            .map(|v| v.name)
            .map_err(|e| e.to_string())
    });

    let cloud = AgentCloud::from_seed([88u8; 32]);
    let handle = cloud
        .deploy(&qa_spec("agent:devops", 10, &["verify_deploy"]))
        .unwrap();
    let plan = vec![AgentAction::Invoke {
        service: "verify_deploy".into(),
    }];
    let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);

    // The QA ran (and was charged + receipted), and the verdict is a real FAIL.
    assert_eq!(report.admitted, 1);
    assert_eq!(report.receipts.len(), 1);
    let (_, ok, summary) = &report.tool_results()[0];
    assert!(!ok, "the tampered deploy is caught: {summary}");
    assert!(summary.contains("FAILED"), "names the failure: {summary}");
    // A caught-tamper verdict is itself a sound, re-witnessable receipt.
    verify_agent_run(&report).expect("the fail receipt re-witnesses");
}

#[test]
fn a_tool_outside_the_bundle_is_refused() {
    let (bundle, owner_key) = deploy_signed_site([99u8; 32], "blog");
    let verify_bundle = bundle.clone();
    let toolkit = Toolkit::new()
        .with_verify_deploy("verify_deploy", move || {
            verify_site_bundle(&verify_bundle, Some(owner_key))
                .map(|v| v.name)
                .map_err(|e| e.to_string())
        })
        .with_check_health("check_health", || HealthSnapshot::healthy("ok"));

    // The bundle grants ONLY check_health — not verify_deploy.
    let cloud = AgentCloud::from_seed([100u8; 32]);
    let handle = cloud
        .deploy(&qa_spec("agent:narrow", 10, &["check_health"]))
        .unwrap();
    let plan = vec![
        AgentAction::Invoke {
            service: "check_health".into(),
        }, // granted
        AgentAction::Invoke {
            service: "verify_deploy".into(),
        }, // NOT granted → refused
    ];
    let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);

    assert_eq!(report.admitted, 1, "only the granted tool ran");
    assert_eq!(
        report.cap_refused, 1,
        "the ungranted verify_deploy is refused"
    );
    assert_eq!(report.receipts.len(), 1, "the refused call left no receipt");
}
