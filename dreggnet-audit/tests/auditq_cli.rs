//! End-to-end tests for the `auditq` bin: build a fixture JSONL store through
//! the crate's OWN types + writer (no hand-rolled schema), then drive the real
//! binary (`CARGO_BIN_EXE_auditq`) and assert query / correlate / stats /
//! replay behavior on its actual output.

use dreggnet_audit::{
    Actor, AuditEvent, AuditLog, AuditOutcome, Decision, Input, Surface, find_leak,
};
use std::path::PathBuf;
use std::process::{Command, Output};

const TURN_HASH_A: &str = "aa11aa11aa11aa11aa11aa11aa11aa11aa11aa11aa11aa11aa11aa11aa11aa11";
const TURN_HASH_B: &str = "bb22bb22bb22bb22bb22bb22bb22bb22bb22bb22bb22bb22bb22bb22bb22bb22";

/// Fixture: two sessions across two platforms — a web dungeon session with a
/// landed turn, a refusal, and a gated act; and a telegram market press that
/// landed. Deterministic correlation ids so assertions can name them.
fn write_fixture(dir: &PathBuf) {
    let log = AuditLog::open(dir, "fixture");
    let mut evs = vec![
        AuditEvent::new(
            "web",
            Actor::asserted("anon").with_identity("d1".repeat(32)),
            Surface::Http,
            Input::new("GET /offerings/{key}/session/{id}", serde_json::Value::Null),
        )
        .correlated("corr-view-1")
        .in_session(Some("dungeon".into()), Some("dungeon-web".into())),
        AuditEvent::new(
            "web",
            Actor::asserted("anon").with_identity("d1".repeat(32)),
            Surface::Http,
            Input::new(
                "POST /offerings/{key}/session/{id}/act",
                serde_json::json!({"turn": "fire", "arg": "goblin"}),
            ),
        )
        .correlated("corr-fire-2")
        .in_session(Some("dungeon".into()), Some("dungeon-web".into()))
        .with_outcome(AuditOutcome::Landed {
            turn_hash: TURN_HASH_A.into(),
            ended: false,
        }),
        AuditEvent::new(
            "web",
            Actor::asserted("anon").with_identity("d1".repeat(32)),
            Surface::Http,
            Input::new(
                "POST /offerings/{key}/session/{id}/act",
                serde_json::json!({"turn": "bid"}),
            ),
        )
        .correlated("corr-refuse-3")
        .in_session(Some("dungeon".into()), Some("dungeon-web".into()))
        .with_decision(Decision::refused("not_offered")),
        AuditEvent::new(
            "tg-miniapp",
            Actor::initdata_verified("99", Some("e2".repeat(32))),
            Surface::InitData,
            Input::new(
                "POST /tg/offerings/{key}/session/{id}/act",
                serde_json::json!({"turn": "go", "arg": "north"}),
            ),
        )
        .correlated("corr-gate-4")
        .in_session(Some("dungeon".into()), Some("dungeon-web".into()))
        .with_decision(Decision::gated("initdata:stale")),
        AuditEvent::new(
            "telegram",
            Actor::custodial("424242", "f3".repeat(32)),
            Surface::Callback,
            Input::new(
                "offering:bid",
                serde_json::json!({"turn": "bid", "arg": "3"}),
            ),
        )
        .correlated("corr-market-5")
        .in_session(Some("market".into()), Some("market-tg".into()))
        .with_outcome(AuditOutcome::Landed {
            turn_hash: TURN_HASH_B.into(),
            ended: true,
        }),
    ];
    // Deterministic, strictly increasing timestamps (fixture ordering is the
    // ground truth the tool must reproduce).
    for (i, ev) in evs.iter_mut().enumerate() {
        ev.ts_ms = 1_784_380_000_000 + (i as u64) * 1000;
    }
    for ev in &evs {
        log.emit(ev);
    }
    log.sync();
}

fn fixture_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "auditq-cli-{tag}-{}-{}",
        std::process::id(),
        dreggnet_audit::correlation_id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    write_fixture(&dir);
    dir
}

fn auditq(dir: &PathBuf, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_auditq"))
        .arg(args[0])
        .args(["--dir", dir.to_str().unwrap()])
        .args(&args[1..])
        .env_remove("DREGG_AUDIT_DIR")
        .output()
        .expect("run auditq")
}

fn stdout(out: &Output) -> String {
    assert!(
        out.status.success(),
        "auditq failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout.clone()).unwrap()
}

#[test]
fn query_filters_by_actor_decision_offering_and_time() {
    let dir = fixture_dir("query");

    // Actor by dregg_identity matches the same events as by platform_id.
    let by_ident = stdout(&auditq(
        &dir,
        &["query", "--actor", &"d1".repeat(32), "--json"],
    ));
    assert_eq!(by_ident.lines().count(), 3, "web actor made 3 interactions");
    let by_pid = stdout(&auditq(&dir, &["query", "--actor", "anon", "--json"]));
    assert_eq!(by_pid, by_ident);

    // Decision + reason.
    let refused = stdout(&auditq(
        &dir,
        &[
            "query",
            "--decision",
            "refused",
            "--reason",
            "not_offered",
            "--json",
        ],
    ));
    assert_eq!(refused.lines().count(), 1);
    assert!(refused.contains("corr-refuse-3"));

    // Offering + platform.
    let market = stdout(&auditq(&dir, &["query", "--offering", "market", "--json"]));
    assert_eq!(market.lines().count(), 1);
    assert!(market.contains("\"platform\":\"telegram\""));

    // Outcome kind + turn-hash point lookup.
    let landed = stdout(&auditq(&dir, &["query", "--outcome", "landed", "--json"]));
    assert_eq!(landed.lines().count(), 2);
    let by_hash = stdout(&auditq(
        &dir,
        &["query", "--turn-hash", TURN_HASH_B, "--json"],
    ));
    assert_eq!(by_hash.lines().count(), 1);
    assert!(by_hash.contains("corr-market-5"));

    // Time range: only the first two fixture events (ts 0s and 1s offsets).
    let early = stdout(&auditq(
        &dir,
        &[
            "query",
            "--since",
            "1784380000000",
            "--until",
            "1784380001000",
            "--json",
        ],
    ));
    assert_eq!(early.lines().count(), 2);

    // Surface filter uses the serialized snake_case word.
    let initdata = stdout(&auditq(
        &dir,
        &["query", "--surface", "init_data", "--json"],
    ));
    assert_eq!(initdata.lines().count(), 1);
    assert!(initdata.contains("initdata:stale"));

    // --json is a strict passthrough: every line re-parses as an AuditEvent.
    for line in landed.lines() {
        let ev: AuditEvent = serde_json::from_str(line).expect("passthrough stays schema-true");
        assert!(matches!(ev.outcome, AuditOutcome::Landed { .. }));
    }

    // Pretty mode prints one line per match too (count via corr markers).
    let pretty = stdout(&auditq(&dir, &["query", "--decision", "gated"]));
    assert!(pretty.contains("gated(initdata:stale)"));
    assert!(pretty.contains("corr=corr-gate-4"));

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn correlate_resolves_correlation_session_and_turn_hash() {
    let dir = fixture_dir("correlate");

    // correlation_id → the single interaction.
    let one = stdout(&auditq(&dir, &["correlate", "corr-fire-2"]));
    assert!(one.contains("correlation_id = corr-fire-2"));
    assert!(one.contains("1 event(s)"));
    assert!(one.contains(TURN_HASH_A));

    // session_id → the full ordered chain with the receipt join surfaced.
    let sess = stdout(&auditq(&dir, &["correlate", "dungeon-web"]));
    assert!(sess.contains("session_id = dungeon-web (4 event(s)"));
    let idx = |needle: &str| {
        sess.find(needle)
            .unwrap_or_else(|| panic!("missing {needle}"))
    };
    // Recorded order is preserved.
    assert!(idx("corr-view-1") < idx("corr-fire-2"));
    assert!(idx("corr-fire-2") < idx("corr-refuse-3"));
    assert!(idx("corr-refuse-3") < idx("corr-gate-4"));
    // The receipt-correlation seam is named on the landed step.
    assert!(sess.contains(&format!("receipt join: turn_hash={TURN_HASH_A}")));
    assert!(sess.contains("GET /offerings/dungeon/session/dungeon-web/verify"));
    // The summary separates what reached the chain from what never did.
    assert!(sess.contains("1 landed (on-chain), 3 never reached the receipt chain"));

    // turn_hash → the envelope (receipt → human act direction).
    let join = stdout(&auditq(&dir, &["correlate", TURN_HASH_B]));
    assert!(join.contains("turn_hash (receipt → envelope)"));
    assert!(join.contains("424242[custodial]"));

    // Unknown ids fail loudly, not silently-empty.
    let miss = auditq(&dir, &["correlate", "no-such-id"]);
    assert!(!miss.status.success());
    assert!(String::from_utf8_lossy(&miss.stderr).contains("no event matches"));

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn stats_counts_decisions_offerings_surfaces() {
    let dir = fixture_dir("stats");
    let out = stdout(&auditq(&dir, &["stats", "--json"]));
    let v: serde_json::Value = serde_json::from_str(&out).unwrap();
    assert_eq!(v["events"], 5);
    assert_eq!(v["decision"]["routed"], 3);
    assert_eq!(v["decision"]["refused"], 1);
    assert_eq!(v["decision"]["gated"], 1);
    assert_eq!(v["decision_reasons"]["gated:initdata:stale"], 1);
    assert_eq!(v["outcome"]["landed"], 2);
    assert_eq!(v["outcome"]["none"], 3);
    assert_eq!(v["offering"]["dungeon"], 4);
    assert_eq!(v["offering"]["market"], 1);
    assert_eq!(v["surface"]["http"], 3);
    assert_eq!(v["platform"]["web"], 3);

    // Filters compose with stats (the "what is failing on web" read).
    let web = stdout(&auditq(&dir, &["stats", "--platform", "web", "--json"]));
    let v: serde_json::Value = serde_json::from_str(&web).unwrap();
    assert_eq!(v["events"], 3);
    assert_eq!(v["decision"]["refused"], 1);

    // Pretty mode renders the same counts.
    let pretty = stdout(&auditq(&dir, &["stats"]));
    assert!(pretty.contains("5 event(s)"));
    assert!(pretty.contains("refused"));
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn replay_emits_ordered_script_with_expectations_and_honest_scope() {
    let dir = fixture_dir("replay");

    let out = auditq(&dir, &["replay", "--session", "dungeon-web", "--json"]);
    let script = stdout(&out);
    let stderr = String::from_utf8_lossy(&out.stderr);

    // stdout is a pure JSONL script: header + 4 steps, every line parses.
    let lines: Vec<&str> = script.lines().collect();
    assert_eq!(lines.len(), 5);
    let header: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
    assert_eq!(header["replay_script"], 1);
    assert_eq!(header["steps"], 4);
    // The script names what a real re-drive additionally needs (no overclaim).
    let requires = header["requires"].as_array().unwrap();
    assert!(
        requires
            .iter()
            .any(|r| r.as_str().unwrap().contains("live host"))
    );
    assert!(
        requires
            .iter()
            .any(|r| r.as_str().unwrap().contains("re-signing keys"))
    );
    let steps: Vec<serde_json::Value> = lines[1..]
        .iter()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    // Ordered inputs with the recorded expectations attached.
    assert_eq!(steps[0]["seq"], 1);
    assert_eq!(steps[1]["input"]["detail"]["turn"], "fire");
    assert_eq!(steps[1]["expect"]["outcome"]["turn_hash"], TURN_HASH_A);
    assert_eq!(steps[2]["expect"]["decision"]["reason"], "not_offered");
    assert_eq!(steps[3]["expect"]["decision"]["kind"], "gated");
    // The honesty note rides stderr so stdout stays machine-clean.
    assert!(stderr.contains("does not") || stderr.contains("Re-driving it needs"));

    // --until-corr truncates the script one step after the named event.
    let cut = stdout(&auditq(
        &dir,
        &[
            "replay",
            "--session",
            "dungeon-web",
            "--until-corr",
            "corr-fire-2",
            "--json",
        ],
    ));
    let header: serde_json::Value = serde_json::from_str(cut.lines().next().unwrap()).unwrap();
    assert_eq!(header["steps"], 2);

    // Pretty mode carries the same honesty note inline.
    let pretty = stdout(&auditq(&dir, &["replay", "--correlation", "corr-market-5"]));
    assert!(pretty.contains("1 step(s)"));
    assert!(pretty.contains("expect: decision=routed"));
    assert!(pretty.contains(&format!("outcome=landed turn={TURN_HASH_B} ended=true")));
    assert!(pretty.contains("credentials the audit log deliberately omits"));

    // Missing scope is an error, not an accidental full-store replay.
    let bad = auditq(&dir, &["replay"]);
    assert!(!bad.status.success());

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn correlate_joins_across_per_process_files_in_one_dir() {
    // The whole point of per-process filenames: two SERVICES share ONE
    // correlate-able dir (distinct files, never contending on one) and auditq
    // still joins a chain that spans them. Two `AuditLog`s opened for different
    // platforms in the same dir land in DIFFERENT `audit-DATE.<platform>-<pid>.NN`
    // files — this is the cross-process shape a real deploy produces.
    let dir = std::env::temp_dir().join(format!(
        "auditq-cli-xproc-{}-{}",
        std::process::id(),
        dreggnet_audit::correlation_id()
    ));
    std::fs::create_dir_all(&dir).unwrap();

    let shared_sess = "shared-across-services";

    // Service A (web): an earlier landed act on the shared session.
    {
        let web = AuditLog::open(&dir, "web");
        let mut ev = AuditEvent::new(
            "web",
            Actor::asserted("anon"),
            Surface::Http,
            Input::new(
                "POST /offerings/dungeon/session/x/act",
                serde_json::json!({ "turn": "fire" }),
            ),
        )
        .correlated("corr-web-A")
        .in_session(Some("dungeon".into()), Some(shared_sess.into()))
        .with_outcome(AuditOutcome::Landed {
            turn_hash: TURN_HASH_A.into(),
            ended: false,
        });
        ev.ts_ms = 1_784_380_000_000;
        web.emit(&ev);
        web.sync();
    }

    // Service B (telegram): a later act on the SAME session id, different process.
    {
        let tg = AuditLog::open(&dir, "telegram");
        let mut ev = AuditEvent::new(
            "telegram",
            Actor::custodial("42", "f3".repeat(32)),
            Surface::Callback,
            Input::new("offering:fire", serde_json::json!({ "turn": "fire" })),
        )
        .correlated("corr-tg-B")
        .in_session(Some("dungeon".into()), Some(shared_sess.into()));
        ev.ts_ms = 1_784_380_002_000;
        tg.emit(&ev);
        tg.sync();
    }

    // The two services wrote SEPARATE segment files in the one shared dir.
    let files = std::fs::read_dir(&dir)
        .unwrap()
        .flatten()
        .filter(|e| {
            e.file_name()
                .to_str()
                .is_some_and(|n| n.starts_with("audit-") && n.ends_with(".jsonl"))
        })
        .count();
    assert_eq!(
        files, 2,
        "web and telegram wrote SEPARATE per-process files in the shared dir"
    );

    // auditq correlate joins the chain ACROSS both files, ordered by time.
    let out = stdout(&auditq(&dir, &["correlate", shared_sess]));
    assert!(
        out.contains("session_id = shared-across-services (2 event(s)"),
        "the cross-service chain has both events: {out}"
    );
    let iw = out
        .find("corr-web-A")
        .expect("web event in the joined chain");
    let it = out
        .find("corr-tg-B")
        .expect("telegram event in the joined chain");
    assert!(
        iw < it,
        "the joined chain is ordered by time across the two service files"
    );

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn tool_output_carries_no_secret_shaped_values() {
    // The store schema is secret-free by design; the tool must not ADD any.
    // Denylist the env-shaped values a regressed build might leak.
    let dir = fixture_dir("hygiene");
    let fake_token = "MTIzNDU2Nzg5.FIXTURE.token-value";
    let fake_secret = "ee".repeat(32);
    for args in [
        vec!["query", "--json"],
        vec!["correlate", "dungeon-web"],
        vec!["stats"],
        vec!["replay", "--session", "dungeon-web", "--json"],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_auditq"))
            .arg(args[0])
            .args(["--dir", dir.to_str().unwrap()])
            .args(&args[1..])
            .env("TELEGRAM_BOT_TOKEN", fake_token)
            .env("BOT_SECRET", &fake_secret)
            .output()
            .unwrap();
        let all = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(find_leak(&all, &[fake_token, fake_secret.as_str()]), None);
    }
    std::fs::remove_dir_all(&dir).ok();
}
