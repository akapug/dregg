//! `mldsa_seed_signing_refusal` answers what the gate WILL do, on the shipping path.
//!
//! A host that cannot use the gate's `abort()` as a refusal (wasm32 traps it as a message-less
//! `RuntimeError: unreachable`) asks this predicate first and refuses with a typed error. That
//! is only sound if the predicate and the gate agree in every configuration, so each case below
//! reads the predicate AND then performs the sign it is about, in a re-executed child whose
//! environment the parent controls (the env opt-in is read once per process, so a subprocess is
//! the only way to vary it). `None` must be followed by a completed sign; `Some(site)` must be
//! followed by the abort, never by a signature.

use std::process::Command;

const ROLE: &str = "DREGG_PQ_SEED_SIGNING_PROBE_ROLE";

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// A stand-in keygen core (the crate expansion behind a `fn` pointer), so the KEYGEN direction
/// is answered and only SIGN is left to the gate — the same test double `unaudited_refusal.rs`
/// uses to reach the sign gate.
fn install_stand_in_keygen_core() {
    use fips204::ml_dsa_65;
    use fips204::traits::{KeyGen as _, SerDes as _};
    dregg_pq::install_lean_keygen_core_real(|wire| {
        let bytes: Vec<u8> = (0..wire.len() / 2)
            .map(|i| u8::from_str_radix(&wire[2 * i..2 * i + 2], 16).ok())
            .collect::<Option<Vec<u8>>>()?;
        let seed: [u8; 32] = bytes.try_into().ok()?;
        let (pk, sk) = ml_dsa_65::KG::keygen_from_seed(&seed);
        Some(format!(
            "{} {}",
            hex(&pk.into_bytes()),
            hex(&sk.into_bytes())
        ))
    });
}

fn child_body(role: &str) -> ! {
    match role {
        "probe" => {}
        "probe-with-keygen" => install_stand_in_keygen_core(),
        other => {
            eprintln!("CHILD: unknown role {other}");
            std::process::exit(3);
        }
    }
    eprintln!("PROBE {:?}", dregg_pq::mldsa_seed_signing_refusal());
    let sig = dregg_pq::ml_dsa_sign_from_seed(&[7u8; 32], b"ctx", b"msg");
    eprintln!("SIGNED {:?}", sig.map(|s| s.len()));
    std::process::exit(0);
}

fn run_child(role: &str, allow_unaudited: bool, require_lean: bool) -> (bool, String) {
    let mut cmd = Command::new(std::env::current_exe().expect("current_exe"));
    cmd.arg("child_dispatcher")
        .arg("--exact")
        .arg("--nocapture")
        .arg("--test-threads=1")
        .env(ROLE, role);
    if allow_unaudited {
        cmd.env("DREGG_ALLOW_UNAUDITED_PQ", "1");
    } else {
        cmd.env_remove("DREGG_ALLOW_UNAUDITED_PQ");
    }
    if require_lean {
        cmd.env("DREGG_REQUIRE_LEAN", "1");
    } else {
        cmd.env_remove("DREGG_REQUIRE_LEAN");
    }
    let out = cmd.output().expect("spawn child");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.success(), text)
}

#[test]
fn child_dispatcher() {
    if let Ok(role) = std::env::var(ROLE) {
        child_body(&role);
    }
}

/// The predicate says REFUSE at `site`, and the gate then aborts the sign: no signature emerges.
fn assert_refuses(role: &str, allow: bool, require_lean: bool, site: &str) {
    let (ok, text) = run_child(role, allow, require_lean);
    assert!(
        text.contains(&format!("PROBE Some({site})")),
        "{role} allow={allow} require_lean={require_lean}: the predicate must name {site}:\n{text}"
    );
    assert!(
        !ok && !text.contains("SIGNED"),
        "{role} allow={allow} require_lean={require_lean}: the predicate said refuse but the sign \
         went through — predicate and gate disagree:\n{text}"
    );
    assert!(
        text.contains("FATAL: dregg-pq refused"),
        "the gate's own refusal must follow:\n{text}"
    );
}

#[test]
fn no_core_no_opt_in_refuses_at_keygen() {
    assert_refuses("probe", false, false, "MlDsaKeygen");
}

#[test]
fn require_lean_revokes_the_opt_in_and_the_predicate_says_so() {
    assert_refuses("probe", true, true, "MlDsaKeygen");
}

#[test]
fn keygen_answered_leaves_sign_as_the_refusing_direction() {
    assert_refuses("probe-with-keygen", false, false, "MlDsaSign");
}

#[test]
fn declared_bypass_answers_and_the_sign_completes() {
    let (ok, text) = run_child("probe", true, false);
    assert!(
        text.contains("PROBE None"),
        "the declared bypass must answer:\n{text}"
    );
    assert!(
        ok && text.contains("SIGNED Some(3309)"),
        "the predicate said answerable, so the sign must complete with a full signature:\n{text}"
    );
}
