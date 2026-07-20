//! The refusal gate, exercised on the SHIPPING code path.
//!
//! `dregg-pq`'s unit tests run with a `#[cfg(test)]` override that permits the
//! unaudited fallback (a unit-test binary cannot link the Lean archive, so every
//! one of them is on the crate path by construction). That override does NOT
//! exist here: an integration test links `dregg-pq` as an ordinary downstream
//! crate, exactly as a deployed binary does. So these tests drive the real gate.
//!
//! The refusal is `process::abort()`, which cannot be caught in-process — so the
//! only way to observe it is to BE a subprocess. This test re-executes its own
//! binary with a marker variable set; the child performs one PQ operation with no
//! verified core installed, and the parent asserts on how the child died.

use std::process::Command;

/// Marker telling a re-executed child which operation to attempt.
const ROLE: &str = "DREGG_PQ_REFUSAL_TEST_ROLE";

/// The child half: perform one PQ operation with NO verified core installed and
/// NO opt-in, then report if it somehow survived.
fn child_body(role: &str) -> ! {
    match role {
        "verify" => {
            // Well-formed lengths so the fail-closed length check does not
            // short-circuit before the gate: the gate must be what stops this.
            let pk = vec![0u8; 1952];
            let sig = vec![0u8; 3309];
            let accepted = dregg_pq::ml_dsa_verify(&pk, b"ctx", b"msg", &sig);
            eprintln!("CHILD SURVIVED THE GATE: ml_dsa_verify returned {accepted}");
        }
        "encaps" => {
            let ek = vec![0u8; 1184];
            let out = dregg_pq::ml_kem768_encaps(&ek);
            eprintln!(
                "CHILD SURVIVED THE GATE: ml_kem768_encaps -> {:?}",
                out.is_some()
            );
        }
        other => {
            eprintln!("CHILD: unknown role {other}");
            std::process::exit(3);
        }
    }
    // Reaching here means the unaudited primitive answered without refusal.
    std::process::exit(0);
}

/// Re-exec this test binary as a child in `role`, and return its output.
fn run_child(role: &str, allow_unaudited: bool) -> std::process::Output {
    let exe = std::env::current_exe().expect("current_exe");
    let mut cmd = Command::new(exe);
    // Run only the dispatcher test in the child, single-threaded.
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
    cmd.output().expect("spawn child")
}

/// The re-exec landing pad. In a normal (parent) run the marker is unset and this
/// is a no-op; in a child run it performs the operation and never returns.
#[test]
fn child_dispatcher() {
    if let Ok(role) = std::env::var(ROLE) {
        child_body(&role);
    }
}

/// ★ THE GATE: with no verified core installed and no opt-in, an ML-DSA verify
/// must ABORT the process rather than quietly answer from the `fips204` crate.
#[test]
fn verify_without_core_aborts_loudly() {
    let out = run_child("verify", false);
    let stderr = String::from_utf8_lossy(&out.stderr);

    assert!(
        !out.status.success(),
        "ml_dsa_verify SURVIVED with no verified core installed — the unaudited \
         fips204 fallback answered silently. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("CHILD SURVIVED THE GATE"),
        "the gate did not stop the call:\n{stderr}"
    );

    // SIGABRT (6), not a catchable panic: a panic would be swallowed by a task
    // boundary in a deployed server, restoring the silent substitution.
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        assert_eq!(
            out.status.signal(),
            Some(6),
            "expected SIGABRT (process::abort), got {:?}. stderr:\n{stderr}",
            out.status
        );
    }

    // The message must NAME the unaudited crate that would otherwise have run.
    for needle in [
        "refused to run UNAUDITED post-quantum crypto",
        "ML-DSA-65 verify",
        "fips204 0.4",
        "install_verified_mldsa_verify_core",
        "DREGG_ALLOW_UNAUDITED_PQ=1",
    ] {
        assert!(
            stderr.contains(needle),
            "refusal message is missing {needle:?} — it must name the unaudited \
             crate and the install that fixes it. stderr:\n{stderr}"
        );
    }
}

/// The same for the KEM half, naming `ml-kem` instead.
#[test]
fn encaps_without_core_aborts_loudly() {
    let out = run_child("encaps", false);
    let stderr = String::from_utf8_lossy(&out.stderr);

    assert!(
        !out.status.success(),
        "ml_kem768_encaps SURVIVED with no verified core installed. stderr:\n{stderr}"
    );
    for needle in [
        "refused to run UNAUDITED post-quantum crypto",
        "ML-KEM-768 encaps",
        "ml-kem 0.2.3",
        "install_verified_mlkem_encaps_core",
    ] {
        assert!(
            stderr.contains(needle),
            "refusal message is missing {needle:?}. stderr:\n{stderr}"
        );
    }
}

/// The opt-out must work — otherwise the gate would break every legitimate
/// non-verified build — and it must ANNOUNCE itself, so an operator who set the
/// variable (or inherited it from a script) still learns this process is running
/// unaudited crypto.
#[test]
fn explicit_opt_in_permits_and_announces() {
    let out = run_child("verify", true);
    let stderr = String::from_utf8_lossy(&out.stderr);

    assert!(
        out.status.success(),
        "DREGG_ALLOW_UNAUDITED_PQ=1 must permit the fallback. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("UNAUDITED crate primitives"),
        "the opt-in must still WARN that this process runs unaudited crypto. \
         stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("CHILD SURVIVED THE GATE"),
        "with the opt-in set the operation should have completed. stderr:\n{stderr}"
    );
}
