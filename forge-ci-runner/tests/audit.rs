//! THE POLES — the confined runner produces a work-bound signed verdict that
//! (i) re-verifies HONEST and satisfies the L1 forge `CiRun` gate; (ii) a LYING
//! host's fabricated verdict is CONVICTED by re-execution; and (iii) the
//! serve-X-commit-Y attack (run over X, commit Y) is refused / convicted.
//!
//! Every run MATERIALIZES the PR's committed code (a patch [`History`]) itself —
//! the command provably runs over the committed bytes, and L3 re-materializes the
//! SAME committed history rather than trusting a host-supplied dir.
//!
//! macOS-only: these drive the real Seatbelt jail. Run:
//!   cd forge-ci-runner && cargo test

#![cfg(target_os = "macos")]

use std::path::Path;

use dregg_doc::check::CiRunWitness;
use dregg_doc::{
    planned_ci_run_hash, AtomId, Author, CheckRefusal, CheckWitness, CiVerdict, History, Patch,
    RequiredCheck,
};
use forge_ci_runner::{
    canonical_input_root, confinement_id, reexecute_and_verify, run_check_confined, AuditVerdict,
};

// RFC 8032 §7.1 TEST 1 Ed25519 (seed, verifying-key) pair — the SAME real pair
// the dregg-doc CI-gate tests use; the executor derives KEY from SEED by standard
// key generation, so a verdict signed with SEED verifies against KEY.
const SEED: [u8; 32] = [
    0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec, 0x2c, 0xc4,
    0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19, 0x70, 0x3b, 0xac, 0x03, 0x1c, 0xae, 0x7f, 0x60,
];
const KEY: [u8; 32] = [
    0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7, 0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64, 0x07, 0x3a,
    0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25, 0xaf, 0x02, 0x1a, 0x68, 0xf7, 0x07, 0x51, 0x1a,
];

// The CI-run region cell's identity (repo policy — the verifier rebuilds the
// identical genesis cell) and the required check's command id.
const CI_EDITOR: u8 = 7;
const CI_REGION: u8 = 8;
const COMMAND: [u8; 32] = [0x11; 32];

const CAT: &str = "/bin/cat";

/// The argv that cats the materialized document — the exact committed bytes.
fn cat_document_argv() -> Vec<String> {
    vec![format!("{}/document.txt", forge_ci_runner::WORK_TOKEN)]
}

/// A one-atom document history whose rendered `document.txt` is exactly `text`.
fn doc_history(text: &str) -> History {
    let mut h = History::new();
    let (_a, op) = Patch::add(1, text, AtomId::ROOT);
    h.commit(Patch::by(Author(2), [op]));
    h
}

// ─────────────────────── POLE (i): HONEST re-verifies + satisfies the gate ─────

#[test]
fn honest_run_reverifies_and_satisfies_the_forge_gate() {
    // A deterministic check: `/bin/cat {WORK}/document.txt` prints the committed
    // document's exact bytes — stable across runs, so its output digest is
    // reproducible.
    let h = doc_history("the exact bytes CI ran against\n");
    let argv = cat_document_argv();

    // L2 — the confined runner materializes h and produces a signed, work-bound
    // verdict over exactly those bytes.
    let out = run_check_confined(
        &h,
        Path::new(CAT),
        &argv,
        COMMAND,
        SEED,
        CI_EDITOR,
        CI_REGION,
    )
    .expect("confined run + verdict commit");

    assert_eq!(
        out.verdict.exit_code, 0,
        "the deterministic check command succeeded confined"
    );
    assert!(
        out.receipt.executor_signature.is_some(),
        "the CI host signed the verdict receipt"
    );
    // input_root is the REAL substrate_commit of the committed code.
    assert_eq!(
        out.verdict.input_root,
        canonical_input_root(&h),
        "the verdict binds the committed code's real substrate commitment"
    );

    // THE L1 IN-TURN BINDING: the signed receipt's turn hash equals the
    // fresh-genesis re-derivation over the verdict (what the forge check runs).
    assert_eq!(
        planned_ci_run_hash(CI_EDITOR, CI_REGION, &out.verdict),
        Some(out.receipt.turn_hash),
        "the verdict is bound INSIDE the signed genesis turn"
    );

    // L3 — re-execution (re-materializing the SAME committed history) reproduces
    // the verdict exactly → Honest.
    let audit = reexecute_and_verify(&out.verdict, &h, Path::new(CAT), &argv)
        .expect("re-execution audit runs");
    assert_eq!(audit, AuditVerdict::Honest, "an honest host re-verifies");

    // THE FORGE GATE (`RequiredCheck::ci_run.satisfied_by` — exactly what
    // `PullRequest::land` calls): bound to a PR whose input_root matches, the
    // work-bound, signed, exit-0 verdict SATISFIES.
    let check = RequiredCheck::ci_run("build", COMMAND, CI_EDITOR, CI_REGION, vec![KEY]);
    let witness = CheckWitness::CiRun(CiRunWitness::signed(
        out.receipt.clone(),
        out.verdict.clone(),
    ));
    check
        .satisfied_by(&witness, out.verdict.input_root)
        .expect("the L1 forge CiRun check accepts the work-bound signed verdict");

    // And it is genuinely BOUND to this PR's code: a mismatched input_root refuses.
    let mut other_root = out.verdict.input_root;
    other_root[0] ^= 0xff;
    match check.satisfied_by(&witness, other_root) {
        Err(CheckRefusal::InputRootMismatch { .. }) => {}
        other => panic!("expected InputRootMismatch for a different PR's code, got {other:?}"),
    }
}

// ─────────────────────── POLE (ii): a LYING host is CONVICTED ──────────────────

#[test]
fn lying_host_is_caught_by_reexecution() {
    let h = doc_history("honest input bytes\n");
    let argv = cat_document_argv();

    // Honest baseline: what the command REALLY produces confined.
    let honest = run_check_confined(
        &h,
        Path::new(CAT),
        &argv,
        COMMAND,
        SEED,
        CI_EDITOR,
        CI_REGION,
    )
    .expect("honest confined run");
    assert_eq!(honest.verdict.exit_code, 0);

    // THE LIE: a well-formed verdict with the SAME (real) input_root, command,
    // confinement, and a passing exit code — but a FABRICATED output_digest. The
    // host could sign this (it is the executor); re-execution convicts it.
    let bogus_digest = [0xAB; 32];
    assert_ne!(
        bogus_digest, honest.verdict.output_digest,
        "the lie must differ from the truth"
    );
    let lie = CiVerdict {
        output_digest: bogus_digest,
        ..honest.verdict.clone()
    };

    let audit =
        reexecute_and_verify(&lie, &h, Path::new(CAT), &argv).expect("re-execution audit runs");
    match audit {
        AuditVerdict::HostLied {
            field,
            claimed,
            recomputed,
        } => {
            assert_eq!(field, "output_digest", "the divergent field is named");
            assert_eq!(claimed, hex(&bogus_digest));
            assert_eq!(recomputed, hex(&honest.verdict.output_digest));
        }
        AuditVerdict::Honest => panic!("a fabricated output_digest must be CONVICTED"),
    }
}

#[test]
fn lying_about_exit_code_is_caught() {
    // A command that really FAILS: cat a file that does NOT exist in the work
    // dir → nonzero exit. (Its stderr text embeds the ephemeral path, so its
    // OUTPUT is not reproducible — but the audit checks exit_code before
    // output_digest, and confinement_id is path-agnostic, so the exit-code lie
    // is caught cleanly.)
    let h = doc_history("present\n");
    let argv = vec![format!(
        "{}/does-not-exist.txt",
        forge_ci_runner::WORK_TOKEN
    )];

    let honest = run_check_confined(
        &h,
        Path::new(CAT),
        &argv,
        COMMAND,
        SEED,
        CI_EDITOR,
        CI_REGION,
    )
    .expect("confined run of a failing command");
    assert_ne!(
        honest.verdict.exit_code, 0,
        "cat of a missing file fails confined"
    );

    // THE LIE: claim success (exit 0) over a run that really failed, keeping the
    // real confinement id so the audit reaches the exit-code comparison.
    let lie = CiVerdict {
        exit_code: 0,
        ..honest.verdict.clone()
    };
    let audit =
        reexecute_and_verify(&lie, &h, Path::new(CAT), &argv).expect("re-execution audit runs");
    match audit {
        AuditVerdict::HostLied { field, claimed, .. } => {
            assert_eq!(field, "exit_code");
            assert_eq!(claimed, "0");
        }
        AuditVerdict::Honest => panic!("claiming success over a failing run must be CONVICTED"),
    }
}

#[test]
fn confinement_id_binds_the_command() {
    // A verdict whose confinement_id does not match the command being audited is
    // convicted on that field first (the audit binds WHICH sandbox/command ran).
    let h = doc_history("x\n");
    let argv = cat_document_argv();
    let honest = run_check_confined(
        &h,
        Path::new(CAT),
        &argv,
        COMMAND,
        SEED,
        CI_EDITOR,
        CI_REGION,
    )
    .expect("honest run");

    // Claim it ran under a DIFFERENT command's confinement.
    let wrong_cid = confinement_id("/bin/echo", &argv, &brew());
    let lie = CiVerdict {
        confinement_id: wrong_cid,
        ..honest.verdict.clone()
    };
    match reexecute_and_verify(&lie, &h, Path::new(CAT), &argv).unwrap() {
        AuditVerdict::HostLied { field, .. } => assert_eq!(field, "confinement_id"),
        AuditVerdict::Honest => panic!("a mismatched confinement id must be caught"),
    }
}

// ── POLE (iii): SERVE-X-COMMIT-Y is CONVICTED end-to-end by L3 ─────────────────

#[test]
fn serve_x_commit_y_is_convicted_by_l3_rematerialization() {
    // The real PR code Y renders "the real reviewed code\n"; the attacker's X is
    // different bytes that also exit 0 under cat.
    let y = doc_history("the real reviewed code\n");
    let x = doc_history("attacker-controlled-code\n");
    let argv = cat_document_argv();

    // THE ATTACK: the host runs the command over X but wants a verdict that reads
    // as "CI green for Y". It runs an honest confined run over X (which yields the
    // output/exit over X), then SIGNS a verdict with input_root spoofed to R_Y.
    let over_x = run_check_confined(
        &x,
        Path::new(CAT),
        &argv,
        COMMAND,
        SEED,
        CI_EDITOR,
        CI_REGION,
    )
    .expect("host runs the command over X");
    let lie = CiVerdict {
        input_root: canonical_input_root(&y), // R_Y — what the forge L1 gate binds
        ..over_x.verdict.clone()              // exit/output/confinement are over X
    };

    // L3 — re-materialize the TRUSTED committed Y into a fresh dir and re-run: the
    // true output over Y diverges from the output over X → CONVICTED.
    let audit = reexecute_and_verify(&lie, &y, Path::new(CAT), &argv).expect("audit runs");
    match audit {
        AuditVerdict::HostLied {
            field: "output_digest",
            claimed,
            recomputed,
        } => {
            assert_eq!(
                claimed,
                hex(&over_x.verdict.output_digest),
                "claim = output over X"
            );
            assert_ne!(claimed, recomputed, "the true output over Y differs from X");
        }
        other => panic!("serve-X-commit-Y must be convicted on output_digest, got {other:?}"),
    }
}

// ── The forge L1 gate ITSELF refuses a verdict whose materialized tree is not the
//    committed code: a runner that materializes Y produces input_root == R_Y, so a
//    verdict over X can never carry R_Y honestly (the input_root_of_dir guard). ──

// ─────────────────────────────── helpers ──────────────────────────────────────

fn brew() -> String {
    std::env::var("HOMEBREW_PREFIX").unwrap_or_else(|_| "/opt/homebrew".to_string())
}

fn hex(b: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(b.len() * 2);
    for &x in b {
        s.push(HEX[(x >> 4) as usize] as char);
        s.push(HEX[(x & 0x0f) as usize] as char);
    }
    s
}
