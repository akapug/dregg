//! GUARD — the `test-stubs` firewall: `dregg-cell/test-stubs` must never
//! unify into a production build graph.
//!
//! # What it protects
//!
//! `dregg-cell`'s `test-stubs` feature arms the *accept* path of
//! `StubVerifier` (`cell/src/predicate.rs`), which is otherwise FAIL-CLOSED on
//! every proof. A host that selects the stub registry
//! (`WitnessedPredicateRegistry::with_stubs()`) in a build where the feature is
//! armed gets a verifier that accepts any non-empty proof bytes. `test-stubs`
//! is therefore a soundness gate, and `cell/Cargo.toml` states that production
//! builds never set it.
//!
//! **That statement was false as packaged.** `tests/Cargo.toml` listed
//! `dregg-cell = { path = "../cell", features = ["test-stubs"] }` as a normal
//! `[dependencies]` entry, and `dregg-tests` is in the workspace's `members`
//! AND `default-members` — so a root `cargo build --release` built this crate,
//! unified the feature across the graph, and armed the stub accept path inside
//! `dregg-node`, the production node binary. The fix was to move the entry to
//! `[dev-dependencies]`, matching `turn`/`intent`/`exec-lean`, which had it
//! right: under resolver 3 a dev-dependency's features are not unified into a
//! non-test build.
//!
//! This guard is the probe that found the leak, kept as a test so the build
//! graph cannot regress silently. It is defense in depth with
//! `cell/src/predicate.rs`'s `compile_error!` (which fires if `test-stubs` is
//! ever on in a `debug_assertions`-off build): the `compile_error!` catches a
//! leak into a *release* build; this catches a leak into the *dev* graph, where
//! `debug_assertions` is on and the `compile_error!` stays quiet.
//!
//! # The falsifier
//!
//! Move `dregg-cell`'s entry in `tests/Cargo.toml` back to `[dependencies]`
//! with `features = ["test-stubs"]` and this test goes RED. (That is exactly
//! how it was verified — the probe printed `dregg-cell feature "test-stubs"`
//! before the fix and nothing after.)

use std::path::{Path, PathBuf};
use std::process::Command;

/// Walk up from `CARGO_MANIFEST_DIR` to the directory holding the workspace
/// root `Cargo.toml` (the one that declares `[workspace]`).
fn workspace_root() -> PathBuf {
    let mut dir: PathBuf = env!("CARGO_MANIFEST_DIR").into();
    loop {
        let manifest = dir.join("Cargo.toml");
        if manifest.exists() {
            let text = std::fs::read_to_string(&manifest).unwrap_or_default();
            if text.contains("[workspace]") {
                return dir;
            }
        }
        assert!(
            dir.pop(),
            "walked past the filesystem root without finding a [workspace] Cargo.toml"
        );
    }
}

fn cargo_tree(root: &Path, args: &[&str]) -> String {
    let out = Command::new(env!("CARGO"))
        .current_dir(root)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("failed to run `cargo {}`: {e}", args.join(" ")));
    assert!(
        out.status.success(),
        "`cargo {}` failed:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("cargo tree emitted non-UTF-8")
}

/// The gate. `-e features,no-dev` resolves exactly what a real (non-test)
/// build resolves: normal dependency edges only. `dregg-node` is the
/// production node binary and `dregg-tests` is the crate that leaked the
/// feature; asking for both together is what forces the unification the leak
/// depended on.
///
/// NOTE the `no-dev`: a bare `cargo tree -e features` includes dev-dependency
/// edges and therefore prints `test-stubs` even when the firewall is intact —
/// it is showing this crate's own (legitimate) dev-dependency. `no-dev` is what
/// makes the probe measure the production graph rather than the test graph.
#[test]
fn test_stubs_does_not_unify_into_the_production_node_graph() {
    let root = workspace_root();

    // ── HONEST POLE FIRST. The probe must actually be looking at a graph that
    // contains dregg-cell — otherwise "test-stubs not found" would be trivially
    // true and this test would be measuring a typo in its own arguments.
    let production = cargo_tree(
        &root,
        &[
            "tree",
            "-p",
            "dregg-node",
            "-p",
            "dregg-tests",
            "-e",
            "features,no-dev",
            "-i",
            "dregg-cell",
        ],
    );
    assert!(
        production.contains("dregg-cell"),
        "the probe did not resolve dregg-cell at all — it is measuring nothing.\n\
         Output:\n{production}"
    );
    assert!(
        production.contains("dregg-node"),
        "the probe did not reach dregg-node — the production binary is not in this graph, \
         so a leak into it could not be detected.\n\
         Output:\n{production}"
    );

    // ── THE GATE.
    assert!(
        !production.contains("test-stubs"),
        "SOUNDNESS: `dregg-cell/test-stubs` unified into the PRODUCTION dependency graph \
         (normal edges only, no dev-dependencies). It arms StubVerifier's accept-anything \
         path inside dregg-node.\n\n\
         Some crate enables `dregg-cell/test-stubs` as a normal [dependencies] entry. Move \
         it to [dev-dependencies] — see turn/intent/exec-lean/tests for the correct shape.\n\n\
         cargo tree -p dregg-node -p dregg-tests -e features,no-dev -i dregg-cell:\n{production}"
    );

    // ── AND the counter-pole: the feature IS still reachable over dev edges,
    // because this crate's own `#[cfg(test)]` modules legitimately use
    // `with_stubs()`. Without this assertion the gate above would also pass if
    // someone "fixed" the leak by deleting the dev-dependency outright — a
    // green that means the tests silently stopped exercising the stub plumbing.
    let with_dev = cargo_tree(
        &root,
        &[
            "tree",
            "-p",
            "dregg-tests",
            "-e",
            "features",
            "-i",
            "dregg-cell",
        ],
    );
    assert!(
        with_dev.contains("test-stubs"),
        "`test-stubs` is not reachable even over DEV edges — dregg-tests' dev-dependency on \
         `dregg-cell` with `features = [\"test-stubs\"]` is gone, so the stub-plumbing tests \
         are no longer testing the accept path they claim to.\n\
         cargo tree -p dregg-tests -e features -i dregg-cell:\n{with_dev}"
    );
}
