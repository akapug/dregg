//! ⚑ THE LINKED ARCHIVE MUST NOT PREDATE THE LEAN IT CLAIMS TO BE.
//!
//! ── THE WOUND (measured 2026-08-07, and it had been open for a week) ─────────────────────────
//! `deployed_constraint_probe` — the REALITY-GATE canary for `@[export] dregg_constraint_admits` —
//! reported `8 passed` every day from 2026-07-30 to 08-06 while SIX of its eight assertions were
//! false. The admission wire's header grew from 6 tokens to 17 on 07-30/08-01; the probe's builder
//! still emitted six. The evaluator refused every one of those wires, and
//! `DeployedConstraint.admitsWire` THEN rendered a refusal-to-parse as `"1"` — the same string as
//! `ConstraintViolated` — so the probe could not tell. (That collision is closed as of the same
//! day: an unreadable wire renders `"7 <stage>"` and decodes to
//! `ProgramError::ConstraintOracleWireMalformed`. This gate is still the one that catches a STALE
//! object, which is a different failure — a stale evaluator can be perfectly self-consistent.)
//! It went green anyway because the archive
//! linked on the box carried a **2026-07-25** `Dregg2_Exec_DeployedConstraint.o`: a six-token
//! evaluator, agreeing with a six-token builder. Re-splicing the archive refreshed the evaluator
//! alone and the six reds surfaced at once.
//!
//! ── WHY NOTHING EXISTING CAUGHT IT ───────────────────────────────────────────────────────────
//! Three gates already look at this archive and NONE of them can see one stale member:
//!   * `build.rs`'s PROVENANCE DOWNGRADE is whole-archive and control-flow-shaped — it fires when
//!     the Lean build did not run. The Lean build ran. The `.c` was current. The splice ran.
//!   * `scripts/check-lean-seed-closure.sh` asks whether a module has a MEMBER. It had one.
//!   * `scripts/check-lean-seed-freshness.sh` compares the pin's `DREGG_CLOSURE_HASH` — a fact
//!     about a published seed asset, not about the archive this binary linked.
//! The missing question is per-member and it is the cheap one: **is this object older than the
//! `.lean` it was compiled from?** `build.rs`'s member-stamp sidecar records when each object was
//! compiled; `metatheory/` records the source's mtime. One read and a stat answer it in about a second.
//!
//! ── AND THE SEED, WHICH THIS TEST CANNOT REACH ───────────────────────────────────────────────
//! This test's subject is whatever archive `build.rs` LINKED. That is the right subject for a
//! build, and it left the SEED (`dregg-lean-ffi/libdregg_lean.a`) unwatched — the artifact every
//! new `OUT_DIR` is copied from, that arrives by fetch/rsync/bootstrap and is inherited across
//! checkouts, and that NO process links directly. On 2026-08-07 the working archive was clean and
//! the seed was 56 stale of 188 against this comparison (174 of 197 once the emitted `.c` counts
//! too). The seed's gate is `scripts/check-lean-seed-member-freshness.py` — same question, fixed
//! path, no cargo, and a local-gates row (`lean-seed-member-freshness`) with its own `-red` run.
//! Its comparison is `max(.lean, .lake/build/ir/*.c)`: the `.lean` half is this file's, unchanged;
//! the `.c` half only ever fires more, because lake regenerates a module's C when its compiled
//! image changes for reasons the module's own source file cannot show.
//!
//! ── WHAT THIS REFUSES ────────────────────────────────────────────────────────────────────────
//! Every `Dregg2_<Mod>.o` member of the archive `build.rs` actually linked, mapped back to
//! `metatheory/Dregg2/<Mod>.lean` by inverting the flattened object name against the real source
//! tree (so a module name containing `_` cannot be mis-split). A member older than its source is
//! named, with both timestamps, and the run FAILS. Measured on this checkout at landing: the
//! per-`OUT_DIR` working archive is CLEAN (0 of 323), and the git-ignored SEED at
//! `dregg-lean-ffi/libdregg_lean.a` carried **56 stale members of 188** — `Dregg2_Exec_
//! DeployedConstraint.o` among them. That is the artifact that hid the six reds, and this test
//! names it whenever a build links it un-refreshed. (The seed itself was re-spliced to 0 stale
//! the same day and now has its own always-on gate; see the section above.)
//!
//! ⚠ A GATE WHOSE INPUT IS ABSENT IS A FAULT, NOT A PASS. An unset `DREGG_LEAN_LINKED_ARCHIVE`,
//! an unresolvable `metatheory/`, an unreadable archive, no `ar` on PATH, a member listing this
//! cannot parse, or fewer than [`MIN_DREGG2_MEMBERS`] resolvable members all FAIL. The one
//! honest quiet path is "this build did not link the archive at all", which routes through
//! `demand_lean` exactly like every other Lean-gated test in this crate — loud under
//! `DREGG_TEST_REQUIRE_LEAN=1`, and never printing `ok` for a check that did not run.
//!
//! ── WHAT "OLDER THAN ITS SOURCE" MEANS NOW (2026-10-01) ──────────────────────────────────────
//! CONTENT, not mtime, and not from `ar`. Two measurements on hbox retired the old clock:
//!   * GNU binutils builds DETERMINISTIC archives by default (`ar`'s `D` modifier: every member
//!     at the epoch). `ar tv` listed all 346 members as `Dec 31 1969`, the stamp reader could use
//!     none, and this test was red on every Linux box while measuring nothing.
//!   * mtime is not what Lake keys on. With honest per-object compile times this test named
//!     `Dregg2_Games_MultiwayTug.o` stale because `MultiwayTug.lean` had been REWRITTEN WITH
//!     IDENTICAL BYTES — Lake (content-hashed) correctly rebuilt nothing, so no build could ever
//!     clear the finding. A gate a correct build cannot turn green is a wall, not a gate.
//! `build.rs` now writes a provenance table beside the working archive (`DREGG_LEAN_MEMBER_STAMPS`,
//! `libdregg_lean.dregg2-members.tsv` in `OUT_DIR`): per Dregg2 member, its size and the BLAKE3 of
//! the `.lean` it was built from, snapshotted BEFORE that build's `lake build` (an edit landing
//! mid-build is recorded as the older content, so it reads stale, never fresh). This test lists the
//! archive (names + sizes — every member must have a row of the same size, so the table cannot vouch
//! for a different object; a member with no row is a FAULT) and refuses every member whose source
//! on disk now hashes differently from what its object was built from. Edit a `.lean` and do not
//! rebuild: red, naming it. Rebuild: green. Touch it without changing it: green, correctly.
//!
//! Run:  cargo nextest run -p dregg-lean-ffi --features lean-lib --test linked_archive_freshness
#![cfg(feature = "lean-lib")]

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;

/// A reader that harvests nothing must not read as clean. The `Dregg2.FFI` boundary closure is
/// ~243 modules and the seed carries 188 of them; a working archive carries 323–346. Anything
/// under this means the member listing or the source mapping broke, not that the tree got smaller.
const MIN_DREGG2_MEMBERS: usize = 100;

/// The archive `build.rs` emitted a link directive for (the per-`OUT_DIR` working copy, or the
/// runtime-trim archive when `DREGG_LEAN_FFI_RUNTIME_TRIM=1`). Absent when the Lean link was
/// skipped entirely.
const LINKED_ARCHIVE: Option<&str> = option_env!("DREGG_LEAN_LINKED_ARCHIVE");
/// The member-provenance table `build.rs` writes for a current-source archive (header above).
const MEMBER_STAMPS: Option<&str> = option_env!("DREGG_LEAN_MEMBER_STAMPS");
/// The `metatheory/` directory `build.rs` compiled from (honours `DREGG_METATHEORY_DIR`).
const METATHEORY_DIR: Option<&str> = option_env!("DREGG_LEAN_METATHEORY_DIR");

/// The table's first line; anything else is a format this reader does not know.
const MEMBER_STAMPS_HEADER: &str =
    "# dregg2-member-provenance v2\tmember\tbytes\tsource_blake3\tcompiled_unix_seconds.nanos";

/// List an archive's members with `ar tv`, falling back to `llvm-ar` (`build.rs::ar_tool` picks
/// between the same pair). PROBED BY DOING THE JOB, not by `--version`: Apple's `ar` does not
/// accept `--version` and prints a usage banner at exit 0, so a version probe selects a binary
/// that then cannot list anything — and this test would have failed on every macOS box.
fn ar_listing(archive: &Path) -> Result<(&'static str, String), String> {
    let mut tried = Vec::new();
    for candidate in ["ar", "llvm-ar"] {
        match Command::new(candidate).arg("tv").arg(archive).output() {
            Ok(out) if out.status.success() && !out.stdout.is_empty() => {
                return Ok((candidate, String::from_utf8_lossy(&out.stdout).into_owned()));
            }
            Ok(out) => tried.push(format!(
                "{candidate}: exit {} ({})",
                out.status,
                String::from_utf8_lossy(&out.stderr).trim()
            )),
            Err(e) => tried.push(format!("{candidate}: {e}")),
        }
    }
    Err(tried.join(" · "))
}

/// One row of the provenance table.
#[derive(Debug, Clone, PartialEq)]
struct Provenance {
    bytes: u64,
    /// BLAKE3 hex of the `.lean` the object was built from; `None` when build.rs found no source.
    source: Option<String>,
    /// `secs.nanos` the cached object was compiled, or `-` (a seed object) — for messages only.
    compiled: String,
}

/// Parse `ar tv`'s listing into `(member, size)` for every `Dregg2_*.o`. Each line ends
/// `… <size> <Mon> <D> <HH:MM> <YYYY> <name>`; the STAMP is deliberately ignored (it is the epoch
/// in a deterministic archive). A line without that shape, or whose size is not a number, is
/// skipped, and the caller's floor turns "skipped everything" into a failure.
fn parse_ar_listing(listing: &str) -> Vec<(String, u64)> {
    let mut out = Vec::new();
    for line in listing.lines() {
        let f: Vec<&str> = line.split_whitespace().collect();
        if f.len() < 8 {
            continue;
        }
        let name = f[f.len() - 1];
        if !name.starts_with("Dregg2_") || !name.ends_with(".o") {
            continue;
        }
        let Ok(size) = f[f.len() - 6].parse::<u64>() else {
            continue;
        };
        out.push((name.to_string(), size));
    }
    out
}

fn is_blake3_hex(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// Parse the table into `member -> Provenance`. Strict: a wrong header, a row that is not exactly
/// four tab-separated fields, a size that is not a number, a source that is neither `-` nor 64
/// lowercase hex digits, or a duplicate member is an ERROR — a half-read table under-reports.
fn parse_member_stamps(text: &str) -> Result<HashMap<String, Provenance>, String> {
    let mut lines = text.lines();
    match lines.next() {
        Some(h) if h == MEMBER_STAMPS_HEADER => {}
        other => return Err(format!("unknown member-provenance header {other:?}")),
    }
    let mut out = HashMap::new();
    for (i, line) in lines.enumerate() {
        let row = i + 2;
        let f: Vec<&str> = line.split('\t').collect();
        let [name, bytes, source, compiled] = f.as_slice() else {
            return Err(format!("row {row} is not `member\\tbytes\\tsource\\tcompiled`: {line:?}"));
        };
        let bytes: u64 = bytes
            .parse()
            .map_err(|_| format!("row {row}: bytes {bytes:?} is not a number"))?;
        let source = match *source {
            "-" => None,
            h if is_blake3_hex(h) => Some(h.to_string()),
            other => return Err(format!("row {row}: source {other:?} is not a BLAKE3 hex digest")),
        };
        let p = Provenance {
            bytes,
            source,
            compiled: (*compiled).to_string(),
        };
        if out.insert((*name).to_string(), p).is_some() {
            return Err(format!("row {row}: duplicate member {name}"));
        }
    }
    Ok(out)
}

/// Pair every listed member with its row. A member with NO row, or whose row records a different
/// size than the archive holds, is a fault (all of them returned) — the table must describe THIS
/// archive's objects, not vouch for some other build's.
fn provenance_of<'a>(
    listed: &[(String, u64)],
    table: &'a HashMap<String, Provenance>,
) -> Result<Vec<(String, &'a Provenance)>, Vec<String>> {
    let mut members = Vec::new();
    let mut faults = Vec::new();
    for (name, size) in listed {
        match table.get(name) {
            None => faults.push(format!("  {name} — in the archive, NO provenance row")),
            Some(p) if p.bytes != *size => faults.push(format!(
                "  {name} — archive holds {size} bytes, the table recorded {}",
                p.bytes
            )),
            Some(p) => members.push((name.clone(), p)),
        }
    }
    if faults.is_empty() {
        Ok(members)
    } else {
        Err(faults)
    }
}

/// Every `Dregg2/**/*.lean` under `metatheory/`, keyed by the FLATTENED object name `build.rs`'s
/// `splice_obj_name` produces (`Dregg2/Exec/DeployedConstraint.lean` → `Dregg2_Exec_
/// DeployedConstraint.o`). Built by walking the real tree, so a module whose own name contains
/// `_` maps correctly — inverting the flattening by splitting on `_` would not.
fn source_index(meta: &Path) -> HashMap<String, PathBuf> {
    fn walk(dir: &Path, root: &Path, out: &mut HashMap<String, PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, root, out);
            } else if p.extension().map(|x| x == "lean").unwrap_or(false) {
                if let Ok(rel) = p.strip_prefix(root) {
                    let flat = rel
                        .with_extension("")
                        .components()
                        .map(|c| c.as_os_str().to_string_lossy().into_owned())
                        .collect::<Vec<_>>()
                        .join("_");
                    out.insert(format!("{flat}.o"), p.clone());
                }
            }
        }
    }
    let mut out = HashMap::new();
    walk(&meta.join("Dregg2"), meta, &mut out);
    out
}

/// THE COMPARISON, factored out so the red-proof below can drive the WHOLE assembly — table
/// reader, join, name mapping and the content test. Returns `(resolved, findings)`: `resolved` is
/// how many members mapped to a live `.lean` (the floor the caller applies, so a broken mapping
/// cannot report "nothing stale"), `findings` one line per object built from other content than the
/// source on disk now.
fn stale_members(
    members: &[(String, &Provenance)],
    sources: &HashMap<String, PathBuf>,
    meta: &Path,
) -> (usize, Vec<String>) {
    let mut resolved = 0usize;
    let mut stale = Vec::new();
    for (name, p) in members {
        // A member whose module no longer exists in the tree is not a staleness finding — the
        // splice prunes those — and not silently ignored either: the caller's `resolved` floor
        // fails the run if the mapping stops resolving in general.
        let Some(src) = sources.get(name) else {
            continue;
        };
        resolved += 1;
        let rel = src.strip_prefix(meta).unwrap_or(src).display().to_string();
        let now = match std::fs::read(src) {
            Ok(bytes) => blake3::hash(&bytes).to_hex().to_string(),
            Err(e) => {
                stale.push(format!("  {name} — cannot read its source {rel}: {e}"));
                continue;
            }
        };
        match &p.source {
            Some(built) if *built == now => {}
            Some(built) => stale.push(format!(
                "  {name} — built from {rel} @ {}…, the file on disk is now {}… (object compiled \
                 {})",
                &built[..12],
                &now[..12],
                p.compiled
            )),
            None => stale.push(format!(
                "  {name} — build.rs recorded NO source for it, and {rel} exists now"
            )),
        }
    }
    (resolved, stale)
}

#[test]
fn the_linked_archive_is_not_older_than_its_lean_sources() {
    // The one honest quiet path: this build did not link the Lean archive at all. Routed through
    // `demand_lean` so it PANICS under `DREGG_TEST_REQUIRE_LEAN=1` rather than printing `ok`.
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available() && LINKED_ARCHIVE.is_some(),
        "a linked libdregg_lean.a (DREGG_LEAN_LINKED_ARCHIVE, emitted by build.rs)",
    ) {
        return;
    }

    let archive = PathBuf::from(LINKED_ARCHIVE.expect("checked above"));
    assert!(
        archive.is_file(),
        "build.rs said it linked {} and there is no file there. This test cannot measure what \
         shipped, which is a FAULT, not a pass.",
        archive.display()
    );

    let meta = METATHEORY_DIR.unwrap_or("");
    assert!(
        !meta.is_empty(),
        "build.rs could not resolve a metatheory/ directory, so there is nothing to compare the \
         archive's objects against. An absent input is a FAULT, not `no drift`."
    );
    let meta = PathBuf::from(meta);
    let sources = source_index(&meta);
    assert!(
        sources.len() >= MIN_DREGG2_MEMBERS,
        "indexed only {} Dregg2 .lean sources under {} — the source walk is broken, not the tree",
        sources.len(),
        meta.display()
    );

    let table_path = PathBuf::from(MEMBER_STAMPS.unwrap_or(""));
    let table_text = std::fs::read_to_string(&table_path).unwrap_or_else(|e| {
        panic!(
            "no member-provenance table at {:?} ({e}). build.rs writes it whenever the archive it \
             links is current-source, so a linked archive without one was not certified by this \
             build.rs — this test cannot measure it, which is a FAULT, not a pass.",
            table_path
        )
    });
    let table = parse_member_stamps(&table_text)
        .unwrap_or_else(|why| panic!("{} is unreadable: {why}", table_path.display()));

    let (_ar, listing) = ar_listing(&archive).unwrap_or_else(|why| {
        panic!(
            "neither `ar` nor `llvm-ar` could list {} — so this test cannot see what shipped, \
             which is a FAULT, not a pass. Tried: {why}",
            archive.display()
        )
    });
    let listed = parse_ar_listing(&listing);
    assert!(
        listed.len() >= MIN_DREGG2_MEMBERS,
        "parsed only {} Dregg2_*.o members out of {}. A listing this cannot read is a broken \
         READER, and a broken reader reports zero findings — which is why this floor exists.",
        listed.len(),
        archive.display()
    );
    let members = provenance_of(&listed, &table).unwrap_or_else(|faults| {
        panic!(
            "{} of {} Dregg2 members of {} are not described by {}:\n{}\n\
             The table must describe THIS archive's objects. Rebuild (`cargo build -p \
             dregg-lean-ffi --features lean-lib`) — build.rs rewrites both together.",
            faults.len(),
            listed.len(),
            archive.display(),
            table_path.display(),
            faults.join("\n")
        )
    });

    let (resolved, stale) = stale_members(&members, &sources, &meta);
    assert!(
        resolved >= MIN_DREGG2_MEMBERS,
        "only {resolved} of {} archive members mapped to a .lean source — the NAME MAPPING is \
         broken, and a broken mapping finds nothing stale by construction",
        members.len()
    );

    assert!(
        stale.is_empty(),
        "{} of {resolved} Dregg2 objects in the archive this binary LINKED were built from other \
         Lean than the source on disk now:\n{}\n\n\
         Every verified-gate test in this crate is deciding against those objects, so a green \
         from one of them is a claim about that older Lean — which is exactly how six \
         `deployed_constraint_probe` assertions reported `ok` for a week (see this file's \
         header).\n\
         FIX: rebuild — `cargo build -p dregg-lean-ffi --features lean-lib` re-runs build.rs, \
         which `lake build`s the closure, recompiles each changed `.c`, re-splices the working \
         archive and rewrites this table. If that does not clear it, the archive being linked is \
         not this OUT_DIR's working copy (a seed linked un-refreshed: `./scripts/bootstrap.sh` or \
         `scripts/fetch-lean-seed.sh` for a HEAD-matching one).",
        stale.len(),
        stale.join("\n"),
    );
}

/// ⚑ THE RED PROOF, and it is not optional: the headline is a NEGATIVE assertion, which passes
/// just as happily when its own reader is broken. Everything here runs on strings and on a
/// scratch source tree in this test's own temp dir, so the shared tree is never mutated.
#[test]
fn the_freshness_reader_can_go_red() {
    // 1 · THE LISTING READER takes names and sizes from a DETERMINISTIC listing — the exact shape
    //     measured on hbox (GNU ar, every member at the epoch, owner 0/0). The old reader took
    //     nothing from these lines; that is the regression this file was rewritten for.
    let listing = "rw-r--r-- 0/0 620280 Dec 31 19:00 1969 Dregg2_Exec_DeployedConstraint.o\n\
                   rw-r--r-- 0/0  11128 Dec 31 19:00 1969 Dregg2_FFI.o\n\
                   rw-r--r-- 0/0   4096 Dec 31 19:00 1969 Mathlib_Order_Basic.o\n";
    assert_eq!(
        parse_ar_listing(listing),
        vec![
            ("Dregg2_Exec_DeployedConstraint.o".to_string(), 620280),
            ("Dregg2_FFI.o".to_string(), 11128)
        ],
        "the reader must take both Dregg2 members (names AND sizes) and leave the Mathlib one"
    );
    // ...a macOS-shaped listing (real stamps, uid/gid 501/20) reads identically...
    assert_eq!(
        parse_ar_listing("rw-r--r--     501/20       620280 Jul 25 03:02 2026 Dregg2_A.o\n"),
        vec![("Dregg2_A.o".to_string(), 620280)]
    );
    // ...and an unreadable listing yields nothing, so the caller's floor fails the run.
    assert!(parse_ar_listing("garbage\nrw-r--r-- 1 2 3 Dregg2_X.o\n").is_empty());

    // 2 · THE TABLE READER is strict.
    let h = MEMBER_STAMPS_HEADER;
    let ha = "a".repeat(64);
    let table = parse_member_stamps(&format!(
        "{h}\nDregg2_Exec_DeployedConstraint.o\t620280\t{ha}\t1784948520.000000000\n\
         Dregg2_FFI.o\t11128\t-\t-\n"
    ))
    .expect("a well-formed table parses");
    assert_eq!(table.len(), 2);
    assert_eq!(table["Dregg2_Exec_DeployedConstraint.o"].source.as_deref(), Some(ha.as_str()));
    assert_eq!(table["Dregg2_FFI.o"].source, None);
    for bad in [
        format!("# dregg2-member-stamps v1\tmember\tbytes\tcompiled\nDregg2_A.o\t1\t{ha}\t-\n"),
        format!("{h}\nDregg2_A.o\t1\t{ha}\n"),
        format!("{h}\nDregg2_A.o\tone\t{ha}\t-\n"),
        format!("{h}\nDregg2_A.o\t1\t{}\t-\n", "A".repeat(64)),
        format!("{h}\nDregg2_A.o\t1\tdeadbeef\t-\n"),
        format!("{h}\nDregg2_A.o\t1\t{ha}\t-\nDregg2_A.o\t1\t{ha}\t-\n"),
    ] {
        assert!(parse_member_stamps(&bad).is_err(), "must refuse: {bad:?}");
    }

    // 3 · THE JOIN refuses a table that does not describe this archive: a member with no row, and
    //     a member whose size differs (the table is vouching for some other object).
    let faults = provenance_of(
        &[
            ("Dregg2_Exec_DeployedConstraint.o".to_string(), 620281),
            ("Dregg2_Missing.o".to_string(), 1),
        ],
        &table,
    )
    .err()
    .expect("a size mismatch and a missing row must both fault");
    assert_eq!(faults.len(), 2, "{faults:?}");
    assert!(faults.iter().any(|f| f.contains("NO provenance row")));
    assert!(faults.iter().any(|f| f.contains("620281") && f.contains("620280")));

    // 4 · THE WHOLE ASSEMBLY against a REAL scratch source tree — only this proves
    //     `stale_members` REPORTS a finding.
    let tmp = std::env::temp_dir().join(format!(
        "dregg-freshness-redproof-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    let nested = tmp.join("Dregg2/Exec");
    std::fs::create_dir_all(&nested).expect("scratch tree");
    // A module whose NAME CONTAINS AN UNDERSCORE, on purpose: inverting the flattened object name
    // by splitting on `_` would map `Dregg2_Exec_Deployed_Constraint.o` to a path that does not
    // exist, `resolved` would drop, and the gate would find nothing.
    let body = b"-- red-proof fixture\n";
    for name in ["DeployedConstraint.lean", "Deployed_Constraint.lean"] {
        std::fs::write(nested.join(name), body).expect("scratch source");
    }
    let sources = source_index(&tmp);
    assert_eq!(sources.len(), 2, "the source walk missed the scratch tree: {sources:?}");
    assert!(sources.contains_key("Dregg2_Exec_Deployed_Constraint.o"));
    let built = blake3::hash(body).to_hex().to_string();
    let listed = vec![
        ("Dregg2_Exec_DeployedConstraint.o".to_string(), 10),
        ("Dregg2_Exec_Deployed_Constraint.o".to_string(), 20),
    ];
    let table = parse_member_stamps(&format!(
        "{h}\nDregg2_Exec_DeployedConstraint.o\t10\t{built}\t1784948520.0\n\
         Dregg2_Exec_Deployed_Constraint.o\t20\t{built}\t1784948520.0\n"
    ))
    .unwrap();
    let members = provenance_of(&listed, &table).expect("sizes agree");

    // Built from exactly what is on disk: clean.
    let (resolved, findings) = stale_members(&members, &sources, &tmp);
    assert_eq!(resolved, 2, "both members must map to a source");
    assert!(findings.is_empty(), "objects built from the current bytes are fresh: {findings:?}");

    // Rewritten with IDENTICAL bytes (a fresh mtime, the MultiwayTug case): still clean.
    std::fs::write(nested.join("DeployedConstraint.lean"), body).unwrap();
    assert!(stale_members(&members, &sources, &tmp).1.is_empty(), "a no-op rewrite is not drift");

    // ONE BYTE of the source changes and nothing is rebuilt: red, naming the object and the file.
    std::fs::write(nested.join("Deployed_Constraint.lean"), b"-- red-proof fixturE\n").unwrap();
    let (resolved, findings) = stale_members(&members, &sources, &tmp);
    assert_eq!(resolved, 2);
    assert_eq!(findings.len(), 1, "exactly the edited module is stale: {findings:?}");
    assert!(
        findings[0].contains("Dregg2_Exec_Deployed_Constraint.o")
            && findings[0].contains("Deployed_Constraint.lean"),
        "a finding must NAME the object and its source: {:?}",
        findings[0]
    );

    // A member build.rs recorded no source for, whose source exists now: red.
    let none = parse_member_stamps(&format!(
        "{h}\nDregg2_Exec_DeployedConstraint.o\t10\t-\t-\n"
    ))
    .unwrap();
    let members = provenance_of(&listed[..1], &none).expect("size agrees");
    assert_eq!(stale_members(&members, &sources, &tmp).1.len(), 1);

    let _ = std::fs::remove_dir_all(&tmp);
}
