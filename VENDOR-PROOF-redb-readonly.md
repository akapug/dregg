# Vendor fidelity proof: `vendor/redb-readonly` (task/4268)

The review's open gap (helm-codex, bounded SOURCE CONCUR at 501f2c265, row
d8ff43f2b08d): a file manifest is not vendor proof — it does not show the
vendored tree is the pristine upstream crate plus named deltas, nothing else.
This document is that proof, produced source-only (no store opens, no native
execution).

## Method

`diff -rq` between the vendored tree and the pristine crates.io source of
`redb` 2.6.3, extracted by cargo from the registry archive (cargo verifies the
crate's published checksum before extraction, so the pristine side carries
crates.io provenance):

- pristine: `~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/redb-2.6.3/`
  (`.cargo_vcs_info.json` in the vendor records the same crate's git sha1
  `f4e3eb69dc2a4b4e01fefff0b9e039c6c7ab98f6`)
- vendored: `vendor/redb-readonly/` in this lane

## Result — every file accounted for

The vendored tree holds 77 files; the pristine crate 78.

- **74 files byte-identical** to the pristine crate (the whole `diff -rq`
  output is the four lines below — nothing else differs).
- **`Cargo.toml.orig` — dropped, vendored tree does not carry it.** Cargo's
  normalized `Cargo.toml` is present and identical; the `.orig` original is
  packaging metadata with no compiled effect.
- **3 files modified — the entire ReadOnlyDatabase backport:**
  1. `src/lib.rs` (+1 line): exports `ReadOnlyDatabase` from the crate root.
  2. `src/db.rs` (+40 lines): the `ReadOnlyDatabase` handle — `open` takes a
     plain read-only `File` (no writable descriptor), `open_with_backend`
     builds `TransactionalMemory::new_read_only`, registers the **committed**
     transaction id (a write transaction can never start; `.next()` on a
     committed `u64::MAX` would wrap/panic), and `begin_read` returns a
     `ReadTransaction` on a read-guard. No repair, upgrade, compaction, or
     write path is reachable from the handle.
  3. `src/tree_store/page_store/page_manager.rs` (~75 net lines): the
     read-only mode plumbing — `new_read_only` (never initializes), refusals
     for invalid magic/corrupt primary slot, non-v2 format, recovery-required
     state, and layout/file-length mismatch; the file length is captured ONCE
     and re-measured reads must agree or the open refuses; the allocator
     region-header parse is skipped (unreachable state on a read-only handle,
     so malformed region headers refuse instead of panicking); the repair
     branch is independently unreachable (a second guard ahead of it); and
     `Drop` never writes recovery state from a read-only handle.

No file was added, no file deleted (modulo `Cargo.toml.orig` above), no
dependency or build-script change: `Cargo.toml`, `Cargo.lock`, `build.rs` are
byte-identical to the pristine crate.

## What this proves and what it does not

Proven (source-level): the vendored tree is the crates.io-published redb 2.6.3
plus exactly the backport characterized above — the review's "is the vendor
complete and unmodified elsewhere?" question is answered exhaustively, not by
manifest count.

Not proven here (unchanged from the review's reservations): compiled or
runtime behavior — cargo build, the synthetic controls, and any store open
remain separately gated native acts; the author's 342+15 test report is the
author's, not an independent pass.
