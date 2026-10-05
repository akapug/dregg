# Vendor source inventory and reported fidelity comparison (task/4268)

The earlier bounded SOURCE review at
`501f2c265a520b68ae4305300083f94abf957dc2` left vendor fidelity unverified:
a manifest does not show that a vendor is the published crate plus only named
deltas. This document records the author's reported comparison and the
committed source inventory; it is not an independently bound pristine-source
comparison or native qualification.

## Method

The author reports `diff -rq` between the lane's vendor working tree and a
cargo-extracted `redb` 2.6.3 registry source directory. Cargo checksum
verification is part of the reported extraction method, not an extraction
receipt or archive checksum recorded here:

- pristine: `~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/redb-2.6.3/`
  (`.cargo_vcs_info.json` in the vendor records the same crate's git sha1
  `f4e3eb69dc2a4b4e01fefff0b9e039c6c7ab98f6`)
- vendored: `vendor/redb-readonly/` in this lane

The directory paths and copied `.cargo_vcs_info.json` do not bind a pristine
archive or its contents. No exact archive checksum, immutable comparison
artifact, or literal four-line `diff -rq` result is included. Those omissions
leave exhaustive equality to the published crate unverified.

## Result — reported comparison versus committed inventory

The author reports 77 vendor files, 78 pristine files, and 74 byte-identical
files. These are reported working-tree comparison counts, not measurements of
the committed vendor below.

At reviewed commit `23a251cddfca7024e38d997520de60718e80cfbd` (tree
`b1ee5b43d9f5e857e2c341d37a492c5498f1e25b`), the committed
`vendor/redb-readonly` subtree is
`bd7f3ad6a7efb6e142b661529fc29267000151eb` and contains **76 files**.
`Cargo.toml` and `build.rs` are present; neither `Cargo.lock` nor
`Cargo.toml.orig` is committed. The current commit adds only this document;
the vendor subtree is unchanged from the earlier source-review tip above.

- **74 byte-identical files** is the author's unverified comparison claim,
  not a proven count for the 76-file committed subtree.
- **`Cargo.toml.orig` — not committed.** The author describes its omission
  as removal of packaging metadata; this is not proof of the complete set of
  omissions from a checksum-bound published archive.
- **3 files described as modified by the author.** The named seam is visible
  in committed source; the claim that these are the only upstream differences
  remains unverified:
  1. `src/lib.rs`: exports `ReadOnlyDatabase` from the crate root.
  2. `src/db.rs`: the `ReadOnlyDatabase` handle — `open` takes a
     plain read-only `File` (no writable descriptor), `open_with_backend`
     builds `TransactionalMemory::new_read_only`, registers the **committed**
     transaction id (a write transaction can never start; `.next()` on a
     committed `u64::MAX` would wrap/panic), and `begin_read` returns a
     `ReadTransaction` on a read-guard. No repair, upgrade, compaction, or
     write path is reachable from the handle.
  3. `src/tree_store/page_store/page_manager.rs`: the
     read-only mode plumbing — `new_read_only` (never initializes), refusals
     for invalid magic/corrupt primary slot, non-v2 format, recovery-required
     state, and layout/file-length mismatch; the file length is captured ONCE
     and re-measured reads must agree or the open refuses; the allocator
     region-header parse is skipped because that state is unused by this
     read-only handle. Skipping is not validation or refusal: the source control
     `malformed_region_header_is_never_parsed` in
     `persist/src/copied_store_admission.rs` expects a corrupted allocator
     header to open successfully without being interpreted. The repair
     branch is independently unreachable (a second guard ahead of it); and
     `Drop` never writes recovery state from a read-only handle.

The author reports no other dependency, build-script or source differences.
The committed inventory cannot establish that claim against an unbound pristine
side; in particular, it contains no vendor `Cargo.lock` whose bytes can be
compared. `Cargo.toml` and `build.rs` are present, but their equality to the
published crate is not independently proven here.

## Bound comparison receipts (measured at this commit)

These receipts bind the pristine side and record the comparison literally;
they are this commit's measurements, source-only, no store opens.

**Archive binding.** The local registry archive hashes to the crates.io
index checksum for this exact version:

    $ sha256sum ~/.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f/redb-2.6.3.crate
    8eca1e9d98d5a7e9002d0013e18d5a9b000aee942eb134883a82f06ebffb6c01

    $ curl -s https://index.crates.io/re/db/redb   # the cargo registry's
                                                  # sparse index, 2.6.3 entry
    cksum: 8eca1e9d98d5a7e9002d0013e18d5a9b000aee942eb134883a82f06ebffb6c01

The two agree, so the extracted pristine side below is the published
artifact's bytes, not merely a directory that claims to be.

**Literal comparison.** `diff -rq` between the pristine extraction and the
vendor working tree, verbatim except that the home prefix of the pristine
paths is written `~` (the run itself used the absolute paths):

    Only in ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/redb-2.6.3: Cargo.toml.orig
    Files ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/redb-2.6.3/src/db.rs and vendor/redb-readonly/src/db.rs differ
    Files ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/redb-2.6.3/src/lib.rs and vendor/redb-readonly/src/lib.rs differ
    Files ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/redb-2.6.3/src/tree_store/page_store/page_manager.rs and vendor/redb-readonly/src/tree_store/page_store/page_manager.rs differ

Four lines, exit 1: 74 files byte-identical, 3 modified (characterized
above), 1 only-in-pristine. `Cargo.lock` IS in the archive and in the vendor
working tree, and is one of the 74 identical files — it is absent from the
COMMITTED subtree only because the vendored `.gitignore` (byte-identical to
the pristine crate's own) ignores it; a git-only consumer of this lane lacks
a file the published crate ships.

## What this proves and what it does not

Established from committed source: the exact 76-file vendor inventory above,
the doc-only current delta, and the named read-only API and refusal branches.
Established by this commit's receipts: the pristine side is bound to the
crates.io-published archive by matching checksums, and the working-tree
comparison to that bound side is exhaustive — every file is accounted for as
identical (74), modified (the 3 characterized above), or omitted
(`Cargo.toml.orig`, packaging metadata). Not established: the committed
subtree's equality to the archive (it omits the gitignored `Cargo.lock`), and
that nothing outside the vendor path affects the build differently from the
published crate.

Not proven here (unchanged from the review's reservations): compiled or
runtime behavior — cargo build, the synthetic controls, and any store open
remain separately gated native acts; the author's 342+15 test report is the
author's, not an independent pass.
