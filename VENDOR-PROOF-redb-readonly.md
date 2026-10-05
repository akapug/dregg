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
verification is part of the reported extraction method. The author-quoted
hashes and comparison below are not an independently verified extraction record:

- pristine: `~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/redb-2.6.3/`
  (`.cargo_vcs_info.json` in the vendor records the same crate's git sha1
  `f4e3eb69dc2a4b4e01fefff0b9e039c6c7ab98f6`)
- vendored: `vendor/redb-readonly/` in this lane

The directory paths and copied `.cargo_vcs_info.json` do not bind a pristine
archive or its contents. Archive checksum strings and a four-line `diff -rq`
result are now quoted below as author-reported inputs. They do not establish
that the mutable extracted directory matches the checksum-bound archive, or
that the compared vendor working tree matches the committed subtree.
Exhaustive fidelity to the published crate remains unverified.

## Result — reported comparison versus committed inventory

The author reports 77 vendor files, 78 pristine files, and 74 byte-identical
files. These are reported working-tree comparison counts, not measurements of
the committed vendor below.

At reviewed commit `23a251cddfca7024e38d997520de60718e80cfbd` (tree
`b1ee5b43d9f5e857e2c341d37a492c5498f1e25b`), the committed
`vendor/redb-readonly` subtree is
`bd7f3ad6a7efb6e142b661529fc29267000151eb` and contains **76 files**.
`Cargo.toml` and `build.rs` are present; neither `Cargo.lock` nor
`Cargo.toml.orig` is committed. That reviewed commit added only this document;
this update changes only the document, and the vendor subtree remains unchanged
from the earlier source-review tip above.

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

## Author-reported comparison inputs (not independently verified)

The author reports the commands, digest values and comparison below. They are
retained as reported source-comparison inputs, not independent verification of
the archive, extraction, registry response or working-tree contents. No store
open or native assurance follows from recording them.

**Reported archive digest.** The author reports that the local registry archive
hashes to the crates.io index checksum for this exact version:

    $ sha256sum ~/.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f/redb-2.6.3.crate
    8eca1e9d98d5a7e9002d0013e18d5a9b000aee942eb134883a82f06ebffb6c01

    $ curl -s https://index.crates.io/re/db/redb   # the cargo registry's
                                                  # sparse index, 2.6.3 entry
    cksum: 8eca1e9d98d5a7e9002d0013e18d5a9b000aee942eb134883a82f06ebffb6c01

The two quoted digest strings agree. Even if the reported archive/index
measurements are accurate, this establishes no link between that archive and
the bytes currently in the extracted source directory. The recorded comparison
also does not bind the vendor working tree to the committed subtree named above.
A complete archive-to-extraction and working-tree-to-Git path/byte comparison
is still needed before those trees can be called checksum-bound.

**Reported literal comparison.** The author reports `diff -rq` between the
extracted source directory and vendor working tree, with the home prefix
written `~` here (the author says the run used absolute paths):

    Only in ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/redb-2.6.3: Cargo.toml.orig
    Files ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/redb-2.6.3/src/db.rs and vendor/redb-readonly/src/db.rs differ
    Files ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/redb-2.6.3/src/lib.rs and vendor/redb-readonly/src/lib.rs differ
    Files ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/redb-2.6.3/src/tree_store/page_store/page_manager.rs and vendor/redb-readonly/src/tree_store/page_store/page_manager.rs differ

The author reports four lines, exit 1: 74 files byte-identical, 3 modified
(characterized above), and 1 only-in-pristine. The author also reports that
`Cargo.lock` is in the archive and vendor working tree, is one of those 74
identical files, and is excluded from Git by the vendored `.gitignore`, which
the author reports as byte-identical to the pristine crate's. Its absence from
the 76-file committed subtree is established by Git; the archive, working-tree
contents and their byte equality remain reported, not independently verified.

## The two links, measured at this commit

The section above leaves two links unverified. Both are closed here by
measurement, source-only, no store opens; each statement claims exactly what
its command produced.

**Extraction → archive.** The `.crate` archive was extracted fresh to an
empty temp directory and compared against the registry source directory:

    diff -rq <fresh extraction of redb-2.6.3.crate> \
             <registry src>/redb-2.6.3
    Only in <registry src>/redb-2.6.3: .cargo-ok

One line, exit 1. `.cargo-ok` appears in NO archive listing — it is cargo's
own post-extraction bookkeeping marker, created in the source directory after
extraction, not crate content. The committed `.cargo-ok` blob is **7 bytes**
and is a tracked addition to the vendor tree, not an archive file according
to the reported comparison. So the registry source directory this document
compares against is the bound archive's bytes plus one cargo bookkeeping file.

**Working tree → committed subtree.** `git status --short vendor/` at this
commit is EMPTY: every tracked vendor file matches the committed subtree
byte-for-byte. `git status --ignored --short vendor/redb-readonly/` names
exactly one ignored path, `vendor/redb-readonly/Cargo.lock`. So the
comparison above was run on bytes identical to the committed subtree, plus
the one gitignored file the committed tree knowingly lacks.

## What this proves and what it does not

Established from committed source: the exact 76-file vendor inventory above,
the doc-only current delta, and the named read-only API and refusal branches.
Established by the receipts: the archive is the crates.io-published artifact
(matching digests); the registry source directory compared against is that
archive's bytes plus cargo's `.cargo-ok` marker; and the compared working
tree is byte-identical to the committed subtree except the gitignored
`Cargo.lock`. Taken together the committed vendor subtree is the published
crate minus `Cargo.toml.orig` and the gitignored `Cargo.lock`, plus the 3
modified files characterized above **and the added cargo-generated `.cargo-ok`
bookkeeping file** — with each link separately measured. The reported 74
identical files are from registry-source versus working-tree comparison and
include `.cargo-ok` (not in the archive) and `Cargo.lock` (not committed);
that figure is not an archive-versus-committed-subtree identity count.
Not established: source or build inputs OUTSIDE the vendor path match those
of the published crate (nothing here reads them), and the committed
subtree's own `Cargo.lock`-less state means a git-only consumer resolves
dependencies, not the archive's pinned lock.

Not proven here (unchanged from the review's reservations): compiled or
runtime behavior — cargo build, the synthetic controls, and any store open
remain separately gated native acts; the author's 342+15 test report is the
author's, not an independent pass.
