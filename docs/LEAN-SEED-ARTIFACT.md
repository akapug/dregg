# The Lean seed as a release artifact — verified nodes in minutes, not hours

The single biggest barrier to a stranger running a **verified** `dregg-node` is the Lean seed:
`dregg-lean-ffi/libdregg_lean.a`, a ~180 MB native static archive of the compiled verified
executor plus its entire mathlib/batteries/aesop/Qq dependency closure (~6000 objects). It is
**gitignored** (an architecture-native Mach-O/ELF blob — never a repo blob), so a fresh clone that
runs `cargo build` without it silently builds **marshal-only**: `lean_available()==false`, and the
node runs the *un-verified* Rust executor. Regenerating the seed from source is an **hours-long**
cold `lake` bootstrap (it compiles mathlib).

This document describes the mechanism that turns that into a **minutes-long** download: publish a
HEAD-matching seed as a **GitHub release asset**, and fetch it on a fresh clone.

See also `docs/BUILD-LEAN-LINKED-NODE.md` (the build-time story + the `DREGG_REQUIRE_LEAN` gate).

## The pieces

| File | Role |
|------|------|
| `scripts/lean-seed-key.sh` | Computes the seed **provenance + content key** (platform · Lean toolchain · mathlib rev · Dregg2 tree hash) and the canonical asset name. Shared by fetch + publish. |
| `dregg-lean-ffi/lean-seed.pin` | The committed **pointer**: which release `TAG` holds the current seed, and the provenance it was cut from. Rewritten by the publish workflow. |
| `scripts/fetch-lean-seed.sh` | Downloads the platform-native seed asset from the pinned release, **verifies the sha256 + the `dregg_*` exports**, and installs it at `dregg-lean-ffi/libdregg_lean.a`. |
| `.github/workflows/lean-seed.yml` | The **publish** workflow: build the seed on a beefy host, compress, upload the asset + `.sha256` to a release, and bump the pin. |
| `scripts/run-node-10min.sh` | The end-to-end "clone → seed → build → run → verify" convenience path. |

## The seed key (why an asset is HEAD-matching)

A seed archive is valid only for a specific **platform** (Mach-O arm64 ≠ ELF x86_64), **Lean
toolchain** (the runtime/stdlib ABI it links against), **mathlib pin** (its dependency closure),
and **Dregg2 source tree** (the executor slice baked in — used verbatim on the fetch path, where a
fresh clone has no warm `.lake` to re-splice from). `scripts/lean-seed-key.sh` hashes exactly those
into a short key and names the asset:

```
libdregg_lean-<os>-<arch>-<lean-tag>-<key>.a.zst
# e.g. libdregg_lean-Linux-x86_64-v4.30.0-1a2b3c4d5e6f7a8b.a.zst
```

Same key ⇒ interchangeable seed. `fetch-lean-seed.sh` computes the local key, downloads the asset
of that exact name, and **warns loudly** if the committed pin's `DREGG_TREE_HASH` has drifted from
your checkout (a stale seed whose Dregg2 slice predates your source — the closure link may then
need a warm local `.lake`).

## Fetching (the fast path, for everyone)

```sh
# 1. elan + the pinned toolchain must be on PATH (installs in minutes; NO mathlib compile):
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh    # then re-open your shell

# 2. fetch the prebuilt seed for your platform:
./scripts/fetch-lean-seed.sh

# 3. build a VERIFIED node, failing loud on any silent marshal-only degrade:
DREGG_REQUIRE_LEAN=1 cargo build -p dregg-node --release
```

The seed links against the toolchain's Lean runtime; if `lake env` can't be found at build time,
export the sysroot explicitly: `export DREGG_LEAN_SYSROOT="$(cd metatheory && lake env printenv LEAN_SYSROOT)"`.

If no seed release has been cut yet, `fetch-lean-seed.sh` **fails loud** and points you at either a
local `./scripts/bootstrap.sh` (the slow, hours-long path) or cutting a release (below). The
`DREGG_REQUIRE_LEAN=1` gate guarantees you can never *silently* ship a marshal-only node — the
build panics with the exact cause instead. (Confirmed wired: `dregg-lean-ffi/build.rs`
`degrade_guard`, and a `--release` native build defaults the gate ON.)

## Cutting a seed release (needs a beefy build host — "lassie")

Seeding compiles thousands of leanc objects and needs the mathlib checkout at the **local path**
pinned in `metatheory/lakefile.toml` (currently an absolute path — a stock GitHub-hosted runner has
neither the checkout nor the hours). Cut seeds on a **self-hosted beefy host** (David's *lassie*)
that carries a warm `.lake` + the mathlib pin.

### Via the workflow (preferred)

`Actions → Publish Lean seed → Run workflow`, with a `tag` (e.g. `lean-seed-2026-07-01`) and the
self-hosted `runner` label. It runs `bootstrap.sh`, compresses, uploads the asset + `.sha256` to
the release, and commits the pin bump. Run it once **per platform** you want to serve (each
self-hosted host contributes its own native asset to the same tag).

### By hand on lassie (when the workflow host is down)

```sh
# on lassie, in a fresh-ish breadstuffs checkout at the target commit:
./scripts/bootstrap.sh                                  # (re)seed a HEAD-matching libdregg_lean.a
asset="$(scripts/lean-seed-key.sh --asset)"
zstd -q -19 --long=27 -T0 dregg-lean-ffi/libdregg_lean.a -o "$asset"
sha256sum "$asset" > "$asset.sha256"
gh release create lean-seed-YYYY-MM-DD --title "Lean seed YYYY-MM-DD" --notes "seed for <commit>" \
  || true
gh release upload  lean-seed-YYYY-MM-DD "$asset" "$asset.sha256" --clobber
# then bump dregg-lean-ffi/lean-seed.pin: set TAG + the provenance from `scripts/lean-seed-key.sh`,
# commit, push. fetch-lean-seed.sh now serves it in minutes.
```

The compressed asset is small (~20 MB for the ~180 MB archive, ≈8.6× with `zstd -19`).

## The security posture

- The seed is **content-addressed** by a published `.sha256` sidecar; `fetch-lean-seed.sh` refuses
  to install on a checksum mismatch (corruption/tamper) and refuses an archive lacking the
  `dregg_exec_full_forest_auth` export (wrong/placeholder file).
- A seed is a *build accelerator*, not a *trust root*: the verified guarantee comes from the Lean
  proofs compiled into it, and the same source rebuilds it bit-for-bit deterministically. A paranoid
  operator can always ignore the artifact and `./scripts/bootstrap.sh` from source.
- The seed is **never** committed to the repo (`.gitignore`: `libdregg_lean.a*`) — only published as
  a release asset.

## Known rough edge

`metatheory/lakefile.toml` pins mathlib as an **absolute local path** (`/Users/ember/src/mathlib4`).
That is fine on the maintainer's box and on a provisioned lassie, but it means bootstrap on a
stranger's machine needs mathlib at that same path (or a `DREGG_METATHEORY_DIR`/symlink workaround).
This is exactly why the **fetch path exists** — a stranger should fetch the seed and never bootstrap.
Making the mathlib pin relative is tracked separately (it touches the Lean build config).
