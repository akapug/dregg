# HANDOFF — cut the HEAD-matching Lean seed on lassie

**For:** opus-driver, running the cold bootstrap on **lassie** (dual-EPYC, 128
threads). ember hands this recipe; there is no cross-team access, so everything
below runs entirely on lassie from a fresh-ish `breadstuffs` checkout at the
target commit.

**Why this exists:** `dregg-lean-ffi/libdregg_lean.a` is a ~190 MB native static
archive of the compiled verified executor + its entire mathlib/batteries/aesop/Qq
closure. It is gitignored (a per-arch Mach-O/ELF blob — never a repo blob). A
fresh clone that builds without it silently degrades to **marshal-only** (the
un-verified Rust executor). Rebuilding it from source is a long cold `lake`
bootstrap that compiles the Dregg2 closure (mathlib itself arrives as prebuilt
oleans in minutes via `lake exe cache get`). Publishing a HEAD-matching seed as a
GitHub release asset turns that into a **minutes-long download** for everyone
else (`scripts/fetch-lean-seed.sh`). Background: `docs/LEAN-SEED-ARTIFACT.md`.

---

## The key shape

A seed is valid only for a specific **platform · lean-toolchain · mathlib-rev ·
Dregg2-tree-hash**. `scripts/lean-seed-key.sh` hashes exactly those four into a
short key and names the asset:

```
libdregg_lean-<os>-<arch>-<lean-tag>-<key>.a.zst
```

Two of the four are stable committed pins:

```
LEAN_TOOLCHAIN  = leanprover/lean4:v4.30.0          (metatheory/lean-toolchain)
MATHLIB_REV     = 1c2b90b13009c65b090d95a83c98e248deafb6f1   (metatheory/lakefile.toml)
```

The other two — `DREGG_TREE_HASH` (`git rev-parse HEAD:metatheory/Dregg2`) and the
platform string — move with every Dregg2 edit and per host. **Never copy hex
values from a doc or from another host's run**; compute them live at the target
commit:

```bash
scripts/lean-seed-key.sh            # prints KEY / PLATFORM / provenance / ASSET
scripts/lean-seed-key.sh --asset    # e.g. libdregg_lean-Linux-x86_64-v4.30.0-<key>.a.zst
```

> For reference, the staged Darwin-arm64 cut (see "Current pin state" below) named
> its asset `libdregg_lean-Darwin-arm64-v4.30.0-cfe2a7b28c339332.a.zst`. lassie's
> `<key>` differs (different platform string, and the Dregg2 tree hash at the
> handed commit) — that is correct and expected. Same provenance triple ⇒ the
> seeds are interchangeable *within a platform*.

---

## The recipe (copy-paste on lassie, at the target commit)

```bash
# 0. be at the exact commit ember names on lassie, then ground the provenance:
git rev-parse HEAD
scripts/lean-seed-key.sh    # sanity: MATHLIB_REV matches the lakefile pin;
                            # DREGG_TREE_HASH == $(git rev-parse HEAD:metatheory/Dregg2)

# 1. (re)seed a HEAD-matching libdregg_lean.a — the hours-long cold bootstrap
#    (128 threads help here; compiles mathlib once into a warm .lake):
./scripts/bootstrap.sh

# 2. compress with the canonical settings (~190 MB → ~21 MB, ≈9×):
asset="$(scripts/lean-seed-key.sh --asset)"
zstd -q -19 --long=27 -T0 dregg-lean-ffi/libdregg_lean.a -o "$asset"
sha256sum "$asset" > "$asset.sha256"

# 3. publish the asset + checksum sidecar to a dated release:
tag="lean-seed-$(date +%Y-%m-%d)"
gh release create "$tag" --title "Lean seed $(date +%Y-%m-%d)" \
   --notes "seed for $(git rev-parse --short HEAD)" || true
gh release upload  "$tag" "$asset" "$asset.sha256" --clobber
```

### 4. Bump the committed pin

Rewrite `dregg-lean-ffi/lean-seed.pin` so `fetch-lean-seed.sh` serves it — using
the values `scripts/lean-seed-key.sh` printed in step 0, never stale copies:

```
TAG=lean-seed-YYYY-MM-DD
LEAN_TOOLCHAIN=leanprover/lean4:v4.30.0
MATHLIB_REV=1c2b90b13009c65b090d95a83c98e248deafb6f1
DREGG_TREE_HASH=$(git rev-parse HEAD:metatheory/Dregg2)
GENERATED_UTC=<date -u +%Y-%m-%dT%H:%M:%SZ>
NOTE=published on lassie for <commit>
```

Then commit + push the pin. From that point, on any matching platform:

```bash
./scripts/fetch-lean-seed.sh                                   # minutes, not hours
DREGG_REQUIRE_LEAN=1 cargo build -p dregg-node --release       # fails loud, never silent-degrades
```

The preferred alternative to the by-hand path is the workflow
(`Actions → Publish Lean seed → Run workflow`, self-hosted `runner` label) —
`.github/workflows/lean-seed.yml` runs steps 1-4 and commits the pin bump. Run it
**once per platform** you want to serve (each self-hosted host contributes its own
native asset to the same tag).

---

## Grounded caveats

- **Current pin state: cut but unpublished.** `dregg-lean-ffi/lean-seed.pin` has
  `TAG=` (deliberately empty — publishing is a public-remote push, ember-gated).
  A **Darwin-arm64** seed was CUT + VERIFIED on nextop (the smoke bin round-trips
  the Lean kernel; `nm` shows every gate export) and its compressed asset is
  STAGED (see the pin's `NOTE` for the exact asset + sha256 + publish one-liner).
  **No Linux seed exists** — this recipe cuts it. The pin's `DREGG_TREE_HASH` is a
  *reference snapshot* that drifts behind HEAD as Dregg2 changes; treat
  `scripts/lean-seed-key.sh` at the handed commit as the only authority. Until a
  release is published, `fetch-lean-seed.sh` fails loud and the only verified path
  is a local `./scripts/bootstrap.sh`.
- **mathlib resolves portably.** `metatheory/lakefile.toml` pins mathlib as a
  `git`+`rev` require — `lake` fetches it into `.lake/packages/mathlib` on any
  host, no assumption about checkout layout. Optional fast path if lassie already
  has a warm mathlib checkout at the pinned rev: symlink it in *before* the first
  `lake build` (`ln -sfn /path/to/mathlib4 metatheory/.lake/packages/mathlib`).
- **The seed is a build accelerator, not a trust root.** Its guarantee is the
  Lean proofs compiled in; the same source rebuilds it deterministically.
  `fetch-lean-seed.sh` refuses any archive whose sha256 mismatches the published
  sidecar or that lacks the `dregg_exec_full_forest_auth` export.
- lassie is Linux → it serves the `Linux-x86_64` asset. The Darwin-arm64 asset is
  the staged nextop cut (same tag once published; each platform's asset is its own
  native run).
