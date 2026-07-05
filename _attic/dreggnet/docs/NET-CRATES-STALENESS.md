# DreggNet `net/` crates — staleness vs the internal Elide source tree

A read-only survey: are DreggNet's bundled `net/*` crates older than the
freshest source in the internal Elide source tree, and how do we sync them carefully? This is a
**report**; the sync itself is a reviewed follow-up. No code was touched.

Dates in this doc are commit dates; verify against HEAD before acting.

## TL;DR

- DreggNet's bundle is the **`dhttp` `whoahaha` HEAD `8a5a5e121` (2026-03-31)**
  snapshot, copied **byte-for-byte** (`httpe/src` diffs **0 files**). Only two
  files carry DreggNet-local edits: `net/builder/build.rs` and
  `net/rpc/build.rs` (bundling adaptations — must be preserved on any sync).
- **The net stack is end-of-life upstream.** `origin/main` (`a38e9e0d0`,
  2026-04-22) has **deleted** httpe, tailscale, wireguard, iocoreo, pki,
  foreign-gai and jvm-stubs (the `fix/emergency-codebase-cleanup` teardown,
  merged 04-22). Only `transport` and `core` still live on `main`. **There is no
  future upstream for the HTTP engine** — DreggNet is now its de-facto home.
- The **freshest still-whole** source is **`origin/main-catastrophe`
  (`fdbbd9b8b`, 2026-04-15)** — same full-stack line as the bundle, with the
  complete crate set (foreign-gai + jvm-stubs + tailscale + wireguard) intact.
- The bundle is **behind `main-catastrophe` by 6 net-crate commits** but is
  **not a clean fast-forward** — the two lines diverged at `92eeff7a7`, and the
  bundle line carries **4 commits `main-catastrophe` lacks**. Sync is a
  **reviewed merge**, not a mechanical overwrite.
- The `[patch.crates-io]` forks are **identical** to dhttp's and **resolve to
  the same SHAs** in both lockfiles — DreggNet is **not behind** on the forks.
  The reproducibility hazard is the pre-existing one already documented in
  `HTTPE-TIDY-PLAN.md`: rustls / ntex×16 / hickory are **branch-pinned**, not
  rev-pinned. The committed `Cargo.lock` makes today's build reproducible; a
  `cargo update` would float them. Recommend rev-pinning to the lock SHAs.

## 1. The internal Elide worktree survey

The internal Elide source tree is one git repo (the Elide monorepo) checked out into **many
worktrees** — `git worktree list` from any of them enumerates all of them. The
net crates live at `crates/<name>`. The bundle's root comment names an
internal Elide HTTP-engine source tree as the source; that worktree is on branch `whoahaha`
at `8a5a5e121` (the documented and confirmed bundle source).

Worktrees / branch tips that still contain a **live** `crates/httpe`:

| Source | Tip | Date | httpe last-touched | Crate set | Note |
|---|---|---|---|---|---|
| `dhttp` / `whoahaha` | `8a5a5e121` | 2026-03-31 | `91c6d67e0` (03-31) | **full** | **the bundle source** |
| `origin/main-catastrophe` | `fdbbd9b8b` | 2026-04-15 | `40c2ad144` (04-04) | **full** | **freshest full stack** |
| `origin/mark/stable-jit-pt2` | `cac0fce41` | 2026-04-09 | `cac0fce41` (04-09) | no foreign-gai/jvm-stubs | divergent experimental httpe (see §2.1) |
| `ouroboros` | `f47374a6b` | 2026-03-22 | (03-22) | full | older |
| `verification` | `16f661ae4` | 2026-03-18 | (03-18) | full | older |
| `origin/fix/emergency-codebase-cleanup` | `b4d7bca64` | 2026-04-18 | removed 04-11 | **httpe deleted** | the teardown branch |
| `origin/main` | `a38e9e0d0` | 2026-04-22 | **deleted** | only transport+core | net stack EOL |

So the freshest source is **`main-catastrophe`** for the full coherent stack.
Two divergent experimental httpe lines also exist (`mark/stable-jit-pt2` and the
pre-deletion `emergency-codebase-cleanup`) — see §2.1; they are *not* drop-in
replacements.

## 2. Per-crate staleness (bundle `8a5a5e121` → freshest full-stack `fdbbd9b8b`)

`localmod` = files DreggNet changed vs the bundle base (local patches to keep).
`gap` = churn pulling the bundle up to `main-catastrophe`.

| Crate | localmod | gap (files / +ins / -del) | Status |
|---|---|---|---|
| **httpe** | 0 | 57 / +2983 / −978 | **STALE** — the engine; the bulk of the gap |
| transport | 0 | 8 / +208 / −40 | STALE |
| nodeapi | 0 | 6 / +203 / −106 | STALE (incl. seccomp aarch64 fix) |
| pki | 0 | 5 / +170 / −31 | STALE |
| iocoreo | 0 | 3 / +93 / −30 | STALE |
| foreign-gai | 0 | 2 / +56 / −494 | STALE (net deletion — vendored data trimmed) |
| sys | 0 | 2 / +36 / −4 | STALE (incl. seccomp aarch64 fix) |
| macros | 0 | 1 / +52 / −11 | STALE |
| base | 0 | 1 / +12 / −6 | STALE (dep updates) |
| tailscale | 0 | 1 / +1 / −1 | trivially behind (version bump) |
| wireguard | 0 | 1 / +1 / −1 | trivially behind (version bump) |
| core | 0 | 0 | **SAME** |
| dns | 0 | 0 | **SAME** |
| bindings | 0 | 0 | **SAME** |
| native-dispatch | 0 | 0 | **SAME** |
| **builder** | **1** (`build.rs`) | 0 | SAME + **DreggNet local mod** |
| **rpc** | **1** (`build.rs`) | 0 | SAME + **DreggNet local mod** |
| jvm-stubs | 0 | (n/a on this line) | bundle-only crate set |

### The 6 upstream commits in the gap (notable changes)

These are the commits `main-catastrophe` adds over the bundle. Most are
fixes/hardening — relevant to a crate that *serves the hosting*:

- `40c2ad144` **fix: thinning, attempt 2 (#748)** — httpe + sys (binary-size / build).
- `68ac98825` **disable prebugger in public builds (#737)** — httpe, nodeapi, pki, foreign-gai. **Hardening** (don't ship the debugger hook in release).
- `6f3182589` **fix seccomp allowlist for aarch64: guard x86_64-only syscalls** — nodeapi, sys. **Security/correctness** of the sandbox on arm64.
- `0a367c61b` **unreasonably large feature collection for 1.1.0 (#638)** — broad: httpe, nodeapi, pki, transport, iocoreo, sys, base. The widest commit; feature surface — **review carefully** (interacts with feature wiring).
- `ef6d25f57` **chore: dep updates (x2) (#730)** — httpe, nodeapi, pki, base. Dependency bumps.
- `9d3c09c33` **fix: installer bugs (#734)** — httpe (installer path).

### The 4 commits the bundle has that `main-catastrophe` LACKS — must NOT be lost

The two lines diverged (merge-base `92eeff7a7`); the bundle line carries:

- `8a5a5e121` converge main and fmt
- `e14f489c0` chore: converge some cleanups
- `91c6d67e0` some docs and functionality fix
- `056778e03` fix/nodeapi-force-link: squashed branch  ← **nodeapi link fix; load-bearing**

A blind overwrite with `main-catastrophe` would drop these. The sync must be a
**merge** (or a reviewed three-way), not a copy.

### The 2 DreggNet local modifications (preserve verbatim)

Both are **bundling adaptations** so the crates build standalone outside the
monorepo — keep them on any re-bundle:

- `net/builder/build.rs` — replaces the monorepo `make setup` / git-worktree
  panic gate with a standalone no-op (the GraalVM/javac gate is monorepo
  dev-ergonomics, not a build requirement for the Rust net crates).
- `net/rpc/build.rs` — resolves the internal schema dir relative to
  `CARGO_MANIFEST_DIR` (`net/rpc/schema`) instead of the monorepo path
  `crates/rpc/schema`.

### 2.1 The divergent experimental httpe lines (optional, reviewed-only)

Two other branches carry httpe work that is **not** on the `main-catastrophe`
line and is **not** a drop-in:

- `mark/stable-jit-pt2` (`cac0fce41`, 04-09): httpe diverges from the bundle by
  **96 files / ~42k insertions / ~18k deletions** — proptest (h2 streams, hpack,
  response-handle), loom CAS tests, TLA+-found keep-alive PBF fix, and the
  `transport` UnsafeCell→RefCell refactor. This is a **hardening/verification**
  line but lacks foreign-gai and jvm-stubs.
- `fix/emergency-codebase-cleanup` (pre-removal, `52ec6a2c3^`): has the transport
  refcell refactor + iocoreo dead-slot cleanup + foreign-gai + jvm-stubs, but
  already removed tailscale/wireguard/webrtc.

These are candidate **cherry-picks for specific hardening** (the TLA+ keep-alive
fix, the loom tests), reviewed individually — not part of the mechanical sync.

## 3. The `[patch.crates-io]` forks

DreggNet's patch set is carried over **verbatim** from dhttp's root `Cargo.toml`,
and both lockfiles resolve the floating branches to the **same** commits:

| Fork | Pin kind | Locked SHA (DreggNet == dhttp) | Reproducible? |
|---|---|---|---|
| `compio-*` (11 crates) | **rev** `6a97636…` | `6a97636…` | yes |
| `jni` | **rev** `52526ed…` | `52526ed…` | yes |
| `ntex` + 15 siblings | **branch** `elide/scatter-gather-write` | `e28d6115…` | **lock-only** |
| `rustls` | **branch** `elide/zero-copy-plaintext` | `6031dba8…` | **lock-only** |
| `hickory-resolver` / `hickory-proto` | **branch** `compio` | `8fb93982…` | **lock-only** |

Findings:
- **Not behind.** Every fork SHA matches dhttp's lock exactly. There is nothing
  newer in the internal Elide source tree to pull for the forks.
- **Reproducibility hazard (pre-existing, already documented in
  `HTTPE-TIDY-PLAN.md` §1.5/§2).** rustls, the 16 ntex crates, and hickory are
  pinned by **branch**. The committed `Cargo.lock` pins exact SHAs, so today's
  build is reproducible — but a `cargo update` (or a lockless resolution) would
  silently float the engine to the branch tip. **Recommend rev-pinning** the
  `[patch.crates-io]` entries to the lock SHAs above (the rev-pinned compio/jni
  already meet this bar). This is independent of the crate sync and is the
  highest-leverage supply-chain fix.

## 4. Sync plan

**Target:** `origin/main-catastrophe` `fdbbd9b8b` (the freshest whole stack).
Note this is upstream's **final** full-stack state — `main` deleted the engine
afterward, so this is a one-time catch-up, not an ongoing track.

**Classification: REVIEWED, not safe-mechanical.** It is overnight-doable behind
a green gate, but three things forbid a blind overwrite: (a) the lines diverged —
the bundle carries 4 commits `main-catastrophe` lacks (incl. the nodeapi
force-link fix); (b) the two `build.rs` local mods must survive; (c) `#638`
("unreasonably large feature collection") is broad and touches feature wiring.

Recommended order:

1. **Snapshot & baseline.** Confirm the current bundle still equals `8a5a5e121`
   per-crate (it does today: 16/18 crates 0-diff, builder/rpc = the 2 local
   `build.rs`). Record this so the merge base is exact.
2. **Three-way per crate, not copy.** For each STALE crate, apply the
   `8a5a5e121 → fdbbd9b8b` diff onto the DreggNet tree (e.g. format the upstream
   range as a patch and `git apply --3way`), so the bundle's 4 divergent commits
   and the 2 `build.rs` mods are preserved by the merge rather than clobbered.
   Re-confirm `builder/build.rs` and `rpc/build.rs` still carry the standalone
   adaptations afterward.
3. **Crate order (low-risk first):** tailscale, wireguard, base (trivial) →
   macros, sys, iocoreo, foreign-gai → pki, transport, nodeapi → **httpe last**
   (the 57-file engine bulk).
4. **Patch forks:** leave the SHAs as-is (not behind). Optionally, in the same
   pass, **rev-pin** rustls/ntex/hickory to the §3 lock SHAs (eliminates the
   reproducibility hazard). Do **not** `cargo update` the forks.
5. **Rebuild + test gate (green-or-bust):** the existing `make test` /
   `scripts/test.sh` service-crate suite + a from-clean `cargo build` of the net
   members. The net stack is nightly + Linux-only (see `HTTPE-TIDY-PLAN.md`), so
   gate on the same target it deploys to. Do not ship if red.
6. **Cherry-pick hardening separately (optional):** the §2.1 TLA+ keep-alive fix
   and loom tests from `mark/stable-jit-pt2`, reviewed one at a time — out of
   scope for the mechanical catch-up.

**Risk:** moderate, concentrated in httpe (#638 feature breadth, #730 dep bumps)
and the divergent merge. Low for the 0-diff and trivial crates. The seccomp
aarch64 fix and the prebugger-disable are worth pulling for any arm64/public
deployment.

## 5. Licensing boundary

The `net/*` sources carry a **proprietary Elide license header**
and `license = "Private"` (workspace). These are **ember's
work at Elide** — **freely usable here, not relicensable**. Keep the headers
intact on any re-bundle; do not strip them, do not relicense, and keep the
crates `publish = false` / unpublished. The sync copies Elide-internal code
between two of ember's own trees; it does not change that boundary.

---
*Survey method: all internal Elide worktrees are one repo; per-crate `diff -rq` of
`net/<crate>` vs `git archive` of candidate commits, plus `git log`/`git diff
--shortstat` over the `8a5a5e121..fdbbd9b8b` range and the fork lockfile SHAs.*
