# Ejecting the Elide `net/*` stack — the path to a public, AGPL-clean DreggNet

## Why

The `net/*` crates were vendored from ember's Elide (research-director) HTTP-engine
tree. Every one of them carries an **Elide Technologies, Inc.** proprietary copyright
header. ember can *use* them, but cannot *relicense* them AGPL — so they were the one
genuinely-non-relicensable thing blocking a public release. This document records the
audit, the eject, and the recommended history-clean path.

## The dependency audit (exact, as of the eject)

Authoritative reverse-dependency picture (`cargo tree -i <crate> --target
x86_64-unknown-linux-gnu`, the deploy target — most `net/*` linkage was Linux-gated):

**The entire Elide linkage collapsed to ONE edge:** `dreggnet-control → wireguard`
(`#[cfg(target_os = "linux")]`). Everything else that linked Elide code did so *only*
transitively through that one edge.

| net/* crate | package | status before eject |
| --- | --- | --- |
| `wireguard` (lib `elidewireguard`) | the userspace WireGuard mesh engine | **REAL LINK** — `control` (linux-only), the sole product edge |
| `transport`, `pki`, `dns`, `iocoreo`, `core`, `base`, `sys`, `macros`, `native-dispatch`, `bindings` | transitive closure of `wireguard` | **REAL (transitive)** — pulled in solely by the `control → wireguard` edge |
| `httpe` | the Elide HTTP engine | **VESTIGIAL** — zero product reverse-deps (gateway had already moved to the owned `dreggnet-http`) |
| `tailscale`, `rpc`, `nodeapi`, `foreign-gai`, `builder`, `jvm-stubs` | — | **VESTIGIAL** — present in the tree, nothing linked them |
| `conformance-kit` | `conformance-kit` | **DreggNet-owned** — self-contained (bitflags/blake3/serde), no Elide code. Kept. |

`gateway → dreggnet-http` (path `../http`) was confirmed to link **zero** `httpe` (no
`httpe` reference anywhere in `gateway/src`). The `httpe → dregg-http` ejection was
already complete.

Also found and removed: `protocol/elide/v1/*` (40 Elide-copyright `.capnp`/`.proto`
schema files), which were consumed only by the now-deleted `net/rpc`.

## The eject (done)

### 1. The one real link: `control → wireguard`

`control` used a *tiny* surface of `elidewireguard`, and it renders the WireGuard INI
itself (`MeshConfig::wireguard_ini`):

```rust
elidewireguard::config::WireGuardConfig::from_ini(&str)  // parse the rendered INI
elidewireguard::tunnel::WireGuardEngine::new(config)     // build the engine
engine.peer_count()                                      // count peers
```

**Replacement:** the owned, AGPL-clean `dreggnet_control::wg` module
(`control/src/wg.rs`), backed by **`boringtun`** (Cloudflare, **BSD-3-Clause** — the
reference userspace WireGuard implementation, and already the crate `elidewireguard`
itself used internally). It provides:

- a clean-room parser for the public `wg-quick` INI format (`WireGuardConfig::from_ini`),
- a real engine (`WireGuardEngine::new`) that builds one `boringtun::noise::Tunn` per
  peer under the interface key — construction validates every key as a genuine 32-byte
  x25519 WireGuard key,
- `peer_count()`.

`boringtun` is cross-platform userspace, so the mesh engine is no longer Linux-only:
`WireguardMesh` and the `LinkState::Wireguard` path were un-gated and are now built and
unit-tested natively on every host (previously untestable off Linux). `default_mesh`
semantics are unchanged (Linux → `WireguardMesh`, other hosts → the in-crate `StubMesh`;
`TailscaleMesh` still rides the host's existing tailnet/headscale overlay).

Verified green:
- `cargo build -p dreggnet-control` (macOS native)
- `cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-control` (the deploy target)
- `cargo test -p dreggnet-control` — 4 `wg::` unit tests + all 12 `mesh::` tests pass
  (the WireGuard mesh path, including `bad_key_is_a_setup_error_not_a_panic`, is now
  covered natively).

### 2. The vestigial removal

With the one real edge cut, **every** Elide `net/*` crate became vestigial. Removed:

- 18 Elide `net/*` crate directories deleted (`base bindings builder core dns foreign-gai
  httpe iocoreo jvm-stubs macros native-dispatch nodeapi pki rpc sys tailscale transport
  wireguard`). Only `net/conformance-kit` (DreggNet-owned) remains under `net/`.
- Their `members` entries and `[workspace.dependencies]` path entries removed from the
  root `Cargo.toml`; `noq-proto` (a third-party git dep used only by `net/transport`)
  removed.
- `protocol/elide/` (the 40 orphaned Elide schema files) deleted.

The working tree now contains **zero Elide-copyright code**.

## Remaining Elide-proprietary *source* in the tree (NON-linked)

Zero-linkage is achieved (see verdict), but a full sweep for the Elide proprietary
header found more Elide *source* sitting in the tree — **none of it linked** (no
workspace member, no product dep). Removed as part of this eject:

- `protocol/elide/v1/*` — 40 orphaned schema files (was consumed only by the deleted `net/rpc`). **Deleted.**
- `project/content/strings/` + `packages/generated/i18n/` — orphaned i18n build-inputs for the deleted `net/base` codegen (zero references). **Deleted.**

Left in place (belongs to the in-flight **test-rigor / conformance** lane, out of scope
for this eject — coordinate with that lane):

- `docs/engine/oracle/elide-{cli,licensing,pkl,sidecar}/` — the "external-oracle"
  differential-testing reference the conformance-kit names as a future backend seam
  (`todo!()` bodies; conformance-kit itself links **none** of it — it is bitflags/blake3/
  serde only). Standalone, not a workspace member, not linked. It is Elide-proprietary,
  so the **big-bang seed must exclude it** (or the conformance lane must eject/replace it
  first). This is the last Elide-proprietary source remaining in the tree.

## Verdict: can DreggNet reach zero-Elide-linkage? — YES, reached.

DreggNet links zero Elide `net/*` code. The remaining effort is **zero** for linkage; the
only follow-ups are cosmetic/OSS-hygiene, not the AGPL blocker:

- **`[patch.crates-io]` + crates.io forks (secondary, non-blocking).** The root
  `Cargo.toml` still carries `[patch.crates-io]` entries and `[workspace.dependencies]`
  for third-party **forks of third-party OSS** (ntex, compio, the forked rustls
  fork, hickory forks, oxc, syntect, minify-html, i18n-embed, tough, jni, capnp-serde,
  keygen-rs, java_native, clap-i18n-richformatter, miring, …). These are **not
  Elide-proprietary** — they are Elide's forks of MIT/Apache/BSD crates and retain their
  upstream OSS licenses, so they do **not** block an AGPL release. Most were pulled only
  by the deleted net stack and are now unused patches (cargo warns, does not fail). A
  clean-up pass (drop the now-unused patches; repoint any still-live fork — e.g. the
  rustls fork if reqwest/tls still pulls it — to the crates.io upstream) is worthwhile
  for a tidy public repo but is a separate, non-blocking task. Do it before publish, verify
  with a full `cargo build --workspace`.
- **`LICENSE`** still reads `Private`. Flipping it to AGPL is now *unblocked* but is
  ember's decision, deliberately not done here.

## The history-clean recommendation: **big-bang fresh repo (recommended)**

Even after the eject, the Elide `net/*` source still lives in git **history** (every past
commit). Two paths to a public repo with zero Elide code anywhere:

1. **Big-bang / fresh-clean-repo — RECOMMENDED.** Seed a brand-new git repo from the
   *current ejected working tree* (one initial commit, or a small curated set), then set
   it as the public origin. **Certainty:** no Elide blob can survive because there is no
   inherited history — what you publish is exactly the tree you can see is clean. The cost
   is losing the granular commit history (which is private/internal anyway).

2. **`git filter-repo` rewrite.** Rewrites every commit to strip `net/*` +
   `protocol/elide/*` from all of history, preserving the commit graph. **Riskier:** it
   must be *exhaustive* — any missed path, renamed file, or blob in an old commit leaks
   Elide code into the public history, and it is easy to miss one. Only choose this if
   preserving history is a hard requirement.

Because the goal is a *publishable, provably Elide-free* repo, the **big-bang seeded from
the ejected tree** is the clean, certain move: the published history contains, by
construction, only what is in the audited-clean tree.
