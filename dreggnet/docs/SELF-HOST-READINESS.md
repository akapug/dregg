# Self-Host Readiness — the public/private boundary + can a stranger run it?

Audit date: 2026-06-30. Read-only survey of `~/dev/breadstuffs` (the public AGPL
`dregg` repo, GitHub `emberian/dregg`) and `~/dev/DreggNet` (this private
working repo, GitHub `emberian/DreggNet` — the DreggNet product is AGPL-3.0; this
tree is kept private for history + live-infra + the retained Elide `docs/engine/oracle/` sources).

Two questions, answered grounded and honest:

1. **The boundary** — what exists ONLY in DreggNet (private) vs in breadstuffs
   (public, AGPL-3.0)?
2. **Self-hostability** — for each PUBLIC artifact, can a stranger
   `git clone → build → run`? Alone? With light Claude help?

The one-line headline: **the agent runtime yes (green, one command); the SDKs
yes (published); the extension yes (prebuilt); a node runs but is *silently
unverified* on a fresh clone — the verified Lean-linked node is the wall; the
cloud is not self-hostable by design.**

---

## Part 1 — The boundary (crate-level map)

### Direction of dependence (confirmed)

DreggNet depends on breadstuffs; **nothing in breadstuffs depends on DreggNet.**
Clean open-core hygiene.

- `exec/Cargo.toml` → `dregg-agent = { path = "../../breadstuffs/dregg-agent" }`
- `agent-host/Cargo.toml` → same `dregg-agent` path dep
- `umem/Cargo.toml` → `dregg-cell = { git = "https://github.com/emberian/dregg.git", … }` + `dregg-merge = { path = "../../breadstuffs/dregg-merge" }`
- `webauth/Cargo.toml` → `dregg-types = { path = "../../breadstuffs/types" }`
- Reverse check: `grep -rn dreggnet --include=Cargo.toml` over breadstuffs = **no hits.** No public crate secretly needs a private dep. ✅

### PUBLIC — breadstuffs (AGPL-3.0, `emberian/dregg`)

The entire formally-verified substrate + apps: ~90 workspace members. The
verified Lean metatheory (`metatheory/`), the circuit/prover, the turn/cell/exec
executor cluster, the deos desktop + starbridge apps, and the shippable
artifacts below.

Shippable public artifacts and their dependency reach:

| Artifact | Where | Dep reach |
|---|---|---|
| **`dregg-node`** (the federation node daemon) | `node/` | **HEAVY — full Lean substrate.** Links `libdregg_lean.a` via `dregg-exec-lean` + `dregg-lean-ffi` (the verified executor/finality/admission FFI). |
| **`dregg`** (the CLI) | `cli/` | Light-to-medium (protocol crates); the `dregg` binary is dist-shipped. |
| **`dregg-agent`** (the agent runtime) | `dregg-agent/` | **LIGHT LEAF.** No path deps at all — only `serde`/`serde_json`/`blake3`/`ed25519-dalek`/`hmac`/`sha2`/`subtle`/`base64`/`postcard`/`reqwest`(opt). No Lean, no substrate crates. |
| **cipherclerk extension** | `extension/` + `wasm/` | Light — a wasm32 build of `dregg-wasm` (`no-lean-link`). No Lean. `dist/` ships prebuilt `.zip` (Chrome) + `.xpi` (Firefox). |
| **`@dregg/sdk`** (npm) | `sdk-ts/` | Pure TS + `@noble/ed25519`/`@noble/hashes`. No Rust build. |
| **`dregg`** (PyPI) | `sdk-py/` | pyo3/maturin over the Rust SDK — needs Rust to build from source; wheels published. |
| **`dregg-sdk`** (Rust) | `sdk/` | Light protocol crate. |

Dep-reach summary: **only `dregg-node` pulls the full Lean substrate.** The
agent, the extension, and all three SDKs are light — they ride `dregg-types` /
`dregg-auth` / `dregg-agent` (leaf crates: serde + blake3 + ed25519), never the
Lean archive.

### PRIVATE working repo — DreggNet (AGPL-3.0 product; `emberian/DreggNet` kept private)

The service/hosting/billing layer. It is **AGPL-3.0, open-core** on the public
substrate; this working repo is kept private only for its history, live-infra
config, and the retained Elide `docs/engine/oracle/` sources.

Workspace members (from `Cargo.toml`):

- **`net/*`** — the Elide HTTP-engine stack: `httpe` (the full gateway), `transport`, `iocoreo`, `pki`, `tailscale`, `wireguard`, plus vendored local Elide deps (`base` `core` `sys` `dns` `nodeapi` `rpc` `bindings` `builder` `macros` `native-dispatch` `foreign-gai` `jvm-stubs`) + `conformance-kit`. **These are the non-relicensable piece** — ember's own work as research director at Elide Technologies, carry an Elide proprietary header, *not relicensable*. This was *why* DreggNet could not be open-sourced — until the Elide net stack was ejected (see `ELIDE-NET-EJECTION.md`); DreggNet is now AGPL-3.0.
- **Service layers:** `gateway`, `control`, `exec`, `storage`, `webapp`, `billing`, `guard`, `org`, `dregg-secrets`, `dreggnet-logs`, `console`, `status`, `landing`, `attach`, `agent-host`, `ops`, `webauth`.
- **Runtime/data:** `durable`, `bridge` (fulfills a dregg execution-lease on polyana), `umem` (registries-as-umem heap), `http` (clean-room HTTP/1.1 vocabulary), `receipt`.
- **Integrations:** `dregg-domains`, `dregg-ipfs`, `sandstorm-bridge`, `dregg-deploy` (DreggNet's git-auto-deploy), `deploy/node-agent`, `tests/workload`.
- **`polyana/`** — git submodule → `polyana`, **Apache-2.0**, co-developed with an operator. Excluded from the workspace; NOT DreggNet-owned, NOT breadstuffs.

### Surprises / gotchas worth flagging

- **Two different `net/` crates.** breadstuffs `net/` = `dregg-net` (the P2P
  networking crate). DreggNet `net/` = the Elide `httpe` stack. Same directory
  name, unrelated code. Don't conflate.
- **Two different `dregg-deploy`.** breadstuffs `dregg-deploy` (userspace verify
  helper family) and DreggNet `dregg-deploy` (git → clone → build → publish-site
  workflow) are distinct crates with the same name.
- **`dregg-agent` was extracted to breadstuffs** (public) and is consumed by
  DreggNet `exec` + `agent-host` as a path dep. Confirmed: the cloud *wraps* the
  open core, it doesn't own it (`docs/AGENT-RUNTIME-OPEN-SOURCE.md`).
- **The cipherclerk extension + all SDKs are public** in breadstuffs
  (`extension/`, `wasm/`, `sdk-ts/`, `sdk-py/`, `sdk/`).

---

## Part 2 — Self-hostability (the real question)

### A dregg node (`dregg-node`) — the wall

`QUICKSTART.md` §1 gives a clean path:

```sh
cargo build -p dregg-node
./target/debug/dregg-node init --data-dir /tmp/my-dregg
./target/debug/dregg-node run  --data-dir /tmp/my-dregg --enable-faucet --port 8421 &
curl -s http://localhost:8421/status   # shows "state_producer":"lean"
```

**The honesty gap:** that `state_producer:"lean"` output is what a *bootstrapped*
tree produces. A **fresh clone cannot reproduce it.** The verified Lean archive
`dregg-lean-ffi/libdregg_lean.a` is **gitignored** (`.gitignore:41 libdregg_lean.a*`,
`dregg-lean-ffi/.gitignore:7 *.a`) — a **171 MB** architecture-native artifact
produced locally, not committed. On a fresh clone:

- `cargo build -p dregg-node` finds **no seed** → `build.rs` prints a
  `cargo:warning` and compiles **marshal-only** (`lean_available() == false`,
  the **un-verified Rust executor**). The node still runs; turns still commit —
  but it is NOT the verified thing the README promises, and **QUICKSTART.md never
  mentions `bootstrap.sh` or the seed** (`grep bootstrap QUICKSTART.md` = no hits
  on the build path). A stranger following the quickstart gets a silently
  degraded node.

To get a genuinely verified node you must:

1. `./scripts/bootstrap.sh` — installs/checks elan+lake (Lean, pinned
   `leanprover/lean4:v4.30.0`), `lake build Dregg2.Exec.FFI` (**cold = compiles
   mathlib, hours**; warm `.lake` reuses the platform-independent `.olean` cache),
   then seeds `libdregg_lean.a`.
2. `DREGG_REQUIRE_LEAN=1 cargo build -p dregg-node --release` — the fail-loud
   gate (landed this session, `3485c2332`) turns any marshal-only degrade into a
   hard build panic instead of a lost warning.
3. Verify with `nm` that the FFI symbols are defined (recipe in
   `docs/BUILD-LEAN-LINKED-NODE.md`).

Two documented traps: (a) **no seed → silent marshal-only** (above); (b) **stale
seed → closure-link failure** ("closure hit the 16-pass bound / undefined
reference to `runtime_initialize_mathlib_*`") when the seed predates the Lean
HEAD's mathlib references.

**Landed this session (credit where due):** `DREGG_REQUIRE_LEAN=1` build gate +
a node-startup tripwire (`node/src/main.rs` logs a loud `error!
MARSHAL-ONLY BUILD DETECTED` when `lean_available()==false`) + a full-mode hard
refusal to finalize on the un-verified `tau` + the `BUILD-LEAN-LINKED-NODE.md`
doc. This makes a *silent* unverified deploy no longer possible. It does **not**
make the verified build *easy*.

Verdict:
- **Unverified (marshal-only) node, alone:** 🟡 works and runs, but is not the
  verified node the README sells, and QUICKSTART doesn't warn you.
- **Verified node, alone:** 🔴 the cold Lean/mathlib bootstrap + closure-link
  troubleshooting is real build expertise.
- **Verified node, +Claude:** 🟡 achievable — Claude can drive `bootstrap.sh`,
  diagnose the closure-link failure, and set `DREGG_REQUIRE_LEAN=1`.

### `dregg-agent` — the easy win

`dregg-agent/demo/README.md`: one command, `bash demo/business.sh`. It builds
once (light leaf crate — no Lean, no substrate path deps), runs a live
reason→act→observe loop (cap-gated · metered · receipted), re-witnesses the
receipt chain, and shows a tampered line caught. With a model key in
`~/.nvidiakey` / `$NVIDIA_API_KEY` it drives live; without one a bundled
transcript replays (tools still run for real). The doc is explicitly written for
a **judge** to run.

Verdict: **alone 🟢 / +Claude 🟢.** The hackathon "a judge can run it" claim is
true.

### The cipherclerk extension

`extension/dist/` already ships prebuilt `dregg-cipherclerk-chrome.zip` +
`dregg-cipherclerk-firefox.xpi` + `background.js`/`content.js`/`page.js` — load
unpacked / install the `.xpi`, no build required. Rebuilding needs `cargo` +
`wasm-bindgen-cli` (`extension/build.sh`). Store-listing + reviewer docs present
(`STORE-LISTING.md`, `REVIEWER-NOTES.md`, `PRIVACY.md`, `LOGIN-CONTRACT.md`).

Verdict: **alone 🟢 (prebuilt) / +Claude 🟢.**

### The SDKs

- **`@dregg/sdk` (npm):** published at `0.3.0`. `sdk-ts/PUBLISHED-VERIFY.md`
  records a fresh-consumer check against the registry tarball (2026-06-28):
  installs clean, ESM+CJS import, 46 exports, constructs+signs turns offline,
  byte-faithful to the Rust facade. Publish workflow: `.github/workflows/publish-sdk-ts.yml`.
  Caveat: a **live** round-trip needs a reachable node (the devnet edge is down).
  Verdict: **alone 🟢 / +Claude 🟢** (offline turn construction); live use is
  gated on you running a local node.
- **`dregg` (PyPI):** maturin/pyo3 (`sdk-py/`, `module-name = dregg.dregg`),
  typed (`.pyi` + `py.typed`), README quickstart, publish workflow
  `.github/workflows/publish-sdk-py.yml` (`gh-action-pypi-publish`). Install +
  import is fine; anything live needs a local node (`QUICKSTART.md`).
  Verdict: **alone 🟢 for install / 🟡 for a live hello-world** (needs a node).

### The cloud (DreggNet)

**Not one-command self-hostable by others — by design** (it reaches live infra
behind operator config + credentials). DreggNet itself is **AGPL-3.0** (this working
repo is kept private for history + infra); the earlier open-source blocker was the
*non-relicensable* Elide `net/*` stack (Elide proprietary header), now ejected. The
AGPL-release path would require decoupling the Elide net stack (`httpe` +
`wireguard`/`tailscale`/`transport`/`pki`). The clean-room `http/` crate (a
pure-std HTTP/1.1 vocabulary "so the gateway can drop the Elide `httpe`
dependency") + the artifact-agnostic `conformance-kit` are the *start* of that
decouple, but `httpe` is still the live gateway and the mesh still rides Elide
`wireguard`/`tailscale`. `polyana` is already Apache-2.0 (no blocker there).

Verdict: **🔴 by design; not the goal.**

---

## Part 3 — Verdict table + ranked fixes

| Artifact | Alone | +Light-Claude | Blocking barrier |
|---|:--:|:--:|---|
| `dregg-node` (unverified / marshal-only) | 🟡 | 🟢 | Runs, but silently un-verified on a fresh clone; QUICKSTART doesn't warn |
| `dregg-node` (verified Lean-linked) | 🔴 | 🟡 | 171 MB gitignored seed + cold `lake`/mathlib bootstrap (hours) + closure-link troubleshooting |
| `dregg-agent` runtime | 🟢 | 🟢 | none — `bash demo/business.sh`, one command |
| cipherclerk extension | 🟢 | 🟢 | none — prebuilt `.zip`/`.xpi` in `dist/` |
| `@dregg/sdk` (npm) | 🟢 | 🟢 | published + verified; live use needs a local node |
| `dregg` (PyPI) | 🟢 / 🟡 | 🟢 | install fine; live hello-world needs a local node |
| DreggNet cloud | 🔴 | 🔴 | needs operator infra + credentials; retained Elide `oracle/` non-relicensable (by design) |

### The single biggest self-host barrier

**The verified Lean-linked node build.** The 171 MB `libdregg_lean.a` seed is
gitignored, so a fresh `cargo build -p dregg-node` silently produces a
marshal-only (un-verified) node — and `QUICKSTART.md` shows the verified
`state_producer:"lean"` output a fresh clone can't reproduce, without ever
mentioning `bootstrap.sh`. Getting the real thing means a cold `lake`/mathlib
bootstrap (hours) plus closure-link troubleshooting. That is the wall between "a
stranger runs a node" and "a stranger runs a *verified* node."

### Ranked fix-list

1. **Make QUICKSTART honest about the node build (cheap, do first).** §1 must
   either (a) tell the reader to run `./scripts/bootstrap.sh` first and set the
   cold-build expectation, or (b) state plainly "a fresh-clone node is
   marshal-only / un-verified; to get the verified Lean producer see
   `docs/BUILD-LEAN-LINKED-NODE.md`." Today it prints `state_producer:"lean"`
   output a fresh clone won't reproduce. This is a text-honesty gap, hours to fix.

2. **Ship a prebuilt HEAD-matching Lean seed as a release artifact (biggest
   lever).** Publish `libdregg_lean.a` (per-platform Mach-O/ELF) *or* the warm
   `.lake` `.olean` IR cache per node release, and have `bootstrap.sh` fetch it.
   This turns the hours-long cold bootstrap into minutes and removes the
   closure-link failure mode entirely — it converts the verified node from 🔴 to
   🟡/🟢 alone. This is the single highest-value fix.

3. **Wrap a "verified node in ~10 min" one-script path** around fetch-seed +
   `DREGG_REQUIRE_LEAN=1 cargo build` + the `nm` verify. The recipe already
   exists in `BUILD-LEAN-LINKED-NODE.md`; it just isn't one command a stranger
   can run.

4. **Credit + keep the fail-loud gate (landed this session), but don't mistake
   it for enough.** `DREGG_REQUIRE_LEAN=1` + the startup tripwire stop *silent*
   unverified deploys — necessary, and good. They do NOT make the verified build
   *easy*; #2 is what does that.

5. **SDKs: confirm the PyPI release actually ran.** npm `@dregg/sdk@0.3.0` is
   published + verified; the pip publish workflow exists — verify a release fired
   and add a `PUBLISHED-VERIFY.md` twin like sdk-ts has.

6. **Point strangers at the easy wins.** The README/QUICKSTART should route by
   effort: agent demo (green, one command) → SDKs (green, published) → node
   (needs bootstrap) → cloud (not self-hostable). Right now the node — the
   hardest path — is the front door of QUICKSTART.

---

*Honest both ways: the agent runtime, the extension, and the SDKs are genuinely
runnable by a stranger today; the fail-loud marshal-only guards landed this
session and are real; the verified node is the one real wall, and the fix (a
prebuilt seed) is known and tractable.*
