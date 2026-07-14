# PRIVATE-NODE — running a single private dregg-node on hbox

The **private-deployment FOUNDATION**: one real `dregg-node` running on hbox as a
solo committee-of-one, over the **verified Lean executor**, reachable **only
privately** (localhost by default; the hbox LAN / a WireGuard peer if you widen
the bind). It executes real turns on the effect-VM. No public exposure, no real
value, not the federation.

This is deliberately the small, honest thing: a node you (ember/us) can start,
stop, poke, and dogfood on hbox. The bigger pieces — the multi-node federation,
the on-chain settle, the demo wiring — are **named and separate** (see
[Honest scope](#honest-scope)).

Manage it with [`scripts/private-node.sh`](../../scripts/private-node.sh).

---

## What it is (observed, 2026-07-13 on hbox)

- **Binary:** `dregg-node`, built on hbox from the working tree, linking the
  **verified Lean executor** archive (`libdregg_lean.a`). Startup logs
  `verified-executor archive linked: lean_available() is true — this node runs
  the PROVED Lean executor over the C ABI` (not the marshal-only tripwire). The
  node **refuses to start** marshal-only unless `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`
  — we do not use that escape hatch here.
- **Running:** solo · blocklace consensus · `--enable-faucet` · `--prove-turns`,
  bound to **`127.0.0.1:8420`** (verified: `ss -tlnp` shows `LISTEN 127.0.0.1:8420`,
  never `0.0.0.0`). `/status`:

  ```json
  {"healthy":true,"federation_mode":"solo","consensus_live":true,
   "state_producer":"lean","lean_producer":true,"full_turn_proving":true,
   "producer_covered_effects":21, ...}
  ```
- **A real turn executes on the verified effect-VM.** `POST /api/faucet`
  (amount 1000) builds a real faucet-signed `Transfer` turn, runs it through the
  **Lean producer** (`state_producer:"lean"`), and commits: `GET /api/cell/<id>`
  then returns `"found":true,"balance":1000`. The ledger state changed — this is
  the real effect-VM, not a mock.

### The private-access model (not public)

- **Bind private.** Default `127.0.0.1` (localhost only — nothing off-box can
  reach it). To reach it from another LAN host or a WireGuard peer, set
  `DREGG_PRIV_BIND=192.168.50.39` (hbox's LAN IP) — still private.
- **hbox firewall is untouched and stays that way.** `ufw` is **active**,
  default-deny inbound, LAN `192.168.50.0/24` + SSH only. This work changed **no**
  ufw rule and opened **no** public port. The node never binds `0.0.0.0`
  (`private-node.sh` refuses it), and `dreggcloud` on `:8787` was not disturbed.
- No gateway, no DNS, no TLS, no public reverse-proxy. If you ever want it
  reachable off-LAN, do it over WireGuard the way `OPS-RUNBOOK.md` describes for
  the demos — the gateway/tunnel is ember's outward step, out of scope here.

---

## Run it

Run **on hbox**, from the synced build lane (`~/dregg-build/privnode`; sync it
with `scripts/hbuild privnode true` from the Mac, or rsync the tree). State lives
**outside** the lane at `~/dregg-priv/` so a re-sync of the lane never wipes it.

```bash
# build the verified node on hbox (first build links the Lean archive; see below)
cd ~/dregg-build/privnode
SR="$(cd metatheory && lake env printenv LEAN_SYSROOT)"
DREGG_LEAN_SYSROOT="$SR" DREGG_REQUIRE_LEAN=1 cargo build --release -p dregg-node

# start / check / stop
scripts/private-node.sh start     # init fresh dev genesis on first run, then start; waits for /status
scripts/private-node.sh status    # is it up? prints /status
scripts/private-node.sh check     # submits a real faucet Transfer, asserts it EXECUTED (+ proof status)
scripts/private-node.sh logs 60   # tail the node log
scripts/private-node.sh stop
```

Config via env (all optional): `DREGG_PRIV_PORT` (8420), `DREGG_PRIV_BIND`
(`127.0.0.1`; or `192.168.50.39` for LAN), `DREGG_PRIV_GOSSIP` (9420),
`DREGG_PRIV_DATA` (`~/dregg-priv/data`), `DREGG_PRIV_BIN`
(`./target/release/dregg-node`). Log + pid live in `~/dregg-priv/`.

### The verified-executor build (the artifacts it needs)

`dregg-node` links `libdregg_lean.a`, the Linux-native (ELF) archive of the
compiled Lean kernel (mathlib + `Dregg2.*`). It is **not committed** and is
**architecture-native** — a macOS-built seed will NOT link on hbox (its objects
are Mach-O; the linker reports `neither ET_REL nor LLVM bitcode` / `BSD format`).
Produce a HEAD-matching **Linux** seed on hbox, reusing the box's warm `.lake`:

```bash
cd ~/dregg-build/privnode/metatheory
lake build Dregg2.Exec.FFI Dregg2.Exec.DistributedExports Dregg2.Exec.FFIDirect   # HEAD Dregg2 :c facets
cd ..
dregg-lean-ffi/scripts/seed-dregg2-closure.sh    # leanc → ELF objects → GNU archive (libdregg_lean.a)
# then the cargo build above (DREGG_REQUIRE_LEAN=1) splices the fresh Dregg2 + closure-completes
```

Verify the link took: `nm target/release/dregg-node | grep -c dregg_exec_full_forest_auth`
(> 0 = the verified executor is in). See `docs/BUILD-LEAN-LINKED-NODE.md` for the
full recipe and the fail-loud guards.

> Solo-node caveat: the seed's three FFI roots realize the **executor** core
> (`dregg_exec_full_forest_auth`), which is what a solo node runs. The
> **consensus/finality/admission** exports (`dregg_tau_order`,
> `dregg_blocklace_finalize`, `dregg_strand_admit`) are NOT in that closure and
> are only needed for **full BFT** mode; a full-mode node needs a seed that also
> splices `Dregg2.Distributed.{FinalityGate,StrandAdmission}`.

---

## Honest scope

**This IS:** a single real `dregg-node` running privately on hbox, over the
verified Lean executor, executing real turns on the effect-VM. Dogfoodable. No
public surface, no real value, no mainnet.

**This is NOT (each is a named, separate next step):**

- **The multi-node FEDERATION** — n=4 validators, blocklace BFT finality,
  cross-node attested turns. That needs a full-mode seed (finality/admission
  exports, above) + a committee `genesis.json` + peers. See
  `docs/OPERATOR-ONBOARDING.md` and `deploy/aws/N3-RUNBOOK.md`. This solo node
  produces blocks but finalizes as a committee-of-one.
- **The on-chain SETTLE** — the EVM/Solana/Cosmos settlement wiring is its own
  lane (`chain/`, `bridge/`); nothing here broadcasts to any chain.
- **The demos** — DrEX / launchpad hosting is the `OPS-RUNBOOK.md` lane.

### Known open at this HEAD: full-turn PROVING of a cohort turn

The node runs with `--prove-turns` and spawns the async STARK prove pool, and the
**prover pipeline is real and runs** (it builds the trace and fails *closed* — it
never fakes a proof). But at the **current working-tree HEAD** a value-bearing
cohort turn (a `Transfer` / `SetField`) routes through the **wide rotated IR-v2**
proving leg, and that leg cannot yet realize the **15-bit range table** (wire id
`84 = 64 + 15 + 5`) in its layout resolver:

```
async full-turn proof generation failed: ... wide rotated IR-v2 proof:
constraint 294: custom table id 84 has no realized relation
(only the submask table, id 5, is bound; the custom-table contents manifest
 is the named IR follow-up)
```

This is a genuine **in-flight circuit seam**, not a build/seed/env problem: the
error is pure Rust circuit logic (`circuit/src/descriptor_ir2.rs`), the 15-bit
range-table **emission** landed (`AVAILABILITY WELD LIVE … 15-bit IR-2 range
tables`) but its **realized relation** in the wide layout resolver is the owed
follow-up (corroborated by the active optimizer work — `BUS_P2_1` narrow chip,
the untracked WIP `metatheory/Dregg2/Circuit/NarrowChip.lean`). Both proof legs
route cohort turns here: the async pool hits the seam directly, and the finalized
commit-path proof (which would populate `GET /api/turn/<hash>/proof`) is
additionally preempted in solo mode by a faucet nonce-replay on re-execution.

So today the foundation node **executes real turns on the verified effect-VM**;
**full-turn proof attestation of a cohort turn is the named next thing to close**
(realize the 15-bit range table in `resolve_main_layout`, then re-run
`scripts/private-node.sh check` — it will fetch a real proof and flip to PROVEN).
