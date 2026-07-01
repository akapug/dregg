# STAND-INS census — what's faked that needs to become real

A read-only sweep (HEAD, 2026-06-29) across both repos — `DreggNet` (the
orchestration / hosting / economy plane) and `dregg` (`~/dev/breadstuffs`, the
AGPL verified core) — for the pattern:

> a **stand-in / mock / stub / placeholder / in-process fake** that occupies the
> slot where a **real durable / on-chain / external / hardware** implementation
> is intended.

This is the *"what's faked that needs to be real"* map. It is **distinct from**
the three under-wired catalogs, which census a different defect:

- `docs/UNDER-WIRED-features.md` — built-but-not-live (a crate/test/proof exists,
  no live call site).
- `docs/UNDER-WIRED-circuit.md` — executor-enforces-but-VK-doesn't (a pure light
  client cannot witness it).
- `docs/UNDER-WIRED-parity.md` — Lean-proves-but-Rust-under-enforces.

A built-but-unwired thing is *real code waiting for a call site*. A **stand-in**
is *fake code occupying the slot of real code*. They overlap (several items below
are also UNDER-WIRED rows); where they do, this doc **cross-refs and does not
restate** — it adds the "what is faked / what the real impl is / replacement
effort / is the replacement already built / safe-autonomous vs reviewed-go" lens.

This census is **honest in both directions**: some "stand-ins" are *deliberate,
sound boundaries* (the AGPL link-isolation gate, the LocalProvider dev default,
the `DnsResolver` trait seam, the deos-hermes confinement stand-in) and are NOT
debt — they are called out in [§ Deliberate sound boundaries](#deliberate-sound-boundaries-not-fakes).
Out of scope: the `polyana` submodule (separate repo) and `net/tailscale`
(vendored upstream) — their internal stubs are not DreggNet's to replace here.

Effort: **S** = <1 day · **M** = 1–5 days · **L** = 1–2 weeks.
Disposition: **safe-autonomous** (no live deploy / real money / external service
/ hardware to touch) vs **reviewed-go** (one of those gates applies).

---

## Summary table

| # | What's faked | Where (file:line) | Real impl | Effort | Disposition | Real impl exists? | Cross-ref |
|---|--------------|-------------------|-----------|--------|-------------|-------------------|-----------|
| **Compute / exec** |
| 1 | `invoke()` resolves a **caller-registered service map** | `exec/src/host_api.rs:62-67` | the breadstuffs **ToolGateway** cap/turn rail | M | reviewed-go (cross-repo wire) | **Yes** — `breadstuffs/deos-hermes/src/{lib,bridge}.rs` | new |
| 2 | Firecracker `MicroVm` **boots then `call()` errors** (dead guest plane) | `exec/src/lib.rs:1117`; `polyana/src/firecracker-provider/src/lib.rs:20` | vsock+JSON guest wire + kernel/rootfs image + jailer | M | reviewed-go (KVM hardware) | partial (VM lifecycle real; guest unbuilt) | UNDER-WIRED-features #8 |
| 3 | `Ec2Provider` reports a **stubbed AWS API surface** | `control/src/ec2.rs:98,168` | live `aws ec2 run-instances` + mesh dispatch | M–L | reviewed-go (real cloud / $) | argv builder real; no API exec | UNDER-WIRED-features #22 |
| **Hosting / web** |
| 4 | Web-publish writes an **in-process `SiteRegistry`**; `content_root` is an **FNV-1a** stand-in | `webapp/src/hosting.rs:44,424`; `webapp/src/hosting.rs:180` | `Effect::Write` to a dregg node → committed **Poseidon2** umem heap root, witnessed as a receipt (the `dregg-verify` flip) | M | reviewed-go (AGPL flip + live node) | **Yes** — Poseidon2 in breadstuffs; `bridge/src/dregg_verify.rs` is the read half | UNDER-WIRED-features #18/#19 |
| 5 | Storage object leaf hash is an **FNV-1a** stand-in for the Poseidon2 commit | `storage/src/object.rs:47-50,187-223` | Poseidon2 `content_root` (the real `verify_opening` already uses it on-node) | S–M | reviewed-go (rides #4's node write) | **Yes** — Poseidon2 carrier exists | UNDER-WIRED-features #16 |
| 6 | Custom-domain DNS verify uses **`MockDns`** | `dregg-domains/src/lib.rs:237-275`; `gateway/src/hosting.rs:177-198` | a real `DnsResolver` over a DNS client (hickory/trust-dns) for the TXT/CNAME challenge | S | reviewed-go (external DNS + cert mint) | trait seam real; no live resolver impl | new |
| **Economy / metering** |
| 7 | `MeterTick` increments an **in-process counter** (`ConservingLedger`/`metrics`), not a chain charge | `durable/src/settle.rs:187`; `durable/src/lib.rs:45,506` | a dregg `Payable` charge: one Postgres txn = duroxide checkpoint + lease charge against `pg-dregg` | M | reviewed-go (real value move) | settlement twin real; `NodeApiSettlement`→`Transfer` is the node-facing real path | UNDER-WIRED-features #15 |
| 8 | `bridge::Lease` is a **MOCK struct** mirroring breadstuffs `LeaseTerms` | `bridge/src/lib.rs:32-39,143-156` | read a funded `execution-lease` cell from a dregg node | M | reviewed-go (live node) | breadstuffs `LeaseTerms` real; `DreggNodeFeed` is the read path | UNDER-WIRED-features #19 |
| 9 | `MockFeed` is an **in-memory channel** of leases (dev source) | `bridge/src/watch.rs:235-313` | `from_node_log` light-client RPC (the `dregg-verify` verified read) | M | reviewed-go (AGPL flip + live node) | `VerifiedNodeLeaseSource` built (`bridge/src/dregg_verify.rs`) | UNDER-WIRED-features #19 |
| **Consensus / node / control** |
| 10 | `StubMesh` returns no live tunnel; dispatch over a plain stub is the named deploy step | `control/src/mesh.rs:384-431,549-572`; `control/src/bin/dreggnet-provider.rs:140` | `WireguardMesh` two-node overlay handshake | L | reviewed-go (overlay + hardware) | `TailscaleMesh`/`WireguardMesh` built + loopback-tested | UNDER-WIRED-features #20 |
| 11 | `CellSource::Mock` + `LocalProvider` **in-process leases** (default) | `control/src/config.rs:241-264,274`; `control/src/local.rs:16` | `DreggNodeFeed` verified on-chain lease read driving a real fleet | L | reviewed-go (AGPL + fleet) | the verified read exists; this is the **deliberate dev default** | UNDER-WIRED-features #11/#19/#21 |
| **Sandstorm** |
| 12 | sandstorm-bridge is a **design prototype**: `DreggCapRef`/`SturdyRef`/`receipt:String` stand in for the real cap rail | `sandstorm-bridge/src/powerbox.rs:45,72-83,108-113`; `sandstorm-bridge/src/lib.rs:1-30` | weld onto breadstuffs `dregg-cell` `CapabilityRef`/`EffectMask` + `starbridge-v2/src/powerbox.rs` (CapDesk) + real `TurnReceipt` | M–L | reviewed-go (cross-repo weld) | **Yes** — the real CapDesk powerbox is proven in breadstuffs | new |
| **dregg core (cross-ref only — detail lives in the breadstuffs catalogs)** |
| 13 | `BridgeMint` foreign-proof binding is **executor-only** (circuit credits balance only); Solana path is plain `Mint` + off-circuit attest + a relayer double-mint hole | `turn/src/executor/apply.rs:1411`; `circuit/src/trace.rs:707`; `bridge/src/verifier.rs:29` | fold the built `bridge_action_air` into `effect_vm`+IVC; a live relayer | M–L | reviewed-go (real money / VK epoch) | `bridge_action_air` built + Lean-sound | UNDER-WIRED-circuit G1 |
| 14 | deos-hermes **agent body inside the jail is a Rust stand-in**, not live `hermes acp` | `breadstuffs/deos-hermes/src/host.rs:40`; `confined.rs:22`; `surface.rs:66` | the live `hermes acp` venv subprocess | M | reviewed-go (external agent) | confinement real; **deliberate** (proves the jail, not the agent) | UNDER-WIRED-features #27 |
| 15 | EVM settlement is **mock-mode** (no SP1 prove, no live deploy) | `breadstuffs/chain/src/lib.rs:85-107`; `chain/src/withdraw.rs:135-173` | real SP1 proving + Base Sepolia/Mainnet deploy | M | reviewed-go (real chain / $) | structural scaffold real, mock-only | UNDER-WIRED-features #26 |
| 16 | pg-dregg tier-c attest is a **fail-closed stub** until the S3 circuit flip | `breadstuffs/pg-dregg` (S3 line) | one circuit flip turns the shadow-attest into a real verifier | M | safe-autonomous (circuit work) | S1/S2 built; S3 is the one line | UNDER-WIRED-features #12 |
| 17 | M2 privacy effects (shielded transfer / pool / ZK attest) are **complete crypto with zero executor call sites** | `breadstuffs/circuit-prove/src/shielded/*.rs` | an Effect-vocabulary integration (admission gate + proof-in-action) | M | safe-autonomous (plumbing, not crypto) | **Yes** — the crypto is real + both-polarity tested | UNDER-WIRED-features #1–3 |

---

## Per-stand-in detail (the genuinely-faked, DreggNet-native set)

### 1 — `invoke()` stand-in service registry → the real ToolGateway

`exec/src/host_api.rs:62-67`. A workload's `invoke(service, args)` resolves
against a **caller-registered `ServiceFn` map** (`Arc<dyn Fn(Json) -> Result<Json,
String>>`). The doc-comment names it exactly: *"The real `invoke` target is the
dregg ToolGateway (the breadstuffs cap/turn rail); until that is wired into
`exec`, a workload's `invoke` resolves against a caller-registered service map.
This is the named seam, not a hole — the cap-gate / meter / receipt around it is
already the real surface."* The surrounding spine **is** real: `gate_effect_set`
(dregg's proven monotone attenuation), the metering pre-charge, and the
`TurnShadowReceipt` chain all bite. Only the *target resolution* is faked.

- **Real impl exists:** **Yes.** `breadstuffs/deos-hermes/src/{lib,bridge}.rs`
  carries a real `ToolGateway` (the cap/turn-gated tool-call rail, red-team
  tested). The replacement is wiring `exec`'s broker `invoke` onto it.
- **Effort:** M (cross-repo wire; the bridge vocabulary already maps `invoke →
  tool-call`). **Disposition:** reviewed-go (touches the AGPL core seam).

### 2 — Firecracker microVM: boots then refuses

`exec/src/lib.rs:1117`; `polyana/src/firecracker-provider/src/lib.rs:20` ("dead
guest plane"). The VM **lifecycle** is real (spawn the firecracker API process,
boot, teardown, `with_jailer`), but a booted VM **errors on `call()`** because the
vsock guest-invocation wire + in-guest agent are not landed. No workload runs
inside a microVM yet — it boots and refuses (the clean, honest hardware-gated
refusal on a non-KVM host). Full detail in UNDER-WIRED-features #8.

- **Real impl exists:** partial (lifecycle real; guest plane unbuilt).
- **Effort:** M. **Disposition:** reviewed-go (KVM hardware).

### 3 — `Ec2Provider` stubbed AWS API

`control/src/ec2.rs:98,168`. The `run_instances_argv` / `terminate-instances`
argv builders are real and tested, but the provider "reports its stubbed API
surface" rather than actually shelling out to AWS; `run_lease` dispatches over a
mesh only when one is attached, else "reports an unwired stub." The real impl is
executing the argv (or the AWS SDK) to provision a live box, then dispatching the
workload to its bridge agent over the mesh.

- **Real impl exists:** argv real; no API execution. **Effort:** M–L.
  **Disposition:** reviewed-go (real cloud spend). Coupled to #10 (the mesh).

### 4 — Web-hosting: in-process `SiteRegistry` + FNV `content_root`

`webapp/src/hosting.rs:44,180,424`. A published site **is** a cell, and the
publish→serve round-trip over real TCP is tested — but the publish writes an
**in-process `SiteRegistry`**, and the `content_root` is an **FNV-1a/64** hash
over the canonical `(path, content_type, body)`, the in-process stand-in for the
cell's **committed umem heap root**. The real move is an `Effect::Write` to a
dregg node, the heap committed with **Poseidon2**, witnessed as a receipt — i.e.
the `dregg-verify` flip (#9/#11). The serving is real; the on-chain dimension is
the stand-in. Detail in UNDER-WIRED-features #18.

- **Real impl exists:** **Yes** — Poseidon2 is the deployed carrier in breadstuffs;
  `bridge/src/dregg_verify.rs` is the verified-read half. **Effort:** M.
  **Disposition:** reviewed-go (AGPL flip + a live node carrying data).

### 5 — Storage object: FNV-1a leaf hash

`storage/src/object.rs:47-50,187-223`. *"on a dregg node this is the object's
committed leaf hash (Poseidon2); in-process it is the FNV-1a stand-in."* A small
deterministic `Fnv` hasher stands in for the Poseidon2 leaf. The trustless object
store's `verify_opening` is otherwise real. Same Poseidon2 swap as #4, riding the
same node-write flip.

- **Real impl exists:** **Yes** (Poseidon2). **Effort:** S–M. **Disposition:**
  reviewed-go (rides #4).

### 6 — Custom domains: `MockDns`

`dregg-domains/src/lib.rs:237-275`; consumed at `gateway/src/hosting.rs:177-198`.
The DNS challenge-verify (TXT/CNAME) runs against a deterministic in-memory
`MockDns`. The `DnsResolver` trait **is** the real seam (`dregg-domains` doc:
*"a real implementation wraps a DNS client; tests use `MockDns`"*); the production
resolver over a live DNS client is simply not written, and no cert is ever minted.

- **Real impl exists:** trait seam real; no live resolver/cert path. **Effort:**
  S (wrap hickory/trust-dns). **Disposition:** reviewed-go (external DNS + ACME
  cert mint).

### 7 — `MeterTick` in-process counter → dregg `Payable`

`durable/src/settle.rs:187` (`ConservingLedger`, "the faithful in-process twin");
`durable/src/lib.rs:45,506` (the in-process `metrics` ledger). The metered tick
increments a process-local counter, not a real chain charge. The "transactional
twin" (work + meter committed together) is real *within duroxide's history*, but
the meter side is not a chain transfer. The real rung: make `MeterTick` a
`Payable` against `pg-dregg` (one Postgres txn = the duroxide checkpoint + the
lease charge). **Note (honest):** the *node-facing* settlement path
(`NodeApiSettlement` → `Effect::Transfer` per period, with a fsync'd dedup ledger)
IS real and wired in `dreggnet-provider` — it just isn't a deployed binary (#10).
The in-process `ConservingLedger` is an **honestly-labelled twin**, not a
disguised fake. Detail in UNDER-WIRED-features #15.

- **Real impl exists:** the settlement twin + `NodeApiSettlement` are real; the
  `pg-dregg` charge is the rung. **Effort:** M. **Disposition:** reviewed-go
  (real value move); blocked on pg-dregg #16.

### 8 / 9 — `bridge::Lease` MOCK + `MockFeed`

`bridge/src/lib.rs:32-39,143-156`; `bridge/src/watch.rs:235-313`. The `Lease`
struct mirrors breadstuffs' `LeaseTerms` but is constructed in-process
(`Lease::funded`); `MockFeed` is an in-memory channel of leases (the dev source).
The real source is `from_node_log` — the light-client verified read
(`VerifiedNodeLeaseSource`, built in `bridge/src/dregg_verify.rs`) reading funded
leases off a node's receipt log. The seam between "where leases come from" and the
watcher is clean; the verified RPC is named, not yet the default.

- **Real impl exists:** **Yes** (`VerifiedNodeLeaseSource`). **Effort:** M.
  **Disposition:** reviewed-go (AGPL `dregg-verify` flip + live node with data).

### 10 — `StubMesh` mesh dispatch

`control/src/mesh.rs:384-431,549-572`; placeholder overlay handshake material at
`control/src/bin/dreggnet-provider.rs:140`. On non-Linux (the dev host) and by
honest default, the mesh is a `StubMesh` with no live tunnel; a plain stub link
"cannot carry the workload — that is the live-overlay deploy step," and dispatch
is exercised only against a loopback fulfill stub. The real impl
(`WireguardMesh`/`TailscaleMesh`) is built and loopback-tested; the live two-node
WireGuard handshake is never brought up. Detail in UNDER-WIRED-features #20.

- **Real impl exists:** **Yes** (mesh engines built). **Effort:** L.
  **Disposition:** reviewed-go (overlay bring-up + a second machine).

### 11 — `CellSource::Mock` + `LocalProvider` (the dev default)

`control/src/config.rs:241-264`; `control/src/local.rs:16`. The default-green path
is in-process mock leases + a `LocalProvider` running workloads in-process via the
bridge — *no dregg node required*. This is a **deliberate dev default**, not a
disguised production fake (it is honestly named "mock (in-process leases)"), but
it occupies the slot the verified `DreggNodeFeed` + real fleet fill. Listed for
completeness; see [§ Deliberate sound boundaries](#deliberate-sound-boundaries-not-fakes).

### 12 — sandstorm-bridge prototype

`sandstorm-bridge/src/powerbox.rs:45,72-83,108-113`; `sandstorm-bridge/src/lib.rs`.
The whole crate is a **design prototype** that models the grain=cell / powerbox=cap
/ SturdyRef=HeldToken mappings "as plain Rust + tests, so the design can be
exercised before the production weld." `DreggCapRef` stands in for a real
`CapabilityRef`+`EffectMask`; `to_sturdyref()` is a deterministic handle standing
in for the encoded `dga1_…`/`HeldToken`; `PowerboxGrant.receipt: String` stands in
for a real `TurnReceipt`. The crate's own doc names the real target:
*"the same shape the real `starbridge-v2/src/powerbox.rs` (CapDesk) already
proves."*

- **Real impl exists:** **Yes** — the real CapDesk powerbox + cap rail are proven
  in breadstuffs. **Effort:** M–L (weld the manifest/grain/powerbox onto the real
  crates). **Disposition:** reviewed-go (cross-repo weld + the `.spk` supervisor).

### 13–17 — dregg-core cross-refs (detail in the breadstuffs catalogs)

These are genuine faked-needs-real items, but they live in `breadstuffs` and are
already documented in the under-wired catalogs; recorded here only so the map is
complete:

- **13 BridgeMint** — executor-only foreign-proof binding; the Solana mirror path
  is plain `Mint` + off-circuit attest with a documented concurrent-relayer
  double-mint hole. **A pure light client can be fooled about a bridge mint's
  backing.** Real money. (UNDER-WIRED-circuit G1.)
- **14 deos-hermes agent body** — a Rust ACP stand-in, deliberately (it proves the
  confinement, not the agent). (UNDER-WIRED-features #27.)
- **15 EVM settlement** — mock-mode only; no SP1 prove, no live deploy.
  (UNDER-WIRED-features #26.)
- **16 pg-dregg tier-c attest** — a fail-closed stub until the S3 circuit flip
  (attests nothing until then — the safe direction). The load-bearing blocker
  under #4/#7/#9. (UNDER-WIRED-features #12.)
- **17 M2 privacy effects** — complete, both-polarity-tested crypto with zero
  executor call sites; the gap is Effect-vocabulary plumbing, not crypto.
  (UNDER-WIRED-features #1–3.)

---

## Deliberate sound boundaries (NOT fakes)

Honest the other way — these read as "stand-ins" but are *correct, sound
boundaries*, and replacing them would be a regression or a license violation:

- **`exec/src/lib.rs:869,1001-1030`** — when the `polyana` feature is off (or on
  macOS where a tier is unsandboxed), `exec` returns **`Err`** rather than a fake
  success. An honest refusal is the right behavior; there is nothing to "make
  real."
- **`CellSource::Mock` + `LocalProvider` (#11)** — the deliberate offline/dev
  default so the binary builds + runs green with no node. The real path is opt-in
  (`--features dregg-verify` + a node URL), exactly the no-reflexive-features
  architecture wants. Keep the dev default; flip to verified for production.
- **`MockFeed` (#9) / `MockDns` (#6) — the trait seams.** `LeaseFeed` and
  `DnsResolver` are real abstractions; the mock is the *test instance*. The work
  is writing the production instance behind the same trait, not deleting a fake.
- **deos-hermes stand-in agent (#14)** — the confinement (cap-bounded PD launch,
  sandbox-probe verdict) is real and is what's being proven; the agent body is a
  stand-in *by design* so the test exercises the jail, not a live LLM.
- **`durable` `ConservingLedger` (#7)** — an *honestly-labelled* in-process twin
  of a dregg `Payable`, not a disguised stub; the real node-facing
  `NodeApiSettlement`→`Transfer` path already exists beside it.
- **The `dregg-verify` AGPL gate (#4/#9/#11)** — keeping the verified on-chain
  read behind a feature so the default build stays Apache-pure is a deliberate
  **license isolation** boundary, not laziness. The flip is a workspace-patch +
  live-node step, correctly gated.
- **sandstorm-bridge (#12)** — explicitly a *design prototype* to exercise the
  mapping before the production weld; sound as a prototype, named as one.

---

## Replace-next shortlist (value × tractability: real-impl-exists + safe-autonomous first)

1. **#16 pg-dregg S3 circuit flip** (one line, **safe-autonomous**, real impl
   built) — turns the tier-c attest from a fail-closed stub into a real verifier
   and **unblocks #4 / #5 / #7 / #9** (the on-chain content-root + the real
   `Payable` charge all sit on top of it). Highest leverage smallest move.
2. **#17 wire the M2 privacy effects** (**safe-autonomous**, crypto already real)
   — a complete, sound crypto library is one Effect-vocabulary integration away
   from shippable shielded transfers + ZK attestations. No live deploy, no money.
3. **#1 `invoke` → real ToolGateway** (real impl exists in breadstuffs) — closes
   the last fake in the otherwise-real host-API spine (cap-gate/meter/receipt
   already bite). Cross-repo wire; reviewed-go for the AGPL seam.
4. **#4 + #5 Poseidon2 content-root** (real impl exists; rides #16) — swap the FNV
   stand-ins for the real committed heap root once the node-write flip is taken,
   making hosting + storage genuinely on-chain-verifiable.
5. **#6 real `DnsResolver`** (S, trait seam ready) — small, but reviewed-go
   (external DNS + cert mint); the production resolver behind the existing trait.
6. **#7 `MeterTick` → `Payable`** (reviewed-go; rides #16) — turns metered demos
   into genuinely on-chain-settled services.
7. **#10 / #3 the distributed fleet** (mesh overlay + EC2 API + deploy
   `dreggnet-provider`) — largest lift, reviewed-go (hardware/cloud/$), gated
   mostly on ops not code; the mesh engines are built.
8. **#13 BridgeMint in-circuit weld** (reviewed-go, real money, VK epoch) — the
   highest soundness-value but heaviest; fold the built `bridge_action_air` into
   `effect_vm`. Also close the Solana double-mint hole.

**One sentence:** the DreggNet-native fakes are a small, honestly-named set —
mostly **FNV-for-Poseidon2** content roots, **in-process-for-chain** meters/leases,
**mock-for-real** DNS, and a **stub mesh / stubbed EC2** fleet — almost all of
which have their real implementation **already built** in breadstuffs or behind a
deliberate `dregg-verify` flip, with the **pg-dregg S3 circuit line** as the
single highest-leverage unblock, and the `invoke→ToolGateway` wire as the one fake
in an otherwise-real host-API spine.
