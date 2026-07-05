# The myopia audit — generic cloud wearing a dregg hat, surface by surface

*A read-only, adversarial review of `~/dev/DreggNet` at HEAD (branch `dev`,
2026-06-30) against ONE thesis ember named:*

> **The swarm built a generic cloud — fly.io-clone machines, an S3-clone bucket
> store, a Vercel-clone deploy, a Vault-clone secret store, a CloudWatch-clone log
> store, a Stripe-clone invoice — with a *verifiable veneer* bolted on, when
> DreggNet was supposed to be dregg's *native primitives* (umem, the capacities,
> the cap algebra, turns/effects, the merge runtime, checkpointable/time-travel,
> the reactor) extended into real resources. dregg looks "decorative" for hosting
> BECAUSE we built generic hosting, not dregg-native hosting.**

This audit grades that. It is **complementary** to and does not restate the three
existing reviews — `docs/ARCHITECTURE-CRITIQUE.md` (thesis drift: receipts-as-logs,
per-op settlement, bridge over-relay, the missing merge runtime), `docs/CRITIQUE-ARCH.md`
(structural debt/duplication), and `docs/SOUNDNESS-TWINS-CENSUS.md` (proven-vs-twin:
the cloud reimplements PROVEN primitives as unverified twins). This one grades a
fourth axis: **for each cloud surface, is it a generic reimplementation or a dregg
primitive extended — and if generic, what does that cost?**

Honest both ways. The verdict is more interesting than a flat "yes, it's myopic":
**the cloud is genuinely dregg-shaped in its *authorization + audit* spine (caps,
receipts, budget ceilings) and almost entirely generic in its *resource substrate*
(the thing being hosted/stored/computed) — because the one primitive that would make
a server/bucket/site/grain a witnessed, forkable, snapshottable, mergeable object,
`umem`, is used in ZERO surfaces.**

---

## 0 · The keystone finding — two axes, and umem is on neither call site

A whole-cloud grep settles the question before the surface walk:

- **`umem`** appears in the cloud's Rust **only in doc-comments** (`webapp/src/hosting.rs`,
  `storage/src/{lib,object,bucket}.rs`, `exec/src/host_api.rs`) as the aspirational
  *"the cell's committed umem heap root"* the on-chain seam *would* commit to — plus
  **one stand-in type** in `sandstorm-bridge/src/cell.rs` (`Umem`, a SHA-256-committed
  `BTreeMap` explicitly *"the prototype's stand-in for turn/src/umem.rs"*, §7). There
  is **no real `umem` dependency, no kernel umem cell, anywhere in the product** — the
  one place a grep finds the word in executable code, it's a serde-map stub.
- The only **`Effect::`** reference in the data/compute crates is a doc-comment in
  `durable/src/verified.rs:69` describing the S3-gated *future* `Effect::Transfer`.
  No surface issues a real kernel turn/effect.
- Every data-plane surface is an **in-memory `Mutex<HashMap|BTreeMap>` registry**:
  sites (`webapp/src/hosting.rs:576`), buckets (`storage/src/registry.rs:52`),
  domains (`dregg-domains/src/lib.rs:408`), secrets
  (`dregg-secrets/src/store.rs:46`), servers (`control/src/server.rs:529`), mesh
  nodes (`control/src/mesh.rs:737`), machines (`control/src/local.rs:19`),
  scheduler/orchestrator workloads (`scheduler.rs:106`, `orchestrator.rs:182`), logs
  (`dreggnet-logs/src/lib.rs:246`). Persistence, **where it exists at all**, is the
  from-scratch JSON-lines `dreggnet-store::RegistryLog` (`store/src/lib.rs`).

So there are **two different "dregg-native" axes**, and the cloud scores oppositely
on them:

| Axis | What it is | Cloud's grade |
|---|---|---|
| **Authorization + audit veneer** | the `dga1_` cap algebra (attenuate=append, no-amplify), the receipt chain, the `ReplenishingBudget` ceiling | **genuinely dregg-shaped + load-bearing** — but as **unverified twins/ports**, not kernel deps (`SOUNDNESS-TWINS-CENSUS`) |
| **Resource substrate** | the cell itself: the durable, *witnessed*, *forkable*, *snapshottable*, *mergeable*, *time-travelable* state being hosted/stored/run | **generic** — a serde struct in a `Mutex` map + a JSON-lines log; **umem is used nowhere** |

ember's thesis is correct, but the precise shape is: **the veneer IS dregg (the
caps/receipts are not naming — they're real ed25519 caveat chains and prev-hash
receipt chains the front office leans on). The *substrate* is the myopia: we
reimplemented persistence (`dreggnet-store`) that umem already gives, held every
"cell" as a serde struct, and deferred the umem cell / the turn / the light-client
witness to "the circuit swarm's VK-epoch." The verifiable veneer (Poseidon2
`content_root` + `dga1_` caps + ed25519 receipts) sits on top of a generic data
plane — and the umem superpowers (fork/snapshot/merge/time-travel) that should
DIFFERENTIATE the resources are absent precisely because the resources aren't umem
cells.**

The rest of this doc walks each surface against that frame.

---

## 1 · Hosting (`webapp/src/hosting.rs`, `gateway/src/hosting.rs`) — "a site is a cell"

**What we built.** `SiteRegistry` (`webapp/src/hosting.rs:574`) is a
`Mutex<BTreeMap<String, SiteCell>>` (+ a parallel `Mutex<BTreeMap<…, PublishReceipt>>`
at `:589`), optionally durably-backed by a `dreggnet-store` JSON-lines log. A
`SiteCell` (a serde struct: name, owner, `content_root`, `content: path→Asset`) is
inserted on publish; `resolve` maps `host→name→Asset`. **Genuinely dregg-native
parts:** the `content_root` is the **REAL sorted-Poseidon2 umem heap root** via
`dregg_circuit` (no stand-in, post-`0b2457d` which killed the FNV scar); the publish
is `PublishCap`-gated (`site-host/<name>`, a real attenuation); a `PublishReceipt`
is sealed into the prev-hash ed25519 `dreggnet-receipt` chain; and the trustless
per-asset opening re-witnesses served bytes against the committed root.

**What the dregg-native version would be.** A site IS a **umem cell on a node**;
`publish` is a real cap-gated **`Effect::Write`** turn whose receipt is the kernel
`TurnReceipt`; the durable state is the **committed umem heap**, not a serde struct
in a `Mutex` map shadow-persisted to a JSON log. The hosting module's own doc
(`:39-47`) names exactly this as the seam: *"committing the SiteCell to a dregg node
— the publish turn as a real Effect::Write … is the circuit swarm's VK-epoch."*

**Load-bearing or decorative, and why.** **Half-and-half, decorative-because-generic
on the substrate axis.** The cap-gate, the Poseidon2 root, and the trustless read
are real and load-bearing (a host *cannot* lie about served bytes). But the *cell*
is a serde struct: there is no fork, no snapshot, no merge, no time-travel, no
in-circuit witness of the write — because it isn't a umem cell. The "site is a cell"
claim is true of the *commitment shape* and false of the *runtime object*.

**The re-dregg move.** Make `SiteCell` a thin view over a real umem cell; route
`publish` through a real `Effect::Write` turn (the dependency, not the twin, now that
the AGPL firewall is dissolved — `FIREWALL-DISSOLUTION.md`). **Unlocks:** atomic
preview/branch deploys (fork the site cell, serve the fork, stitch or discard —
free from umem branch/stitch), instant rollback (time-travel to a prior committed
root), and the in-circuit light-client witness that the served root is the genuine
committed state — none of which a `Mutex<BTreeMap>` can do.

---

## 2 · Object storage (`storage/`) — the S3 clone with a real commitment

**What we built.** `BucketRegistry` is a `Mutex<BTreeMap<String, BucketCell>>`
(`storage/src/registry.rs:52`); a `BucketCell` (serde struct: name, owner,
`content_root`, `content: key→Object`) with `put`/`get`/`delete`/`verified_get`
emitting `BucketReceipt`/`PutReceipt`/`DeleteReceipt` (`registry.rs:302`). This is an
S3 surface (buckets, keys, objects, content-types). **Genuinely dregg-native parts:**
like hosting, the `content_root` is a **real wide-8-felt Poseidon2 cell-heap root**
(`storage/src/bucket.rs:136-187`, via `dregg_circuit::heap_root::compute_heap_root_entries`
+ `wire_commit_8`), the op is cap-gated (`storage-bucket/<name>`), and `verify_opening`
(`bucket.rs:228`) is a genuine trustless leaf-fold read.

**What the dregg-native version would be.** A bucket IS a **umem state-cell**;
`put`/`delete` are **turns** over its heap; persistence is the committed heap. The
module's own doc (`bucket.rs:42-52`) calls the real on-chain write the named seam and
labels the in-memory registry the stand-in.

**Load-bearing or decorative.** Same split as hosting: the *commitment + cap + read*
are real and load-bearing; the *bucket-as-object* is generic (a `Mutex` map). The
S3 clone is the most defensible generic surface — object storage genuinely IS a
key→bytes map — but the differentiator dregg promised ("storage as mergeable,
witnessed umem-state-cells") is absent.

**The re-dregg move.** Bucket → umem cell; `put`/`delete` → turns; let two replicas
of a bucket **merge** coordination-free over the I-confluent (grow-only object-set)
fragment, settling at a boundary — the `ARCHITECTURE-CRITIQUE.md §5.4` merge runtime,
which a serde-struct bucket structurally cannot host. **Unlocks:** CRDT-mergeable
multi-writer buckets, witnessed durability (the heap root IS the durability), and
the light-client read.

---

## 3 · Compute / machines (`control/src/{server,scheduler,orchestrator}.rs`, `gateway/src/gateway.rs`) — the fly.io-machines clone

**What we built.** The most overtly generic surface. `gateway/src/gateway.rs:1` is
literally *"an in-memory machine registry that maps fly create calls onto dregg
leases."* A `Machine`/`ServerRecord` is a serde struct with a lifecycle enum
(`ServerState::{Created,Running,Stopped,Lapsed,Destroyed}`, `server.rs:72`); a
persistent server is a `Mutex<HashMap<String, LiveServer>>` (`server.rs:529`) over a
`VmProvider` machine, durably recorded in a JSON-lines `ServerStore`. *"Today a
gateway 'machine' is an in-memory HashMap entry"* (`server.rs:33`). The
provision→run→meter→reap loop is real and exactly-once; the lease-gate and conserving
settlement are real (`orchestrator.rs`).

**What the dregg-native version would be.** This is the **highest-payoff myopia**,
because dregg *already has the primitive that makes it native*: a server is a
**checkpointable umem cell** — forkable, snapshottable, passable — not "a container we
manage." dregg's umem revolutions LIVE include **checkpointable-runtime** and
**time-travel** (MEMORY: umem-as-primitive epoch). A "stopped/sleeping" server should
be a **checkpoint to its committed umem heap** (the VISION's "pay-only-while-awake"
property); a "wake" should be a heap restore; a fork should be a cell branch. Instead
`stop`/`wake` is a lifecycle enum that releases/re-provisions a `VmProvider` machine —
the fly.io model, not the umem model.

**Load-bearing or decorative.** **The lease-gate, metering, and settlement are
load-bearing and real; the compute UNIT is fully generic.** dregg is decorative on
the compute object itself — a `ServerRecord` is a fly Machine with a `lessee` field.
The VISION's headline superpower #6 (pay-only-while-awake via checkpoint to the
committed umem heap) and #2 (a workload is a cell that transacts) are *described* but
not *built*: the server cannot hold caps, own assets, pay for its own next period, or
checkpoint to a witnessed heap, because it is not a cell.

**The re-dregg move.** A server IS a umem cell carrying a cap-bounded workload; its
running image is a committed heap; sleep = checkpoint, wake = restore, scale = fork.
**Unlocks:** genuine pay-only-while-awake (checkpoint releases the lease, bills only
storage), live migration/fork as a heap pass, time-travel debugging of a crashed
server, and a workload that transacts from inside the sandbox (the §2 VISION
superpower). This is the single change that most converts "a verifiable veneer over
fly.io" into "a cloud whose unit of compute is a unit of account and authority."

---

## 4 · Execution tiers (`exec/`) — owned + in-crate (the wasm tier real, the rest honest seams)

**What we built.** `exec/src/lib.rs::run_workload` maps a dregg lease's `CapTier` → an
**owned, in-crate** execution engine. The `Sandboxed` tier runs on an owned, vendored
pure-Rust `wasmi` interpreter (zero `unsafe`, no external dependency, provider
`dreggnet-wasmi`) that genuinely executes. Every stronger tier — `JitSandboxed`/JIT,
`Caged`/native, `MicroVm`/Firecracker, `Gpu`, and the native python/node langs — is an
honest, **fail-closed seam** (`ExecError::TierNotServed` / `NotWired`): never a fake run,
never a silent downgrade. The cap-grade→tier→engine floor check is dregg-shaped.
`exec/src/budget.rs::ReplenishingBudget` (the sporadic-server replenishing meter the
front office leans on) is a real, sound ceiling cell — though a **twin** of the proven
`cell/src/allowance.rs` (`SOUNDNESS-TWINS-CENSUS` #5).

**Native version / load-bearing.** The owned wasmi Sandboxed tier is real and the
cap→tier mapping is the right dregg-shaped boundary. Two gaps remain: the workload is a
wasmi module instance, **not a cell** (so it can't transact/hold-caps/pay from inside,
the §2 VISION superpower), the metering cell is a twin rather than the proven allowance
cell, and the stronger tiers await an owned engine each (fail-closed until then).

**The re-dregg move.** Land the `ReplenishingBudget` widening *in breadstuffs* at the
named `cell/src/budget.rs` home and depend on it (twin→proof); give the workload a
cell handle so it can pay/attenuate from inside the cage (the host-API spine in
`exec/src/host_api.rs` is already the right seam). **Unlocks:** the proven metering
teeth, and workloads-that-transact.

---

## 5 · The economy / durable settlement (`durable/`, `control/src/{settle_ledger,node_api}.rs`) — the most dregg-reaching surface

**What we built.** The money rail is where the cloud reaches *deepest* into a real
dregg primitive. `durable/src/verified.rs` imports the **REAL** `pg_dregg::mirror`
verified hash chain (`RootChain`/`MirrorBatch`/`revalidate_replicated_chain`) — the
dregg-in-Postgres Tier-C core — so tamper/reorder/replay of a settlement row is
caught for real. Exactly-once `(lease,period)` settlement with write-ahead+fsync
(`settle_ledger.rs`) is the high-water mark of the product. **But** the per-turn root
is a **blake3 stand-in** (`verified.rs:82`), the conservation arithmetic is the
in-process `ConservingLedger` **twin** (`settle.rs:200`, a twin of the proven
`conservation_guarantee`), and the proof-attested on-chain `Payable` is **S3-gated**.

**Native version / load-bearing.** **Genuinely partially-native and load-bearing** —
this is the surface to credit most (it actually depends on a real dregg crate). The
re-dregg move is the smallest: depend on `dregg-payable::Payable::pay` for the
conserving `Effect::Transfer` (delete the `ConservingLedger` twin), swap the blake3
root for the Poseidon2 one, flip the tier-c proof verifier. Note this overlaps the
existing `ARCHITECTURE-CRITIQUE §3/§5.2` cadence critique (settle-per-op vs
reconcile-at-boundary) — orthogonal axis, same surface.

---

## 6 · Front office — dregg-shaped authorization, generic resources

The front-office crates are **more dregg-native than the data plane**, because they
lean on the real cap+receipt+budget disciplines — but they gate *generic* resources.

- **`webauth/` — the foundation (genuinely native, a faithful port).** `cred.rs` is a
  **wire-byte-identical port** of breadstuffs `dregg-auth::credential`: real ed25519
  caveat-chain, BLAKE3 domain-separated digests, attenuate=append-only, fail-closed
  admit, and (post-`0372685`) `account_id.rs:61` derives the account id as the real
  **substrate `CellId::derive_raw`** via `dregg_types`. This is the one crate that
  depends on breadstuffs, and the dga1_ cap the whole front office rests on is **real
  attenuation, not naming**. The scar (`SOUNDNESS-TWINS-CENSUS` #6): it's *ported, not
  depended* — the safe swap is `webauth/cred.rs` → a `dregg-auth` dependency.
- **`org/` — IAM, but "a role IS an attenuation" is LITERAL.** `cap.rs:62`
  `attenuate_to_role` appends a permission-set caveat; the no-amplify proof
  (`cap.rs:157`) shows a viewer can't self-promote. Authorization is real cap-verify
  refusal, not a trusted flag. **Generic part:** membership is a `Vec<Membership>` in
  memory; the membership-event stream is sequenced but not yet receipted (named seam).
  Still — RBAC-as-cap-attenuation is the right dregg shape.
- **`dregg-secrets/` — a Vault clone with real cap-gating + audit.** The KMS hierarchy
  (root→KEK→DEK, plaintext never at rest), cap-scoped access (`cap.rs:60`
  `grants_secret`, no-amplify so `secret:A`'s cap can't reach `secret:B`), and the
  prev-hash receipted access audit are all real. **Generic part:** the store is
  `Mutex<BTreeMap<String, Vec<SecretVersion>>>` (`store.rs:46`) — a secret is not a
  umem cell, so no witnessed/forkable secret state. The honest limit (operator-held
  KMS root can derive+decrypt) is documented.
- **`guard/` — quota/rate-limit, reusing the real ceiling cell.** Rate-limiting reuses
  `dreggnet_exec::budget::ReplenishingBudget` + `prepaid_ceiling_admits` (`rate.rs`,
  `quota.rs`) and governance turns are receipted+verifiable. Load-bearing; the budget
  cell is the (twin) kernel primitive, not a hand-rolled counter.
- **`billing/` — a Stripe invoice, but receipt-anchored.** `BudgetGuard` uses the real
  `ReplenishingBudget` ceiling; `verify_against_receipts` traces each line to its
  settled meter receipts (a padded/forged line fails) — the genuinely-credited
  "verifiable invoice." **Generic part:** invoice assembly is plain aggregation and the
  whole-document `seal()` into the receipt chain is a named seam.
- **`dreggnet-logs/` — a CloudWatch clone with a tamper-evident chain.** Cap-scoped
  (`owner==requester`), SHA-256 hash-linked append-only per resource (verifiable within
  the retention window), durable JSONL. The integration hooks (exec/deploy/server) are
  a named seam. Generic store, real scoping+chain.
- **`status/` — a pure status page, no dregg at all (correctly).** An HTTP-probe health
  rollup; zero kernel interaction, no crypto. **Genuinely fine as generic** — a status
  page has no dregg-native form to miss (the honesty law "unreachable=Unknown, never
  green" is its only discipline).
- **`console/` — a dashboard with verify-don't-trust.** Cap-scoped visibility
  (`owner==subject`, the sole filter), subject from the signed webauth header, and a
  `verify_agent_run` panel that re-witnesses a run's receipt chain + budget bound +
  code-root offline. Load-bearing scoping over generic catalog assembly.

**Front-office verdict.** The authorization + audit spine is **real dregg** (cap
attenuation, receipt chains, ceiling cells) and load-bearing — not a veneer. But it is
the *twin/port* grade (`SOUNDNESS-TWINS-CENSUS`), and the *resources it gates* (orgs,
secrets, logs, invoices) are generic in-memory structures, not umem cells. So even the
"native" front office is native-in-authorization, generic-in-substrate.

---

## 7 · The remaining surfaces

- **`store/` (`dreggnet-store`) — the clearest single myopia.** This crate exists *to
  reimplement persistence umem already gives*. Its own doc (`store/src/lib.rs:1-19`):
  *"DreggNet's money rail is durable; its data plane was not … lived in an in-memory
  HashMap and were lost on restart … This crate generalizes [a JSON-lines fsync'd log]
  into one reusable primitive every in-memory registry persists behind."* It is a
  from-scratch append-only blake3-content-addressed log with torn-tail recovery,
  compaction, and a `content_root` — **a careful, well-built reimplementation of
  exactly what a committed umem heap provides** (durable, content-addressed, witnessed
  state). The re-dregg move *deletes this crate*: registries become umem cells; the
  node's committed heap is the durable store.
- **`dregg-deploy/` — a Vercel clone, but the meter is the real spine.** clone→build→
  publish as a crash-resumable workflow metered through the real
  `dreggnet_exec::meter::ReplenishingMeter` (resumes from the meter's own dedup, never
  double-charges) — load-bearing. **Generic part:** publish lands in the `SiteRegistry`
  (inherits §1's substrate gap); the build sandbox is a cap-bounded owned-wasmi run (good).
  Native-in-metering, generic-in-output-cell.
- **`dregg-ipfs/` — a generic pinning bridge (correctly thin).** The real claim ("a
  dregg blake3 commitment IS an IPFS CIDv1") is verified as a **pure encoding
  alignment** (`cid.rs:80`, no re-hash), and the `IpfsClient` is an injected seam.
  No kernel use; it's a transport bridge and honestly so. **Genuinely fine as generic**
  — IPFS is an external network, not a dregg-native form. (The dregg-native angle it
  *could* reach: pin the umem heap's content-addressed leaves so an IPFS fetch
  re-witnesses against the cell root — but that needs §1/§2's umem cells first.)
- **`sandstorm-bridge/` — grain=cell, with the umem stand-in named in the open.** The
  compute tier (real `dreggnet_exec` at `Caged`/`MicroVm`), the powerbox cap (`SturdyRef`
  = a real `dga1_` HMAC-sealed caveat chain, re-verified on restore), and site serving
  are load-bearing and real. **But** the grain's `Umem` (`cell.rs:27`) is explicitly
  *"the prototype's stand-in for turn/src/umem.rs"* — a SHA-256-committed `BTreeMap`,
  not a kernel umem cell. So even the surface whose entire pitch is **grain = cell**
  stubs the cell. This is the myopia in miniature, honestly labeled: everything around
  the cell is dregg-native; the cell itself is a serde map.
- **`dregg-domains/` — a DNS/ACME clone, durably + cap-gated.** `DomainBinding` is a
  real cap-gated record (ed25519 `dga1_` credential, owner = stable subject) persisted
  in a `dreggnet-store::RegistryLog`. Native-in-cap, generic-in-record (a binding is not
  a cell; the RegistryLog is the §7 reimplementation of umem persistence).

---

## 8 · Synthesis

### Ranked by myopia (biggest gap × highest payoff to re-dregg)

1. **Compute / persistent servers (§3) — MOST MYOPIC, HIGHEST PAYOFF.** A server is a
   fly.io Machine + a lessee field; dregg *already has* the native form
   (checkpointable umem cell — fork/snapshot/wake/time-travel) and it is used nowhere.
   Re-dregging this converts the headline product from "verifiable fly.io" to "the
   cloud whose unit of compute is a unit of account and authority" and unlocks the
   pay-only-while-awake cost model the VISION promises. Biggest gap between what's
   built (generic) and what dregg uniquely enables.
2. **`dreggnet-store` + every `Mutex`-map registry (§1,§2,§7) — the substrate myopia.**
   A whole crate built to reimplement durable, content-addressed, witnessed state —
   i.e. umem — plus ~10 in-memory registries it persists. Re-dregging (registries →
   umem cells, the deletes in `SOUNDNESS-TWINS-CENSUS §1`) removes code and unlocks
   fork/merge/time-travel across hosting, storage, domains at once.
3. **The merge runtime (cross-cutting, also `ARCHITECTURE-CRITIQUE §5.4`).** Because no
   resource is a umem cell, the I-confluent *write/merge* path has nowhere to live —
   the cloud's defining "mostly-offchain coordination" superpower is structurally
   blocked by the generic substrate. Re-dregging §2/§3 is the precondition.
4. **Identity port → dependency (§6 webauth).** Native already, but ported-not-depended
   + the rotation/recovery GAP. Small move, high soundness leverage (it's the
   foundation all caps rest on).
5. **The economy twins (§5).** Smallest re-dregg (depend on `dregg-payable` /
   Poseidon2 / flip tier-c) on the surface that *already* reaches deepest.

### Genuinely fine as-is (not myopic, credit where due)

- **`exec/` (§4)** — delegates to a real external engine; the cap→tier boundary is the
  right dregg shape. Narrow gap (workload-as-cell), not a clone.
- **`status/`** — a status page has no dregg-native form to miss; correctly generic.
- **`dregg-ipfs/`** — an external-network transport bridge, honestly thin; the encoding
  alignment is real.
- **The authorization + audit spine** (webauth caps, receipt chains, ceiling cells) —
  real dregg disciplines, load-bearing across the whole front office. The fix here is
  twin→proof, not generic→native.
- **`durable/verified.rs` / `settle_ledger.rs`** — the one surface that depends on a
  real dregg crate (`pg_dregg::mirror`) with the high-water-mark exactly-once
  discipline.

### The honest verdict — how dregg-native is DreggNet, really?

**DreggNet is dregg-native in its authorization-and-audit *spine* and generic in its
resource *substrate*.** Split cleanly:

- **The veneer is real, not decorative-by-naming.** The `dga1_` cap is a genuine
  ed25519 caveat-chain with proven attenuation semantics; the receipts are real
  prev-hash chains; the budget ceilings are real cells; the content commitments
  (post-FNV-kill) are real Poseidon2 heap roots. ember's "verifiable veneer" phrasing
  understates this layer — it is the right dregg shape and it is load-bearing. *But*
  `SOUNDNESS-TWINS-CENSUS` is right that it's **twin/port grade** — sound by
  construction, but the machine-checked proofs one repo over aren't the ones running.
- **The substrate is the myopia ember named.** Every *resource* — server, site,
  bucket, secret, domain, grain, org, log — is a **serde struct in a `Mutex` map**,
  persisted (if at all) through a **from-scratch JSON-lines log that reimplements
  umem's durability**. The primitive that would make these objects dregg-native
  (umem: witnessed, forkable, snapshottable, mergeable, time-travelable cell heaps)
  is used in **zero** surfaces; the real turn/`Effect::Write`/light-client-witness is
  uniformly deferred to "the circuit swarm's VK-epoch." So the resources cannot
  fork/merge/snapshot/time-travel/transact — the exact superpowers that distinguish a
  dregg cloud from fly.io+S3+Vercel.

**One line:** the cloud wears a *real* dregg hat (caps + receipts + Poseidon2
commitments, load-bearing) over a *generic* body (fly-machines + S3 + Vercel + Vault
+ CloudWatch as `Mutex`-map registries) — and looks "decorative for hosting" not
because the hat is fake, but because **the body was never made out of umem cells, so
the thing being hosted is a container we manage, not a cell that forks, merges,
snapshots, and transacts.** The highest-leverage re-dregg is to make the *resource*
a umem cell (start with the persistent server, §3) — which is *less* code
(`SOUNDNESS-TWINS-CENSUS` proves the fixes delete), now unblocked since the AGPL
firewall dissolved (`FIREWALL-DISSOLUTION.md`).

---

*Dated 2026-06-30. Read-only; no code touched. Method: read both trees at HEAD;
grepped the cloud for `umem`/`Effect::`/`Mutex<…map>` to settle the substrate axis
before the surface walk; grounded each surface to file:line; reconciled against the
three sibling reviews (`ARCHITECTURE-CRITIQUE`, `CRITIQUE-ARCH`,
`SOUNDNESS-TWINS-CENSUS`). Verify any specific file:line against HEAD before relying
on it.*

( ⌐■_■ )  *the hat is real — now carve the body out of umem, and the server learns to fork.*
