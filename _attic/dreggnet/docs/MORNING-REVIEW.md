# MORNING REVIEW — reviewed-go queue for ember

Overnight coordination produced items that are **staged and reviewed-GO**, but
deliberately NOT fired (committee changes and submodule merges are guardrailed).
Each item below is ready; ember's one-word go fires it. More overnight items will
be appended to this file as they land.

Status as of 2026-06-29 (overnight). Author: scout-emberian (overnight runner).

---

## 1. n=4 EPOCH-TRANSITION — READY (David standing by for "proposed")

**What.** Grow the live committee by adding David's two snoopy validators.

**Why it's safe to fire live.** The live epoch transition is WIRED in the dregg
node (`c15780bc5` — "wire LIVE epoch transition into running consensus:
validator add/remove/rotate, chain-continuing"). It is a **live committee change**:
no genesis re-roll, no `federation_id` change, the chain keeps advancing, and it
is **reversible** (a later transition can remove what this one adds). Proposing is
NOT authority — the change only APPLIES once a quorum of the CURRENT committee
ratifies it through finality (`federation/src/epoch.rs::propose_epoch_transition`,
node CLI `ProposeEpochTransition`).

**The two validators to add (David's homelab, both on snoopy 32c/176G):**
- snoopy-lean  `ac8377fd…`  (`:8420` API / `:9420` p2p) — Lean executor
- snoopy-rust  `027e299c…`  (`:8421` API / `:9421` p2p) — Rust executor

This is deliberately a **mixed-executor** committee (Lean ↔ Rust differential
running in production every block).

**Topology reconciliation — a decision ember should make.**
The current live committee is `{edge, persvati, persvati-rust, snoopy}`
(`federation_id 316d14fd`, from the earlier re-roll). David's intended shape is
`{edge, persvati, snoopy-lean, snoopy-rust}`. Adding the two snoopy validators is
unambiguous; the open choice is **persvati-rust**:
- **(a) David's topology** — also remove `persvati-rust`, landing a clean
  4-node `{edge, persvati, snoopy-lean, snoopy-rust}`.
- **(b) keep it** — land a 5-node `{edge, persvati, persvati-rust, snoopy-lean,
  snoopy-rust}` committee (more redundancy; snoopy then carries 2 of 5).

**Note on independence / f.** Both snoopy validators run on ONE machine, so this
is not yet 4 independent fault domains. lassie comes online tomorrow → migrate
`snoopy-rust → lassie` (a rotate transition) for 4 independent machines and true
f=1.

**The op (fires on ember's "proposed"):**
```
dregg-node propose-epoch-transition --add ac8377fd… --add 027e299c…
# add `--remove <persvati-rust-pubkey>` if choosing topology (a)
# (--port/--token as the running node requires)
```

---

## 2. COMPUTE ENGINE — OWNED + IN-CRATE (this item is SUPERSEDED)

**What.** This slot used to be a staged external-submodule mainline merge for the
compute/sandbox engine. That whole path is **superseded and closed**: the external
compute submodule has been **fully removed**, and compute is now **owned and
in-crate**. There is no submodule pointer to bump, no external mainline to adopt, and
no forward-port dependency to wait on.

**The new reality (already landed, not a reviewed-go).** The `Sandboxed` wasm tier
runs on an owned, vendored pure-Rust `wasmi` interpreter (zero `unsafe`, no external
dependency) that genuinely executes — the `add(40,2)=42` dogfood runs here (provider
`dreggnet-wasmi`). Every stronger tier — `JitSandboxed`/JIT, `Caged`/native,
`MicroVm`/Firecracker, `Gpu`, and the native python/node interpreter langs — is now an
honest, fail-closed seam (`ExecError::TierNotServed` / `NotWired`, provider labels
`dreggnet-native (seam)` / `dreggnet-microvm (seam)`): never a fake run, never a silent
downgrade. Wiring an owned engine for each stronger tier is ordinary future work in
this repo — no external merge, no gate.

---

## 3. AUTO-DEPLOY PUBLIC WEBHOOK — REVIEWED-GO (the §3.1 reviewed-go half)

**What's built + green (safe-autonomous, landed).** `dregg-deploy` — the keystone
auto-deploy-from-git DX (`docs/PERMISSIONLESS-CLOUD-PLAN.md` §3.1): `dregg-cloud deploy
<repo>` clones a repo at a pinned commit → detects the project type (static /
node-command / wasm-compute / server) → builds it cap-bounded in the exec tier →
publishes the output as a site cell, modeled as a **crash-resumable, exactly-once,
metered durable workflow** (its own duroxide Clone/Build/Publish/MeterTick
registries over the on-disk SQLite store). The **source commitment** (the cloned
commit) lands in the deploy receipt AND is folded into the published cell's
`content_root` (a `/.well-known/dregg-deploy.json` manifest asset), so "this site
was built from THAT commit" is re-witnessable. Proven locally end-to-end: the
clone→detect→build→publish→serve round-trip (served over real TCP, commit in the
receipt + the served cell), the crash-mid-build resume (clone/build replayed, never
re-run; meter never doubled; the site still goes live), and the under-funded budget
reaping the deploy before publish. The `dregg-cloud deploy <repo>` CLI verb drives it
(`cli/src/main.rs`), e2e-tested against the `dreggnet` binary. New crate
`dregg-deploy/` + one workspace-member line; reuses exec / webapp::hosting /
durable / duroxide. `cargo test -p dregg-deploy` + the cli deploy e2e are green.

**What is REVIEWED-GO (NOT fired — needs ember's go).** A **public push-triggered
webhook receiver** — a hosted-git (GitHub/GitLab/…) `push` event → an automatic
`deploy(repo, ref)`. Per the plan's guardrail, "enabling auto-deploy/CI-deploy" is
explicitly reviewed-go (a public ingress that runs untrusted repo builds on a real
fleet on every push). The pieces it needs, none autonomous: (a) a public webhook
HTTP endpoint with provider signature verification; (b) routing a verified push to
the durable deploy workflow on a real **Caged/MicroVm fleet build** (the local path
runs the build subprocess in-process — the fleet executor seam is named in
`dregg-deploy/src/build.rs`); (c) the live **public go-live** of the served site on
the edge. Also reviewed-go (same plan): charging real `$DREGG` for the build
(metered today; billing flip is the §3.5 ember-decision) and the persistent-server
deploy target (`--server`, the §3.3 lane — detected + refused-with-pointer here).

**The op (fires on ember's go):** stand up the webhook service (a new disjoint
crate over the gateway), wire its verified-push handler to `dregg_deploy::deploy_*`
on a fleet build tier, and flip the public edge mount. Reversible: the webhook is
an additive ingress; disabling it stops auto-deploys without touching published
sites.

---

## 4. CUSTOM DOMAINS — REAL DNS + REAL CERT + LIVE EDGE (the §3.2 reviewed-go half)

**What.** Custom domains (BYO-domain → a dregg-hosted site) is BUILT and proven
locally: the `dregg-domains` crate (a cap-gated `DomainBinding` cell + the DNS
challenge-verify state machine, TXT + CNAME) and the gateway custom-Host routing +
the on-demand-TLS `ask` gating are green. The whole bind → challenge → verify →
route → ask round-trip proves against a deterministic `MockDns` (no live DNS, no
real cert). The three live half-steps are reviewed-go:

- **Real DNS verification.** Swap the `DnsResolver` for a real DNS client
  (`dregg_domains::DnsResolver` is the seam) so `DomainRegistry::verify` resolves
  the owner's actual `_dregg-verify.<domain>` TXT / CNAME against live DNS instead
  of `MockDns`. Reversible: verification is read-only; a failed lookup just leaves
  the binding `Pending`.
- **Real per-domain cert issuance.** The gateway's `ask` already returns `200`
  only for a *verified* binding (`SiteHostHandler::cert_ok`), so Caddy on-demand-TLS
  would mint a Let's Encrypt cert only for a proven domain. Firing this means
  pointing a real domain at the edge and letting Caddy ACME-mint — the live
  certificate authority interaction.
- **The live-edge gateway/Caddy rewire.** The gateway already routes a verified
  custom `Host` to its bound site (`SiteHostHandler::with_domains`); the live step
  is wiring the production `DomainRegistry` to a durable binding store + the control
  surface (`dregg-cloud domains add`), and confirming Caddy's `ask` points at the
  gateway's `/internal/site-exists`. Additive; an unverified/squatted domain earns
  neither a route nor a cert by construction.

**Why it's safe to fire live.** Verification is proof-of-control before any byte or
cert; the gate is structural (only `Verified` bindings route or earn certs), so the
worst case of a premature fire is a `Pending` binding that does nothing. Reversible:
removing a binding stops its route + cert without touching the bound site cell.

---

## 5. PERSISTENT SERVERS — LIVE FLEET BOOT (the §3.3 reviewed-go half)

**What.** Persistent servers (the fly.io-machines model, real — long-running,
durable, per-period-uptime-metered server instances) are BUILT and proven locally:
the `dreggnet-control` `server` module (`control/src/server.rs`) generalizes a
request-scoped machine into a long-running durable server with the full lifecycle
(create → launch → running/metered → stop/sleep → wake → destroy + lapse→reap),
a durable record store (`ServerStore`, append-only + fsync'd, the `settle_ledger`
shape) for crash-survival, and per-period uptime metering folded through the
existing conserving exactly-once `Settlement` rail. The whole round-trip — create →
launch → meter → **control-plane restart** (drop the fleet + provider, reconstruct
from the store) → meter more → destroy — proves over the in-process `LocalProvider`
(`control/tests/persistent_servers.rs`): the running server is reconstructed (not
lost) across the restart, the uptime cursor survives, and the metering is
exactly-once (no re-billing on reconstruct). The live half-step is reviewed-go:

- **The live fleet boot.** A real server *process* on a real KVM/Firecracker node
  (Hetzner/persvati), the long-running server entrypoint that stays up, with the
  data-plane ingress routed to it over the wireguard mesh (`control/src/mesh.rs`).
  The `VmProvider` seam is identical — a real provider provisions a real box where
  `LocalProvider` holds this process — so the lifecycle + per-period metering +
  reconstruct-on-restart proven locally carry over unchanged. Firing this means
  booting a real metered server on the fleet and routing live traffic to it.

- **Charging real `$DREGG` for uptime.** The per-period uptime meter settles through
  the same exactly-once `Settlement` the compute lease economy uses; the local proof
  runs it over the conserving in-process ledger (the `Payable` twin). Flipping the
  beneficiary to a real provider account charging real `$DREGG` per uptime period is
  the same ember-decision as the rest of hosting billing (the early era is
  subsidized).

**Why it's safe to fire live.** The control-plane code is reversible and durable: a
server's record is persisted before it runs, a restart reconstructs running servers
from disk, and the uptime meter never bills beyond what the lease budget authorizes
(an over-budget period lapses → the server is reaped). No box is rented for an
inactive lease (lease-gated admission). The worst case of a premature fire is a
reconstructed-but-idle server that meters nothing until it serves.

---

## Appendix — more overnight items will be appended below.

### A1. Real ToolGateway `invoke` rail + dregg CLI verbs — CODE-PROVEN, two go-lives REVIEWED-GO

**What landed (safe-autonomous, committed `30cb047`).** A workload's host-API
`invoke` now routes through the real ToolGateway enforcement (`exec/src/host_api.rs`,
`host-api` feature): cap-gate (the proven `gate_effect_set`) + the lease's service
allow-set, the per-call budget/meter (402-before-the-call), a CONSERVING `Σδ=0`
payment consumer → provider per priced call, chained into the real
`turn_shadow_receipt`. 11 host_api tests green (admitted-when-granted · 402
over-budget · 402 insolvent · cap-refused · charged Σδ=0 · receipted — driven both
directly and from a real CPython guest). Plus the developer CLI verbs `login` /
`domains add·list·verify` / `ls` / `logs` / `destroy` over the local/in-process path
(5 e2e tests green), including a new `DomainRegistry::adopt`.

The faithful-twin note (honest): the breadstuffs `dregg-sdk::ToolGateway` *type*
cannot link into `exec` — it pulls the whole verified core (circuit / lean-ffi /
lightclient) and the owned exec/bridge surface deliberately isolates only the thin
proven cap-gate/receipt surface; and `durable`'s `ConservingLedger` is downstream of
`exec` (a cycle). So `invoke` realizes that rail in-process over the linkable
surface — the same sanctioned pattern as `ConservingLedger ≡ the dregg Payable twin`.

**REVIEWED-GO (ember's word fires each):**

- **The live gateway redeploy** — pushing this (and the standing data-corruption fix)
  to the live public gateway edge. The code is reversible + green; firing it is the
  live-edge step.
- **Real public service-invocation billing** — flipping the conserving per-call
  charge from the in-process value ledger (the `Payable` twin) to a real provider
  account charging real `$DREGG` per `invoke`. Same ember-decision as the rest of
  hosting billing (the early era is subsidized).

**Not fired:** nothing public was touched; the literal `dregg-sdk::ToolGateway`-type
link (needs the verified-core link + a bridge pin bump) is a separate, larger
integration left for a dedicated session.

### A2. Real EC2 provider (mock-proven) + real overlay mesh as the fleet default — CODE-PROVEN, live spin-up REVIEWED-GO

**What landed (safe-autonomous, `control/` only).** The `Ec2Provider` now issues its
AWS operations over a seam — the `AwsCli` trait (`run(argv) -> JSON`). The production
backend (`SystemAwsCli`, the default) shells out to the real `aws` CLI
(RunInstances / TerminateInstances / DescribeInstances / DescribeInstanceStatus);
a mock backend simulates the instance state machine, so the **whole lifecycle**
(provision → poll-running → list / status → terminate) is proven with no AWS account,
no creds, and no `aws` binary (`ec2_lifecycle_against_a_mock_aws_client`). The launch
now also carries a security group (`--security-group-ids`) and an overlay-join
`--user-data` cloud-init (`overlay_join_user_data`) so a freshly-launched worker comes
up on the mesh. A real fleet is built with `Ec2Provider::for_fleet`, which attaches
the **real overlay mesh** (`TailscaleMesh`, the proven edge→persvati `:8021/fulfill`
path) as the configured dispatch default; `Ec2Provider::new` stays mesh-less so unit
tests attach a `StubMesh` explicitly. `config::build_provider` routes the `ec2`
backend through `for_fleet` (+ a new optional `[backend] security_group`). Dispatch
over the real mesh-client path is proven against a loopback `/fulfill` backend
(`for_fleet_dispatches_over_the_real_overlay_mesh`). `cargo test -p dreggnet-control`
green (60 lib + integration tests; the live test stays `#[ignore]`).

**REVIEWED-GO (ember's word fires each):**

- **Live EC2 spin-up** — actually launching real instances against a real AWS account
  (`SystemAwsCli`, real $). Gated behind `DREGGNET_EC2_LIVE=1`; the end-to-end
  `ec2_live_provision_and_terminate` test is `#[ignore]`d. Set `DREGGNET_EC2_AMI` /
  `DREGGNET_EC2_REGION` to target your account.
- **The live fleet on real machines** — bringing real workers up on the live overlay
  (the two-node tailnet/headscale handshake + the worker registering its mesh
  identity on boot via the overlay-join user-data). The mesh-client path is proven
  against loopback; the live overlay bring-up is the ops step.

**Not fired:** no instance was launched; no live overlay was brought up.

---

## (appended) Custom-domains LIVE DNS resolver — landed; live cert is REVIEWED-GO

**What landed (safe-autonomous, pushed).** `dregg-domains` now carries a real
production `DnsResolver`: `LiveDns` does actual TXT/CNAME lookups over
`hickory-resolver` for the `_dregg-verify.<domain>` TXT / `<site>.dregg.works`
CNAME challenge (STAND-INS-CENSUS #6). `MockDns` stays the test instance of the
trait seam; the bind → challenge → verify → route state machine is proven over the
mock, and the live resolver is verified end-to-end by an `#[ignore]`d network test
(real TXT on `example.com`, real CNAME on `www.github.com`, NXDOMAIN → empty).
Edge cases handled: NXDOMAIN/timeout → Pending (never a false-positive cert),
multi-record + multi-segment TXT, no stale negatives (cache off + zero negative
TTL), FQDN queries (no search-domain suffixing), TCP fallback on dropped UDP.
`cargo test -p dregg-domains` green.

**REVIEWED-GO (ember's word fires each):**

- **Verify against a real registered domain on the live edge** — pointing the CLI
  `dregg-cloud domains verify` (and the gateway's verify path) at `LiveDns` instead of the
  owner-supplied `MockDns` seed, then running it against a domain you actually
  control so its binding flips to Verified off live DNS. The resolver is built and
  proven; this is the wire-up + a real domain.
- **Live cert issuance for a verified domain** — the Caddy on-demand-TLS `ask`
  (`/internal/site-exists` → `DomainRegistry::is_verified`) minting a real per-domain
  certificate once a domain is verified. External ACME + cert mint; the gate is
  wired, the live mint is the ops step.

**Not fired:** no live cert was minted; no real domain was verified against the edge.

---

## (appended) pg-dregg verified store as the settlement backing store — landed; verified-proof / on-chain Payable is S3-GATED

**What landed (safe-autonomous, pushed — `dreggnet-durable`).** The in-process
`ConservingLedger` twin now has a real `pg-dregg`-backed twin: a **verified
conserving store** (off-by-default `pg-dregg` feature, the AGPL verified-store lane
like the bridge's `dregg-verify`). Each settled `(lease, period)` becomes one
verified turn — a real `pg_dregg::mirror::MirrorBatch` whose cell post-images are
the payer/beneficiary balance cells (Σδ = 0), chained so turn N's `ledger_root` is
turn N+1's `prev_root` and gated by the SAME anti-substitution tooth
(`RootChain`/`verify_chain_step`) the extension's `dregg.commit_log` trigger runs.
The store **re-validates its own Postgres state** (`revalidate_replicated_chain`),
it does not trust it (STAND-INS-CENSUS #7).

- `VerifiedChain` (postgres-free pure core): conserving + exactly-once + chain-gated
  + tamper/reorder/truncation refusal over the real `pg-dregg` types — proven
  offline (9 tests, always-green, no postgres).
- `VerifiedConservingStore` (pg layer): per-lease hash chains + cross-lease
  conserving balances on the shared `duroxide-pg` pool, authoritative across a
  restart (durable exactly-once via Postgres `UNIQUE(lease_id, period)`, not an
  in-memory map). Proven over a **real Postgres** (4 `#[ignore]`+`DATABASE_URL`
  tests, all passing against a throwaway pg18 cluster during development):
  conservation, exactly-once, **crash-resume across a restart**, concurrent settles
  dense + conserved, and a **raw-SQL-tampered row REFUSED** on re-validation.
  Default (sqlite) + license-clean `pg` paths unchanged.

  Verify: `cargo test -p dreggnet-durable --features pg-dregg` (offline-green); the
  live half: `DATABASE_URL=… cargo test -p dreggnet-durable --features pg-dregg
  --test verified_store_pg -- --ignored`.

**S3-GATED (the circuit/metatheory swarm's pg-dregg S3 circuit flip — NOT fired
here; greppable as `dreggnet_durable::verified::S3_GATED_SEAM`):**

- **Real Poseidon2 `ledger_root`** — the per-turn root is currently a deterministic
  blake3 **content-binding stand-in** (census #4/#5 content-root). When S3 lands,
  the root becomes the kernel's real Poseidon2 commitment a **light client
  witnesses** (not just a re-executing validator). The anti-substitution chain
  STRUCTURE is real + un-gated today; the light-client-witnessable root is the flip.
- **Proof-attested on-chain `Payable`** — the conserving move is real, durable, and
  chain-gated today, but it is NOT yet a real on-chain dregg `Effect::Transfer`
  whose receipt `dregg_attest_range` verifies against a pinned VK. S3 flips
  pg-dregg's `tier-c` proof verifier from its fail-closed stub; only then does each
  settled period become a proof-attested on-chain `Payable`. (Real value move →
  reviewed-go on top of S3.)

**Not fired:** no real on-chain transfer; no proof attestation (the S3 verifier is
the swarm's fail-closed stub until flipped).

## (appended) Solana bridge LIVE off-chain relayer — landed (mock/devnet); LIVE MAINNET relayer is REVIEWED-GO

**Landed (safe-autonomous, breadstuffs `bridge/`, green).** The Solana inbound
bridge is no longer library-only. `bridge/src/solana_relayer.rs` is a real
watching service: a `SolanaRpc` seam with a REAL Solana JSON-RPC client
(`SolanaJsonRpc` — genuine `getAccountInfo`/`getProgramAccounts`/`getSlot`
envelopes, base58 pubkeys, base64 account data) over an injected
`JsonRpcTransport`. A dependency-free `std::net` plain-HTTP transport ships for
the local `solana-test-validator` (`http://127.0.0.1:8899`); TLS is the only
injected piece. The relayer watches the bridge vault → gates **finality**
(mints ONLY against a lock present at `finalized` commitment; an un-finalized or
slot-ahead-of-finalized lock is refused) → enforces the **BR-2-B
escrow-to-vault binding** over the REAL on-chain owner/lamports
(`binds_bridge_vault`: wrong vault pubkey or attacker-owned account refused) →
runs structure/binding `verify_lock_proof` over the real bytes → produces the
committed-mint input (`ObservedLock::to_bridge_mint_request`). The mint is the
SOUND, multi-relayer-safe `bridge_mint_against_lock` (consume-once nullifier =
the global double-mint authority). Proven by `tests/solana_relayer_roundtrip.rs`
(lock→finalized→conserving mint Σδ=0, double-lock refused by the committed
nullifier, un-escrowed refused, un-finalized refused) + 11 lib tests incl. the
real JSON-RPC wire-shape parse. `cargo test -p dregg-bridge` green (255 lib + all
integration). Off-chain verify reaches `LockProofTrust::StructureOnly` over a
plain RPC — i.e. a re-executing validator that trusts the RPC's finalized
commitment.

**S-GATED (the circuit swarm's G1 VK-epoch — NOT ours):** for a dregg LIGHT
client (not a re-executing relayer) to witness that a mint is backed by a real
finalized Solana lock, the consensus + vault binding must fold into the EffectVM
as `dregg_circuit::bridge_action_air`. The off-chain relayer verify is the
re-executing-validator half; the in-circuit witness is the swarm's VK-epoch.

**REVIEWED-GO — the LIVE MAINNET relayer (real Solana, real mint, real $):**
- Inject a TLS `JsonRpcTransport` (https endpoint, e.g. `api.devnet.solana.com`
  then mainnet) — TLS is deliberately kept out of the verified core.
- Point the relayer at the real deployed bridge-vault PDA + lock program and run
  the watch loop as a service against real finalized locks.
- The fully-trustless consensus path (`verify_lock_proof_consensus_anchored`,
  stake-weighted votes + 16-ary accounts-Merkle) needs a snapshot/geyser
  pipeline — the StructureOnly relayer is the JSON-RPC-reachable rung.
- This fires real mints against real on-chain locks: ember's go.

---

## HOSTING-BILLING METER — real `$DREGG` on the live edge (S3-gated)

**What's built (safe-autonomous, green, staged).** The unified metered-`$DREGG`
hosting-billing meter (`PERMISSIONLESS-CLOUD-PLAN.md` §3.5): one meter shape over
the five hosting resources — **publish** (op + per-KiB stored), **bandwidth** (the
new per-site served-byte counter), **uptime** (per period), **cert** (per
issuance), **build** (per build-minute) — each accruing a `$DREGG` cost and
settling through the SAME conserving exactly-once ledger compute-leases use
(`dreggnet_durable::Settlement` / `settle_ledger` / `NodeApiSettlement`).

- The new **bandwidth byte-counter** rides the serving path
  (`webapp/src/hosting.rs::BandwidthMeter`, wired into `SiteRegistry::serve_site` —
  the single hook the gateway `SiteHostHandler` and the `dreggnet-host` binary both
  funnel through). It accumulates delivered `200` body bytes per site, exposes the
  unbilled tail a roll-up settles, advances a billing cursor (no double-count), and
  carries a **lapse** flag.
- The control-plane roll-up (`control/src/hosting_meter.rs::HostingMeter`) bills the
  unbilled bytes per period `owner → provider`, Σδ=0, exactly-once keyed
  `(host:<resource>:<site>, period)`. An owner who can't pay → the site **lapses**
  (the serving path then refuses it with `402` — the hosting analog of a compute
  lease reaping).
- Proven local end-to-end (`control/tests/hosting_billing.rs`): serve a real site
  cell 1000× → bandwidth accrues in the serving path → metered → settled (Σδ=0,
  exactly-once replay) + publish/cert/build/uptime each meter+settle; an over-budget
  site lapses and stops serving. `cargo test -p dreggnet-webapp -p dreggnet-control`
  green; gateway green via `cargo zigbuild --target x86_64-unknown-linux-gnu` (the
  macOS host build is blocked by the pre-existing `net/nodeapi` libc red, unrelated).

**REVIEWED-GO / S3-gated (ember's go — charging real money on the live edge):**
- Point the `HostingMeter`'s `Settlement` at the real
  `NodeApiSettlement` (real `$DREGG`, real on-chain conserving `Transfer` against
  real owner/provider cells) instead of the in-process `ConservingLedger`. The seam
  is identical — the meter is constructed over either sink — so nothing in the
  billing logic changes; this only swaps the settlement backend to the live rail.
- This is the same S3-gated swarm flip as the pg-dregg verified-store / on-chain
  `Payable` half: the early hosting era is deliberately subsidized; flipping real
  hosting billing on (and wiring the gateway's live `BandwidthMeter` counter into a
  ticking control loop) is an ember decision.

---

## Stripe LIVE webhook receiver — the USD-credit rail's live half (SAFE-AUTONOMOUS landed)

**What landed (no review needed — committed).** The DreggNet-plane Stripe webhook
**listener** is now a real, compiling, tested HTTP receiver
(`demo/stripe-receiver/`). The breadstuffs side
(`bridge/src/stripe_mirror.rs`) was already the BR-fixed verify→mint primitive
(HMAC-SHA256 over the raw body, constant-time compare, replay window, amount/
currency bounds, the consume-once payment-id nullifier, conserving `Effect::Mint`);
the gap was the HTTP receiver that drives it. The receiver:
- reads the raw body (Content-Length) + the `Stripe-Signature` header, builds a
  `StripeWebhookEvent`, and runs the GENUINE
  `StripeMirrorState::mint_against_webhook` (the same accounting the `dregg-bridge`
  suite exercises) — a forged signature, a stale `t=`, a wrong currency, or a
  re-delivered payment is refused exactly as the substrate refuses it;
- compile gap closed: the dep now enables `dregg-bridge/test-utils` (the in-process
  RAM mint path the receiver was already written against — it ADDS the applier,
  removes no guarantee);
- proven over MOCK webhooks (`cargo test`, 4/4 green): a valid signed event mints
  once with the right `Effect::Mint`; a forged/tampered signature is refused with
  nothing minted; a re-delivered (retried) event does not double-mint
  (`DuplicatePayment`); conservation Σδ=0 (`live_supply == total_verified_payments`,
  invariant holds); and a **real TCP HTTP round-trip** through the handler mints a
  signed POST (the raw-body-for-HMAC contract).

Build/test: `cd demo/stripe-receiver && CARGO_TARGET_DIR=$BREADSTUFFS/target cargo
test` (standalone AGPL demo crate, reuses breadstuffs' warm target).

**REVIEWED-GO (ember's go — real money on the live edge):**
- A real Stripe account + the live endpoint: run `stripe listen --forward-to
  localhost:4242/webhook`, export the printed `whsec_…` as `STRIPE_WEBHOOK_SECRET`,
  and `stripe trigger payment_intent.succeeded` with `metadata.dregg_recipient` +
  `amount`. Real USD → real conserved $DREGG-credit to the agent's cell.
  (`demo/stripe-trigger.sh --live` prints the exact commands.)
- Production hardening: swap the demo's in-process applier for the COMMITTED path
  (`verify_payment` → `bridge_mint_against_lock`, the global consume-once
  `note_nullifiers` authority) against a live dregg node, so double-mint is gated by
  committed state across relayer processes, not a per-process dedup set.
