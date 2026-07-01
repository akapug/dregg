# FIREWALL-DISSOLUTION — dissolve the bogus "AGPL firewall," keep the real Elide constraint

A read-only audit (HEAD, 2026-06-30, both repos) of every place DreggNet avoids
**depending on the real breadstuffs `dregg-*` substrate** — by **porting** code,
**feature-gating** the verified core, **`default-features`/`optional` license
isolation**, or **substituting stubs (FNV-for-Poseidon2)** — *for a license
reason*. The thesis of this doc:

> **Ember owns the copyright to the dregg substrate (`~/dev/breadstuffs`,
> AGPL-3.0), is its sole developer, and DreggNet is itself destined for AGPL
> release. A copyright holder is not bound by their own copyleft, and the
> AGPL-clean-default discipline is moot once DreggNet ships AGPL. Therefore every
> "keep DreggNet AGPL-free" maneuver against the *own* substrate is NONSENSE and
> should be dissolved — port→depend, stub→real, gated→default.**

There is **exactly one** genuine, *different* license constraint that this audit
explicitly does **not** lump in: the `net/*` (httpe) stack is **Elide
Technologies, Inc.** copyright — a company, not ember's sole copyright. That one
is real and forces the httpe-decouple before AGPL release. It is treated
separately in §2.

This doc supersedes the "deliberate sound boundary / license isolation" framing
of the `dregg-verify` gate in `docs/STAND-INS-CENSUS.md` (§ Deliberate sound
boundaries, line 265-268) and `docs/CRITIQUE-ARCH.md` (line 270, 307) **for the
own-substrate cases only**. Those docs were honest about *what* the gate is; this
doc corrects *why it's kept* — the "license isolation" justification is the bogus
half.

---

## 0. The critical distinction (read this first)

| | **BOGUS — the dregg-substrate firewall (DISSOLVE)** | **REAL — the Elide-net constraint (KEEP)** |
|---|---|---|
| What it avoids | depending on ember's **own** AGPL `dregg-*` crates | bundling **Elide Technologies, Inc.** proprietary code |
| Copyright holder | **ember** (sole) | **Elide** (a company) |
| Why the avoidance was claimed | "keep the default build AGPL-clean / Apache-pure / offline" | "not relicensable — can't ship Elide-proprietary as AGPL" |
| Validity | **None.** Owner isn't bound by own copyleft; DreggNet goes AGPL anyway | **Valid.** Ember can *use* Elide net code by right but cannot *relicense* it AGPL |
| Action | port→depend · stub→real · gated→default | decouple: own the thin types, drop the Elide engine (the httpe-decouple) |

A useful sub-distinction inside the BOGUS column: a few gates have a **secondary,
non-license** reason — the verified core pulls a **heavy** closure (arkworks/
plonky3/Lean/lockstitch fork-patches) and the default build wants to stay light +
cross-platform. That heaviness is a *legitimate* reason to keep a dep optional —
**but the fix per ember's own "no reflexive cargo features" rap is a separate
verified-build artifact, not a license feature flag with an AGPL excuse in the
comment.** Where a gate has this secondary reason, the dissolution is: **strip the
license justification, re-justify honestly on heaviness, and prefer a separate
artifact over a feature.** The `webauth` port has **no** heaviness excuse (it ports
a light ed25519/blake3 crate) — it is pure license-firewall and the cleanest swap.

---

## 1. The bogus-firewall inventory (own substrate — DISSOLVE)

Ranked roughly by payoff in §3. Each row: what was avoided · the real substrate
crate it should depend on · the simplification.

### 1a. `webauth` ports the credential core instead of depending on the identity cell — **the keystone**

- **File:line.** `webauth/src/cred.rs:1-27` (the port's own doc-comment):
  *"a faithful, wire-compatible **port** of breadstuffs `dregg-auth::credential` …
  **reproduced here rather than depended-on so the DreggNet workspace builds
  offline and pulls no AGPL dregg git** into its default closure."*
  `webauth/Cargo.toml:22-26` repeats the justification.
- **What was avoided.** Depending on breadstuffs `dregg-auth` (the `dga1_`
  ed25519 caveat-chain credential scheme; its semantics are the machine-checked
  `metatheory/Dregg2/Authority.BiscuitGraph`). The port is byte-for-byte
  wire-compatible (same BLAKE3 contexts, same postcard/base64url `dga1_` form).
- **The deeper cost (this is why it's #1).** `docs/KEY-RECOVERY-AND-KERI.md` is an
  entire document about a launch-blocking GAP — **no key rotation / recovery /
  compromise-response for the live `dga1_` cap-account** — whose root cause it
  names explicitly: *"DreggNet does not depend on the substrate's identity crates …
  the substrate's rotation machinery is … firewalled out of the default closure by
  design (`webauth/Cargo.toml:7-13`)"* (`KEY-RECOVERY-AND-KERI.md:73-77`), and again
  at `:202`, `:252-259`, `:280`. The substrate already has **KERI pre-rotation +
  HINTS social recovery + revocation containment, machine-proven
  (`#assert_axioms`-clean) AND deployed** — `KeyRotationGate`
  (`breadstuffs/cell/src/program/eval.rs:881-974`), `PreRotation.lean`,
  `ThresholdSigVerifier` (`breadstuffs/turn/src/executor/membership_verifier.rs`),
  e2e in `sdk/tests/identity_*_e2e.rs`. The account-recovery table-stake is a
  **weld of proven parts**, and the firewall is what's blocking it.
- **Simplification (port → depend), two steps:**
  1. **Safe swap.** Replace `webauth/src/cred.rs` with a dependency on
     `dregg-auth` (light ed25519/blake3 crate — **no** heaviness excuse). Delete
     the port. Wire-identical, so existing `dga1_` tokens keep verifying.
  2. **The payoff weld (needs-care).** Re-anchor the account subject from
     `subject_of = hash(credential tail)` (`webauth/src/lib.rs:127-133`) to a
     key-derived identity-cell id (`CellId::derive_raw`, the `SESSION-LOGIN.md §2.2`
     design), and rotate/recover via the deployed `KeyRotationGate` + guardian
     quorum. This needs the identity-cell + federation machinery (heavier) — run it
     in the control-plane issuer service, per `KEY-RECOVERY-AND-KERI.md §5 Tier 1`.

### 1b. `dreggnet-bridge` gates the verified on-chain lease read off "for AGPL isolation"

- **File:line.** `bridge/Cargo.toml:29-71` (the `dregg-verify` feature, default
  `[]`): *"OFF by default for two load-bearing reasons: 1. LICENSE — `emberian/dregg`
  is AGPL-3.0-or-later; pulling it in is what makes a build a derivative work."*
  `bridge/src/dregg_verify.rs:78-88` ("LICENSE — load-bearing, do not break the
  isolation"). `bridge/src/watch.rs:40` and `:304` ("off by default for AGPL
  isolation"). The `Lease` struct is a **MOCK** (`bridge/src/lib.rs:32-39`) and the
  dev source is `MockFeed` (`bridge/src/watch.rs:235-313`) *because* the real read
  is firewalled.
- **What was avoided.** `polyana-dregg-bridge` (re-exports breadstuffs
  `polyana-bridge`: `gate_effect_set`, `witness_receipt`,
  `query_shadow_attest_whole_log`) + `dregg-query` — i.e. the light-client-verified
  funded-execution-lease read (`VerifiedNodeLeaseSource`, **already built** behind
  the feature in `bridge/src/dregg_verify.rs`).
- **Secondary (heaviness) reason — real.** Flipping it on needs a root
  `[patch.crates-io]` reconciliation (ark-serialize fork + vendored lockstitch,
  `bridge/Cargo.toml:55-62`) and pulls the proving closure. So this gate has a
  legitimate *heaviness* reason even after the license reason dissolves.
- **Simplification (gated → default, OR separate artifact).** Strip the LICENSE
  reason from the three comment sites. Then either (a) flip `dregg-verify` to the
  deployed default (DreggNet is AGPL — there is nothing to isolate), or (b) per
  no-reflexive-features, make the verified-read a separate `dreggnet-bridge-verified`
  artifact justified purely on the heavy closure, not a license flag. The
  `MockFeed`/`Lease`-mock collapse to the verified `DreggNodeFeed` read once a live
  node is in the loop (cross-ref `STAND-INS-CENSUS.md` #8/#9).

### 1c. `dreggnet-webapp` keeps an FNV-1a `content_root` stub to avoid the real Poseidon2 dep "for AGPL"

- **File:line.** `webapp/Cargo.toml:17-27`: *"`dregg-verify` flips the site
  `content_root` from the FNV-1a in-process stand-in to the REAL sorted-Poseidon2
  cell-heap commitment … **OFF by default for the load-bearing AGPL reason** …
  linking `dregg-circuit` is what makes a build a derivative work."*
  `webapp/Cargo.toml:93-99` (the `dregg-circuit` optional dep, "AGPL-isolated").
  The FNV stand-in itself: `webapp/src/hosting.rs:44,180,424`.
- **What was avoided.** breadstuffs `dregg-circuit` — the **real Poseidon2** heap
  root (`heap_root::compute_heap_root_entries`) + the 8-felt faithful
  state-commitment. A **stub (FNV-1a) substitutes for real crypto** purely to dodge
  the dep.
- **Companion stub.** `storage/src/object.rs:47-50,187-223` — the storage object
  leaf hash is the **same FNV-for-Poseidon2 stand-in**, riding the same flip
  (`STAND-INS-CENSUS.md` #4/#5).
- **Simplification (stub → real).** Strip the AGPL reason; depend on
  `dregg-circuit` and use the real Poseidon2 `content_root`/leaf. Delete the `Fnv`
  hashers in `webapp/src/hosting.rs` and `storage/src/object.rs`. (Heaviness caveat
  as in 1b — Poseidon2 carrier pulls the plonky3/babybear closure; gate on
  heaviness or split an artifact, not on license.)

### 1d. `polyana` keeps the dregg surface behind a "thin proven surface only / Apache-pure" isolation

- **File:line.** `polyana/src/dregg-bridge/README.md:24-36` + `src/lib.rs:15-19`
  ("License (load-bearing)": *"the default-off `dregg-verify` feature is the only
  thing keeping the normal build Apache-pure … a binary built with `dregg-verify`
  on is a derivative work of AGPL code and must not be distributed under
  Apache-2.0"*). `polyana/src/runtime/Cargo.toml:59` ("default-off AGPL shadow
  witness lane") and `:147` ("default-off AGPL feature").
  `polyana/Cargo.toml:38-40` ("LICENSE-LOAD-BEARING: emberian/dregg is AGPL-3.0…").
- **The nuance — partly legitimate.** Polyana is genuinely intended to ship
  **Apache-2.0** as a *standalone* engine (a different product surface than
  DreggNet). For *that* product the Apache-pure gate is a real, ember-chosen
  boundary, **not** bogus — it is ember choosing Apache for polyana-the-engine.
  **What is bogus is only the part where DreggNet (AGPL-bound) mirrors polyana's
  Apache-isolation as if DreggNet needed it.** DreggNet does not — it's AGPL.
- **Simplification.** Leave polyana's own Apache gate alone (ember's product
  choice). On the **DreggNet side**, stop treating "polyana keeps it off, so we
  keep it off" as a constraint (`bridge/Cargo.toml:34-39` cites polyana's gate as
  its reason). DreggNet may take the dregg lane on by default regardless of what
  polyana's default is.

### 1e. `demo/stripe-receiver` is a standalone workspace "so the product never links dregg"

- **File:line.** `demo/stripe-receiver/Cargo.toml:1-11`: *"deliberately a STANDALONE
  crate (its own `[workspace]`) so it is NOT part of the DreggNet
  workspace's dependency graph: **the DreggNet product never links dregg** …
  Because it links AGPL, this demo tool is itself AGPL-3.0."* `license =
  "AGPL-3.0-only"` at `:23`.
- **What was avoided.** Keeping breadstuffs `dregg-bridge` (the real
  `stripe_mirror` verify+mint) out of the DreggNet workspace graph — the whole
  "two repos, scripted together" demo architecture (`docs/HACKATHON-DEMO.md:241-254`)
  exists to preserve the AGPL-free product graph.
- **Simplification.** Once DreggNet is AGPL, the "never links dregg" rationale is
  void — the receiver can be a normal workspace member depending on `dregg-bridge`.
  Lower payoff (it's a demo tool), but it deletes the standalone-workspace +
  duplicate `[patch.crates-io]` (`:61-63`) ceremony.

### 1f. The pervasive doc/disposition framing (`STAND-INS-CENSUS` / `CRITIQUE-ARCH` / `NAMED-RUNGS` / `MATURATION-PLAN`)

- **File:line.** `STAND-INS-CENSUS.md:265-268` calls the `dregg-verify` AGPL gate
  *"a deliberate license isolation boundary, not laziness."* `CRITIQUE-ARCH.md:270`
  ("the one legitimate use"), `:307`. `MATURATION-PLAN.md:378`, `NAMED-RUNGS.md:34`,
  `ORCHESTRATION-LOOP.md:109`, `DEVELOPERS.md:424`, `TESTING.md:78`, `GO-REAL.md:16`,
  `VISION.md:253`, `SELF-HOST.md:118-120`, `LIFTOFF-SURPASS-MATRIX.md:198-203`,
  `DEVNET-ROADMAP.md:21-22` all treat the "AGPL flip" as a real reviewed-go gate.
- **Simplification.** These are not code, but they propagate the bogus reason as
  doctrine ("reviewed-go: AGPL flip"). When the code gates dissolve, scrub the
  "AGPL flip / AGPL isolation / license isolation" language from the disposition
  columns; the genuine remaining gates there are **live-node + heaviness**, not
  license.

---

## 2. The REAL constraint — the Elide net-copyright (KEEP; forces the httpe-decouple)

This is a **different, genuine** constraint. Do not dissolve it.

- **Whose copyright.** The `net/*` crates carry an **Elide Technologies, Inc.**
  proprietary header — e.g. `net/httpe/src/lib.rs:1-12` carries a proprietary Elide
  license header, which is why it could not ship under AGPL. Confirmed
  for the whole stack in `docs/NET-CRATES-STALENESS.md:206-213` (`license =
  "Private"`, workspace) and `ARCHITECTURE.md:99-103`. These are **ember's own work
  as research director at Elide — freely USABLE here by right, but NOT
  relicensable** (it is Elide's copyright, a company's, not ember's sole copyright).
- **What DreggNet bundles.** The full Elide net stack is workspace members
  (`Cargo.toml` members: `net/httpe`, `net/transport`, `net/tailscale`,
  `net/wireguard`, `net/iocoreo`, `net/pki`, + the vendored `net/{base,core,dns,…}`
  Elide deps). `dreggnet-gateway` links the whole engine: `gateway/Cargo.toml:35`
  (`httpe = { workspace = true }`).
- **Why this blocks AGPL release.** An **AGPL DreggNet cannot bundle the Elide
  net stack** — ember cannot relicense another company's proprietary copyright as
  AGPL. At the time of this analysis DreggNet was still proprietary (`LICENSE:3-7`), so
  bundling Elide-proprietary code was fine then; the constraint bit **specifically at the
  AGPL-release transition** — which has since happened (the net stack was ejected and
  DreggNet flipped to AGPL-3.0).
- **The required work — the httpe-decouple (already planned).** `docs/HTTPE-TIDY-PLAN.md`
  is the plan. Its keystone finding (`:14-23`, `:153-154`): *"the gateway links the
  entire `httpe` engine but uses only ~6 of its small value types … the Elide CQ
  engine is compiled and linked in, but never started."* The decouple is **B1**
  (`:344-356`): **own the ~6 thin types** (`Method`, `StatusCode`, `ResponseWriter`,
  `Handler`, `Request`, `HandlerResult`, `content_type`) in a small `gateway-http`
  module and **drop the `httpe` dependency**. Payoff: removes the Linux-only
  constraint, the EAP timebomb, the premium-gating, the moving-branch fork closure
  — and, critically here, **the Elide-proprietary code from the shippable graph,
  which is the precondition for AGPL release.** The gateway's real serving loop is
  already DreggNet's own hand-rolled `std::net::TcpListener` thread-per-connection
  (`HTTPE-TIDY-PLAN.md:16`), so the decouple is behavior-identical.
- **Cross-ref.** `docs/NET-CRATES-STALENESS.md` (the staleness survey + §5
  licensing boundary) and `docs/HTTPE-TIDY-PLAN.md` (the tidy + B1 decouple). The
  net stack is also **EOL upstream** (`NET-CRATES-STALENESS.md:16-19`), so DreggNet
  is its de-facto home — another reason to own the thin types rather than track a
  dead Elide engine.

**Restated for clarity:** the §1 firewall is *internal* (ember's own dregg →
dissolve freely); the §2 Elide constraint is *external* (another company's
copyright → the net stack must be decoupled, not depended-deeper-on, before AGPL).
The httpe-decouple is **required pre-AGPL-release work** and is the one item in
this doc that is genuinely about a license, correctly.

---

## 3. The dissolution plan (ranked by payoff)

Disposition: **safe-autonomous** = a clean port→depend / stub→real swap with
existing wire-compat + tests · **needs-care** = load-bearing identity / live-node /
VK-affecting.

| # | Dissolution | Files | port→depend / stub→real / gated→default | Disposition | What simplifies / deletes |
|---|---|---|---|---|---|
| **1** | **Account-recovery weld** — depend on the real identity cell + `KeyRotationGate` | `webauth/src/cred.rs`, `webauth/Cargo.toml`, `webauth/src/lib.rs:127-133` | port→depend (step 1) **+** the recovery weld (step 2) | step 1 **safe-autonomous**; step 2 **needs-care** (load-bearing identity) | **deletes the `cred.rs` port**; closes the rotation/recovery/revocation GAP (`KEY-RECOVERY-AND-KERI.md`) |
| **2** | **Verified lease read on by default** — depend on `polyana-dregg-bridge` + `dregg-query` | `bridge/Cargo.toml:29-71`, `bridge/src/dregg_verify.rs:78-88`, `bridge/src/watch.rs:40,304` | gated→default (strip license; keep/relabel heaviness) | **needs-care** (live node + root `[patch]` reconcile) | **deletes the `Lease` mock + `MockFeed`** path's reason-to-exist; collapses to `DreggNodeFeed` |
| **3** | **Real Poseidon2 content-root** — depend on `dregg-circuit`, delete the FNV stubs | `webapp/Cargo.toml:17-27,93-99`, `webapp/src/hosting.rs:44,180,424`, `storage/src/object.rs:47-50,187-223` | stub→real (FNV→Poseidon2); gated→default | **safe-autonomous** for the swap (heaviness → relabel/split, not license) | **deletes two `Fnv` hashers**; the on-chain content commitment becomes real |
| **4** | **Stop mirroring polyana's Apache isolation** on the DreggNet side | `bridge/Cargo.toml:34-39`, the DreggNet-side citations of polyana's gate | gated→default (leave polyana's *own* Apache gate alone) | **safe-autonomous** (DreggNet-local reasoning only) | removes the "polyana keeps it off so we do" false dependency |
| **5** | **Fold `demo/stripe-receiver` into the workspace** | `demo/stripe-receiver/Cargo.toml:1-11,23,61-63` | standalone→member; depend on `dregg-bridge` | **safe-autonomous** (demo tool) | **deletes the standalone `[workspace]` + duplicate `[patch]`** ceremony |
| **6** | **Scrub the "AGPL flip / license isolation" doctrine** from disposition columns | `STAND-INS-CENSUS.md:265-268`, `CRITIQUE-ARCH.md:270,307`, `MATURATION-PLAN.md:378`, `NAMED-RUNGS.md:34`, `SELF-HOST.md:118-120`, `TESTING.md:78`, `GO-REAL.md:16`, `VISION.md:253`, `DEVELOPERS.md:424`, `LIFTOFF-SURPASS-MATRIX.md:198-203`, `DEVNET-ROADMAP.md:21-22`, `ORCHESTRATION-LOOP.md:109` | doc cleanup | **safe-autonomous** | the genuine remaining gates become **live-node + heaviness**, never license |
| **E** | **(REAL, separate) httpe-decouple** — own the ~6 thin types, drop the Elide engine | `gateway/Cargo.toml:35`, `gateway/src/main.rs`, new `gateway-http`; plan in `HTTPE-TIDY-PLAN.md:344-356` | NOT a firewall dissolution — **required pre-AGPL** decouple | **needs-care** (dependency-surface change; ember reviews) | removes Elide-proprietary code + EAP timebomb + Linux-only + fork closure from the shippable graph |

### What gets simpler or deleted (summary)

- **Deleted ports:** `webauth/src/cred.rs` (the credential-core port) → depend on
  `dregg-auth`.
- **Deleted stubs:** the FNV-1a hashers in `webapp/src/hosting.rs` and
  `storage/src/object.rs` → real Poseidon2 from `dregg-circuit`.
- **Deleted ceremony:** the `demo/stripe-receiver` standalone `[workspace]` +
  duplicate `[patch.crates-io]`; the `MockFeed`/`Lease`-mock's reason-to-exist.
- **Demoted feature flags:** `dregg-verify` on `bridge` and `webapp` stop being
  *license* gates — either default-on or re-justified as **heaviness** gates
  (preferably a separate verified-build artifact, per no-reflexive-features), with
  the AGPL/derivative-work language removed from every comment.
- **Unblocked:** the account key rotation / social recovery / compromise-response
  table-stake (`KEY-RECOVERY-AND-KERI.md`) — its *only* non-mechanical blocker was
  the firewall.

### The one thing that is NOT dissolved

The **httpe-decouple (row E)** is real, license-driven, and required before AGPL
release — but for the **Elide** copyright, not ember's. Keep it; do not depend
deeper on the Elide engine. Everything in §1 is the bogus firewall against ember's
own substrate and should go.

---

*Audit method: grep for `agpl|license isolation|firewall|relicens|derivative`
across both trees; read each cited `Cargo.toml`/`.rs`/`.md` at HEAD; confirmed the
Elide proprietary headers (`net/httpe/src/lib.rs:1-12`) and DreggNet's own
`LICENSE` (proprietary at audit time, since flipped to AGPL-3.0). No code touched — this doc only.*

( ⌐■_■ )  *you can't trespass on your own land — tear the fence down; the one wall that stays is the neighbor's.*
