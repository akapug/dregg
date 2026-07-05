# UNDER-WIRED — the executor↔Lean under-enforcement catalog

A read-only sweep (HEAD, 2026-06-29) for the pattern: **the Lean kernel proves/specs a
property, but the deployed Rust executor/node does NOT actually enforce it** — it mirrors
only liveness, applies a weaker check, default-allows, or only checks on traces rather than
as a theorem. This is how `CAP-1` (the authority-gate default-allow) and `F1` were found.
The sweep was adversarial: assume the Rust under-enforces until the code proves it matches
the Lean.

Sources read in `~/dev/breadstuffs`: `turn/src/executor/{apply,authorize,execute,execute_tree}.rs`,
`cell/src/{capability,permissions,facet}.rs`, `exec-lean/{src/lean_apply.rs,src/lean_shadow.rs,
tests/rejection_parity.rs}`, `node/src/{executor_setup,blocklace_sync,execution_cursor,coord_gate,
finality_gate}.rs`, `blocklace/src/{ordering,finality,lib}.rs`, and the Lean specs under
`metatheory/Dregg2/` (`Exec/EffectsState.lean`, `Exec/EffectsAuthority.lean`, `Kernel.lean`,
`TurnExecutorFull.lean`, `Distributed/BlocklaceFinality.lean`, `Consensus/TauPrefixMonotone.lean`,
`Proof/CordialMiners*.lean`). The existing audit doc is `breadstuffs/docs/RUST-LEAN-EXECUTOR-PARITY.md`.

## Classification key

- **ALIGNED** — the Rust enforces the same predicate the Lean kernel does (verified in code, not
  merely a comment).
- **UNDER-ENFORCED-EXPLOITABLE** — Rust is genuinely weaker; a turn the verified kernel refuses can
  be committed (CAP-1 class). Mitigations, if any, are noted but do not change the class for the
  bare executor.
- **UNDER-ENFORCED-BENIGN** — Rust is weaker or has a coverage hole, but it is honestly fenced/logged
  and not a soundness break (liveness-only, config-dependent, or off-root side-table).
- **PROVEN-ON-TRACES-NOT-THEOREM** — agreement is asserted by differential fixtures/round-trips, not a
  discharged `∀`-input Lean theorem; sound on the corpus, unproven in general.

## Summary table

| # | Surface | Lean property | Rust behavior | Class | Forkable / exploitable? |
|---|---------|---------------|---------------|-------|--------------------------|
| 1 | **Direct cross-cell cap FACET** | `authorizedB` requires endpoint `rights.contains Auth.write` (`Kernel.lean:54`) | `check_cross_cell_permission`→`has_access_at` checks cap *presence* only, never `allowed_effects` (`apply.rs:3191`, `capability.rs:500`) | **UNDER-ENFORCED-EXPLOITABLE** | Facet-bypass write/transfer on a `None`-permission target; Rust commits, Lean rejects |
| 2 | **xsort tie-break / executed order** | `xsortBy` is a `(round,id)` comparator (`BlocklaceFinality.lean:252`) | `ordering.rs::xsort` is Kahn-topo + global-id tie-break (`ordering.rs:414`); differs *across rounds*, not just within a cohort. Live differential & gate compare only the **set**, never the order | **PROVEN-ON-TRACES-NOT-THEOREM** | Execution-state fork between a Lean-backed peer and a Rust-only/fallback peer on non-commutative turns; mitigated where the deployed order *is* the Lean order |
| 3 | **Producer "covered = root-agreeing"** | (claim) every mappable effect yields `lean_root == rust_root` | backed by per-effect fixtures, not a Lean `∀`-theorem; `produce_via_lean` installs Lean root **unconditionally** and only logs a Rust mismatch (`lean_shadow.rs:623`, `lean_apply.rs:1479-1491`) | **PROVEN-ON-TRACES-NOT-THEOREM** | A covered effect that diverged outside the corpus would commit Lean's root and log, not halt |
| 4 | **Producer coverage holes** | the kernel admits these effects | 7 families are Rust-only with **no** Lean differential: CreateCell, SpawnWithDelegation, BridgeMint, PipelinedSend, ExerciseViaCapability, CreateCellFromFactory, Mint (`lean_shadow.rs:686`) | **UNDER-ENFORCED-BENIGN** | No silent coverage claim — `Fallback`, `warn!`-logged |
| 5 | **Note-set divergence (off-root)** | NoteCreate/NoteSpend edit the nullifier/commitment side-table | the compared digest is the cell-merkle `.root()`; the note set is off-root, so a note-set divergence is **not witnessed** by any differential (`lean_shadow.rs:489`) | **UNDER-ENFORCED-BENIGN** | Structural blind spot of the producer differential |
| 6 | **Lean-archive init failure** | (deployment precondition) | `execute_via_lean` FFI/init failure → `Fallback` → Rust authoritative, per-turn `warn!`; not fail-closed (`lean_apply.rs:1181`) | **UNDER-ENFORCED-BENIGN** | Whole producer guarantee silently degrades to Rust-only if `lean_available()` is false at runtime |
| 7 | **Consensus/ordering fail-open** | Lean order/2PC authoritative | every consensus gate is default-ON but **fallback to Rust-only** when the archive is unlinked (`blocklace_sync.rs:1037`, `coord_gate.rs:117`); no startup hard-check | **UNDER-ENFORCED-BENIGN** | This is exactly the configuration in which #2 becomes live; warn-once, not refuse-to-serve |
| 8 | **`is_cordial` dissemination rule** | cordial-miners dissemination (`CordialMiners.lean:73`, named open) | `is_cordial` is **computed but never called** in `node/src/` (`ordering.rs:569`) | **UNDER-ENFORCED-BENIGN** | Liveness/progress, not safety; cannot fork finality |
| 9 | **SetProgram circuit witness** | a descriptor rung should bind the program write into the turn commitment | `apply_set_program` fully gates authority+liveness, but **no VK-affecting descriptor binds the write** yet (`apply.rs:873`) | **UNDER-ENFORCED-BENIGN** | Light-client cannot witness it (a re-executing validator can); documented, VK-affecting follow-up |
| 10 | **Revocation-channel `None` branch** | (not modeled at this Lean layer) | `apply_exercise_via_capability` skips revocation-channel checks when `self.revocation_channels` is unset (`apply.rs:1622`) | **UNDER-ENFORCED-BENIGN** | Enforcement is only as live as the registry being populated; benign vs the kernel |
| — | Authorize path (caveats, conservation, non-amp, mint, liveness ×9, nonce, reserved-field, exercise facet, level on direct path) | per-effect Lean handlers | enforced with real teeth | **ALIGNED** | see §Aligned |
| — | causalPast closure, finalized-prefix monotonicity, equivocation detection, coord 2PC | Lean specs | match (one was unsound, now fixed) | **ALIGNED** | see §Aligned |

---

## EXPLOITABLE (CAP-1 class) — fix first

### 1. Direct cross-cell capability FACET is not enforced (`CAP-FACET-1`)

**Lean property.** A direct (non-`ExerciseViaCapability`) write/transfer routes through
`authorizedB` (`metatheory/Dregg2/Kernel.lean:54-60`): the actor is authorized iff `actor == src`,
OR it holds a `node` cap, OR it holds an `.endpoint t rights` cap **whose `rights.contains
Auth.write`**. The endpoint's `rights` *are* the facet (`capFacetMaskA (.endpoint _ r) = r`,
`TurnExecutorFull.lean:2534`), and `requiredFacetA` maps `.balanceA`/`.setFieldA` to `Auth.write`
(`TurnExecutorFull.lean:2496`). So Lean enforces the facet on the **direct** path, not just on
exercise.

**What the Rust does.** The direct cross-cell gate is `check_cross_cell_permission`
(`turn/src/executor/apply.rs:3191-3250`), used by `apply_set_field`, `apply_transfer`, and the
cross-cell legs at `apply.rs:497/629/692/763/805/888/2368/2582`, and mirrored by the top-level gate
in `execute_tree.rs:452`. Its access leg is `has_access_including_delegation_at` →
`CapabilitySet::has_access_at` (`cell/src/capability.rs:500-506`), which checks **only**:

```rust
&r.target == target
    && r.permissions != AuthRequired::Impossible
    && r.expires_at.is_none_or(|exp| current_height <= exp)
```

It never reads `r.permissions` as a *level* against the action and never reads `r.allowed_effects`
(the facet mask). After the presence check, the gate consults only the **target cell's** required
permission and rejects iff that is non-`None`:

```rust
let required = cell.permissions.for_action(permission_action);
if matches!(required, AuthRequired::Impossible) { return Err(PermissionDenied...) }
if !matches!(required, AuthRequired::None)       { return Err(PermissionDenied...) }
Ok(())
```

The held cap is reduced to "does an edge exist." By contrast, the `ExerciseViaCapability` path **does**
enforce the facet (`apply.rs:1803-1818`, routing through `is_effect_permitted`, the P2-1 fix) and the
level (`apply.rs:1751-1782`). The CAP-1 closure fixed the *exercise* sibling and left the *direct*
sibling presence-only.

**Soundness impact — EXPLOITABLE, conditioned on a `None`-permission target.** Distinct facet bits
exist (`cell/src/facet.rs`: `EFFECT_SET_FIELD = 1<<0`, `EFFECT_TRANSFER = 1<<1`; `FACET_STATE_WRITER`
deliberately excludes transfer). Attack: an actor holds a c-list cap to `T` with
`allowed_effects = FACET_STATE_WRITER` (SetField only, no Transfer). If `T.permissions.for_action(Send)
== None` — the pure object-capability case, where the facet *is* the entire attenuation boundary — the
actor submits an ordinary `Effect::Transfer { from: T, .. }`. `check_cross_cell_permission` sees a
non-`Impossible` cap (presence ✓) and `required == None` (✓) and **commits the transfer**. The facet
that was supposed to bound the holder to SetField is never consulted. Lean's `authorizedB` refuses the
same move (the endpoint cap lacks `Auth.write`). This is a rejection-parity violation in the dangerous
direction: **Rust accepts what the verified kernel rejects.** It is not currently in the
`rejection_parity.rs` corpus (the corpus exercises the exercise path and target-permission lattice,
not a faceted c-list cap on a `None`-permission target), so it is a genuinely new finding.

LEVEL on the direct path is **benign/conservative**: Rust ignores the cap's level but rejects *any*
auth-requiring target outright (`apply.rs:3238`), which over-restricts rather than under-enforces.
Only the FACET axis under-enforces.

**Mitigation (partial, conditional).** Transfer and SetField are in the producer-mode covered set, and
the deployed default is Lean-authoritative (`DREGG_LEAN_PRODUCER` defaults ON — see #3/#4). If the
wire marshals the faceted c-list cap faithfully as an `.endpoint` cap carrying its `rights`, then
producer-mode Lean would `authorizedB`-reject and **veto** the Rust commit (`lean_apply.rs:1512`,
`LeanShadowVeto`). That mitigation is contingent on (a) producer mode on, (b) the marshaller carrying
the facet into endpoint rights (unverified here), and (c) not on the fallback/Rust-only path. For the
**bare Rust executor** the hole is open. Treat as exploitable until the executor gate itself enforces
the facet.

**Fix.** Extend `check_cross_cell_permission` to resolve the *specific* held cap from the c-list (not
the boolean `has_access_at`) and run `is_effect_permitted(cap.allowed_effects, effect_bit)` — the same
call already used at `apply.rs:1806`. Add a `rejection_parity.rs` case (faceted SetField-only cap + a
`None`-permission target + a `Transfer{from:T}`) to pin it. **Value:** high (closes a CAP-1-class
object-capability bypass). **Effort:** low (one gate + one test).

---

## PROVEN-ON-TRACES-NOT-THEOREM

### 2. xsort tie-break — the executed order is checked as a set, not an order

**Lean.** `xsortBy` (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean:252-254`) is a pure
`(round, id)` comparator sort: strictly round-major, ties broken by id. `tauOrder` (hence the executed
`lean_order`) uses it.

**Rust.** `blocklace/src/ordering.rs::xsort` (`:414-470`) is **not** that function — it is a Kahn
topological sort over causal edges with a min-heap tie-break by raw block-id (`:445/456`). The premise
"Rust sorts by id only" is too generous: Rust's id tie-break is applied **globally among all
ready nodes, not within a round**. Two causally-unrelated blocks at different rounds can both be ready,
and Rust emits the smaller-id one first regardless of round, whereas Lean is always round-major. The
two functions compute **genuinely different total orders** of the same set in general, not merely a
within-cohort permutation. The codebase's docstring claim that the divergence "only reorders within a
round-cohort" (`ordering.rs:1091`, `BlocklaceFinality.lean:249`) is an unproven understatement.

**Theorem or traces?** Traces only. The Lean `xsort_*` lemmas prove the *abstract* `Block.xsort` is a
permutation/total-order; none proves the Rust Kahn order equals Lean's `(round,id)`. The only
cross-checks are `test_tau_differential_against_lean_model` / `..._equivocator_excluded`
(`ordering.rs:1097/1158`), and they **deliberately project the tie-break away** by sorting each
round-cohort before comparing (`ordering.rs:1129-1136`). Worse, the **live** differential in
`poll_finalized_blocks` compares only the sorted `(creator,seq)` multiset (`blocklace_sync.rs:1001`),
and the finality gate's `admits` is set membership (`finality_gate.rs:200`) — neither compares order.
So if `lean_order` and `rust_order` are different orderings of the same set, **nothing flags it.**

**Soundness impact.** In a homogeneous Lean-backed deployment every node executes `lean_order`
(`blocklace_sync.rs:1034`), so the Rust quirk is dormant and there is no fork. On the fallback path
(archive missing / wire ERR / gate disarmed, `:1037-1047`) or for a pure-Rust consensus peer in a
mixed federation, that node executes the Rust Kahn order, which can differ across rounds, yielding a
**different post-state / state-root on the same finalized set** — an execution-state fork undetected
by the set-only differential and set-only gate (the code names this "MIXED-NETWORK DIFFERENTIAL" risk,
`:1010-1016`). A malicious node cannot *choose* the order (deterministic function of the lace), so this
is honest-node state divergence under fallback/mixed deployment, not a finality-fork primitive.

**Fix.** Make Rust `xsort` *be* the `(round,id)` comparator (a predecessor always has a strictly
smaller round, so the Kahn machinery is unnecessary) so Rust ≡ Lean by construction; then compare
**ordered** sequences (not sorted multisets) in the live differential, or discharge
`xsort_kahn = xsortBy` as a Lean theorem. **Value:** high (the only place two honest nodes fork
*state*). **Effort:** low for the comparator + order-comparison; medium for the theorem.

### 3. Producer "covered = root-agreeing" is a fixture claim, and the install trusts Lean

`produce_via_lean` (`exec-lean/src/lean_apply.rs:1420-1518`) is the live, default-ON, Lean-authoritative
producer: on the covered set it installs `*ledger = lean_ledger` **unconditionally** (`:1491`) and
demotes the Rust `TurnExecutor` to a logged cross-check (a mismatch becomes
`ProducerOutcome::LeanAuthoritative { rust_agreed: false }`, an `error!`, not a halt). The covered set
is `producer_root_agreeing_effects` (`lean_shadow.rs:491`) and `producer_root_gap_effects()` now
returns `&[]` (`:623`) — i.e. every mappable effect is *claimed* root-agreeing. But that claim is
backed only by per-effect round-trip fixtures (`lean_state_producer_*` tests), **not** a Lean
`∀`-input proof that `lean_root == rust_root`. If a covered effect diverged on an input outside the
corpus, the node would commit Lean's root and merely log it — even if the fault were in the
marshaller/reconstitution. Sound on the corpus; unproven in general. **Fix:** promote the
root-agreement of the covered set to a discharged theorem (or halt-on-divergence rather than
trust-Lean-and-log). **Value:** medium. **Effort:** high (theorem) / low (halt switch).

---

## UNDER-ENFORCED-BENIGN

### 4. Producer coverage holes — 7 effect families run Rust-only, no Lean differential

The covered set excludes (`producer_uncovered_effects`, `lean_shadow.rs:686`): **CreateCell,
SpawnWithDelegation, BridgeMint, PipelinedSend, ExerciseViaCapability, CreateCellFromFactory, Mint**.
For these, `produce_via_lean` returns `Fallback` and the Rust executor is the **sole** producer with no
differential at all (`executor_setup.rs:169`, `warn!`). CreateCell is deliberately excluded because the
verified `createCellChainA` requires `mintAuthorizedB`, which a fresh-id cell cannot satisfy
(`lean_shadow.rs:950`). Honestly fenced and logged — never a silent coverage claim — but a real hole:
the authority gates for these families (notably `ExerciseViaCapability` and `Mint`) are validated only
by the Rust executor + the separate `rejection_parity.rs` / `conservation_*` tests, not by the live
producer differential. **Value:** medium. **Effort:** medium (extend the marshaller/covered set).

### 5. Note-set divergence is off-root (producer differential blind spot)

NoteCreate/NoteSpend are in the root-agreeing set on the grounds that they edit the nullifier/commitment
side-table **off** the cell merkle root, so they agree on `.root()` (`lean_shadow.rs:489`). The
producer differential's `.root()` check is therefore structurally blind to any nullifier/commitment
divergence between the two producers. (The dedicated note-conservation gate at `execute.rs:1113` still
bites; this item is specifically about the *producer differential's* coverage.) **Value:** low-medium.
**Effort:** medium (add a note-set digest to the compared state).

### 6. Lean-archive init failure degrades to Rust-only, log-only

`execute_via_lean` (`lean_apply.rs:1181`) calls into the FFI with no pre-check; an init/FFI failure
becomes `ExtractError::Ffi` → `Fallback` → Rust authoritative, per-turn `warn!`. So if `lean_available()`
(`dregg-lean-ffi/src/lib.rs:78`) is false at runtime, the entire producer guarantee silently degrades to
Rust-only. The node *links* `dregg_exec_lean` in the native build, but runtime init success is the
load-bearing precondition and the degrade path is log-only, not fail-closed. **Fix:** a startup
hard-check that refuses to serve turns (or at least refuses to claim verified production) when the
archive is absent. **Value:** medium. **Effort:** low.

### 7. Consensus & ordering fail-open when the archive is unlinked

Every consensus gate is default-ON but falls back to **Rust-only** when the Lean archive is unlinked
(`blocklace_sync.rs:1037-1047/1078-1084`, `coord_gate.rs:117-122`). A node built without the
closure-complete archive silently runs Rust-only consensus *and* ordering — exactly the configuration
in which #2's order divergence becomes live. The whole "Lean is authoritative" story is conditional on
the deployed binary linking `dregg_tau_order` / `dregg_blocklace_finalize`. **Fix:** a startup
hard-check refusing multi-party consensus if the verified exports are absent (vs a once-warning).
**Value:** medium. **Effort:** low.

### 8. `is_cordial` is computed but never enforced

`ordering.rs::is_cordial` (`:569`) implements the cordial-miners dissemination predicate, but grep finds
**zero** callers in `node/src/`; it is used only by an unused helper and tests. Lean names this an
explicit open residual (`CordialMiners.lean:73`). Cordiality governs progress, not safety — a
non-cordial block can be inserted/finalized — so this cannot fork finality; it is a liveness/clarity
gap. **Fix:** gate dissemination on `is_cordial`, or delete the dead predicate. **Value:** low-medium.
**Effort:** low.

### 9. SetProgram has no circuit witness (light-client layer, VK-affecting)

`apply_set_program` (`apply.rs:873-876`) fully gates SetProgram authority + liveness at the executor,
but notes that no descriptor rung binds the program write into the turn commitment yet — "that is
VK-affecting." A re-executing validator enforces it; a **light client** cannot yet witness it. Already
named in code as an owed, VK-affecting follow-up. **Value:** medium (light-client completeness).
**Effort:** high (VK-affecting circuit work).

### 10. Revocation-channel `None` branch is config-dependent

In `apply_exercise_via_capability` (`apply.rs:1622`), `if let Some(ref channels) =
self.revocation_channels` — when the executor is built without a revocation-channel registry, the
cap-revocation-channel check is skipped (the `None` branch proceeds). The Lean model does not model
revocation channels at this layer, so this is benign vs the kernel, but cap-revocation enforcement is
only as live as `self.revocation_channels` being populated. **Fix:** require the registry (or fail
closed) in any deployment that relies on channel revocation. **Value:** low-medium. **Effort:** low.

### (note) Refusal-audit EXT slot is developer-writable — BENIGN, Lean-consistent

`apply_set_field` heap path (`apply.rs:370-376`) lets a `SetField{index: REFUSAL_AUDIT_EXT_KEY}`
overwrite the audit slot that `apply_refusal` sets. But Lean's `reservedField` is exactly
{nonce, permissions, verification_key, program}; `refusalField` is not reserved there either, so Lean's
`stateStepDev` equally allows it. It is self-attestation (a cell rewriting its own audit), no cross-cell
break — an aligned weakness, not a Rust divergence. Listed for completeness.

---

## ALIGNED — genuinely matches the verified spec (verified in code at HEAD)

The bulk of the executor mirrors the Lean gates' *enforcement*, not just liveness. Confirmed
guard-by-guard:

- **The kernel-align guards (≈9, the "six" of the audit prose plus more).** self-transfer `src==dst`
  rejected (`apply.rs:397`); per-effect lifecycle-liveness (`!is_live()` / `!accepts_effects()`) on
  every state-mutating arm — SetField `:354`, IncrementNonce `:708`, SetPermissions `:779`, SetVK
  `:844`, SetProgram `:904`, Transfer both legs `:430/:453`, emit-on-sealed `:668`, MakeSovereign
  `:2147`, Refusal `:2397`, mint recipient+well, burn well, ReceiptArchive `:3108`; terminal-agent
  admission `cellLifecycleCanAuthor` wired into the **live** path (`execute.rs:405`, not test-only);
  mint authority `holds_mint_authority` (`apply.rs:2734`, the image of `mintAuthorizedB`); exercise
  facet `Some(0)` fail-closed (`apply.rs:1803`); introduce expiry/height (`apply.rs:1899`); cross-cell
  burn authority (`apply.rs:2581`). ("Reserved slots" in the audit prose is a non-hole — `fields[0..15]`
  are legitimately user-addressable; nonce/perms/vk/program live in separate `Cell` fields, satisfying
  Lean's `reservedField` by construction.)
- **Caveat / `Pred` enforcement** — `execute_tree.rs:962-1014` evaluates every touched cell's
  `CellProgram` against its (old,new) pair and returns `ProgramViolation` on failure; cross-cell +
  exercise inner-effect writes included via `collect_touched_cells`. Matches `stateStepGuarded` /
  `caveatsAdmit` (`EffectsState.lean:248`).
- **Conservation Σδ=0** — `execute.rs:1133` rejects `excess != 0`; note-conservation `:1113`; per-asset
  `atomic.rs:124`. Mint/Burn are conserving well↔holder moves, per-turn net zero.
- **Non-amplification (all three axes)** — `apply_grant_capability` (`apply.rs:539`) enforces the
  permission lattice, facet submask, and expiry-monotone; `apply_introduce` (`:1912`) and
  `apply_attenuate_capability` (`:3003`) enforce `is_attenuation`. Matches `attenuate_subset` /
  `is_attenuation` (`EffectsAuthority.lean:197`).
- **Monotone nonce** — `apply_increment_nonce` always bumps by exactly +1; the non-monotone vector is
  inexpressible, and `SetField` cannot reach the nonce field (separate `Cell` field).
- **`ExerciseViaCapability` level + facet** — `apply.rs:1751-1819` (the CAP-1 closure).
- **LEVEL on the direct cross-cell path** — conservative (rejects any non-`None` target), not weaker.
- **causalPast closure** — `lib.rs:592` unbounded BFS computes the same fixpoint as the fuel-bounded
  `causalPastIncl` (`BlocklaceFinality.lean:134`); acyclicity is structural (content-addressed ids),
  both inclusive of self. (Caveat: the fuel-sufficiency equivalence is argued in a docstring +
  trace-exhibited, not a discharged lemma; sound by construction. A second, *exclusive* `causal_past`
  in `finality.rs:902` is a separate sync helper, not on the consensus path — a naming footgun, not a
  bug.)
- **Finalized-prefix monotonicity** — Lean *refutes* unconditional monotonicity
  (`TauPrefixMonotone.lean:21`) and proves only the conditional `tau_finalized_prefix_monotone`
  (`:170`). The node was rebuilt to **not assume** the refuted property: `execution_cursor.rs` tracks
  executed blocks by identity and serves the set-difference in the current tau order (`:126`), with the
  mid-prefix counterexample reproduced against the real Rust tau (`:247`). The previous index-slicing
  logic was a genuine unsoundness (re-execute one finalized block + permanently skip an honest catch-up
  block) and is **now closed**. A model of metabolizing a refuted Lean property into a corrected Rust
  mechanism.
- **Equivocation detection** — enforced at insert (`finality.rs:639`) and in ordering
  (`ordering.rs:160`), matching `hasEquivInPast` (`BlocklaceFinality.lean:151`).
- **Coord 2PC** — Lean `TwoPhaseCommit.evaluate` authoritative; Rust `Coordinator` is the differential
  sibling; fallback is fail-safe to `Pending` (`coord_gate.rs:30/100`).

---

## Known-open, safe-direction (documented in `rejection_parity.rs`; recorded, not new)

These are real Rust↔Lean asymmetries but in the **safe** direction (the verified kernel is *stricter*,
so under the producer-mode authority-inversion Lean **vetoes** the Rust commit). Listed so the catalog
is honest both ways; none is a new exploitable hole.

- **`burn-no-well`** — Rust accepts a permissionless self-redeem; `execBurn`
  (`Dregg2/Exec/Generators.lean:55`) gates on `mintAuthorizedB`, so a cap-less burn is refused by Lean.
  Conservation half closed (every burn is a conserving holder→well move); authority half closes in the
  Lean Stage-3 split. The *cross-cell* burn authority is already wired (`apply.rs:2581`).
- **`mint-authorized`** — a wire-faithfulness limit, not under-enforcement: the executor gate
  `holds_mint_authority` is present and correct; the shadow marshals `Mint` with synthetic `asset: 0`,
  so the Lean-wire `mintAuthorizedB` can't see the held node-cap. `mint-unauthorized` proves both
  agree-reject when the cap is absent.
- **`GrantCapability` self-grant** — Rust short-circuits a self-grant without checking the c-list edge;
  `recKDelegate` requires the delegator actually hold the edge. On the `rust_lean_divergence_finder`
  known-drift allowlist (`["Burn", "GrantCapability"]`); in producer mode the Rust accept is vetoed
  by Lean. Residual risk is exactly #6/#7 — if Lean isn't initialized, these silently fall back to the
  buggy Rust path.

---

## Priority

1. **#1 CAP-FACET-1** — the one CAP-1-class *exploitable* hole in the bare executor. Fix the gate +
   add the rejection-parity case. Low effort, high value.
2. **#2 xsort order** — make Rust `xsort` the `(round,id)` comparator and compare ordered sequences;
   closes the only honest-node *state*-fork window. Low/medium effort, high value.
3. **#6/#7 fail-open startup hard-checks** — refuse to claim verified production/consensus when the
   archive is absent; this is what keeps #1's mitigation and #2's dormancy real. Low effort.
4. **#3/#4/#5** — promote the covered-set root-agreement toward a theorem or halt-on-divergence; extend
   the producer differential to the uncovered families and the note set.
5. **#8/#9/#10** — liveness/clarity/light-client/config residuals; lower urgency.
