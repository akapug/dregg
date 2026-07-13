# revokedRoot — the committed credential-revocation accumulator (hole #3 / #139)

**Status:** design, ember-approved shape, awaiting a quiet tree. **Why:** without a *committed, canonical*
revocation root, nobody can **attest to correctly-revoked behavior** — and trustless validium interchain
therefore does not hold. (ember, 2026-07-10.)

## 1. The hole (verified, not assumed)

- `turn/src/executor/authorize.rs:1378` — `if let Some(channel_id) = &proof.revocation_channel` — the
  **proof (wire)** supplies which revocation channel the gate consults; `:1317` looks it up in
  `self.revocation_channels`.
- `docs/reference/lean-distributed.md` — the deployed rest-hash encoder absorbs the **revocation-channel
  WIRE root**.
- So the committed state *binds* a wire-supplied root but never proves it **canonical**. A malicious node
  supplies an empty/stale revocation root ⇒ the fail-closed gate sees nothing revoked ⇒ the commitment
  faithfully records the lie ⇒ a light client (holding no revocation set) **cannot detect it**.
- The canonical Lean says exactly this: `RecordKernelState.revoked` is *"the committed set of revoked
  credential nullifiers … read off committed state (**NOT** the wire-supplied `NodeAuth.rev`), so the
  fail-closed gate `gateOK` honours revocation"* — tagged **hole #3 / #139** (`RecordKernel.lean:318-325`).

**Do not conflate** (I did, at first): the Rust `canonical_revocation_tree_for_set(previously_spent)` is a
tree of **spent nullifiers** (the non-revocation/*freshness* circuit), i.e. the nullifier set — already
accumulator-ized. `revoked` is **credential revocation**, a different set with no runtime registry at all.
Also distinct: **delegation** revocation already has a light-client foil (`delegation_epoch` bumped by
`apply_revoke_delegation`, folded into the canonical state commitment — the "pale ghost" mechanism).
**Credential** revocation has no such foil. That is the gap.

## 2. What the canonical Lean already assumes

`NullifierAccumulatorKernelBridge.toNfAccState k = { nullifierRoot := k.nullifierRoot, revokedRoot :=
k.revokedRoot }` — `revokedRoot` is **already modeled on the same `Heap8Scheme` accumulator as
`nullifierRoot`**, and `kernel_revoked_gate_fails` proves: *a revoked `credNul` admits NO non-membership
witness against `revokedRoot` ⇒ the revocation gate cannot pass* (fail-closed). `RecordKernelState` carries
`revokedRoot : Fin 8 → ℤ` and `RH`/`RestHashIffFrame` absorbs it (landed `1dce9523c`). **The canonical side
is done.** The runtime is the ghost that must catch up — same pattern as nullifier/commitments.

## 3. The design (ember-approved)

**Uniform accumulator.** `revoked` joins `nullifier` + `commitments` on the SAME deployed
`CanonicalHeapTree8` (arity-16 sorted-Poseidon2) — one proven primitive, one gate, and the shape the Lean
already models. New `cell/src/revoked_set.rs`: `RevokedSet` — a grow-only `(credNul → value)` map,
`root8() -> Faithful8`, mirroring `NullifierSet`/`CommitmentSet` exactly.

**Leaf value — DECIDED (ember, 2026-07-10): `value = revocation_height`.** The nullifier leaf's `value` is
load-bearing (the note value, `PI[38]`, "the audit felt"). Credential revocation has no published amount,
and the Lean gate needs only membership (`credNul ∈ keysOf8 revokedRoot`); since no revoked-credential
circuit gate exists yet, we chose. `revocation_height` is the audit felt — *when* the credential was revoked:
auditable, monotone, and non-degenerate so the completion lanes stay non-vacuous (a `value = 1` presence
marker would throw the "when" away). Leaf: `HeapLeaf { addr: fold_bytes32_to_bb(credNul), value:
split_u64(revocation_height).0 }` — the SAME encoding `NullifierSet`/`CommitmentSet` use, via the circuit's
own exported helpers so it cannot drift. The Stage-C circuit grow-gate MUST insert this exact leaf; the
differential tooth (Rust `root8()` == in-circuit after-root) then holds by construction and is tested.

**Runtime registry.** `note_revoked: Mutex<RevokedSet>` on `TurnExecutor` (beside `note_nullifiers` /
`note_commitments`). `cap_revoke` / `Effect::RevokeCapability` inserts the revoked `credNul`. Rollback wired
(a failed turn must not leave a phantom revocation). The per-cell cap **tombstone** (limb 25 `cap_root`)
stays — it is capability-slot revocation, orthogonal to the credential registry.

**Gate reads COMMITTED state.** `authorize.rs` stops consulting the wire-supplied `proof.revocation_channel`
root; it verifies a **non-membership witness** for `credNul` against the **committed `revokedRoot`**
(fail-closed: no witness ⇒ refuse). This is the actual hole-#139 closure. Retire/reconcile the
revocation-channel wire root absorbed into the rest-hash.

**Committed geometry (flag-day; VK regen is cheap per ember).** Every faithful-8-felt group is
`(lane-0 in the base region, 7 completion felts in 37..87)`. Base limbs 0..36 are FULL
(`cells_root · r0..r23 · cap_root(25) · nullifier(26) · commitments(27) · heap(28) · lifecycle · epoch ·
committed_height · lifecycle_disc · perms_digest · vk_digest · mode · fields_root(36)`); completion 37..87
has exactly **7 free (81..87)**. So: **widen the base 37→38**, `revoked_root` = base limb **37**, shifting
completion→38..88, carrier→89..112, fields→113..168, pad→169, `V9_NUM_PRE_LIMBS` 169→**170**. Group column
`(37, 82..88)`. Every index ≥37 shifts +1 (mechanical, `sg`-sweepable). Chosen over the zero-churn "append
lane-0 at 169" hack because `revoked_root` IS a base root and the base region is where the circuit expresses
that — keeps `preLimbsAt` honest.

## 3b. THE CRYSTALLIZED DESIGN (after 4 read-only scholars, 2026-07-10) — smaller than it looked

**The scholars' verdict.** Lean PROVES the refusal teeth (`gateOK_revoked_fails`, `kernel_revoked_gate_fails`,
`id_revoked_rejected_forever` — all `#assert_axioms`-clean, genuinely two-valued via
`witness_inhabited_of_bindings`) AND PROVES the registry is frame-invariant (`execFullA_revoked_eq`: *"No
current effect grows it"*). The `⊆` "grow-only" theorem is proved BY REFLEXIVITY. `cap_revoke`,
`revokeCredentialAcc`, and "the MDB root" are COMMENTS WITH NO DEFS, on both sides. **A perfect lock on an
empty registry.** The reader is right; the writer was never built.

**The semantics were already right in the circuit.** `circuit/src/dsl/revocation.rs` +
`circuit/src/non_revocation_witness.rs` prove non-membership of an **`ancestor_hash`** against
`[revocation_root, queried_item]`. That is seL4 MDB `revoke`-tears-down-the-subtree, achieved the cheap way:
each cap proves NO ANCESTOR OF MINE IS REVOKED. Revoking a parent kills descendants with ONE insert — no
subtree walk, no O(N), and the executor never needs the CDT. **The ONLY defect: `revocation_root` is a
wire-supplied single `BabyBear` PI instead of the committed 8-felt root.** That is the entirety of hole #139.

**DECISIONS (ember, 2026-07-10):**
- **Identity `credNul` = the capability instance's derivation-node / provenance hash** — the same
  `ancestor_hash` the circuit already queries (`Poseidon2(cell ‖ slot ‖ parent_hash ‖ derivation_type)` /
  `DerivationNode::hash()` which also folds `created_at ‖ created_by_turn`). **NOT `(cell, slot)`**: slots are
  REUSED after revoke (`derivation.rs:189-190`), so `(cell,slot)` keying makes a revoke-then-regrant inherit
  the revoked identity and permanently poison the slot. **NOT `breadstuff`**: caller-supplied, defaults None,
  already overloaded as a channel_id (`apply.rs:1911`).
- **Batch revoke, without inheriting coarseness.** TWO key-kinds in ONE accumulator, DOMAIN-SEPARATED:
  `credNul = H("dregg-cred-revocation-v1" ‖ provenance_hash)` and
  `chanNul = H("dregg-chan-revocation-v1" ‖ channel_id)`. The gate checks non-membership of BOTH (a cap
  presents its provenance hash, and its channel_id if it names one). Individual revoke = one provenance
  insert; batch revoke = one channel insert killing every subscriber at O(1). This batching is INTENTIONAL
  (caps opt in by subscribing) — unlike `delegation_epoch`'s COLLATERAL coarseness (one bump stales every
  earlier cap from that grantor, targeted or not).
- **Leaf value = `revocation_height`** (the audit felt). `RevokedSet` (Stage A, `5aa0aff86`) takes all of this
  unchanged: `[u8;32] -> u64`.
- **`gatedActionInvG` MUST gain the `revocationGate` conjunct.** Today it has only THREE
  (`credentialValidG ∧ capAuthorityG ∧ caveatsDischarged`), despite its docstring calling it "the
  committed⇒all-four headline" (FullForestAuth.lean:1034-1041). Without this, a committed node does NOT
  attest "was not revoked" — we would wire a registry the attestation still ignores. This is as load-bearing
  as the registry itself for ember's attestation/validium goal.
- **Non-vacuity is the acceptance test.** Today every revocation theorem takes `credNul ∈ revoked` as a
  HYPOTHESIS, discharged only by hand-built fixtures. After this campaign, an ACTION must discharge it.

## 4. Stages (each verified before the next; never leave the tree red)

- **A** `RevokedSet` primitive + `root8()` + differential tooth vs the circuit grow-gate encoding + cross-turn continuity (mirror `nullifier_set.rs`'s test suite).
- **B** Executor registry: `note_revoked` + `cap_revoke` insert + rollback (mirror the commitments lane's journal/rollback wiring).
- **C** Circuit AIR: `revokedRootGroupCol` at `(37, 82..88)`; base widen 37→38; all indices ≥37 shift. Lean emit geometry (`preLimbsAt_length` 37→38) + refinement re-proven.
- **D** Rust commitment twins: `V9RotationContext.revoked_root: Faithful8`; `write_lanes([37,82..88])` in both twins; every existing `write_lanes` index ≥37 shifted. Caller ripple swept.
- **E** Gate cutover: `authorize.rs` verifies non-membership vs the COMMITTED `revokedRoot`; retire the wire root. **This is the hole-#139 closure** — the one stage that changes what the deployed executor *trusts*.
- **F** VK regen + descriptor drift green.
- **G** Live root threading (`turn_proving` + `blocklace_sync`), differential + cross-node tests mirroring nullifier's, whole-tree Lean green.

## 5. Why this matters (the payoff)

With `revokedRoot` committed + the gate reading it: a light client verifies from commitment+proof alone that
(i) revocations accumulated correctly and (ii) the turn honoured them. That yields **attestable
correctly-revoked behavior**, and with it **trustless validium-based interchain** — a remote chain can verify
dregg state transitions without trusting dregg's nodes about revocation. Enforcement ≠ attestability; this
closes the gap.
