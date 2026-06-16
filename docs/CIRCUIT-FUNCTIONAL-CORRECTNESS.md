# Circuit Functional Correctness — Light-Client Unfoolability Through Circuit Semantics

## What this is

A light client verifies a STARK proof against a pinned verifying key and runs nothing else — no
executor, no replayed state. This document states the property that makes that verification *mean
something* — **satisfying the live circuit implies the kernel's behavior happened** — and records the
honest distance between that property and what the live circuit proves today.

The bottom line up front: **the circuit the prover actually runs is not proven semantically
equivalent to the kernel, for any effect.** It is proven anti-tamper and proven to enforce a
field-level *shadow* of each effect; it is not proven that satisfying it implies the kernel's
per-effect step. A light client is therefore trusting the executor it cannot run. Closing this is
the real content of task #103, and it is larger than a per-effect non-amp patch.

## The property (the goal)

The light client's TCB is the pinned `VK_live`, the kernel spec (`execFullForestG` / `fullActionStep`,
`Dregg2/Exec/` + `Dregg2/Circuit/ActionDispatch.lean`), and the named crypto floor. It does **not**
run the executor.

```lean
-- bidirectional: the circuit IS the kernel's semantics (LAW #1), not a sound over-approximation.
theorem lightclient_unfoolable
    {vk}  (hvk : vk = vkOfRegistry liveRegistry)        -- ① binds the LIVE WIRED descriptor set
    [StarkSound] [Poseidon2SpongeCR] :                  -- ② named crypto floor
    ∀ pi π,
      verifyBatch vk pi π = .accept
        ↔ ∃ s t s', execFullForestG s t = some s'
            ∧ pi.pre  = stateCommit s
            ∧ pi.post = stateCommit s'
```

- **⟸ soundness:** a verifying proof against the live VK means the `(pre, post)` is a genuine kernel
  transition — the prover could not fabricate it. (The unfoolability direction.)
- **⟹ completeness:** every turn the kernel accepts has an accepting proof — liveness, and the
  guarantee that the apex is not vacuous.

`⟺` is the claim, not a luxury: LAW #1 is that the circuit *is* the kernel's semantics. Anything
weaker means circuit and kernel have diverged.

### Decomposition

1. **`StarkSound`** — `verifyBatch vk pi π = accept → ∃ trace w, w ⊨ constraints(liveRegistry) ∧ w.pi = pi`.
   A named, documented hypothesis over the audited `p3-batch-stark` verifier; `vk = vkOfRegistry
   liveRegistry` ties the constraint set to the wired registry (①). **No such named hypothesis exists
   today** — STARK soundness is currently implicit inside `RecursiveAggregation.EngineSound`.
2. **◀ the per-effect rung** — for each live effect `e`:
   `descriptorRefines (liveRegistry e) (fullActionStep e)`, stated `⟺`. *Satisfying the live rotated
   descriptor forces the kernel's per-effect step.* **This is the missing rung — for every effect.**
3. **`Poseidon2SpongeCR`** (Circuit/Poseidon2Binding.lean:169) — pins `s` from `pi.pre = stateCommit s`.
4. **Compose** over the forest → `execFullForestG s t = some s'`.

The kernel reference is **`fullActionStep`** (ActionDispatch.lean:168), which is proved
`⟺ execFullA` for all ~30 effects (`fullActionStep_exec_iff`, ActionDispatch.lean:328). So the target
each circuit must refine is complete and well-defined; the gap is entirely on the circuit→kernel side.

## What actually exists today (three circuit models, only one of them live)

| model | what it proves | is it what the prover runs? |
|---|---|---|
| **universe-A full-state** (`effect2CircuitStep` / `satisfiedE2` / `Surface2`, `EffectRefinement.lean`; composed `TurnEffectRefinement.lean`) | the **real** `circuit ⟺ spec ⟺ executor` diamond — for mint, burn, transfer, balanceA, createCell, spawn, delegate | **NO** — a different arithmetization, superseded at the descriptor cutover |
| **rotated `descriptor_ir2` / `Satisfied2`** (the v3 registry: `attenuateV3`, `introduceVmDescriptor`, …) | **anti-tamper** (`rotV3_binds_published` — the commitment binds the whole post-state) + **field-level row shadow** (`rotV3_sound_v1 → satisfiedVm`, a *single-row-window denotation*, not a kernel spec) + a few **partial semantic teeth** (`attenuateV3_non_amp` = `keep ⊑ held`) | **YES** |
| **Argus term-IR** (`interpChained` / `ln`, `Circuit/Argus/`) | connects to the kernel `ln` for the transfer body (`argus_body_is_ln`); partial, per welded effect | NO (a parallel model) |

The fatal mismatch: **the model with real circuit↔kernel equivalence is not the live one, and the live
one has no proof it reaches the kernel at all.** `rotV3_sound_v1` lands in `satisfiedVm` — the
descriptor's *own field-level constraint denotation* — and nothing lifts `satisfiedVm` (or `Satisfied2`)
to `fullActionStep`. For the cap and side-table effects the shadow is *provably* too weak to be a
refinement: the live `introduce` row asserts `cap_root_after = cap_root_before` (frozen), while the
kernel's `introduce` (= `DelegateSpec`, a capability **copy**) *adds* a capability — the row asserts the
negation of the kernel step, with the real mutation pushed "out-of-row" (effects_hash / a system-root).

So the honest status per effect on the **live** circuit:

- **Integrity (anti-tamper):** complete for all 36 (`rotV3_binds_published`).
- **Field-level row shadow:** complete for all 36 (`rotV3_sound_v1`) — but the shadow ≠ the kernel step
  for any effect whose behavior touches caps / side-tables / effects_hash.
- **Semantic equivalence to the kernel (`descriptorRefines`):** proven for **none**. The closest is
  `attenuateV3_non_amp`, which proves *one conjunct* (non-amplification) of attenuate's kernel step, not
  the whole step.

## The work (your 1 → 2 → 3, on the live circuit)

For **every** live effect, build the diamond *on the rotated `descriptor_ir2` circuit* (not the
universe-A model):

1. **Implement the checks in-circuit.** Make the live rotated descriptor enforce the *full* kernel step,
   not a field shadow. Cap/side-table effects need their real mutation gated in-row (membership-open +
   the sorted-tree update for introduce/refresh/revokeDelegation/grant; the effects_hash preimage or the
   system-root mutation for setPermissions/setVK/emitEvent/pipelinedSend; etc.). `attenuateV3` is the
   one effect already carrying its real check (non-amp) — the worked partial example.
2. **Prove sound** (`Satisfied2 (liveRegistry e) ⟹ fullActionStep e`), effect by effect — soundness as
   we go, per your call. An effect whose descriptor is too weak simply fails to discharge; it cannot be
   fake-passed, because the target is the kernel step.
3. **Prove complete** (`fullActionStep e ⟹ ∃ witness, Satisfied2 (liveRegistry e)`), effect by effect.

Then: state `lightclient_unfoolable`, compose the per-effect diamonds over the forest, bind to
`vkOfRegistry liveRegistry`, introduce the named `StarkSound` floor, and add a drift guard (`#guard`:
every descriptor carrying a soundness theorem is in `liveRegistry`) so this can never silently regress.
VK epoch (ember-gated) closes it.

**Mining the universe-A diamonds:** for mint/burn/transfer/balanceA/createCell/spawn/delegate the
*proof content* already exists in `EffectRefinement.lean` — but against a different arithmetization, so
it is a **port**, not a reuse. For the rest it is fresh construction.

### Proposed ordering (mine to pick; soundness-as-we-go)

Two template diamonds first, to fix the pattern at both extremes:
- **transfer / balanceA** — the value template (shadow closest to the kernel step; universe-A diamond +
  `argus_body_is_ln` to mine from).
- **attenuate** — the cap template (already carries non-amp; finish it to the full `AttenuateSpec`).

Then fan out the remaining ~28 effects, soundness first, completeness following, with the apex skeleton
stated early (per-effect obligation carried) so each discharge visibly closes a rung.

## Open items to confirm (flagged, not assumed)

- The exact tie between `Satisfied2`, `satisfiedVm`, and the universe-A `effect2CircuitStep` — three
  denotations; confirm none silently bridges to the kernel (strong evidence they do not).
- `delegateAtten` wire→selector mapping (likely `ATTENUATE_CAPABILITY` = 48 → `attenuateV3`).
- Whether the universe-A `emittedEffect2` path or the rotated `emitVmJson2` path is what the live
  verifier consumes (established: the live verifier parses `emitVmJson2` / the v3 registry).

## Verified status (2026-06-16)

**⚠ Deepest finding — the cap machinery is abstract, so NO effect is soundly tied to the deployed
circuit.** The live cap non-amp (`attenuateV3_non_amp`) opens a `(CAP_KEY ↦ rights-mask)` heap where
`CAP_KEY` is a free param (`prmCol 3` in `EffectVmEmitV2`, never bound to `(actor,target)` / a real
`slot_hash`) and the rights-mask is the only field it sees. The proof never touches the deployed
**7-field** `cap_root::CapLeaf` (`slot_hash, target, auth_tag, mask_lo, mask_hi, expiry, breadstuff`,
`circuit/src/cap_root.rs:91`). `EffectVmEmitCapRoot`'s claim that the prepend-digest, the mapOp heap,
and the sorted tree are "different layers of one root" is **asserted, unproven**. The abstract map
cannot be made faithful (it drops `target`/`auth_tag`/`expiry`, the key is unbound) — so the cap
descriptors must be **rebuilt to open the real 7-field leaf at a bound `slot_hash` key** (a descriptor
change ⇒ **VK epoch**, the true foundation of #103). Until then the cap circuit proves things about a
map the cell never commits to. This corrects the "in-circuit non-amp ✓" framing below: that non-amp
holds over an abstract map, not the deployed cap-tree.

**First rung landed — partial.** `Dregg2/Circuit/RotatedKernelRefinement.lean`'s
`transfer_descriptorRefines` proves a satisfying *live* transfer witness FORCES the kernel's value
move (`BalanceMovementSpec`'s debit/credit + availability) — green, axioms ⊆ {propext,
Classical.choice, Quot.sound} (no crypto needed), with both-polarity conservation teeth. This is the
reusable bridge pattern (`rotatedEncodes`). **It is PARTIAL:** authority (`authorizedB`), liveness,
`acceptsEffects`, and the full state frame are carried as `rotatedEncodes` *assumptions*; the circuit
forces only the two moved limbs + availability.

**The spine = authority, and it is VK-epoch work (verified).** Authority is never circuit-forced for
the value/state effects; the macaroon auth-chain column is a structural fold-binding, not a proof of
`authorizedB`. Forcing authority is BLOCKED on the live descriptor: `transferV3` freezes `cap_root`
but never opens it (zero map-ops, proven), so the row carries no actor-cap key / rights / target. Two
things are required, in order:
  1. **`capTreeEncodes` bridge lemma (VK-NEUTRAL — build first):**
     `opensTo hash cap_root key rights ∧ rights ⊇ {write} ∧ key = hash[actor,src,…] ⟹ authorizedB
     k.caps … = true`, given `cap_root` is the sorted-Poseidon2 commitment of `k.caps`. Connects the
     cap-tree open (which `attenuate` already produces) to the kernel authority predicate. **Does not
     exist anywhere**; the hard shared proof content. Also strengthens `attenuateV3_non_amp` (its
     `opensTo` gains kernel meaning).
  2. **Descriptor widening + VK epoch (ember-gated):** add `(CAP_KEY, HELD_RIGHTS, actor, target)`
     columns + a `transferAuthReadOp` map-op (a shape-clone of attenuate's `heldReadOp`) + key-binding
     gate + rights lookup to every `authorizedB`-gated descriptor, via the existing `v3OfWith` path.
     New columns ⇒ new VK. Effects whose authority is intra-cell (`actor == src`) need no widening.

So the campaign is **"build the shared cap-tree↔Caps bridge, then widen descriptors + bump VK,"** not
"drop a proof in per effect." The cap-open gadget is solved (attenuate); it is undeployed-for-authority
and unconnected-to-the-kernel.

## References

- Live circuit: `circuit/src/descriptor_ir2.rs`, `circuit/src/effect_vm/trace_rotated.rs:394`,
  `circuit/src/lib.rs:244`; `Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean`
  (`attenuateV3` :790, `attenuateV3_non_amp` :1419, `rotV3_sound_v1` :624, `rotV3_binds_published` :696).
- Field-level denotation: `Dregg2/Circuit/Argus/InterpCore.lean` (`satisfiedVm`, `decideVm`).
- Kernel reference (solid): `Dregg2/Circuit/ActionDispatch.lean` (`fullActionStep` :168,
  `fullActionStep_exec_iff` :328); `Dregg2/Exec/` (`execFullA`, `execFullForestG`, `recCexec`).
- The diamonds on the **non-live** model: `Dregg2/Circuit/EffectRefinement.lean`,
  `Dregg2/Circuit/TurnEffectRefinement.lean`; Argus `ln` bridge `Dregg2/Circuit/Argus/Aggregate.lean`
  (`argus_body_is_ln`).
- Crypto floor: `Dregg2/Circuit/Poseidon2Binding.lean` (`Poseidon2SpongeCR` :169).
- Assurance case: `Dregg2/AssuranceCase.lean` (`integrity_guarantee` :361 = the kernel⟹trace binding;
  `unfoolability_guarantee` :615 = the whole-history aggregate). Task #103.
