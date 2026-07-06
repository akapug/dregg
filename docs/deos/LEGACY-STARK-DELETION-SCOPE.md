# Killing the hand-rolled STARK — by making it anew in Lean (2026-07-06)

**Directive (ember):** kill the legacy hand-rolled Rust STARK engine and its ~45
hand-authored AIRs. Not by porting them Rust→Rust onto a nicer prover — that would leave
them Rust-authored, still violating the law — but by **emitting them from Lean** as
byte-pinned descriptors, the way the effect-vm layer already is. The rewrite is not a
downgrade tax; the Lean-emitted version is strictly *better* (see §Even-better).

## The law this restores

Architectural law #1 (REORIENT): *"ZERO Rust-authored constraints or AIRs, ever. All
circuits and constraint semantics are EMITTED FROM LEAN, formally represented. Rust only
interprets Lean-emitted byte-pinned artifacts."* The hand `circuit/src/stark.rs` engine
and every `circuit/src/**/*_air.rs` / `dsl/predicates/*.rs` are the standing violation —
the pre-emit-law legacy the enforcement sweep never reached.

## The diagnosis: two layers, one lawful

| layer | today | lawful? |
|---|---|---|
| **effect-vm turn layer** (transfer, burn, mint, cap-open, cell lifecycle, delegate, exercise, bundle-fold, note-spend…) | **Lean-EMITTED** `EffectVmDescriptor2` (`Circuit/Emit/EffectVmEmit*.lean`, ~40 files), byte-pinned, run by the **p3 IR2 descriptor prover** (`prove_vm_descriptor2_for_config`) | ✅ yes |
| **predicate / membership / DFA / temporal / presentation / shielded layer** | **hand-authored Rust AIRs** (`StarkAir` impls) on the O(n²) hand `stark.rs` engine | ❌ the violation |

The subtlety that makes this tractable: **the Lean specs mostly already exist and are
proven** — `Crypto/{Dfa,DfaAcceptanceAir,PredicateKernel}`, `Authority/{TemporalAlgebra,
QuantifiedPredicate,PrivatePredicate}`, `Circuit/{DecideSatisfied2,SortedTreeNonMembership}`.
What's missing is the **emission**: the Rust AIR was hand-written *beside* the Lean spec
instead of *generated from* it. `Crypto/DfaAcceptanceAir.lean` even documents the hazard
in its own header — the Rust shadow and Lean emit "describe DIFFERENT descriptors." Emit
closes that gap by construction.

## The target engine already takes arbitrary descriptors

No new prover is needed. `prove_vm_descriptor2_for_config` (the effect-vm prover) runs any
`EffectVmDescriptor2`; the parallel lane already drove a *non*-effect-vm statement (the
zkOracle content commitment) through it. And the descriptor IR (`VmConstraint2`) already
speaks the dialects these AIRs need:

- `Base(VmConstraint)` — arithmetic/linear gates + `PiBinding` boundary pins;
- `Lookup(Range { bits })` — the exact bit-decomposition range proofs the predicate AIRs
  hand-roll (`dsl/predicates/arithmetic.rs`'s `diff_bits[0..29]` maps 1:1);
- `Lookup(Poseidon2Chip)` — the hash chains behind membership, note-spend, DFA
  running-hash, and `poseidon2_air` itself.

## Emission difficulty — honest tiers

| tier | families | why |
|---|---|---|
| **T0 — rewire + delete** (emit exists) | membership, accumulator, note-spending | `Circuit/Emit/{AccumulatorInsert,AccumulatorOpen,MembershipAuthRootEdge,EffectVmEmitNoteSpend}.lean` already emit these — the hand AIR is redundant. Just point consumers at the descriptor + delete. |
| **T1 — near-mechanical emit** (IR vocabulary covers it) | arithmetic / relational / compound predicates, `poseidon2_air`, committed_threshold, revocation | constraints are arithmetic gates + `Range` bits + Poseidon2 chip — all IR2-native. Write the `Emit` def from the existing Lean spec, equality-gate vs the hand AIR, rewire. |
| **T2 — emit to author** (vocabulary covers it, no IR extension) | dfa_routing (model = `DfaAcceptanceAir.lean`), derivation, fold, presentation, bilateral_aggregation (ref: `EffectVmEmitBundleFold`), bridge_action, effect_action, multi_step, body_membership | Poseidon2-running-hash / composition shapes the chips express; the Lean model exists; the emit is real work but bounded. |
| **T3 — analyze, maybe extend IR2** | temporal_predicate / temporal_absence, quantified_absence | quantifier + temporal-window non-membership. `SortedTreeNonMembership.lean` is the backing; whether the ∀/∃ + window structure fits `VmConstraint2` as-is or needs a vocabulary add is the one open design question. Scope this family FIRST as the risk. |

## Even-better — what the Lean-emitted version buys (not just parity)

1. **Divergence becomes impossible.** Today the proven Lean spec and the deployed Rust AIR
   are two artifacts that can drift (DfaAcceptanceAir.lean's own warning). Emit makes the
   deployed bytes a *function of* the proof — the `#assert_axioms`-clean spec IS the AIR.
2. **One prover, and it's fast + ZK + foldable.** Everything moves onto `p3 IR2` — off the
   O(n²) single-threaded hand FRI, onto p3's NTT PCS; ZK-capable via `stark_zk`'s
   `HidingFriPcs`; and **recursion-foldable**: a predicate proof becomes a *leaf* that
   folds into the per-turn chain (like the DECO/custom leaves), so predicate/membership
   proofs become light-client-verifiable instead of standalone islands.
3. **The whole single-proof layer inherits the turn layer's machinery** — the faithful
   commitment, the carrier fold, the byte-pinned registry + drift guards — for free.
4. **Two deletions for one migration:** the ~45 hand AIRs *and* the 3977-line `stark.rs`
   engine (its only reason to exist is running those AIRs).

## The kill sequence

1. **T3 risk-scope first** (temporal/quantified) — decide IR2-fits vs needs-extension
   before committing the swarm, so the campaign has no late surprise.
2. **Per family, a lane:** author `Circuit/Emit/<Family>Emit.lean` from the existing spec →
   `#assert_axioms`-clean + non-vacuous → regen the byte-pinned descriptor → an
   **equality gate** (the emitted descriptor's constraint set ≡ the hand AIR's on a
   random-trace corpus, the differential-as-swap-tool discipline) → rewire the consumers
   onto `prove_vm_descriptor2_for_config` → delete the hand AIR.
3. **Fan-out:** the families are independent files — a swarm, one lane per family, main
   loop integrating + owning the shared descriptor registry regen. T0→T1→T2, T3 last.
4. **Delete the engine:** when `grep -r "circuit::stark::\(prove\|try_prove\|verify\)"` over
   non-vendored prod code is empty, `git rm circuit/src/stark.rs`. (The seL4 floor has its
   OWN vendored copy — decoupled, not a blocker. wasm uses `MerkleStarkAir` prove/verify —
   it rides the membership/T0 emit + a compile-check that p3-uni-stark fits wasm, which the
   already-patched-in p3-recursion tower strongly implies.)

## Blockers before a single edit

- **The `circuit/` tree is a live collision** — a concurrent session is mid-write on its
  `endpoints` module and left the tree **red**. A swarm rewriting `circuit/src/**` on top
  of that clobbers it. Must clear + go green first.
- **A swarm this size is a real spend** — needs ember's explicit go / an `ultracode`.
- **My zkOracle STARK work + review docs are still uncommitted and held** behind that same
  red tree. (Note: the zkOracle injection leg I just built is itself a T2-shaped hand-AIR
  on `dfa_routing` — it should be *born* Lean-emitted in this campaign, not ported twice.)
