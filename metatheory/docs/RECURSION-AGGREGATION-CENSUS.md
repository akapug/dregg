# Recursion / Aggregation / Folding Census

A source-grounded census of dregg's proof-aggregation and recursive-proof machinery,
verified at HEAD (`045f22f90`, 2026-06-24). The purpose: separate what dregg
**genuinely does in the live path RIGHT NOW** from built-but-disconnected strands and
stale superseded artifacts, so the Silver→Golden / Mina-zkApp framing rests on an
accurate map of what we have.

Classification scheme (verified per-capability, both directions — neither inflating a
sketch nor dismissing a real proof):

- **ALIVE-WIRED** — in the live apex / executor / circuit / lightclient path TODAY.
- **PROVEN-BUT-DISCONNECTED** — Lean-proven or Rust-built and tested, but not reached
  by a live caller.
- **STALE-ORPHAN** — old campaign-numbered code the live path has moved past; should
  carry a stale banner.
- **ASPIRATIONAL-SKETCH** — design doc / honest-gap only, no realizing code.

---

## HEADLINE

**Yes — dregg already has genuine recursive proof-aggregation, and it is LIVE-WIRED.**

The strongest, most current strand is the **whole-chain IVC accumulator**:

- `circuit-prove/src/ivc_turn_chain.rs::prove_turn_chain_recursive` / `verify_turn_chain_recursive`
  (touched 2026-06-23) folds **N finalized turns into ONE constant-cost recursive STARK
  proof** (`WholeChainProof`) using **real plonky3 in-circuit FRI recursion** (the
  recursion fork, `p3_recursion::{BatchOnly, build_and_prove_aggregation_layer}`) — not
  a hash-chain summary.
- It is consumed by the **live light client**: `lightclient/src/lib.rs::verify_history`
  (line 147) calls `verify_turn_chain_recursive` — **one check, cost independent of N**,
  learns the whole history is correct/ordered/genuinely-folded.
- Its soundness is **Lean-proven gap-free** in `Dregg2/Circuit/RecursiveAggregation.lean`
  (`light_client_verifies_whole_history`, sorry-free, `#assert_axioms`-clean ⊆
  {propext, Classical.choice, Quot.sound}) — the composition of three NAMED, realizable
  recursion-engine soundness hypotheses (`InnerProofSound`, `BindingAirSound`,
  `RecursiveVerifierSound`) into `WellFormedChain` whole-history attestation.

**This is Mina-Pickles-shaped: a succinct proof that attests a whole chain, verified by
a light client in constant work.** dregg ALREADY does the thing the "Golden / folded-DAG"
memory treats as future. The Silver→Golden framing **understates** the live state.

**The stale orphans are a different, older lineage.** `plonky3_recursion.rs` (last
touched 2026-05-26, a month stale) and the `stark_zk.rs` FRI-verifier gadget
(2026-06-11, test-self-referenced only) are **earlier proof-aggregation experiments that
the live `ivc_turn_chain` recursion-fork path moved past**. Do NOT carry these home; they
should get stale banners. `bilateral_aggregation_air.rs` is NOT stale — it is the
*cross-cell single-turn* aggregator, live-wired through the node `/turns/aggregate` route
— a different axis (cross-cell width) from the whole-chain depth the IVC folds.

**The honest carry-home** (smallest step from live-do to offerable recursive succinctness)
is NOT a new build — it is **closing the two precisely-scoped recursion-fork follow-ups**
documented in `ivc_turn_chain.rs` (child-circuit VK identity + cross-layer public-value
propagation) so the whole-chain aggregate is gap-free end-to-end, plus the trivial
**node-verifier leg-chain wiring** (the cohort chain-check already lives in the SDK and
is Lean-proven; the node verifier only checks the lead leg).

---

## 1. PROOF AGGREGATION / BATCH VERIFICATION — what one light-client check covers

dregg aggregates on **TWO orthogonal axes**, both real, at different maturity:

### (A) DEPTH — whole-chain recursive fold (N turns → one proof) — ALIVE-WIRED

- **`circuit-prove/src/ivc_turn_chain.rs`** (HEAD 2026-06-23) — the whole-chain
  accumulator. `prove_turn_chain_recursive` folds a finite K-turn window into ONE root
  recursive proof; each finalized turn's leaf is the **REAL Lean-descriptor turn circuit**
  re-proven as a recursion-compatible uni-STARK, verified IN-CIRCUIT by the plonky3
  recursion fork's verifier. Module docs lines 5–13, 39–96. The temporal tooth
  (`new_root[i] == old_root[i+1]`) is enforced by a wrapped `TurnChainBindingAir`
  (`ivc_turn_chain.rs:246`).
- **`lightclient/src/lib.rs::verify_history`** (line 147, calls
  `verify_turn_chain_recursive`) — the LIVE consumer. One verification, cost independent
  of N, reads off the genuine `genesis_root → final_root` + `chain_digest`. This IS
  genuine aggregation, not sequential re-check: the light client re-executes nothing,
  re-hashes nothing, walks no blocklace (lib.rs docs lines 4–16).
- **Lean backing — `Dregg2/Circuit/RecursiveAggregation.lean`** (HEAD 2026-06-22,
  sorry-free, axiom-clean). `light_client_verifies_whole_history` (line ~169) +
  `conserves_from_verification`: IF the aggregate root verifies (the named
  `recursive_sound`), THEN every leaf executed (`recCexec pre turn = some post`), the
  chain is ordered (`ChainBound`), and the final root is the genuine fold —
  `AggregateAttests`. The three engine hypotheses (`EngineSound`, line 115) are
  `structure` FIELDS (realizable crypto carriers), NOT axioms. This is the honest
  boundary: you cannot prove plonky3 FRI soundness in Lean; everything ABOVE that
  boundary (the composition where an aggregation bug would hide) is proved gap-free.

### (B) WIDTH — cross-cell single-turn aggregation (N cells → one proof) — ALIVE-WIRED

- **`circuit/src/bilateral_aggregation_air.rs`** (HEAD 2026-06-23, the recent touch is a
  kernel-align fix, not aggregation churn) — collapses N per-cell proofs + the bilateral
  schedule of ONE shared turn into ONE outer AIR with fixed-width (23-felt) public inputs
  independent of N. A Lean-emitted descriptor (law #1). This is the "γ.2" / joint-bilateral
  aggregator.
- **`turn/src/aggregate_bilateral_prover.rs::prove_aggregated_bundle` /
  `verify_aggregated_bundle`** — the Rust prover/verifier over it.
- **LIVE caller: `node/src/api.rs`** — the `/turns/aggregate` route (line 1743,
  `post_aggregate_bundle` at 3363) runs `prove_aggregated_bundle` → real outer STARK →
  `verify_aggregated_bundle`, with `WitnessedReceipt::verify_bilateral_chain` as the
  soundness gate. Also reached from `node/src/mcp.rs` and `node/src/blocklace_sync.rs`.
  **This is wired into the live node API — NOT a dead orphan.**

### (C) The per-turn / per-cohort fold (many effects → one turn statement) — ALIVE-WIRED (Lean) + PARTIALLY-WIRED (node verifier)

- **`Dregg2/Circuit/CircuitSoundness.lean::turnDecodeChain_refines_turnSpec`**
  (lines 633–684, HEAD 2026-06-24) — the per-turn fold: a left-to-right list induction
  over `List (DecodedStep S)` composing many per-effect circuit accepts into a single
  `execFullTurnA s acts = some s'`, with the seam DERIVED from commitment binding (the
  frame tooth `stateDecodeChain_frame_continuous`), not assumed. **Not recursive** — a
  structural list fold, but genuine aggregation (one turn statement covers up to 36
  heterogeneous mixed effects).
- **`Dregg2/Circuit/ClosureForest.lean::lightclient_unfoolable_circuit_sound_turn`**
  (lines 144–177) — the CLOSED apex: routes each step through its proven per-effect
  `<e>_closedLog` rung (36-way split), folded along the `TurnDecodeChain`. Non-vacuity
  proven for a genuinely mixed turn (cellSeal + revoke + mint simultaneously,
  `closedLogExtract_family_covers_mixed`).
- **`Dregg2/Circuit/RotatedKernelForestCohortChain.lean::chainForcesEveryCohort`**
  (lines 28–44) — forces EVERY cohort leg's transition (not just the lead) + the
  anti-splice chain-rejection tooth (`chainBroken_rejects`). **NOTE the wiring gap it
  documents (lines 16–19): the DEPLOYED prover `sdk/full_turn_proof.rs::prove_cohort_run_chain`
  ALREADY emits the per-turn leg chain, and the SDK `verify_full_turn_bound` ALREADY
  chain-checks it — but the deployed NODE verifier `turn/executor/proof_verify.rs`
  resolves ONE descriptor by `vm_effects.first()` (the lead cohort) and does NOT iterate
  the legs.** This module is the Lean soundness backing for wiring that same iterate+chain
  shape into the node leg. ADDITIVE, NOT live-wired (Lean self-attests this).

**Answer to "what does one light-client check cover?":** at the whole-history level, a
single `verify_history` covers a WHOLE K-turn chain (axis A). At the turn level, a single
turn proof covers up to 36 mixed effects (axis C). Cross-cell, one aggregate covers N
cells of one turn (axis B). All three are genuine aggregation (one check, many
effects/turns/cells), not sequential re-verification.

---

## 2. RECURSIVE PROOF / IVC / proof-carrying-proof

| Question | Answer | Where |
|---|---|---|
| Is there a proof that VERIFIES other proofs in-circuit? | **YES** | `ivc_turn_chain.rs` — the recursion fork's in-circuit FRI verifier (`verify_p3_batch_proof_circuit` run as a circuit) verifies each wrapped child leaf proof |
| Is the per-turn proof recursive (turn-proof attests prior turn-proof)? | **NO** at the per-turn layer — proofs are independent per-turn; the receipt chain threads a `previous_receipt_hash` ([u8;32] HASH, not a proof). Recursion lives in the SEPARATE `ivc_turn_chain` accumulator layer that folds N already-finalized turns. | `turn/src/witnessed_receipt.rs` (hash link), `turn/src/verify.rs` (hash-chain verify), vs `circuit-prove/src/ivc_turn_chain.rs` (the recursive fold) |
| Is the receipt chain itself recursive? | **NO** — hash-linked log (`previous_receipt_hash`), proven-chained in `turn/src/verify.rs::verify_receipt_chain` (genesis = None, each links prior BLAKE3). Recursion is the additional `ivc_turn_chain` layer over it. | `turn/src/verify.rs:104–170` |
| Attenuation/delegation-depth IVC | **ALIVE** but DIFFERENT scope — `circuit/src/ivc.rs` folds an *attenuation* fold-chain (delegation depth), hash-chain accumulation with a real STARK backend (`StateTransitionAir`). NOT the whole-turn-chain accumulator. | `circuit/src/ivc.rs` |

So: dregg HAS recursive proof-carrying-proof, realized at the **whole-turn-chain
accumulator** (`ivc_turn_chain`), Lean-proven in `RecursiveAggregation.lean`. It is NOT
at the per-turn or receipt-hash layer (those are independent + hash-linked by design).

---

## 3. THE STARK FOLD / FRI — recursive STARK verifier

- **LIVE recursion**: `circuit-prove/src/ivc_turn_chain.rs` uses the **plonky3 recursion
  fork** (`p3_recursion::{BatchOnly, build_and_prove_aggregation_layer,
  build_and_prove_next_layer}`) — a genuine in-circuit recursive STARK verifier with real
  FRI. This is the live fold.
- **STALE-ORPHAN — `circuit/src/stark_zk.rs::FriVerifierGadget` / `RecursiveFriAir`**
  (HEAD 2026-06-11, a hand-rolled "STARK-in-STARK recursion (CG-1)" gadget that
  algebraically enforces `folded = even + beta * odd` per FRI layer). **It is referenced
  ONLY by its own file** (no live caller in node/turn/lightclient; grep for
  `RecursiveVerification`/`build_recursive_trace` hits only `stark_zk.rs` itself). This is
  the EARLIER hand-rolled recursion experiment, superseded by adopting the plonky3
  recursion fork in `ivc_turn_chain`. **Should carry a STALE banner.**
- **STALE-ORPHAN — `circuit/src/plonky3_recursion.rs`** (HEAD **2026-05-26**, ~1 month
  stale). Its OWN docstring says "This is NOT full in-circuit recursion … What we provide
  is proof aggregation: combining N proofs into 1 by proving knowledge of their public
  inputs in a hash chain" (lines 12–28). A Poseidon2 hash-chain aggregation AIR; inner
  proofs verified OUTSIDE the circuit. Referenced by `plonky3_verifier_air.rs` (test) and
  re-exported, but the live recursion is the fork in `ivc_turn_chain`. **Should carry a
  STALE banner.**
- **`circuit/src/proof_forest.rs`** — explicitly RETIRED (its own docstring lines 1–12:
  "The original bespoke-EffectVmAir proof FOREST is RETIRED with the v1 hand-AIR. The
  recursion tower folds the rotated leaf in `crate::ivc_turn_chain` / `crate::joint_turn_recursive`
  instead."). Now carries only `CUTOVER_READY_SELECTORS` metadata. Already self-bannered.

---

## 4. GAMMA-AGGREGATION + SILVER/GOLDEN — actual state

- **Silver** (per memory `project-silver-and-golden-visions.md`) = "integration-complete"
  (every primitive wired, executor-trust). **Golden** = "full distributed-semantics
  algebraic constraint / folded-DAG of attestations" (cross-cell causality proved
  algebraically; the full mesh up to now provable as one folded object).
- **γ.2 (joint bilateral aggregation)** = the WIDTH axis (cross-cell, one turn). It is
  **BUILT + LIVE** as `bilateral_aggregation_air.rs` + the `/turns/aggregate` node route
  (§1B above). The "γ.2 is the entry point to Golden, optional for Silver" doc framing is
  now **out of date in the conservative direction** — it landed.
- **The folded-DAG / whole-mesh-as-one-object (the true "Golden")** is **realized along
  the DEPTH axis** by `ivc_turn_chain` (§1A) — a whole-chain fold IS a folded DAG of
  per-turn attestations. The honest residual is NOT "build the fold" (it exists) but the
  two scoped recursion-fork follow-ups (§ carry-home below).
- Archived `STAGE-7-GAMMA-AGGREGATION-DESIGN.md` (deleted from `docs-history/` per git
  status) and `STAGE-7-GAMMA-2-PHASE-2-SKETCH.md` are **ASPIRATIONAL-SKETCH docs of the
  OLD plan** that the live `ivc_turn_chain` + `bilateral_aggregation_air` superseded. They
  are design history, not the current state.

---

## 5. MINA CORRESPONDENCE — what dregg matches, the honest gap

| Mina / Pickles | dregg | State |
|---|---|---|
| Succinct proof of the whole chain, verified by a light client in constant work | `lightclient::verify_history` over `WholeChainProof` | **MATCHED, LIVE** |
| Recursive SNARK folding per-block proofs (Pickles wrapping) | `ivc_turn_chain::prove_turn_chain_recursive` (plonky3 recursion fork, in-circuit FRI verify of child leaves) | **MATCHED** (K-bounded window) |
| Each leaf proof attests genuine state transition | leaf = REAL Lean-descriptor turn circuit, executor-sound per-effect (`WholeTurnTriangle`) | **MATCHED + Lean-proven** |
| Unbounded online accumulator (single running proof, O(1) memory, re-folded forever) | `fold_two_turns` 2-step inductive core exists; the unbounded driver needs the fork's `into_recursion_input::<BatchOnly>` chaining driven as a fold not a tree | **GAP** (bounded-K today; unbounded is fork work) |
| Full in-band leaf-circuit identity binding | child-circuit VK identity not yet pinned in-band (fork follow-up); cross-layer public-value propagation hardcoded empty (`BatchOnly` `table_public_inputs`) | **GAP** (two precisely-scoped recursion-fork follow-ups, documented `ivc_turn_chain.rs:100–150`) |

**Honest Mina-recursion gap, precisely:** dregg matches Mina's succinct-whole-chain +
recursive-fold + executor-sound-leaves shape TODAY for a **bounded K-turn window**, with
**Lean-proven composition** (which Mina does NOT have — Mina's recursion soundness is not
machine-checked above the SNARK boundary). The two open items are (1) the **unbounded**
online accumulator (Mina is unbounded; dregg's `fold_two_turns` core exists but the
unbounded driver is unbuilt) and (2) two **in-band binding** follow-ups in the recursion
fork (child VK identity + cross-layer public propagation). These are the EXACT honest gaps
the live code documents — not vague aspiration.

---

## THE CARRY-HOME STRAND (highest leverage, relative to LIVE capability)

dregg already LIVE-DOES recursive whole-chain aggregation. The smallest honest step from
what we do now to **offering** gap-free recursive succinctness (and being able to state
"dregg is a Mina-shaped recursive light client" without an asterisk):

1. **Close the two scoped recursion-fork follow-ups** in `circuit-prove/src/ivc_turn_chain.rs`
   (lines 100–150): (a) check the child-circuit public-input vector at host verification
   (`verify_all_tables` takes no public values today) so leaf op-list identity is pinned
   in-band; (b) thread `table_public_inputs` through batch-to-batch chaining + check at the
   root so leaf publics re-expose up the tree. These are NAMED, BOUNDED fork lever items,
   not research. This converts `WholeChainProof` from "sound under VK-pin + carried binding"
   to gap-free.

2. **Wire the node verifier to iterate cohort legs** — `turn/executor/proof_verify.rs`
   today checks only `vm_effects.first()`; the SDK `verify_full_turn_bound` already
   chain-checks all legs and `RotatedKernelForestCohortChain.lean::chainForcesEveryCohort`
   is the Lean backing. This is a wiring task (lift the SDK's iterate+chain shape into the
   node leg), closing the per-turn forest-forcing gap (#2) in the live verifier.

3. **(Larger) the unbounded online accumulator** — drive `fold_two_turns` as a running
   fold (not a K-tree) for O(1)-memory perpetual aggregation, matching Mina's unbounded
   recursion. This is genuine fork work, the right "Golden→beyond" frontier AFTER (1)+(2).

**Do NOT carry home** `stark_zk.rs`'s `FriVerifierGadget` or `plonky3_recursion.rs` — they
are the superseded hand-rolled / hash-chain recursion experiments; the live path is the
plonky3 recursion fork in `ivc_turn_chain`.

---

## MEMORY / DOCS CORRECTIONS

### (a) Claims that UNDERSTATE the live capability

- **`project-silver-and-golden-visions.md`** — "Silver (integration-complete) precedes
  Golden (full algebraic / folded-DAG)" treats the folded-DAG / recursive whole-chain
  aggregation as a FUTURE Golden frontier. **Verified truth:** the recursive whole-chain
  fold is LIVE-WIRED (`ivc_turn_chain` → `lightclient::verify_history`) and Lean-proven
  gap-free above the FRI boundary (`RecursiveAggregation.lean`, sorry-free, axiom-clean).
  The Golden "folded-DAG" along the DEPTH axis exists; only the unbounded driver + two
  in-band binding follow-ups remain. Silver→Golden is NOT "future vs now" — Golden's core
  shipped.

- **`project-circuit-soundness-apex.md`** — frames the apex as per-turn/per-effect
  unfoolability; does NOT surface that a SEPARATE live layer (`RecursiveAggregation` /
  `ivc_turn_chain`) already lifts this to a **whole-history** light-client attestation in
  constant work. The memory should note the whole-chain recursive aggregate as a live,
  Lean-proven capability, not just per-turn.

- **The Mina-zkApp-subsumption question** can be answered AFFIRMATIVELY for the
  bounded-window recursive light client TODAY (with the two named gaps), with a
  Lean-proven composition Mina lacks — stronger than any prior framing suggested.

### (b) Stale modules/docs that masquerade as current (should get STALE banners)

- **`circuit/src/plonky3_recursion.rs`** — last touched 2026-05-26 (~1mo stale); its own
  docstring concedes it is hash-chain aggregation, not in-circuit recursion. The live
  recursion is the plonky3 fork in `ivc_turn_chain`. **Add a stale/superseded banner**
  pointing to `circuit-prove/src/ivc_turn_chain.rs`.

- **`circuit/src/stark_zk.rs` (`FriVerifierGadget` / `RecursiveFriAir`, the "CG-1"
  gadget)** — touched 2026-06-11, referenced ONLY by its own file (no live caller). The
  hand-rolled FRI-recursion experiment superseded by adopting the plonky3 recursion fork.
  **Add a stale/superseded banner** for the recursion half (the ZK-PCS half via
  `HidingFriPcs` may still be live — verify separately before bannering that part).

- **Archived `STAGE-7-GAMMA-AGGREGATION-DESIGN.md` / `STAGE-7-GAMMA-2-PHASE-2-SKETCH.md`**
  (already deleted from `docs-history/` per git status) — ASPIRATIONAL-SKETCH of the OLD
  γ-plan; `bilateral_aggregation_air.rs` + `ivc_turn_chain.rs` superseded them. They are
  design history; ensure no live doc cites them as current state.

- **`turn/src/witnessed_receipt.rs` docstring** (lines ~79–98) uses "Silver Vision /
  Golden Vision (recursive proof)" to describe a per-receipt REPLAY-level compression —
  this "recursive" is the trace-replay sense, distinct from the whole-chain `ivc_turn_chain`
  recursion. Worth a one-line clarification so the two senses of "recursive" don't
  conflate.

---

## APPENDIX — file:line index of the load-bearing capabilities

| Capability | File:line | Class |
|---|---|---|
| Whole-chain recursive fold (prover) | `circuit-prove/src/ivc_turn_chain.rs::prove_turn_chain_recursive` | ALIVE-WIRED |
| Whole-chain recursive verify | `circuit-prove/src/ivc_turn_chain.rs::verify_turn_chain_recursive` | ALIVE-WIRED |
| Live light-client whole-history check | `lightclient/src/lib.rs::verify_history` (line 147) | ALIVE-WIRED |
| Lean recursive-aggregation soundness | `Dregg2/Circuit/RecursiveAggregation.lean::light_client_verifies_whole_history` (~169); `EngineSound` (115) | ALIVE-WIRED (proven, sorry-free) |
| Cross-cell single-turn aggregation AIR | `circuit/src/bilateral_aggregation_air.rs` | ALIVE-WIRED |
| Cross-cell aggregate prover/verify | `turn/src/aggregate_bilateral_prover.rs::{prove,verify}_aggregated_bundle` | ALIVE-WIRED |
| Live cross-cell aggregate route | `node/src/api.rs::post_aggregate_bundle` (3363); route 1743 | ALIVE-WIRED |
| Per-turn effect fold (Lean) | `Dregg2/Circuit/CircuitSoundness.lean::turnDecodeChain_refines_turnSpec` (633–684) | ALIVE-WIRED |
| Closed mixed-effect turn apex | `Dregg2/Circuit/ClosureForest.lean::lightclient_unfoolable_circuit_sound_turn` (144–177) | ALIVE-WIRED |
| Cohort-chain forcing (Lean) | `Dregg2/Circuit/RotatedKernelForestCohortChain.lean::chainForcesEveryCohort` (28–44) | PROVEN; node-verifier wiring PENDING |
| Deployed cohort-leg-chain prover | `sdk/full_turn_proof.rs::prove_cohort_run_chain` | ALIVE-WIRED (prover); node verify checks LEAD leg only |
| Attenuation/delegation-depth IVC | `circuit/src/ivc.rs` | ALIVE-WIRED (different scope) |
| Receipt hash-chain (NOT recursive) | `turn/src/verify.rs::verify_receipt_chain` (104–170); `turn/src/witnessed_receipt.rs` | ALIVE-WIRED (hash-linked) |
| 2-step inductive fold core (unbounded seed) | `circuit-prove/src/ivc_turn_chain.rs::fold_two_turns` | PROVEN-BUT-DISCONNECTED (driver unbuilt) |
| Hand-rolled FRI recursion gadget | `circuit/src/stark_zk.rs::FriVerifierGadget` (29–48) | STALE-ORPHAN (no live caller) |
| Hash-chain proof aggregation | `circuit/src/plonky3_recursion.rs` | STALE-ORPHAN (2026-05-26) |
| Retired v1 proof forest | `circuit/src/proof_forest.rs` | RETIRED (self-bannered) |
