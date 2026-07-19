# E2 — retire the per-turn double-prove; escalate fold arity to 8 (execution-ready design)

2026-07-19. Design lane for EFFICIENCY-BACKLOG item E2 (rank 2,
`docs/EFFICIENCY-BACKLOG-circuit-minimality.md:263-291`, cutover recipe `:173-190`), grounded at
HEAD = `f11d6d63e`. Provenance: probe GO `1df4bc4cc`
(`circuit-prove/tests/e2_fold_arity_recompose_probe.rs`, 2/2 green, measured) + the 2026-07-19
HORIZONLOG entry (`HORIZONLOG.md:9893`). Evidence classes follow the backlog vocabulary:
[M] measured, [P] parsed from code at HEAD, [A] analytic, [U] unknown.

**Tree-state caveats at write time:** `circuit-prove/src/joint_turn_aggregation.rs` (E9 lane) and
`joint_turn_recursive.rs` (E12 lane) are DIRTY, visibly mid-surgery (working diff −797 lines net
across the two); `circuit/src/descriptor_ir2.rs` is dirty with an UNRELATED zk-lane fix
(HidingFriPcs byte-table degree pin at `:5825`; the E2-relevant knobs are untouched). All citations
into those three files are to the committed HEAD content (`git show HEAD:`), not the working tree.
Everything else cited is clean at HEAD.

## §0 Verdict

**The double-prove premise is CONFIRMED at the code level.** Every finalized turn on the node's
commit path is fully STARK-proven twice — once for serving (`ir2_config`, fold-by-8), once for the
recursion fold (`ir2_leaf_wrap_config()`, fold-by-2) — over the same statement, regenerated from
the same execution context, with a fail-closed anchor tie bridging the two. The second prove exists
ONLY to cross a FRI-engine gap (one knob: fold arity; plus a nominal config-type split), and the
probe has now measured that the gap is not real: the unchanged leaf-wrap absorbs a
production-arity-8 leaf and two such leaves aggregate [M].

**Recommendation: DELETE, with the soundness obligation and canary set below.** The deletion is a
Rust prover-side dedup — the FRI-math side is already Lean-proven and CI-rooted at HEAD with no new
obligations for the lb-6 endpoint. The genuinely new load-bearing surface is the in-circuit
arity-4/8 recompose arms of the Rust recursion verifier, previously dead code on every dregg proof;
the canary set (§4.4) exists to put adversarial teeth on exactly that surface. One recursion-side
FS epoch; ride the Epoch-2 bundle window as its step 2 (`EFFICIENCY-BACKLOG:112`).

## §1 The double-prove, exactly

### 1.1 Prove #1 — the served FullTurnProof (production engine, arity 8)

On the node commit path (`node/src/blocklace_sync.rs:5244-5252`),
`turn_proving::prove_and_verify_finalized_turn` (`node/src/turn_proving.rs:679-766`) mints the
turn's `FullTurnProof`. Its rotated effect-vm leg is minted by
`sdk/src/full_turn_proof.rs:1532-1562` (`prove_effect_vm_rotated_wide`):

```rust
let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)  // :1559
```

`prove_vm_descriptor2` (`circuit/src/descriptor_ir2.rs:5630`, HEAD) proves under `ir2_config()`
(`:5645` → `:5423`), type `DreggStarkConfig`, knobs (`:5452-5456`):

```rust
pub const IR2_FRI_LOG_BLOWUP: usize = 6;
pub const IR2_FRI_LOG_FINAL_POLY_LEN: usize = 0;
pub const IR2_FRI_MAX_LOG_ARITY: usize = 3;   // fold by up to 8
pub const IR2_FRI_NUM_QUERIES: usize = 19;
pub const IR2_FRI_QUERY_POW_BITS: usize = 16;
```

The leg rides inside the composed proof as an `AttachedSubProof` (postcard proof bytes;
`sdk/src/full_turn_proof.rs:4155`), and the whole FullTurnProof is natively verified before serving
(`verify_full_turn`, `node/src/turn_proving.rs:766`; rotated-leg verify = `verify_vm_descriptor2`
at `ir2_config`, `descriptor_ir2.rs:5785-5790` HEAD). The proof's 8-felt wide anchors are read off
the leg and carried on `ProvenFinalizedTurn::{old_commit,new_commit}` (`turn_proving.rs:142-151`).

### 1.2 Prove #2 — the recursion-fold re-mint (leaf-wrap engine, arity 2)

Immediately after, the SAME commit path (`blocklace_sync.rs:5264-5290`) calls
`mint_and_encode_finalized_turn` (`node/src/turn_proving.rs:1497-1538`), which calls
`dregg_turn::rotation_witness::finalized_turn_from_full_turn`
(`turn/src/rotation_witness.rs:734`). Step 1 of that adapter (`:749-762`) is a comment-labeled
re-prove:

```rust
// 1. Re-prove the rotated leg under the leaf-wrap config (statement-equality: same descriptor,
//    same trace, same PI vector as the FullTurnProof's rotated leg). ...
let leg = mint_rotated_participant_leg(...)
```

`mint_rotated_participant_leg` (`rotation_witness.rs:577`) re-runs the FULL wide producer
(`generate_rotated_effect_vm_descriptor_and_trace_wide`, `:652-663`) from the same execution
context, then proves and self-verifies under the wrap config (`:673-687`):

```rust
let wrap_config = ir2_leaf_wrap_config();
let proof = prove_vm_descriptor2_for_config(&desc, &trace, &dpis, ..., &wrap_config)  // :675-684
verify_vm_descriptor2_with_config(&desc, &proof, &dpis, &wrap_config)                 // :685-687
```

`ir2_leaf_wrap_config()` (`circuit-prove/src/ivc_turn_chain.rs:951-966`) is built by
`create_recursion_config_for_inner_fri(6, 0, 0, 16)` (`ivc_turn_chain.rs:869-882` pins
`IR2_INNER_LOG_BLOWUP=6 / LOG_FINAL_POLY_LEN=0 / COMMIT_POW=0 / QUERY_POW=16`), which hardcodes the
one differing knob (`circuit-prove/src/plonky3_recursion_impl.rs:392-418`):

```rust
pub const INNER_FRI_MAX_LOG_ARITY: usize = 1;   // :116 — fold by 2
pub const INNER_FRI_NUM_QUERIES: usize = 19;    // :119
```

with the PROBE comment at `:401-411`: *"the recursion in-circuit verifier's recompose path is
exercised at arity 1 (fold by 2) in every existing recursion test. Use arity 1 here to isolate
whether higher-arity folding is the obstruction; the in-circuit verifier reads the count/arity from
the proof."* So the two engines are knob-identical EXCEPT arity (2 vs 8) — and the arity-2 choice
was a diagnostic that fossilized [P].

The bridge is made faithful by the fail-closed anchor tie (`rotation_witness.rs:765-787`): the
freshly minted leg's PI-tail wide 8-felt anchors must equal the served proof's proven
`(old_commit, new_commit)`, else refuse. The type of the fold input is
`Ir2BatchProof<DreggRecursionConfig>` (`joint_turn_aggregation.rs:105-108` HEAD, on
`RotatedParticipantLeg`), vs prove #1's `Ir2BatchProof<DreggStarkConfig>` — the "SIDESTEP option a"
type split (`ivc_turn_chain.rs:927-935`).

### 1.3 The verification chain each proof feeds

- Prove #1 is verified NATIVELY once (`verify_full_turn`, arity-8 path — the production-hardened
  native arity-8 verifier every served proof already exercises) and is then only served/stored.
  It is NEVER folded.
- Prove #2 is verified natively at mint (`:685-687` self-verify), retained
  (`RetainedFinalizedTurnBytes`, `turn_proving.rs:1470-1494`; proof bytes decode back to
  `Ir2BatchProof<DreggRecursionConfig>`), re-verified natively at fold admission
  (`verify_descriptor_participant`, `joint_turn_aggregation.rs:1252-1266` HEAD, at
  `ir2_leaf_wrap_config`), and finally verified IN-CIRCUIT by the leaf wrap
  (`prove_descriptor_leaf_rotated_with_config`, `ivc_turn_chain.rs:970`), whose output folds
  through the aggregation tree — the whole rotated tree at ONE engine
  (`prove_chain_core_rotated`, `ivc_turn_chain.rs:2871-2913`), root verified at the same config
  (`ivc_turn_chain.rs:2661`, `:3898`).

### 1.4 Premise verdict

**It is a genuine redundant re-prove, not two different checks.** Same descriptor, same trace
generation, same PI vector (statement-equality is the adapter's own stated basis,
`rotation_witness.rs:700-712`); the second prove adds zero statement content and exists only
because (a) the wrap engine's arity knob differs and (b) the config TYPE differs. Both walls are
now measured/known crossable: the probe [M] wrapped and aggregated real arity-8 leaves with the
UNCHANGED wrap code, and the type wall is already crossed at the byte level in production — the
retention path serializes the proof with postcard and decodes it as
`Ir2BatchProof<DreggRecursionConfig>` (`turn_proving.rs:1483-1494`), which only works because the
two configs' proof serializations are structurally identical (same MMCS/hash/challenger types,
`plonky3_recursion_impl.rs:429-441` doc).

Two honest nuances, neither rescuing the re-prove:

1. Prove #2 re-runs WITNESS GENERATION from the execution context rather than reusing served
   bytes. Both runs are the same trusted-Rust producer invoked by the same node, so this is not an
   independent check of anything — divergence is caught only by the 8-felt anchor tie, which
   survives the deletion (§2.1).
2. Prove #1 is a composed multi-leg proof; prove #2 is the rotated leg alone. Deletion therefore
   requires EXTRACTING the bare leg + PI vector from the served proof rather than "dropping bytes
   in" (§2.1, step D2).

## §2 The deletion

### 2.1 What dies, what survives, what must be built

**Dies:**
- The re-prove: `rotation_witness.rs:749-762` (`mint_rotated_participant_leg` call inside
  `finalized_turn_from_full_turn`) and the mint self-verify `:685-687` as exercised on this path.
  (`mint_rotated_participant_leg` itself stays for recipe/joint-turn callers until those migrate;
  the per-turn commit-path invocation dies.)
- The arity-2 diagnostic: `INNER_FRI_MAX_LOG_ARITY = 1` (`plonky3_recursion_impl.rs:116`) flips to
  3; the `:401-411` PROBE comment retires.
- The `DreggStarkConfig`/`DreggRecursionConfig` split as a semantic boundary
  (`ivc_turn_chain.rs:927-935`): after the flip the knob sets are identical, so the production mint
  IS the fold input type. 15 files in `circuit-prove/src` reference the wrap config / recursion
  config in leaf-adapter position [P]; the collapse is mechanical type unification. (A cheaper
  fallback exists — keep the nominal split and byte-bridge via postcard, the mechanism retention
  already uses — but the split is itself the fossil; collapse is the recommended shape.)

**Survives (and is what the deletion leans on):**
- The anchor tie (`rotation_witness.rs:765-787`): keep, retargeted — the retained leg's PI-tail
  anchors must equal `ProvenFinalizedTurn::{old_commit,new_commit}`. Post-deletion it binds the
  retained blob to the served turn (a stale or wrong-turn proof cannot be retained under this
  turn's key), rather than bridging two mints.
- Fold-admission native verify (`verify_descriptor_participant`,
  `joint_turn_aggregation.rs:1252-1266` HEAD) — now at the unified arity-8 config.
- The in-circuit wrap + aggregation + root verification chain, now at arity 8 throughout.

**Built:**
- D1: flip `INNER_FRI_MAX_LOG_ARITY` 1→3 so `ir2_leaf_wrap_config()` ≡ `ir2_config` knobs.
- D2: leg extraction — `finalized_turn_from_full_turn` consumes the served rotated
  `AttachedSubProof` (proof bytes + PI vector) directly instead of re-minting. [U to verify in the
  lane: that the served sub-proof carries the FULL descriptor PI vector verbatim, not a projection;
  `full_turn_proof.rs:4155` region and the verify path `:5034-5066` are where to confirm. If it
  carries a projection, the node retains the bare `(proof, dpis)` pair at prove time instead —
  `prove_effect_vm_rotated_wide` already returns exactly that pair, `:1541-1546`.]
- D3: the type collapse (or byte-bridge) so the extracted leg types as the fold input.
- D4: retention-envelope version bump `RETAINED_FINALIZED_TURN_V1` → 2 (`turn_proving.rs:1468`),
  refusing pre-flip arity-2 blobs fail-closed (§4.3).

### 2.2 The soundness obligation, named

The redundant prove protected NOTHING an adversary could exploit — it was the honest node
re-proving its own statement to itself. What the CUTOVER changes in the adversary's favor is
exactly one thing: the recursion chain's in-circuit FRI verification moves from the arity-2 posture
to the arity-8 posture. The obligation is therefore:

**(O1) The per-fold soundness spend is priced through the ledger, not a comment.** Arity is a
soundness lever worth log₂(m−1) bits. At logBlowup 6: goodCount 2016 → 14112 (×7), perFoldBits
112 → 109. This is ALREADY a Lean theorem at HEAD, `#assert_axioms`-clean and CI-rooted:

- `FriLedgerSound.arity8_costs_seven_times_arity2_at_logBlowup6`
  (`metatheory/Dregg2/Circuit/FriLedgerSound.lean:342-350`) — the two ledgers differ by exactly
  ×7 / 3 bits.
- `FriLedgerSound.wrap_ledger_perFoldBits = 109` (`:303-305`) and
  `wrap_perFold_soundness_from_ledger` (`:315-325`) — the arity-8 bound stated off the exported
  ledger (`@[export] dregg_fri_ledger`, `metatheory/Dregg2/Circuit/FriLedger.lean:380`).
- The hΦ fiber obligation is discharged UNCONDITIONALLY at the deployed (arity 8, logBlowup 6)
  setup: `FriArityFiberDischarge.friSetupK8Wrap` (k=3, b=6,
  `metatheory/Dregg2/Circuit/FriArityFiberDischarge.lean:500-501`) with
  `arity8_phase_injective` (`:509-514`) and `arity8FiberBound_holds` (`:530-531`).

So for the lb-6 endpoint there is **no new Lean obligation**; the cutover's Lean work is the
posture RE-PIN: `ir2LeafWrapRotatedConfig` (`FriLedgerSound.lean:277-279`, the ONE shipped config
the ~112.6 posture describes) stops describing any shipped config, and
`fri_params_soundness_budget.rs` moves its wrap-chain expectations from (arity 2, 2016, 112) to
(arity 8, 14112, 109) via the exported ledger (the drift tooth at
`fri_params_soundness_budget.rs:959-993` and the `lean_model` pin at `:452` are the exact lines
that move; `PER_FOLD_FLOOR_BITS = 109` at `:205` already floors at the arity-8 number, so the
floor itself does not move for E2 alone).

**(O2) The surviving in-circuit check must actually implement arity-8 recomposition soundly.**
This is the genuinely new load-bearing surface: the p3-recursion in-circuit verifier's arity-4/8
reconstruct arms (`reconstruct_evals` + `one_hot_from_bits` — probe header,
`e2_fold_arity_recompose_probe.rs:19-20`) were DEAD CODE on every dregg proof until now (every
recursion test folded by 2). The probe proves COMPLETENESS of these arms [M] (honest arity-8
leaves wrap and aggregate green, schedule `[2,2,3,1]` demonstrably walked); it proves nothing
about their SOUNDNESS. There is no Lean refinement of the Rust in-circuit verifier — this
inherits the tree's standing witness-gen/implementation caveat and must be described at that
resolution. The mitigation is not a proof but the adversarial canary set (§4.4): corrupt-and-
expect-reject teeth aimed specifically at the arity-8 arms. Note the honest baseline: the arity-2
in-circuit arms carry the same unverified-implementation status today; the deletion changes WHICH
unverified arms are load-bearing, not whether unverified arms are.

**(O3) Posture honesty.** Describe the spend as "3 bits off the perFold ledger column
(112 → 109)", never as a system-security delta — the deployed system's holistic FRI posture
carries its own floor caveats (johnson column = idealisation, capacity = refuted-conjecture
canary; see `project-fri-soundness-reality`), and per-fold is one column of that ledger, not a
headline.

### 2.3 Lean keystone or Rust dedup?

**Rust prover-side dedup, with the Lean half already banked** — for the E2-alone (lb 6) endpoint.
The one configuration where a NEW Lean proof is required is the E2+E4 combined endpoint: lb 8 is
NOT among `FriArityFiberDischarge`'s discharged setups (instances exist at (k3,b6) `:500` and
(k3,b3) `:537-540` only [P]), so if E4's re-grid rides E2's epoch, the (arity 8, lb 8) `friSetupK`
instance (k=3, b=8) must land with it or the new perFold number rides an undischarged hypothesis
(the backlog says exactly this, `EFFICIENCY-BACKLOG:161-164`).

## §3 Fold arity 8 — the commit-phase inflation

### 3.1 Where the arity lives and what it costs

Current chain arity: 2, pinned at `plonky3_recursion_impl.rs:116` and inherited by every layer of
the rotated tree — leaf mint #2, leaf wrap, aggregation, root — because `prove_chain_core_rotated`
runs the whole tree at `ir2_leaf_wrap_config` (`ivc_turn_chain.rs:2871`, `:2913`). The production
member engine is already arity 8 (`descriptor_ir2.rs:5454`).

Commit-phase round count is structural: rounds = ⌈(log|D⁰| − logBlowup)/maxLogArity⌉ — Lean-modeled
in `friCommitLedger` (`FriLedger.lean:322` `rounds := ceilDiv (logD0 - cfg.logBlowup)
cfg.maxLogArity`), i.e. rounds = trace log-height at arity 2, /3 (ceiling) at arity 8. Wrap-step
trace heights are floored at degree_bits ≥ 16 by the `min_trace_height` fixed-shape ceiling
(`circuit-prove/src/accumulator.rs:217-240`; measured heights
`fri_trace_height_measure.rs:51-55`). The measured fixture behavior [M, probe]: 8 phases → 4
phases at 2^8-ish height; at deployed wrap heights the backlog's figure is ~18 → ~6 rounds.

### 3.2 The ~3.8× derivation and its hedges

Per query, each commit phase costs one Merkle path on the phase's (shrinking) domain plus the
coset-leaf absorb. Arity 2 at log-domain d: ~d−lb rounds with path depths d−1, d−2, …; arity 8:
one-third the rounds with depths d−3, d−6, … but 8-element coset openings per round. Summing path
lengths at the deployed wrap shape gives ≈3–3.8× on the commit-phase Merkle-path hashing term; the
backlog's verified hedge stands: **~3.8× applies to the commit-phase Merkle-path term only; the
whole hashing table drops by less than 3×** because input-round paths are arity-independent
(`EFFICIENCY-BACKLOG:292-299`). The 2^15-row poseidon2-W16 hashing table (~11,000 perms) in every
wrap circuit is precisely this term. Class: [P] structure, [A] arithmetic, with the probe's 8→4
phase halving as the [M] anchor and the at-height confirmation explicitly assigned to the cutover
lane (HORIZONLOG `:9928-9931`). Measured free riders from the probe: −7.1% leaf wire (402,539 →
373,951 B, same trace) and wrapped root 229,594 B [M].

Downstream latency claim this serves: post-Epoch-2 the recursion stack is >99% of settlement
latency (`EFFICIENCY-BACKLOG:288-291`, R11), and the deleted re-prove is one full descriptor prove
per finalized turn on the commit path (~425–440 ms post-S2 [A]; 638 ms was the pre-S2 [M] figure —
`EFFICIENCY-BACKLOG:706`).

### 3.3 What the flip requires, layer by layer

- **Rust knob (the whole flip):** `INNER_FRI_MAX_LOG_ARITY` 1→3. The in-circuit verifier allocates
  its targets from the proof's own schedule, so no recursion-verifier code changes [M, probe with
  UNCHANGED wrap code]. The wrap/aggregation circuits change SHAPE (fewer, wider commit-phase
  layers) → the root VK fingerprint changes → this is the FS/VK epoch (§4.3).
- **Apex shrink:** `apex_shrink.rs` verifies the recursion apex in-circuit under
  `ir2_leaf_wrap_config` (`apex_shrink.rs:24`, `:50`, `:120`) using the same p3-recursion
  machinery — expected to absorb arity-8 the same way [P; the probe did NOT run the apex layer —
  canary C5]. Its OUTER output config (`dregg_outer_config.rs:134/136/144`: lb 3, 38q,
  `OUTER_FRI_MAX_LOG_ARITY = 1`) is a SEPARATE knob set and may stay arity-2.
- **gnark (the precisely-scoped long pole):** the ETH wrap verifies the OUTER proof, and
  `friFoldRowArity2` (`chain/gnark/fri_verify_native.go:228`; also `:25`, `:156`) hardcodes
  arity-2 for THAT layer — the gnark `FriConfig` carries no arity field at all
  (`dregg_outer_config.rs:139-142` doc). So E2 alone does NOT require a gnark arity-8 `fold_row`:
  it is required only if the OUTER config also escalates. The ETH wrap still RE-LANDS once
  regardless, because the apex proof's shape change can move the outer shrink trace shape and
  hence the Groth16 circuit/VK — which is why the backlog bundles this with apex lever B
  (`EFFICIENCY-BACKLOG:186-188`) so the ETH wrap re-lands exactly once. [U: whether the outer
  trace height actually crosses a power-of-two boundary at arity 8 — measure in the lane before
  assuming the gnark circuit is byte-stable.]
- **dregg_fri_ledger / budget gate:** expectations move as §2.2(O1); the always-on gate is the
  compiled Lean ledger, so the move is a re-pin of Rust-side expected tuples, not new arithmetic.

### 3.4 Interaction with E4 (FRI re-grid) — they compose, with one shared obligation

E4's ledger verdicts (`EFFICIENCY-BACKLOG:36-51`, landed `daa0a16`) are all stated at
**arity 2^3** — i.e., E4's numbers already assume the E2 arity flip on the member statement:
deployed (6,19,16) = 109/73/130/67, (8,15,16) = 105/76/136/60, (8,14,16) = 105/72/128/60. The
interactions:

1. **Epoch:** E4 rides E2's FS epoch (backlog sequencing `:112-113`); a lone E4 flip would be a
   second flag day. E2 defines the epoch; E4 is a rider.
2. **perFold floor:** E2 alone lands the chain at 109 = the existing `PER_FOLD_FLOOR_BITS`
   (`fri_params_soundness_budget.rs:205`) — no floor movement. E2+E4 lands at 105, BELOW the 109
   floor: a *documented floor re-pin*, a second, separate decision (E4's, not E2's).
3. **Fiber discharge:** E2 alone is fully discharged ((k3,b6) unconditional). E2+E4 needs the new
   (k3,b8) `friSetupK` instance (§2.3) — the ONE new Lean proof in the combined campaign.
4. **Commit-phase column:** E4's finding — lb 6→8 costs 7 commit-phase bits (67→60), invisible to
   the closed-form columns — is computed at arity 8 already; E2's arity flip is what makes those
   numbers describe the deployed chain. Arity does enter `friCommitLedger` (sumArities =
   rounds·m, `FriLedger.lean:323`), so the wrap-chain commit column at measured heights should be
   re-read from the ledger after the flip rather than assumed (the `commitBits` column is
   trace-height-dependent; `fri_trace_height_measure.rs` is the harness).
5. **Cumulative honesty:** if both land, the wrap chain's perFold posture moves 112 → 105 total.
   Say that in the cutover commit; do not book the two 3-4 bit spends in separate sentences that
   never meet.

## §4 Blast radius, staging, canaries

### 4.1 Files touched (deletion + arity-8; excludes E4 riders)

Rust — semantic:
- `circuit-prove/src/plonky3_recursion_impl.rs` — `:116` knob flip; retire `:401-411` PROBE
  comment + `:107-115` doc; the stale "prover side unchanged from create_recursion_config
  (lb 3, 38q)" doc at `:380-384` is WRONG at HEAD (the engine is fully self-consistent at the
  inner knobs, `:429-441`) and should die in the same commit. `RECURSION_*` consts (`:95-105`,
  create_recursion_config, lb3/38q/pow14) are NOT touched — that is E11's held territory
  (production-live via `gpu_backend.rs:4459`).
- `turn/src/rotation_witness.rs` — `finalized_turn_from_full_turn` re-prove deletion + leg
  extraction (D2); anchor tie retargeted, kept fail-closed.
- `circuit-prove/src/ivc_turn_chain.rs` — `ir2_leaf_wrap_config` doc re-pin; the SIDESTEP-era doc
  block `:875-935`; type collapse touchpoints (`TurnChainBindingProof.proof:
  Ir2BatchProof<DreggStarkConfig>` at `:1488` STAYS — the binding descriptor is natively verified,
  never folded).
- `circuit/src/descriptor_ir2.rs` — type collapse side (`prove_vm_descriptor2` return type or the
  unified config alias); knobs `:5452-5456` unchanged by E2.
- `node/src/turn_proving.rs` — `mint_and_encode_finalized_turn` consumes the served leg;
  `RETAINED_FINALIZED_TURN_V1` → 2.
- `sdk/src/full_turn_proof.rs` — leg extraction surface (or bare-leg retention at prove time).
- ~15 leaf adapters + `accumulator.rs`, `apex_shrink.rs`, `merge_pool.rs`,
  `field_delta_range_air.rs`, `shielded_ring_clearing*.rs` — mechanical config/type unification
  [P: 15 `circuit-prove/src` files reference the wrap-config surface].
- ⚠ `circuit-prove/src/joint_turn_aggregation.rs` / `joint_turn_recursive.rs` — multiple
  `ir2_leaf_wrap_config` mint sites at HEAD (`:680-1154`) ride the flip automatically; both files
  are OWNED BY LIVE LANES (E9/E12) right now — sequence E2's edits AFTER those lanes land, or
  hand E9/E12 the one-knob heads-up. `recursive_witness_bundle.rs` is NOT on this path (Golden-v1
  `EffectVmShapeAir` stratum, E11's held question) — no E2 changes there.

Lean:
- No new theorem for E2-alone (§2.2). Doc/pin motion only: `FriLedgerSound.lean`
  `ir2LeafWrapRotatedConfig` banner (`:270-279`) — it becomes a historical config, kept as the
  arity-drift tooth's reference point. If E4 rides: NEW `FriArityFiberDischarge` (k3,b8) instance.

gnark:
- Nothing mandatory for E2-alone (§3.3). Optional/bundled: arity-8 `fold_row` beside
  `friFoldRowArity2` (`fri_verify_native.go:228`) iff the OUTER config escalates; ETH-wrap
  re-land bundled with apex lever B either way.

Tests that move (expectations, not deletions):
- `fri_params_soundness_budget.rs` `:452`, `:959-993` (ledger expectations via the export).
- `recursion_vk_determinism.rs` — determinism harness unchanged (it pins no absolute fingerprint,
  `:87-150`); the out-of-band anchors are the real re-pin (§4.3).
- `rotation_batchstark_leaf_smoke.rs` — ALREADY RED at HEAD on stale geometry pins
  (GRAD_ROT_WIDTH/46-PI vs the committed 1702-wide/50-PI member; probe commit message) — repoint
  in the same lane.
- `e2_fold_arity_recompose_probe.rs` — becomes the standing regression gate; its arity-2
  comparison arm inverts into the "old engine still mintable" check or retires.
- `ivc_turn_chain_rotated*.rs`, `descriptor_leaf_recursion.rs`, `gpu_recursion_fold_e2e.rs`,
  binding/tooth tests listing `ir2_leaf_wrap_config` [P: 18 test files reference it].

### 4.2 Staging (the backlog recipe `:173-190`, refined by this design)

Inside the Epoch-2 bundled cutover window, step 2 (after the chip retype, before E4):

1. D1 knob flip + doc retirements. Whole-tree build + the full gate list.
2. D2 leg extraction + D4 retention bump (fail-closed on v1 blobs). The anchor tie stays.
3. D3 type collapse (one mechanical commit; adapters + tests).
4. Posture re-pin commit: budget-gate expectations + `VK-REGEN-LOG.md` entry + lightclient anchor
   re-distribution (§4.3). State the 112→109 spend and its ledger citation in the commit message.
5. (Bundled, separate lane) apex/ETH re-land with lever B; gnark `fold_row` only if OUTER
   escalates.
6. E4 riders if taken: re-grid flip + (k3,b8) discharge + floor re-pin.

### 4.3 Epoch accounting

**One recursion-side FS/VK epoch, no descriptor-side VK regen from E2 itself.** E2 touches no
descriptor bytes and no member VK (`ir2_config` unchanged) — what changes is the recursion
circuit shape at every layer, hence: (a) proofs across the flip are not interchangeable —
pre-flip retained `FinalizedTurn` blobs are arity-2; refuse them via the v2 envelope bump rather
than deciding mixed-arity fold semantics [the alternative — accepting mixed schedules — is
technically plausible since the verifier reads the schedule from the proof, but it makes the root
fingerprint depend on the leg mix and is rejected here]; (b) the root VK fingerprint — the light
client's distributed trust anchor (`lightclient/src/lib.rs:175-195`; anchor-model property
`:1313-1337`) — rotates, so every distributed anchor re-issues at the flag day; wasm bindings
(`wasm/src/bindings_lightclient.rs`, `bindings_multiway_tug.rs`) and `grain-verify/src/r3.rs`
ride the same re-pin. It rides the bundled Epoch-2 window (its step-2 slot) — it does NOT need
its own epoch, and E4 rides ITS epoch in turn.

### 4.4 Canary / falsifier set (the teeth that prove the surviving path binds everything)

- **C1 (exists, becomes gate):** `e2_fold_arity_recompose_probe` — honest arity-8 wrap +
  aggregation, non-vacuity teeth (schedule contains log_arity ≥ 2; all queries one schedule;
  fewer phases than arity-2 of the same trace).
- **C2 (new, THE soundness canary for O2):** adversarial in-circuit rejection at arity 8. Take an
  honest arity-8 leaf, corrupt in turn: one commit-phase sibling in a log_arity=3 phase; the
  claimed folded eval; a `log_arity` byte in the schedule (2↔3); a final-poly coefficient — and
  assert the WRAP (not just native verify) rejects each. No such test exists at HEAD [P: no
  corrupt/tamper test touches `commit_phase_openings` outside the probe]. This is the direct
  probe of the previously-dead reconstruct arms.
- **C3 (new):** anchor-tie retarget canary — a retained-blob/served-proof anchor mismatch (wrong
  turn's proof under this turn's key) still refuses, post-deletion.
- **C4 (new):** cross-epoch replay — a v1 retained blob (arity-2) presented to the post-flip fold
  is REFUSED at decode (envelope version), and a pre-flip root fails the post-flip lightclient
  anchor.
- **C5 (new, [P]→[M] promotion):** apex shrink over an arity-8 apex — the one layer the probe did
  not exercise — plus the outer-trace-shape measurement feeding the gnark stability question.
- **C6 (exists):** `recursion_vk_determinism` (in-process + cross-process fingerprint equality at
  the new shape); `fri_params_soundness_budget` (re-pinned expectations, including the
  arity-drift recovery tooth `:959-993` which keeps the 2016/112 arity-2 row as the
  counterfactual); `ivc_turn_chain_rotated*` chain tests; the full binding/tooth suite.

## §5 The falsifier, stated

**If the double-prove is deleted and the surviving in-circuit check does NOT cover the gap, the
adversary gains a history-forgery primitive against every constant-cost verifier.** Concretely:
the parties that verify a folded chain WITHOUT re-running native verification on each leg are the
light client (`verify_history`'s three teeth: anchor fingerprint, root in-circuit verify, segment
— `lightclient/src/lib.rs:37-58`) and anything downstream of the apex/ETH wrap. Host admission
(`verify_descriptor_participant`) protects only an HONEST fold operator; a malicious compressor
skips it. So post-deletion, the in-circuit arity-8 recompose arms are the ONLY thing standing
between a corrupted leg and an accepted root.

The concrete forgery the deletion must be proven to prevent: an adversary crafts a "wrapped leg"
whose inner `Ir2BatchProof` does NOT verify — e.g. a transfer whose `wide_new_root8` anchors a
state where their balance grew with no matching debit constraint satisfied — by exploiting an
under-constrained arity-8 arm (a one-hot coset selector not forced to one-hot, a reconstructed
eval not bound to the Merkle-opened siblings, a schedule byte the circuit trusts but does not
constrain against the transcript). They fold it into a chain whose other legs are honest, present
the root to `verify_history`: the VK fingerprint MATCHES (the anchor fingerprints the honest —
buggy — circuit shape), the root self-verifies, the segment reads the forged `new_root`. Result: a
fabricated state transition accepted at constant cost by every light client, and — through the
apex → outer → gnark path — potentially by the on-chain verifier.

Honest calibration of this falsifier: the same class of surface exists TODAY at arity 2 (the wrap
is already load-bearing for folds; the arity-2 arms are equally unverified Rust). What the
deletion changes is (a) the load moves onto arms that have never been load-bearing or
adversarially exercised on any dregg proof, and (b) the belt-and-suspenders native re-prove+verify
pair on the mint side disappears, so the fold input is whatever the retention store serves rather
than something the node just proved to itself. C2/C3/C4 are the teeth this design requires
landed IN THE SAME COMMIT as the deletion — the deletion without C2 is not a lane this document
endorses.

Secondary falsifier (quantified, accepted): the 3-bit perFold spend (O1/O3). An adversary
attacking FRI folding directly gets error < 2^-109 per fold instead of < 2^-112, under the
ledger's stated model and its standing caveats. This is priced, Lean-proven, and inside the
109-bit floor the budget gate already enforces; it is a decision, not a gap.

## §6 Effort, calibrated

Backlog unit: S2 deletion = 1 heavy lane; narrow-bus campaign = 6.

- **E2-alone (D1–D4 + posture re-pin + C1–C4/C6):** 1 heavy lane dregg-side (the S2-class
  deletion+flip with its canaries), + 0.5 lane for the type collapse mechanicals across the 15
  adapters/tests. Matches the backlog's "1–2 lanes dregg-side".
- **Apex/ETH re-land (C5, lever-B bundle, gnark fold_row iff OUTER escalates):** 1 lane, gnark
  being the long pole.
- **E4 riders if taken in the same epoch:** +1 lane incl. the (k3,b8) Lean discharge instance.
- Total for the narrow E2 campaign: 2–3 lanes; with E4: ~4.

## §7 Open unknowns (each is one bounded check inside the lane, none blocks GO)

1. Served-leg PI completeness: does the rotated `AttachedSubProof` carry the full descriptor PI
   vector verbatim (§2.1 D2)? If not: bare-leg retention at prove time (mechanical).
2. Outer-shrink trace-shape stability at arity-8 apex (§3.3) — decides whether the gnark circuit
   is byte-stable or the ETH wrap re-land is shape-changing.
3. The at-height (~18→~6 rounds) confirmation of the ~3.8× term — the cutover lane's first
   measurement (HORIZONLOG assigns it there); fixture-height halving is already [M].
4. Whether plonky3 native verify enforces schedule ≤ config max or schedule ≡ derived — decides
   if the v1-blob refusal (D4) is defense-in-depth or the only wall against mixed-arity folds.
   The design assumes only defense-in-depth and refuses at the envelope regardless.
5. Joint-turn lanes (E9/E12) land order — their files carry mint sites that ride this flip;
   sequence after, or coordinate the one-knob rebase.
