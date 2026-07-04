# Composition-Soundness Census — the adversary attacks the SEAMS

**Frame.** The per-effect forces are done (every effect's stamp/root/epoch is deployed-FORCED at
its own descriptor rung). This census attacks the next frontier: does light-client unfoolability
hold of **turns** and **turn-sequences**, not just individual effects? The adversary no longer
attacks an effect — it attacks the *seam between* effects (intra-turn) and the *seam between* turns
(inter-turn / forest). A composition forgery is a turn / turn-sequence that `verifyBatch` ACCEPTS but
that is **not** a genuine kernel evolution.

**Discipline applied.** Every claim below is checked against source, both directions: I did not cry
forgery from a label, and I did not trust "composes fine" without finding the binding. Where a seam
holds, the file:line of the forcing lemma is given; where it is a carried obligation, that is said
plainly; where a forgery is reachable, the concrete witness is given.

---

## Headline

1. **The live whole-turn apex genuinely quantifies over MULTI-EFFECT turns.**
   `CircuitSoundness.lightclient_turn_unfoolable_forest` (`CircuitSoundness.lean:836`) takes a
   `TurnDecodeChain` of *arbitrary length* and concludes `execFullTurnA start acts = some fin` for a
   *list* `acts`. The whole-turn capstone `lightclient_turn_unfoolable_forest_assembled`
   (`CircuitSoundnessAssembled.lean:463`) instantiates it at the live registry `Rfix`. So the
   denominator IS multi-effect turns, not atoms. **This is real, not assumed.**

2. **The intra-turn kernel seam is FORCED, not free.** The dangerous-looking move — `TurnDecodeChain`
   carries a prover-supplied `seam : IsChain (a.post = b.pre)` — is disarmed: the *kernel half* of
   that seam is DERIVED from the commitment binding (`turnDecodeChain_seam_kernel_derived`,
   `CircuitSoundness.lean:593`, via `stateDecodeChain_frame_continuous` →
   `CommitSurface.commit_binds`). A prover whose intermediate kernel commitment disagrees across the
   seam is rejected. **No intra-turn kernel-splice forgery.** (Witness of the binding below, seam #1.)

3. **The genuinely-uncovered residual is the LOG (receipt-chain) half of the intra-turn seam** — the
   commitment surface commits only `RecChainedState.kernel`, so the `log` continuity of `a.post = b.pre`
   is a NAMED carried field, not a forced one (`CircuitSoundness.lean:551–563`). This is honest and
   named, but it IS the one intra-turn seam an adversary is not blocked from by the apex. **Rank-1 to
   force next** (close shape: bind a log-root limb into the commitment surface; small).

4. **The turn-sequence (inter-turn) binding lives OUTSIDE the apex** and is a separate compose
   (`CrossTurnFreshness` + `SettlementSoundness`), with two **named, deferred plumbing residuals**
   (R1/R2 in `CrossTurnFreshness.lean:353–391`) that connect the abstract `TurnChain` to the deployed
   `runTurn` sequence. The no-replay core is proven; the wiring to the live executor sequence is the
   gap. **Rank-2.**

5. **The Universe-A turn chain (`TurnEmit.TurnEmittedChain`) has NO commitment-bound seam at all** —
   its `chain` is entirely prover-supplied and `stepEmittedSat` checks only tag + `satisfiedEmitted`
   on bytes (`TurnEmit.lean:175–235`). **BUT it is not the live apex**, and its soundness theorem
   explicitly carries the per-step refinement as a hypothesis `hstep` and is flagged "NOT whole-turn
   adversarial soundness" / "honest-trace only" in its own docstring (`TurnEmit.lean:217–235,
   378–389`). It is a parametric scaffold, not a load-bearing unfoolability claim. **Not a live
   forgery; a labeling hazard if ever cited as the apex.** Rank-3 (documentation/wiring discipline).

6. **The cross-cell forest's overlapping-cell case is explicitly OPEN and fail-closed** — a
   same-cell duplicate forest is REJECTED by the `distinctCells` NoDup gate (verified live,
   `CrossCellForest.lean:503–522`). The copy-laundering forgery (codex P2) is CLOSED. The genuine
   open is contended/overlapping mutable cells across nodes — named `-- OPEN:`, not a silent hole.
   **Not a reachable forgery in the committed construction; a named research frontier.** Rank-4.

---

## Prioritized seam table

| # | Seam | Verdict | Witness / proof (file:line) | Danger |
|---|------|---------|------------------------------|--------|
| 1 | Intra-turn KERNEL seam (effect B sees A's post) | **HANDLED — forced** | `turnDecodeChain_seam_kernel_derived` `CircuitSoundness.lean:593`; `stateDecodeChain_frame_continuous` `:279`; `commit_binds` `:288` | low |
| 2 | Intra-turn accumulator (two noteSpend / two mint in one turn) | **HANDLED — definitionally threaded** | `turnSpec` `ActionDispatch.lean:243–246` (`fullActionStep st a st1 ∧ turnSpec st1 rest st'`); per-step kernel forced by seam #1 | low |
| 3 | Intra-turn LOG (receipt-chain) seam | **REAL residual (named, carried)** | `TurnDecodeChain.seam` log-half `CircuitSoundness.lean:551–563, 582–584` | **MED — rank 1** |
| 4 | `pubSeam` published-root authenticity | **HANDLED w/ caveat** | `c.sat` ties trace→`d.pc` `:575–577`; decode ties `d.pc`→kernel `:190–192`; `pubSeam` only needs to derive kernel chain | low |
| 5 | Turn-sequence no-replay (cross-turn) | **CORE proven; wiring deferred** | `no_replay` `CrossTurnFreshness.lean:162`; `deployed_no_replay` `:295`; residuals R1/R2 `:353–391` | **MED — rank 2** |
| 6 | Cross-turn authority-laundering (revoke-after-branch) | **HANDLED — settlement-tip** | `SettlementSoundness.lean` compose (3 legs); revoked bound by `recStateCommit_binds_kernel` | low |
| 7 | Universe-A `TurnEmittedChain` unbound seam | **NOT live apex; honest-trace scaffold** | `TurnEmit.lean:175–235`; self-flagged `:217–235, 378–389` | low (labeling) |
| 8 | Joint / forest adversarial scheduler (cross-cell Σ=0) | **HANDLED — binding carried + NoDup** | `crossForest_conserves` `CrossCellForest.lean:295`; `distinctCells` reject `:503–522`; `JointTurn.joint_sound` binding-premise | low |
| 9 | Overlapping/contended cross-cell forest | **OPEN — fail-closed, named** | `-- OPEN:` `CrossCellForest.lean:573–579`; dup REJECTED `:517,522` | low (named frontier) |
| 10 | Same-`turn`-index across all intra-turn steps (no per-step turn bump) | **needs audit — see below** | `pubSeam` only forces *adjacent* `turn`-equality `:586` | **LOW-MED** |

---

## Per-seam detail with witnesses

### Seam #1 — Intra-turn kernel seam: HANDLED (forced by commitment binding)

The fold `turnDecodeChain_refines_turnSpec` (`CircuitSoundness.lean:633`) walks a prover-supplied
`chain`/`seam`. The naive forgery would be: supply a `seam` where `a.post.kernel ≠ b.pre.kernel` so
that effect B runs against a forged intermediate the circuit never produced. **Blocked.** The kernel
half is a theorem, not a field:

```
turnDecodeChain_seam_kernel_derived :  IsChain (fun a b => a.post.kernel = b.pre.kernel) c.steps
  ← stateDecodeChain_frame_continuous (a.pc.pubPost = b.pc.pubPre at equal turn ⟹ a.post.kernel = b.pre.kernel)
    ← StateDecode.postBinds / preBinds (pc binds S.commit kernel)
    ← CommitSurface.commit_binds (injective)
```

The `pubSeam` field (`:586`) supplies `a.pc.pubPost = b.pc.pubPre`; the per-step decode + injective
commit then *force* `a.post.kernel = b.pre.kernel`. A forged intermediate kernel commitment cannot
satisfy both `c.sat` (trace→pc) and `pubSeam` (pc-chain) without colliding `commit`. **No forgery.**

### Seam #2 — Intra-turn accumulator (double noteSpend / double mint): HANDLED

`turnSpec st (a::rest) st' := ∃ st1, fullActionStep st a st1 ∧ turnSpec st1 rest st'`
(`ActionDispatch.lean:243–246`). The post of step `a` IS the pre of `rest` **definitionally**. So a
second noteSpend in the same turn runs against `st1`, whose nullifier set already contains the first
spend's nullifier; `fullActionStep`'s noteSpend grow-gate (per-effect, already proven) rejects a
double-spend. The accumulator is threaded by the *recursive structure* of `turnSpec`, and each `st1`
kernel is pinned by seam #1. **No accumulator double-count forgery** — the two-spend-in-one-turn case
is exactly the sequential `fullActionStep ∘ fullActionStep` the executor runs, with intermediate
kernel forced. (Note: this rests on `fullActionStep`'s own per-effect gate being sound, which is the
per-effect frontier, not a composition concern.)

### Seam #3 — Intra-turn LOG seam: REAL RESIDUAL (rank 1)

`recStateCommit` commits only `RecordKernelState` (`CircuitSoundness.lean:555–556`). So the
full-state seam `a.post = b.pre` decomposes into:
  - **kernel half** — forced (seam #1);
  - **log half** (`a.post.log = b.pre.log`, the receipt/observation chain) — **a prover-supplied
    field, NOT forced by any commitment.**

The docstring is honest about this (`:551–563`): "the log-continuity of the seam is the genuine
residue the commitments cannot certify. It is carried EXPLICITLY as a chain field." A malicious
prover could thread a discontinuous `log` between two steps while keeping kernels continuous, and the
apex would still conclude `execFullTurnA ... = some fin` — because `turnSpec`/`fullActionStep`
themselves DO thread the log, but the light client's *commitment* doesn't bind it, so two different
log-threadings decode to the same commitments. **This is the one intra-turn seam an adversary is not
provably blocked from.**

- **Is it a forgery of the headline?** Subtly: the apex concludes a genuine `execFullTurnA` run
  EXISTS with matching *kernel* endpoint commitments. It does NOT claim the *receipt chain* the
  prover published is the genuine one. So unfoolability "this is a real kernel evolution" holds; "the
  receipts are the genuine receipts" does not.
- **Closure shape & size:** add a `log`-root limb to `CommitSurface` (a Poseidon2 fold of the
  receipt chain), bind it in `RestHashIffFrame`, and re-derive the log half of the seam exactly as
  the kernel half is derived. **Small** (mirrors an existing pattern; one new limb + one `commit_binds`
  extension). This is the concrete next force.

### Seam #4 — `pubSeam` published-root authenticity: HANDLED with caveat

Could a prover publish a `pubSeam` that *agrees* but whose commitments aren't the real circuit roots?
No: `c.sat` (`:575`) requires, for every step, a `Satisfied2` circuit witness `t` with
`tracePublishedCommit t = d.pc`. So `d.pc` IS the circuit's emitted commitment, and `d.decode` ties
`d.pc` to `d.pre/d.post`. The `pubSeam` field then only restates an equality that is already pinned
to two real circuit roots. The prover cannot publish a `pc` not produced by a satisfying trace.
**Caveat:** this rests on `Satisfied2` + `tracePublishedCommit` being the genuine deployed PI surface
(the `StarkSound`/`WitnessDecodes` floors) — those are the named crypto carriers, not a composition
gap.

### Seam #5 — Turn-sequence no-replay: CORE PROVEN, wiring deferred (rank 2)

`CrossTurnFreshness` proves the genuinely-hard fact axiom-clean: the commitment cannot hide a stale
nonce (`commit_inj_nonce`, `:60`), so a monotone-nonce chain's commitment NEVER repeats
(`commit_no_repeat`, `:128`), hence a `(pre,post)` proof opens the CAS gate at most once
(`no_replay`, `:162`; `deployed_no_replay`, `:295`). Non-vacuity has teeth
(`witnessChain_replay_rejected`, `:345`).

**The two named residuals** (`:353–391`) are the composition gap to the live sequence:
  - **R1** — identify the abstract `TurnChain.seq i` with the kernel after the *i*-th ACCEPTED
    `runTurn` (the live stored-commitment register). Called "mechanical composition, deferred as
    plumbing."
  - **R2** — prove the *net* agent nonce strictly increases across the WHOLE `runTurn` (prologue +
    body), not just the prologue. Partly discharged: `runTurn_strictly_advances_agentNonce` (`:244`)
    proves it GIVEN `BodyNonceNondecreasing` (`:221`), which is *asserted* true of the executor body
    (the two nonce-reset vectors closed) but whose discharge for the full forest-fold executor is the
    named residual.

- **Reachable forgery?** Not at the proven core. The risk is in the *unproven plumbing*: if R2's
  `BodyNonceNondecreasing` is false for some live effect (a body path that writes the agent nonce
  downward), then a turn-sequence could re-open the CAS gate → **replay forgery across turns**.
  **VERIFIED at the executor (not trusted from the comment):** the two nonce-write vectors ARE
  genuinely closed —
  - `reservedField` includes `"nonce"` (`EffectsState.lean:313–314`) and `stateStep` rejects any
    write to a reserved field (`:323`), so `setFieldA "nonce"` is fail-closed;
  - `incrementNonceStep` gates the write on `fieldOf "nonce" (cell target) < n` (`:381–384`), so it
    can only RAISE the nonce (`incrementNonceStep_advances`, `:399`).

  So the building blocks of `BodyNonceNondecreasing` are real. The genuine remaining gap is the
  *whole-executor* lemma (every effect leaves the agent's nonce slot fixed or raised, over the full
  forest-fold body) — the per-effect non-interference is assembled but not yet a single discharged
  lemma. **No reachable downward-nonce write found; the residual is the assembly, not a hole.**
- **Closure shape & size:** discharge `BodyNonceNondecreasing` as a real lemma over the forest-fold
  executor body (audit every effect's effect on the agent's `nonce` slot), then wire
  `acceptedSeq_to_TurnChain` (`:282`) to the `runTurn` sequence. **Medium** (one executor-wide lemma +
  the plumbing instantiation).

### Seam #6 — Cross-turn authority-laundering (revoke-after-branch): HANDLED

`SettlementSoundness` composes the apex (genuine transition) with the commitment binding of
`post.kernel.revoked` (`recStateCommit_binds_kernel`) and topology-bounded revocation, so authority
is evaluated AT the finalized settlement tip, not at branch time. The branch-vs-settlement gap is the
topology delay window, witnessed by a tooth. **Named residual** is a Rust wire-conformance question
(does the deployed rest-hash absorb the revocation channel root) — a per-effect descriptor
conformance, carried as the `RestHashIffFrame` floor, NOT a Lean composition gap.

### Seam #7 — Universe-A `TurnEmittedChain`: not the live apex (labeling hazard)

`TurnEmit.TurnEmittedChain` (`:175`) is a SECOND turn-chain abstraction with **no commitment-bound
seam**: its `chain : List RecChainedState` is a prover-supplied field, `chain_head/chain_last` pin
endpoints, and `step_sat` binds each link only via `stepEmittedSat` = (tag matches) ∧ (descriptor
`satisfiedEmitted` on the step's bytes). Nothing forces `chain[i]` to be the circuit's actual
intermediate state — there is no PI binding between adjacent links. **An adversary could supply any
`chain` whose per-step bytes satisfy the descriptors** and the soundness theorem
`turn_emitted_refines_exec` (`:225`) would conclude `execFullTurnA`.

**Why this is not a live forgery:**
  - `turn_emitted_refines_exec` carries the per-step refinement `hstep` as a *hypothesis* — it does
    not itself extract the step from a circuit witness.
  - Its docstring explicitly says (`:217–235`): "Do not read this as whole-turn adversarial soundness
    of the executor bridge" and "honest-encoded-trace soundness, NOT adversarial-trace soundness."
  - `step_emitted_refines_fullActionStep` (`:390`) carries a **dead `hEnc`** and is flagged "NOT
    whole-turn adversarial soundness" / "honest-trace only" (`:378–389`).
  - The genuine adversarial extraction is done separately and correctly via `mintA_extract` /
    `effect2_step_extracts_circuit` (`:631, 685`) — the PI-bound extractor with no dead hypothesis.

**Verdict:** a parametric scaffold, honestly labeled. **The hazard is purely one of citation** — if
any downstream ever cites `turn_emitted_refines_exec` AS the unfoolability apex it would be an
overclaim. The live apex is `lightclient_turn_unfoolable_forest` (seam #1), which has the bound seam.
**Rank 3 (discipline): keep the Universe-A chain out of any unfoolability headline.**

### Seam #8 — Joint / forest adversarial scheduler: HANDLED (binding carried + NoDup)

`CrossCellForest` flattens the tree to a `Fin n` family and rides `ForestLTS`'s Σ=0 telescoping.
Cross-cell conservation is the explicit Σ=0 binding hypothesis (`crossForest_conserves`, `:295`),
proven load-bearing (`crossForest_needs_binding`, `:374`). The Granovetter no-amplify law holds over
the whole tree (`crossForest_no_amplify`, `:271`). `JointTurn.joint_sound` (`JointTurn.lean:186`)
carries `JointBinding` as a premise, proven irreducible (`binding_is_proper`, `:271`). **An
adversarial scheduler cannot produce an accepted joint/forest turn that no sequential execution
could**, because the family transition is atomic (all-or-nothing `forestApply`) and the binding
carves the admissible subobject.

### Seam #9 — Overlapping/contended cross-cell forest: OPEN, fail-closed (named)

The one cross-cell composition not covered: a child running on a cell ALSO touched by an ancestor.
The `CrossCellForest` lift **rejects** this — the `distinctCells` NoDup gate (`:196`) fails-closed on
duplicate cells, verified live (`dupCellCrossForest` → `execCrossForest ... = none`, `:510–522`).
This CLOSES the copy-laundering forgery (codex P2: two nodes on cell A summing to a phantom net-0).
The genuine contended-mutable-family case is named `-- OPEN:` (`:573–579`) as the next research pole,
NOT a silent hole. **Not a reachable forgery in the committed construction.**

### Seam #10 — Same-`turn`-index across intra-turn steps: NEEDS AUDIT (low-med)

`pubSeam` (`:586`) forces only **adjacent** `a.pc.turn = b.pc.turn` across the chain, which
transitively makes all steps in a turn share one `turn` index — correct (all effects of a turn commit
at the same turn). The cross-turn nonce-monotone (seam #5) keys off the turn-author's agent nonce
across DISTINCT turn indices, so the intra-turn shared index is consistent. **No issue found**, but
the interaction (intra-turn steps all at turn `t`, the nonce bump happening once per turn via the
prologue) is the seam where seam #3's log residual and seam #5's nonce residual MEET: the agent-nonce
bump is a kernel-prologue effect; whether it is bound into the per-step intra-turn commitment chain
(vs only the turn-boundary commitment) is worth a direct check when closing seam #3/#5 together.
Logged as a watch-item, not a forgery.

---

## What the apex's `∀` actually covers (the denominator)

`lightclient_turn_unfoolable_forest` (`CircuitSoundness.lean:836`) and its assembled form
(`CircuitSoundnessAssembled.lean:463`) quantify over:

- **a `TurnDecodeChain` of arbitrary length** (multi-effect turns: YES);
- **with the per-step effect index identified** (`hidx`) and the per-effect family `hrefines`
  discharged (the enumerated `EffectDecodeBridge` family — itself a named carried residual,
  `CircuitSoundnessAssembled.lean:404`);
- **endpoint commitments forced** (`TurnEndpoints` → `turnDecodeChain_endpoints_commit`, `:782`).

It does NOT directly quantify over turn-SEQUENCES — that is a separate compose (`CrossTurnFreshness` /
`SettlementSoundness`), correct in structure with the two named plumbing residuals (R1/R2). And the
intra-turn coverage is **kernel-complete but log-incomplete** (seam #3).

**So:** the apex's unfoolability genuinely covers multi-effect turns at the KERNEL level
(intermediate kernels forced, accumulators threaded, joint/forest binding carried). It does NOT yet
cover: (a) the receipt-LOG continuity within a turn (seam #3, carried), (b) the turn-sequence binding
to the live executor (seam #5, R1/R2 deferred). Those two are the real composition residuals to force
next, in that priority order.

---

## Ranked closure list (the real ones to force)

1. **Seam #3 — bind the receipt-LOG root into `CommitSurface`** so the intra-turn log seam is forced
   like the kernel seam. Small; mirrors the kernel-half derivation.
2. **Seam #5 R2 — discharge `BodyNonceNondecreasing` over the live forest-fold executor body**
   (verify, do not trust, the reserved-field + monotone-nonce gates), then R1-wire
   `acceptedSeq_to_TurnChain` to the `runTurn` sequence. Medium; this is where a real cross-turn
   replay could hide if a body path writes the nonce downward.
3. **Seam #7 — discipline: never cite the Universe-A `turn_emitted_refines_exec` as the unfoolability
   apex.** Documentation/wiring only.
4. **Seam #9 — the contended/overlapping cross-cell forest** remains a named research frontier
   (fail-closed today). Not urgent; not a reachable forgery in the committed construction.

**No concrete, reachable composition forgery of the LIVE apex was found at the kernel level.** The
prize the adversary can still reach is the **intra-turn receipt-log seam (#3)** and the **unverified
executor-body nonce-monotonicity behind the cross-turn replay defense (#5 R2)** — both named, both
small-to-medium to close.
