# VISION — Proof-by-Construction Machinery for Deployed Game/Policy Correctness

**Status:** vision + campaign design, 2026-07-19. Read-only probe; no code, no commits.
**Angle:** make "the deployed program is proven-correct-to-reality" *fall out of authoring
the game in Lean + emitting it* — a **reusable proof architecture**, not a bespoke effort
re-derived per game.

**The through-line the record already established:** a turn is the exercise of an
attenuable proof-carrying token over owned state, leaving a receipt. The correctness of
*which turns the referee admits* is the load-bearing claim. Today we can prove it — but
only one game at a time, by hand, against a reality-gated evaluator. This document designs
the machinery that makes it **generic**.

---

## 0. Where we actually stand (the ground truth this vision builds on)

Two things are now REAL, and everything below leverages them:

1. **One reality-gated evaluator, exported, that the deployed node routes through.**
   `Dregg2.Exec.DeployedConstraint.admits` (`metatheory/Dregg2/Exec/DeployedConstraint.lean:210`)
   is the single Lean source for the deployed constraint evaluator's **pure** (context-free,
   witness-free) subset, authored over the **deployed substrate** (`[FieldElement;16]` + heap,
   unsigned-256 field compares — both audited divergences reconciled to the sound deployed
   semantics, `DeployedConstraint.lean:129-133,203-209`). It is `@[export dregg_constraint_admits]`-ed
   (`:413`), and `cell/src/program/eval.rs::evaluate_constraint_full` routes the pure subset through
   it via the `ConstraintOracle` runtime seam (`cell/src/program/eval.rs:280`,
   `cell/src/program/oracle.rs:32,48`, `exec-lean/src/constraint_oracle.rs:166-193`). The reality-gate
   canary (`exec-lean/tests/constraint_oracle_reality_gate.rs:39`) flips red if the Lean source
   changes — proving `eval.rs`'s decision is COMPUTED BY the Lean object.

2. **Two games proven against it — by hand, two different ways.**
   - **Tug** (`MultiwayTugProgram.lean`): authors `multiwayTugProgram` (`:237`), an abstraction
     `α : GState → Counters` (`abstract`, `:493`), a marshal into the deployed substrate
     (`tugRegIdx :789`, `tugSlots :798`, `mkDInput :885`), and a **forward refinement** landed on
     the deployed evaluator: `program_admits_legal_play_deployed` (`:941`) — *legal ⇒ the exported
     evaluator admits*, for every action-case tooth.
   - **Dungeon** (`DungeonProgram.lean`): authors `dungeonProgram` (`:356`), lifts it into
     `Dregg2.Exec.RecordProgram` (`toExec`, `:391/411/414`), and proves **reverse inversions** over
     arbitrary attacker records — `admitted_verb_conserves :473`, `admitted_verb_capacity :483`,
     `admitted_verb_pays :510`, `admitted_verb_alive :527`, `way_flip_exhibits_key :588`,
     `unknown_method_refused :668` — plus a **driven weld** (`programAdmitsRun crownedRun`, `:719/751`)
     for the forward direction on one run.

**The problem this vision exists to solve:** those two proofs share a deep skeleton, but that
skeleton was **hand-rebuilt both times, differently**, and each copy had to be *separately audited*
(`docs/audit/GAME-PROOF-LARP-AUDIT.md`) — the audit even caught tug's `immutable` heap-atom copy
having silently **diverged** from the deployed one before the reality-gate collapsed them. Four
parallel copies of "the constraint vocabulary" exist right now — tug's (`MultiwayTugProgram.lean:104`),
dungeon's (`DungeonProgram.lean:148`), `DeployedConstraint`'s (`:80`), and `Exec.Program`'s
`StateConstraint` (`metatheory/Dregg2/Exec/Program.lean:269`). **That does not scale to N games.**
`SEMANTIC-LEAN-BOUNDARY.md:131-148` counts ~10 deployed policy families; **4** have any Lean spec,
**0** reach the deployed program by machine-checked refinement, and ~6 (faction, quest, spween,
the dungeon-on-dregg content crates) have **no Lean at any resolution**.

---

## 1. THE AMBITIOUS END-STATE — refinement as a functor, correctness by construction

**A game/policy author writes three things — a Lean spec (`S`, `step`, `legal`), a program value
in ONE shared authored vocabulary, and an abstraction `α : S → DeployedState`. A GENERIC framework
then yields, with no bespoke refinement work: (a) the emitted deployed artifact, and (b) a
machine-checked theorem that the deployed program's admission — *on the reality-gated evaluator Rust
actually runs* — refines the spec.** The only per-game proof work is discharging a small, fixed,
named set of obligations that carry the game's genuine mathematical content.

Concretely, three layers:

### 1a. `ProvenPolicy` — the refinement structure (a Lean structure/typeclass over programs)

A single structure the author instantiates. Its fields are exactly the irreducible inputs:

- **the model** — `S : Type`, `step : S → M → Option S`, `legal : S → M → Prop` (already exists per
  game: `MultiwayTug.applyLegal`, `Dungeon.step`);
- **the program** — a value `prog : CellProgram` in the ONE authored vocabulary (§2, Cycle A);
- **the abstraction** — `α : S → DeployedState` into the substrate `DeployedConstraint.admits` reads
  (today: tug's `abstract`+`tugSlots`, dungeon's `encode`);
- **the obligation payload** — one field per *tooth-kind the program uses*, in each *direction the
  author claims*: a proof that the tooth's semantic condition is discharged by the model on a legal
  step (forward) and/or entails the game law when admitted (reverse). Nothing else.

The structure is *the* place the game-specific facts live, and it is small: it holds the invariants
and the marshal, not the plumbing.

### 1b. The generic soundness theorems (proven ONCE, parameterized by the spec)

Two theorems, stated once over `DeployedConstraint.admits`, instantiated free per game:

- **`deployed_refines_forward` — completeness.** For any `ProvenPolicy`, every legal `step` is
  admitted by the deployed evaluator on the `α`-image:
  `legal s m → deployedAdmits prog (methodOf m) (α s) (α (step s m)) = ok`.
  This is exactly tug's `program_admits_legal_play_deployed` (`:941`) — but proven **once, for all
  policies**, from the obligation payload, instead of re-derived. The scaffolding it currently
  carries (case selection, tooth iteration, the `List.all_append` gymnastics of `commonAndAction_admits`
  `:618`, the marshal-agreement) is all generic.
- **`deployed_refines_sound` — soundness.** For any `ProvenPolicy`, an admitted transition satisfies
  every tooth's semantic condition, hence (via the reverse obligations) the game law:
  `deployedAdmits prog m o n = ok → GameLaw o n`. This is exactly dungeon's inversion family
  (`admitted_verb_* :473-668`) — but proven **once**, with `admits_cases_mem` (`DungeonProgram.lean:425`,
  itself a re-proof of the generic `Exec.RecordProgram.admits` shape at `Program.lean:659-666`)
  provided by the framework, not by each game.

The framework is, precisely, a **forward/backward simulation combinator over the one deployed
evaluator**: `α` is a simulation relation; the theorem says the deployed arrow (`admits`) simulates
the model arrow (`step`) whenever the per-tooth obligations hold. That is the reusable core — and it
is a *theorem about the exported object Rust runs*, so instantiating it is what "correct-to-reality"
means.

### 1c. Proof-generating emit (the frontier form)

The most ambitious shape: the emit path is itself a proven Lean function
`emit : CellProgram → Artifact` whose companion `emit_faithful` theorem guarantees the loaded artifact
denotes the same `prog` the refinement theorem is about — so "the bytes Rust loads" and "the object we
proved about" are one, by construction, not by a drift gate. Further still: an `emitWithProof` that
**emits the refinement certificate alongside the bytes**, so a new game ships its own machine-checked
receipt. The tractable near-term is the parameterized generic theorem (1b) + a proven single emitter
(1c-faithful); the certificate-emitting form is the labeled horizon.

---

## 2. THE PATTERN GENERALIZED — extracting the reusable core from the two bespoke proofs

Lay tug's forward-refinement and dungeon's inversions side by side and the shared skeleton is
unmistakable. Five reusable pieces, each currently **duplicated and hand-built per game**:

| Reusable piece | Tug (today) | Dungeon (today) | Becomes (framework) |
|---|---|---|---|
| **The authored vocabulary** | own `Constraint`/`HeapAtom`/`SimpleConstraint`/`CellProgram` (`MultiwayTugProgram.lean:104`) + own `emitJson` (`:287`) | own `Constraint`/`Guard`/`Case`/`CellProgram` (`DungeonProgram.lean:148`) + own `emitJson` (`:882`) | **ONE** shared `CellProgram` type + **ONE** `emit`, imported |
| **The marshal** (game substrate → deployed) | `tugRegIdx`/`tugSlots`/`mkDInput`/`Constraint.toDC` (`:789-901`) | `encode` (`:689`) + `toExec` (`:391-414`) | a **slot-allocation instance** (~15 lines) over a proven marshal discipline |
| **Tooth ⇔ `DeployedConstraint.admits` agreement** | `heapAdmits_writeOnce_ok :817`, `heapAdmits_monotonic_ok :831`, `sumGo_ok :856`, `sumEquals_conservation_deployed :906` | (over signed-`Int` `Exec`, not yet reaching `DeployedConstraint` — `:82-97`) | a **game-independent discharger/inverter library**, proven ONCE per tooth-kind |
| **The abstraction bridge** `α` + read lemmas | `abstract :493`, `absReg :462`, `absHeap_flag/score :510/515` (all `rfl`/finite) | `encode :689` | author supplies `α`; the read lemmas are mechanical (`rfl`) — framework-generated boilerplate |
| **Case/tooth admission plumbing** | `admitsMethod_action :600` (case filter reduces to the matching arm's teeth) | `admits_cases_mem :425`, `verb_core_teeth :444` | the **generic** `admits_cases_mem` + `matching_case_teeth`, provided once |

The two central insights the framework crystallizes:

- **The tooth-agreement lemmas are game-INDEPENDENT and must be proven once.** `sumGo_ok`
  (`MultiwayTugProgram.lean:856`) and `heapAdmits_*_ok` (`:817-850`) are facts about
  `DeployedConstraint.admits` — nothing tug-specific. Tug proves them locally today; dungeon would
  have to re-prove them (in the reverse direction) to reach the deployed evaluator. They belong in a
  `DeployedConstraint.Discharge` (forward: *condition ⇒ admits*) and `DeployedConstraint.Invert`
  (reverse: *admits ⇒ condition*) library, keyed by tooth-kind. Every game that touches `sumEquals`
  reuses the same two lemmas; the game supplies only *why the condition holds* (its conservation
  invariant).

- **Forward and reverse are the two halves of one simulation, and they decompose the same way.**
  Forward = "each tooth's condition is established by the model's proven invariant on a legal step"
  (tug's `commonAndAction_admits :618` discharges conservation via `MultiwayTug.conservation`, flags
  via `flag_writeOnce_admits`, scores via `geishaCount_mono`, sequencing via `usedCount_applyLegal`).
  Reverse = "the conjunction of admitted teeth entails the game law" (dungeon's `admitted_verb_conserves`
  extracts `sumScalars = RELICS` straight from the `sumEquals` tooth). Both are *tooth-by-tooth*; the
  per-tooth step is generic (the discharger/inverter library); only the *invariant supplied at each
  tooth* is the game. The framework makes the per-tooth wiring disappear and leaves a list of named
  invariant obligations.

---

## 3. THE HARD PARTS — honestly, and how the framework ISOLATES rather than hides them

Not everything can be generic. The value of the framework is that it turns each genuinely-hard thing
into a **small, named obligation slot**, instead of scaffolding re-derived (and separately audited)
per game. Five honest limits:

### 3a. The game invariants are irreducible — and that is the point
The framework cannot generate `MultiwayTug.conservation`, `geishaCount_mono`, or the dungeon's
custody arithmetic. These *are* the mathematics of each game. The framework does not pretend to; it
**isolates** them as the obligation payload (§1a) — the ~150 lines of real content — freeing them from
the ~600 lines of plumbing they are currently entangled in. This is the difference between "a new
game re-implements the whole proof" and "a new game states its invariants and plugs them in."

### 3b. The reverse direction for information-LOSING programs
Tug's counter program is **cardinality-blind**: many `GState`s share one `α`, so `admitted ⇒ legal`
is *false* for the counters alone — soundness of *which card moved* needs the `airPlay` membership
leaf, which is gated on the undischarged `MerkleSound` hypothesis (`MultiwayTugProgram.lean:756-766`,
`MultiwayTugAir.lean`). The framework **cannot** close this generically; what it does is provide a
declared **membership-leaf obligation slot** — a game either proves `admitted ⇒ legal` from its
program directly (dungeon, whose records carry full state, so the inversions ARE clean — a design
lesson the framework should encode: *prefer non-lossy encodings*) or it declares the leaf obligation,
routed to the FRI-soundness campaign. The obligation is named, not narrated away.

### 3c. The substrate bridge is mechanical but not free
`α`/`encode`/`tugSlots` is where the reconciliations live: name→slot-index, present-zero vs absent
(`DeployedConstraint.lean:156-159`), unsigned-256 vs the model's naturals. The framework provides a
**marshal discipline** — a slot-allocation typeclass plus the *proven-once* agreement library — so a
game supplies only the slot map (an instance), not the reconciliation proofs. The reconciliations
themselves were settled once, in `DeployedConstraint`, and never reopen.

### 3d. The non-pure teeth are outside the exported subset — a bounded expansion
Dungeon's teeth use `affineLe`, `allowedTransitions`, `inRangeTwoSided`, `fieldDelta` — **none** in
`DeployedConstraint`'s exported pure subset (`exec-lean/src/constraint_oracle.rs:57-60`,
`DungeonProgram.lean:82-97`). That is *why* the dungeon inversions today reach only the signed-`Int`
`Exec` model, not the deployed unsigned evaluator — an honest two-step gap the file names itself. The
framework's foundation (Cycle A) **extends `DeployedConstraint` + its `@[export]` wire + the
discharger/inverter library to cover these variants**. Each addition is proven once and every game
using it benefits; the gap is bounded (a known finite variant list), not open-ended.

### 3e. The witness/context teeth are a genuinely separate axis
`Custom`, `Witnessed`, `PreimageGate`, `SenderAuthorized`, `RateLimit` read an `EvalContext` /
`WitnessBundle` and stay Rust-evaluated (`DeployedConstraint.lean:76-79`,
`constraint_oracle.rs:57-60`). These are not "not yet ported" — they depend on runtime witness data a
pure evaluator does not see. The framework must **carve them out as a declared trusted-context
predicate slot** (a named seam with its own gate), NOT fold them into the "proven" surface. Pretending
otherwise would reintroduce exactly the LARP shape the audit refuted.

**Resolution honesty (say it out loud).** This framework proves the **admission-time referee**
(`eval.rs`'s accept/reject) refines the spec, for teeth in the exported subset. It does **not** by
itself put those teeth **in-circuit**: the caveat vocabulary has *no* AIR lowering
(`SEMANTIC-LEAN-BOUNDARY.md:150-158`) — the STARK path is the separate effect-VM. "Correct-to-reality"
here = "the deployed node's admission decision is computed by the proven Lean object," which is real
and load-bearing, and orthogonal to both the AIR-lowering axis (T3) and the undischarged FRI floor.
The framework must describe itself at that resolution, always.

---

## 4. THE BIG SWARM-CYCLES — build the machinery, then retrofit

Five cycles. A–C build the framework; D proves the leverage on the existing two games and closes the
dungeon's deployed gap; E scales to the un-Lean'd policies and the frontier. Each cycle is
whole-tree-buildable and independently landable; the read-only/Lean lanes fan wide, the shared-vocabulary
cutover is a single-owner lock (per the build-lock-contention discipline).

### Cycle A — Unify the vocabulary, the substrate, and the emit (the foundation)
Collapse the four parallel constraint vocabularies to **ONE authored `CellProgram`/`Constraint`/`Guard`**
over the deployed substrate; make `DeployedConstraint.admits` the single evaluator (absorbing the
`Cases`/`SlotChanged`/`AnyOf` dispatch currently split between `Exec.RecordProgram.admits`
(`Program.lean:659`) and `DeployedConstraint`), and expand its exported subset to cover the dungeon's
non-pure teeth (§3d). Provide **ONE** proven `emit` with the `emit_faithful` theorem, drift-gated like
`check-descriptor-drift.sh`; delete tug's and dungeon's private `emitJson`/`toExec`/`toDC`. This is the
load-bearing prerequisite — and the place the substrate reconciliations get settled once. *Largest,
highest-risk cycle; single-owner cutover.*

### Cycle B — The generic discharger/inverter library (proven once, per tooth-kind)
For each tooth-kind in the (now-expanded) exported subset, prove both directions as game-independent
lemmas about `DeployedConstraint.admits`: `discharge_T : condition → admits (T args) = ok` and
`invert_T : admits (T args) = ok → condition`. This lifts tug's `heapAdmits_*_ok`/`sumGo_ok`
(`MultiwayTugProgram.lean:817-931`) and dungeon's per-tooth inversion bodies
(`DungeonProgram.lean:473-663`) out of the games into `DeployedConstraint.Discharge`/`.Invert`. *Fully
parallelizable across tooth-kinds; read-mostly; the honesty gate is an adversarial audit that each
`invert_T` is non-vacuous.*

### Cycle C — The refinement functor (the framework proper)
Define `ProvenPolicy` (§1a); prove `deployed_refines_forward` and `deployed_refines_sound` (§1b) once,
parameterized by the obligation payload; provide the generic `admits_cases_mem`/`matching_case_teeth`
plumbing and the marshal discipline (slot-allocation typeclass + the Cycle-B agreement). Include the
declared **membership-leaf** (§3b) and **trusted-context** (§3e) obligation slots as first-class,
gated fields — so their status is structural, never narrated.

### Cycle D — Retrofit tug + dungeon, and close the dungeon's deployed gap (prove the leverage)
Re-express `multiwayTugProgram`/`dungeonProgram` as `ProvenPolicy` instances; delete the re-derived
scaffolding; keep only the game invariants + the K obligation discharges. Land the dungeon inversions
**onto `DeployedConstraint`** (now possible via the Cycle-A variant expansion), closing the "two honest
steps short" gap (`DungeonProgram.lean:82-97`) so dungeon reaches the deployed evaluator, not just the
signed-`Int` model. **Measure the line-count and obligation-count delta — that is the ground-truthed
leverage number.** A red-umbrella whole-tree build gates the cutover.

### Cycle E — Scale to the un-Lean'd policies + the frontier
Author the ~6 no-Lean families (faction `dreggnet-faction/src/lib.rs`, quest `dreggnet-quest`,
spween-dregg, dungeon-on-dregg's content crates — `SEMANTIC-LEAN-BOUNDARY.md:139-142`) as `ProvenPolicy`
instances — now cheap, swarm-parallelizable. Frontier: the certificate-emitting `emitWithProof` (§1c)
and discharging the membership-leaf slot through the FRI/witness-gen campaigns.

---

## 5. THE PAYOFF — "author + emit + discharge K obligations = proven-to-reality"

**Before (today).** A new game's correctness proof is a **from-scratch** effort: re-author the
vocabulary + emitter (~250 lines), re-author the local evaluator/marshal (~120), re-derive the
substrate-agreement lemmas (~200), re-build the case/tooth plumbing (~150), then finally the game
content. Tug's file is **1038 lines**; dungeon's is **910**. Each is a *separate audit surface* —
`GAME-PROOF-LARP-AUDIT.md` had to classify tug's and dungeon's theorems independently, and found tug's
`immutable` copy had **diverged** from deployment and its `Won_iff_program_thresholds` was an `Iff.rfl`
tautology (both now fixed, but only because a human adversarially re-read each copy).

**After (framework).** A new game is:
1. **author** the model + the program value (in the one vocabulary) + `α` — ~150 lines, all genuine
   game content;
2. **emit** — free (the proven shared `emit`, drift-gated);
3. **discharge K obligations** — where K = (tooth-kinds used) × (directions claimed), a **bounded,
   shrinking** number: each is a short proof that a model invariant establishes / is entailed by one
   tooth's condition. The membership-leaf and trusted-context slots are declared, not hidden.

Then `deployed_refines_forward`/`deployed_refines_sound` instantiate for free, over the evaluator Rust
runs. Estimated **~3–5× reduction in proof volume per game** (the ~600 lines of plumbing collapse to a
structure instance + K discharges), and — more valuable than lines — **the scaffolding is proven-once,
not re-audited N times.**

**The compounding leverage, three ways:**

- **The LARP shapes become structurally impossible.** If the only evaluator a game proof can name is
  the exported `DeployedConstraint.admits`, and the only emit is the shared proven one, then
  *parallel-disconnected evaluators* (audit §0) and *hand-copies that diverge* cannot exist by
  construction, and the residual hypotheses are forced into named obligation slots — the honesty
  guarantee moves from "a human re-reads each proof" to "the type won't let you write the lie."
- **Every tooth-kind is a one-time cost.** Expanding `DeployedConstraint` + the discharger/inverter
  library to a new variant (§3d) is proven once and pays out across every current and future game that
  uses it. The marginal cost of the N-th game **falls monotonically** as the shared library saturates.
- **Correctness-to-reality becomes the default, not the exception.** The record's own count is stark:
  **0 of ~10** deployed policy families reach the deployed program by machine-checked refinement today
  (`SEMANTIC-LEAN-BOUNDARY.md:144-148`). The framework's endpoint is that authoring a game *in Lean +
  emitting it* **is** the refinement proof — so the answer flips from "0 of 10, each a months-long
  bespoke effort" to "all of them, by construction, at author-plus-K-obligations cost."

That is the ambition: not to prove the next game correct, but to build the machine that makes "the
deployed referee refines the spec" **fall out of writing the game** — reusable, honest, and pointed at
the object reality actually runs.

---

*Prepared as a vision probe. Every file:line was read or grep-confirmed during this probe. The
reality-gate (DeployedConstraint `@[export]` + the `ConstraintOracle` seam + the canary), the two
bespoke proofs (tug forward-refinement, dungeon inversions), the four parallel vocabularies, the
exported-subset boundary, and the ~10-family / 0-reach count were each independently ground-truthed.*
