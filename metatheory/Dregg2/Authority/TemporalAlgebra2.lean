/-
# Dregg2.Authority.TemporalAlgebra2 — UNTIL/SINCE, the deadline UNIFICATION, scheduling theorems,
and the JUSTNESS weld (the temporal layer, massively boosted).

`TemporalAlgebra.lean` built the height-window atom family (after/before/within/cooled/rate/
challenge) and welded it onto the proven CTL fixpoint calculus over `heightClock`. Four genuinely
modal things were still missing, and this module supplies them — WELDING onto the in-tree machinery
(`Proof/CTL.lean` lfp/gfp calculus, `Proof/MuCalculus.lean` μ-encodings, `Proof/Fairness.lean`
justness, `Time/Deadline.lean` causal-vs-frame) rather than re-deriving any of it:

## §1 — UNTIL / SINCE (the real U/S pair)

The height atoms are all CLOCK-shaped; the modal pair U/S is EVENT-shaped: "bids are admitted
UNTIL the auction closes", "payout is admitted only SINCE the auction closed". The event is a
one-cell REGISTER flip (the `HeapAtom` cost class, same as `rateBound`): `untilEvent flag` admits
while the register reads `0`, `sinceEvent flag` admits once it is non-zero — exact complements
(`until_since_complement`). The modal content rides the abstract `flagClock` (height × monotone
flag — the monotone-register discipline, e.g. a `monotonicSeq` caveat on the flag slot):

  * **U is the in-tree lfp `EU`** — every unflipped state satisfies
    `E[unflipped U flipped]` (`until_holds_EU_flip`), through the PROVEN `EU_unfold`; and the
    μ-calculus face is inherited verbatim through the PROVEN `encode_EU`
    (`until_mu_formula`) — the U operator is the in-tree least fixpoint, not folklore.
  * **the flip is NOT inevitable** — `flip_not_inevitable`: `(ht, false) ∉ AF {flipped}` (by the
    lfp induction rule `AU_least`): no pure branching argument forces the close; that is
    EXACTLY the justness gap §4 closes. Honesty about what U does and does not give.
  * **S is permanence + a past witness** — `sinceEvent_iff_AG`: flipped ⇔ `AG {flipped}` on the
    monotone-flag system ("once closed, closed forever", the gfp reading); and
    `since_flip_in_past`: ANY run from an unflipped state to a flipped one passes through an
    explicit flip step (the past-time S operator's reflection: "since" carries a WITNESS of the
    enabling event, by `Run` induction).
  * **the executor weld** — `close_write_flips_gates`: ONE committed guarded write of a non-zero
    value to the flag slot simultaneously closes the `untilEvent` gate and opens the `sinceEvent`
    gate; `committed_flip_write_steps_flagClock`: that committed write IS a `flagClock.Step` of
    the abstract system (height ticks on the receipt-chain clock, flag goes monotone) — the
    abstract U/S model is the committed-write projection of the running executor, not free-floating.
  * **the install** — `eventStateStepGuarded` runs the event gate as a PRECONDITION beside the
    temporal-atom gate, then the UNCHANGED `stateStepGuarded` (the same `HeapAtom` composition
    pattern; with no atoms it IS the existing write, every keystone lifts verbatim).

## §2 — THE DEADLINE UNIFICATION (one temporal ontology, not two)

`Time/Deadline.lean` carries a SUM: `causalAfter` (a lightcone fact on the lace) vs `frameWithin`
(an attested frame convention with explicit skew). `TemporalAlgebra` carries height windows. The
verdict, PROVED:

  * **frame ≅ height.** A MET `frameWithin` deadline, under the §8 honesty carrier reading the
    chain clock (`FrameHonesty fs ht` — the SAME carrier `Deadline.lean`'s commit-wait bridge
    consumes), denotes the height atom `afterHeight (T − δ)⁺` (`frame_deadline_embeds_afterHeight`);
    and conversely EVERY `afterHeight` atom IS a `frameWithin` deadline against the chain-clock
    authority whose attestation is the height itself (`afterHeight_is_chain_frame_deadline`, an
    iff). The frame face and the height windows are ONE thing.
  * **causal ⊋ height — the lightcone part.** Along ANY strictly-monotone height assignment a met
    causal deadline IMPLIES an `afterHeight` admission (`causal_deadline_implies_height_gate` —
    heights are a SOUND projection of the lace order), but the converse FAILS and we exhibit the
    failure exactly where it must live: on the INCOMPARABLE fork of the demo lace, the height gate
    admits while `CausalAfter` is FALSE (`height_cannot_recover_causal`). Height clocks are LINEAR;
    the lace is a PARTIAL order; what causal deadlines express beyond every height window is
    precisely incomparability (MEV/frontrunning lives in that gap — `Time/Causal.lean §4`).

So: ONE ontology — `Deadline.frameWithin ≅ TemporalAtom.afterHeight` (two readings of one fact),
`Deadline.causalAfter` strictly above both, its excess characterized (the lightcone).

## §3 — SCHEDULING THEOREMS (vesting, auction lifecycle, rate composition)

  * **k-tranche vesting** — `vesting_admits_iff_prefix`: a monotone unlock schedule admits, at
    every height, EXACTLY the cumulative-unlock prefix (`tranche i` admits ⇔
    `i < unlockedCount … ht`); `vesting_prefix_closed` is the prefix property itself.
  * **auction lifecycle** — `AuctionSchedule` (bid < reveal < settle windows, ordering carried as
    FIELDS): `auction_phases_exclusive` (no height admits two phases), `settle_sees_all_reveals`
    (every admissible reveal is strictly below — and `heightClock`-reachable from — every
    admissible settle: settlement causally sees all reveals). The reveal gate COMPOSES with the
    in-tree preimage/commitment gate (`Intent/SealedAuction.validReveal`, the Blake3 CR carrier):
    `reveal_no_late_switching` — an in-window reveal binds to EXACTLY its committed bid under CR.
  * **rate-limit composition** — `rateBound_meet` (two bounds = the min bound, a meet law),
    `rateBound_mono` / `withinWindow_widen` (refinement), `nested_rate_gate_refines` (a nested
    stricter window+rate gate refines the enclosing one), `withinWindow_split` (a window splits
    exactly into two sub-windows — the rotation boundary for per-window counters; the COUNTING
    obligation stays program wiring, as `TemporalAlgebra`'s `rateBound` doc pins).

## §4 — THE JUSTNESS WELD (Track-D: the liveness face of cooling)

§1 proved the flip is not branching-inevitable; `TemporalAlgebra` proved `cooledSince` admits all
futures past the boundary. What forces the boundary to ARRIVE is van Glabbeek JUSTNESS
(`Proof/Fairness.lean`, the locked Track-D decision): `cooledSince_eventually_admits_of_just` —
a persistently-enabled cooled gate (the `JustProgress` package: B-just schedule + the clock-progress
measure) EVENTUALLY ADMITS (`Eventually`, the genuine ◇ from `just_progress`). Non-vacuous BOTH
ways: `coolDemo` is a CONCRETE inhabited package on the REAL executor (`emitFar` ticks the receipt
clock; all four fields proved, two of them by `decide` against `execFullForestA`), yielding the
UNCONDITIONAL `cooling_liveness_demo`; and `cooling_starves_without_justness` shows the SAME gate
under the starving stutter schedule (`Fairness.badSched`) NEVER admits — justness is exactly the
hypothesis that separates the two.

Non-vacuity throughout (`#guard` both ways, executed gates); every keystone `#assert_axioms`-pinned
to {propext, Classical.choice, Quot.sound}.
-/
import Dregg2.Authority.TemporalAlgebra
import Dregg2.Proof.MuCalculus
import Dregg2.Proof.Fairness
import Dregg2.Time.Deadline
import Dregg2.Intent.SealedAuction

namespace Dregg2.Authority.TemporalAlgebra2

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
  (fieldOf stateStepGuarded stateStepGuarded_eq stateStep_factors guarded_state_field_written)
open Dregg2.Execution (System Run Reachable)
open Dregg2.Proof.CTL (AG EF EU AU AF EX AX EU_unfold AU_least AG_iff_all_reachable preAll pre)
open Dregg2.Proof.MuCalculus (Formula denote Env encode_EU)
open Dregg2.Proof.Temporal (Eventually)
open Dregg2.Proof.Fairness
  (JustProgress just_progress npcA afcA interferes concurrent Commits NonBlocking emitFar
   trajA_logMono_le badSched badSched_traj_const)
open Dregg2.Authority.TemporalAlgebra
open Dregg2.Authority.Blocklace
  (Lace Block precedes pointed demoLace g0 g1 f1 f2 demo_precedes_left_g0)
open Dregg2.Time.Causal (CausalAfter Frontier)
open Dregg2.Time.Frame (FrameStatement FrameWithin FrameHonesty Time)
open Dregg2.Time.Deadline (Deadline)
open Dregg2.Authority.Predicate (Registry registryVerify)
open Dregg2.Crypto.PortalFloor (Blake3Kernel)
open Dregg2.Intent.SealedAuction
  (Bid Auction validReveal sealOf reveal_binds_committed validReveal_committed validReveal_phase)

/-! ## §1 — UNTIL / SINCE: the event-flip atom pair (the real U/S operators).

The event is a one-cell register flip (the `HeapAtom` cost class): `flag = 0` means "the event has
not happened" (bidding open), `flag ≠ 0` means "it has" (closed). The pair partitions every record:
`untilEvent` is the BID gate ("admitted until closed"), `sinceEvent` the SETTLE gate ("admitted only
since closed"). The PROGRAM keeps the register monotone (write-once / `monotonicSeq` on the flag
slot) — that discipline is what the abstract `flagClock` models and §1.W welds. -/

/-- The register-flip BIT: has the event register been set (≠ 0)? Absent/ill-typed reads `0`
(dregg1's `FIELD_ZERO`) — fail-closed to "not yet". -/
def flagOf (f : FieldName) (rec : Value) : Bool := decide (fieldOf f rec ≠ 0)

/-- **The UNTIL/SINCE atom pair.** Decidable, computable, FAIL-CLOSED; reads ONE cell's committed
PRE-state register (the `HeapAtom` cost class — same as `rateBound`/`challengeWindow`). -/
inductive EventAtom where
  /-- **`untilEvent flag`** — admit UNTIL the register flips (reads `0`). "Bids until closed."
  The U-shaped gate: its modal face is the lfp `EU` (`until_holds_EU_flip`). -/
  | untilEvent (flagField : FieldName)
  /-- **`sinceEvent flag`** — admit only SINCE the register flipped (reads `≠ 0`). "Settle only
  since closed." The S-shaped gate: permanence is `AG` (`sinceEvent_iff_AG`), and admission
  carries a PAST witness of the flip (`since_flip_in_past`). -/
  | sinceEvent (flagField : FieldName)
  deriving Repr, DecidableEq

/-- **`EventAtom.eval atom rec`** — does the atom admit against the target cell's committed
PRE-state record? (Height-blind: the event clock is the REGISTER, not the height.) -/
def EventAtom.eval : EventAtom → Value → Bool
  | .untilEvent f, rec => !flagOf f rec
  | .sinceEvent f, rec => flagOf f rec

/-- **UNTIL and SINCE are exact complements** — at every record exactly one of the pair admits.
The U/S partition: an event register splits all of time into the before and the since. -/
theorem until_since_complement (f : FieldName) (rec : Value) :
    (EventAtom.untilEvent f).eval rec = !(EventAtom.sinceEvent f).eval rec := rfl

/-! ### §1.M — the modal model: `flagClock` (height × MONOTONE flag).

`Config = ℕ × Bool`: the chain height and the event bit. A step ticks the height by one and keeps
the flag MONOTONE (it may flip `false → true`, never back) — the write-once register discipline.
`heightClock` is the flag-erased projection; the CTL/μ modalities over `flagClock` give U/S their
fixpoint readings. -/

/-- **`flagClock`** — the height-indexed trace CARRYING the event bit. Step: height +1, flag
monotone (`false → true` allowed, `true → false` not — the write-once register). -/
@[reducible] def flagClock : System where
  Config := Nat × Bool
  Step   := fun s t => t.1 = s.1 + 1 ∧ (s.2 = true → t.2 = true)

/-- The flag is monotone along every `flagClock` run: once flipped, flipped at every later
configuration. (The run-level face of the write-once discipline.) -/
theorem flagClock_flag_mono {s t : flagClock.Config} (h : Run flagClock s t) :
    s.2 = true → t.2 = true := by
  induction h with
  | refl s => exact id
  | step hst _ ih => exact fun hs => ih (hst.2 hs)

/-- **`sinceEvent_iff_AG` — S is gfp permanence.** The SINCE gate admits at a record IFF the
abstract configuration satisfies the branching invariant `AG {flipped}` on `flagClock`: "once
closed, closed on EVERY future of the trace". Routed through the PROVEN `AG_iff_all_reachable` —
the whole gfp calculus applies to the settle gate's admission set with zero new machinery. -/
theorem sinceEvent_iff_AG (f : FieldName) (ht : Nat) (rec : Value) :
    (EventAtom.sinceEvent f).eval rec = true
      ↔ (ht, flagOf f rec) ∈ AG flagClock { c | c.2 = true } := by
  rw [AG_iff_all_reachable]
  constructor
  · intro h t hreach
    exact flagClock_flag_mono hreach h
  · intro hall
    exact hall (ht, flagOf f rec) (Dregg2.Execution.Run.refl _)

/-- **`until_holds_EU_flip` — U is the in-tree lfp `EU`.** Every unflipped configuration satisfies
`E[unflipped U flipped]`: there is a branch on which the UNTIL gate stays open until the event
fires. Proved by unfolding the PROVEN fixpoint law `EU_unfold` (the lfp calculus of
`Proof/CTL.lean`) — the U operator IS the least fixpoint already in the tree. -/
theorem until_holds_EU_flip (ht : Nat) :
    (ht, false) ∈ EU flagClock { c | c.2 = false } { c | c.2 = true } := by
  rw [EU_unfold]
  refine Or.inr ⟨rfl, ⟨(ht + 1, true), ⟨rfl, fun _ => rfl⟩, ?_⟩⟩
  rw [EU_unfold]
  exact Or.inl rfl

/-- The atom-level reading: an ADMITTING `untilEvent` gate places the abstract configuration in
the `EU` satisfaction set — "the bid window is open, and a branch closes it properly". -/
theorem untilEvent_admits_to_EU (f : FieldName) (ht : Nat) (rec : Value)
    (h : (EventAtom.untilEvent f).eval rec = true) :
    (ht, flagOf f rec) ∈ EU flagClock { c | c.2 = false } { c | c.2 = true } := by
  have hf : flagOf f rec = false := by
    simpa [EventAtom.eval] using h
  rw [hf]
  exact until_holds_EU_flip ht

/-- **`until_mu_formula` — the μ-calculus face, inherited.** The same fact through the PROVEN
`encode_EU` (`Proof/MuCalculus.lean`): the unflipped state satisfies the μ-formula
`μx. flipped ∨ (unflipped ∧ ◇x)` — U as the literal least-fixpoint formula of the in-tree
modal-μ embedding. Weld, not reinvention. -/
theorem until_mu_formula (ht : Nat) (ρ : Env flagClock) :
    (ht, false) ∈ denote flagClock
      (.mu 0 (.or_ (.atom { c | c.2 = true })
                   (.and_ (.atom { c | c.2 = false }) (.dia (.var 0))))) ρ := by
  rw [encode_EU]
  exact until_holds_EU_flip ht

/-- **`flip_not_inevitable` — the honest negative.** NO unflipped configuration satisfies
`AF {flipped}`: the pure branching calculus cannot force the close (the never-flipping branch is a
real path). Proved by the lfp INDUCTION rule `AU_least` with the flipped set itself as the
inductive bound. THIS is the gap only the §4 justness hypothesis closes — stated here so the U/S
layer never overclaims. -/
theorem flip_not_inevitable (ht : Nat) :
    (ht, false) ∉ AF flagClock { c | c.2 = true } := by
  intro hmem
  have hsub : AF flagClock { c | c.2 = true } ⊆ { c : flagClock.Config | c.2 = true } := by
    refine AU_least flagClock Set.univ _ _ (fun _ h => h) ?_
    rintro ⟨h, b⟩ ⟨-, hpre⟩
    cases b with
    | true  => rfl
    | false =>
        have hbad := hpre (h + 1, false) ⟨rfl, fun hc => (Bool.false_ne_true hc).elim⟩
        exact (Bool.false_ne_true hbad).elim
  exact Bool.false_ne_true (hsub hmem)

/-- **`since_flip_in_past` — the PAST face of S.** Any run from an unflipped configuration to a
flipped one contains an EXPLICIT flip step: there is a height `a` such that the run reaches
`(a, false)`, steps `(a, false) → (a+1, true)`, and continues to the end. "Admitted since the
event" carries a WITNESS of the event — the past-time S operator's reflection as run
decomposition, by `Run` induction. -/
theorem since_flip_in_past :
    ∀ {s z : flagClock.Config}, Run flagClock s z → s.2 = false → z.2 = true →
      ∃ a : Nat, Run flagClock s (a, false)
        ∧ flagClock.Step (a, false) (a + 1, true)
        ∧ Run flagClock (a + 1, true) z := by
  intro s z hrun
  induction hrun with
  | refl s => intro hs hz; rw [hs] at hz; exact (Bool.false_ne_true hz).elim
  | @step s t u hst hrun' ih =>
      intro hs hz
      by_cases ht2 : t.2 = true
      · refine ⟨s.1, ?_, ⟨rfl, fun _ => rfl⟩, ?_⟩
        · have hse : (s.1, false) = s := by rw [← hs]
          rw [hse]
          exact Dregg2.Execution.Run.refl s
        · have hte : t = (s.1 + 1, true) := by rw [← hst.1, ← ht2]
          rw [← hte]
          exact hrun'
      · have ht2' : t.2 = false := Bool.not_eq_true _ ▸ Bool.eq_false_iff.mpr ht2
        obtain ⟨a, h1, h2, h3⟩ := ih ht2' hz
        exact ⟨a, Dregg2.Execution.Run.step hst h1, h2, h3⟩

/-! ### §1.W — the EXECUTOR weld: the close write IS the abstract flip. -/

/-- **`close_write_flips_gates`** — ONE committed guarded write of a non-zero value to the flag
slot simultaneously: OPENS the `sinceEvent` gate and CLOSES the `untilEvent` gate on the
post-state record. The auction close, the challenge filing, the freeze order — each is one
committed write that flips the whole U/S pair. (Via the existing keystone
`guarded_state_field_written`.) -/
theorem close_write_flips_gates {s s' : RecChainedState} {flagField : FieldName}
    {actor target : CellId} {n : Int}
    (h : stateStepGuarded s flagField actor target n = some s') (hn : n ≠ 0) :
    (EventAtom.sinceEvent flagField).eval (s'.kernel.cell target) = true
      ∧ (EventAtom.untilEvent flagField).eval (s'.kernel.cell target) = false := by
  have hw : fieldOf flagField (s'.kernel.cell target) = n := guarded_state_field_written h
  constructor <;> simp [EventAtom.eval, flagOf, hw, hn]

/-- **`committed_flip_write_steps_flagClock` — the abstract model is the committed-write
projection.** A committed close write steps `flagClock`: the height ticks on the receipt-chain
clock (the ChainLink/ObsAdvance conjunct, as in `committed_write_advances_clock`) and the flag
moves monotonically (the write sets it non-zero, so the post-flag is `true` regardless). The U/S
modal claims are about the running executor's trace, not a free-floating model. -/
theorem committed_flip_write_steps_flagClock {s s' : RecChainedState} {flagField : FieldName}
    {actor target : CellId} {n : Int}
    (h : stateStepGuarded s flagField actor target n = some s') (hn : n ≠ 0) :
    flagClock.Step (s.log.length, flagOf flagField (s.kernel.cell target))
                   (s'.log.length, flagOf flagField (s'.kernel.cell target)) := by
  constructor
  · have hfac := stateStep_factors (stateStepGuarded_eq h)
    show s'.log.length = s.log.length + 1
    rw [hfac.2]
    simp
  · intro _
    show flagOf flagField (s'.kernel.cell target) = true
    simp [flagOf, guarded_state_field_written h, hn]

/-! ### §1.I — the INSTALL (the same `HeapAtom` composition pattern, beside the temporal gate). -/

/-- **`eventAtomsAdmit`** — do ALL installed event atoms admit against the target's committed
PRE-state record? FAIL-CLOSED meet semantics (the shared caveat-surface shape). -/
def eventAtomsAdmit (atoms : List EventAtom) (rec : Value) : Bool :=
  atoms.all (fun a => a.eval rec)

/-- **`eventStateStepGuarded`** — the U/S-guarded field write: the event gate first (pre-state
register read), then the UNCHANGED `temporalStateStepGuarded` (temporal atoms, then authority +
membership + lifecycle + per-slot caveats). The full guard stack, fail-closed at every layer. -/
def eventStateStepGuarded (s : RecChainedState) (eAtoms : List EventAtom)
    (tAtoms : List TemporalAtom) (height : Nat) (f : FieldName) (actor target : CellId)
    (n : Int) : Option RecChainedState :=
  if eventAtomsAdmit eAtoms (s.kernel.cell target) = true then
    temporalStateStepGuarded s tAtoms height f actor target n
  else
    none

/-- A committed event-guarded write IS the underlying temporally-guarded write (the event gate
only restricts the domain) — so EVERY `temporalStateStepGuarded` and `stateStepGuarded` keystone
(conservation, auth-graph frame, authority, field-written) lifts verbatim. -/
theorem eventStateStepGuarded_eq {s s' : RecChainedState} {eAtoms : List EventAtom}
    {tAtoms : List TemporalAtom} {height : Nat} {f : FieldName} {actor target : CellId} {n : Int}
    (h : eventStateStepGuarded s eAtoms tAtoms height f actor target n = some s') :
    temporalStateStepGuarded s tAtoms height f actor target n = some s' := by
  unfold eventStateStepGuarded at h
  by_cases hg : eventAtomsAdmit eAtoms (s.kernel.cell target) = true
  · rw [if_pos hg] at h; exact h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- With NO event atoms installed the event-guarded write IS the temporally-guarded write —
nothing downstream regresses (the superset pin). -/
theorem eventStateStepGuarded_nil_eq (s : RecChainedState) (tAtoms : List TemporalAtom)
    (height : Nat) (f : FieldName) (actor target : CellId) (n : Int) :
    eventStateStepGuarded s [] tAtoms height f actor target n
      = temporalStateStepGuarded s tAtoms height f actor target n := by
  unfold eventStateStepGuarded eventAtomsAdmit
  simp

/-- FAIL-CLOSED: one refusing event atom ⇒ the write does NOT commit (a bid after the close, a
payout before it — rejected BY THE GUARDED WRITE). -/
theorem eventStateStepGuarded_violation_fails (s : RecChainedState) (eAtoms : List EventAtom)
    (tAtoms : List TemporalAtom) (height : Nat) (f : FieldName) (actor target : CellId) (n : Int)
    (h : eventAtomsAdmit eAtoms (s.kernel.cell target) = false) :
    eventStateStepGuarded s eAtoms tAtoms height f actor target n = none := by
  unfold eventStateStepGuarded
  rw [if_neg (by rw [h]; simp)]

/-- BALANCE UNCHANGED through the full stack: a committed event-guarded write (of a non-`balance`
field) conserves the total — the lifted keystone, instantiated not re-proved. -/
theorem event_state_conserves {s s' : RecChainedState} {eAtoms : List EventAtom}
    {tAtoms : List TemporalAtom} {height : Nat} {f : FieldName} {actor target : CellId} {n : Int}
    (hf : f ≠ balanceField)
    (h : eventStateStepGuarded s eAtoms tAtoms height f actor target n = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  temporal_state_conserves hf (eventStateStepGuarded_eq h)

-- ### §1 non-vacuity: the pair discriminates, the gates execute (bids-until-closed, live).
#guard (EventAtom.untilEvent "challenge").eval tRec                      -- true  (not yet closed)
#guard ((EventAtom.sinceEvent "challenge").eval tRec) == false           -- false (not yet closed)
#guard (EventAtom.sinceEvent "challenge").eval tRecChallenged            -- true  (flipped)
#guard ((EventAtom.untilEvent "challenge").eval tRecChallenged) == false -- false (flipped)
-- bids UNTIL closed: the in-window bid commits while `settled = 0` …
#guard (eventStateStepGuarded ssTemp [.untilEvent "settled"] [.withinWindow 10 20]
          15 "best_bid" 0 0 7).isSome
-- … the close write (`settled := 1`) flips the register, and the SAME bid is now REJECTED …
#guard ((stateStepGuarded ssTemp "settled" 0 0 1).bind
          (fun s1 => eventStateStepGuarded s1 [.untilEvent "settled"] [.withinWindow 10 20]
            16 "best_bid" 0 0 9)).isSome == false
-- … while the SINCE-gated payout opens on the very same flip (and was closed before it).
#guard ((stateStepGuarded ssTemp "settled" 0 0 1).bind
          (fun s1 => eventStateStepGuarded s1 [.sinceEvent "settled"] []
            25 "unlocked" 0 0 1)).isSome
#guard (eventStateStepGuarded ssTemp [.sinceEvent "settled"] [] 25 "unlocked" 0 0 1).isSome
        == false

/-! ## §2 — THE DEADLINE UNIFICATION: `Time/Deadline.lean` vs the height windows.

The sum type forces causal-vs-frame; the height atoms are a third surface. We prove they are TWO
ontologies, not three — and exactly where the remaining gap lives. -/

/-- **`HeightMap B`** — a strictly-monotone height assignment on the lace: any "block height" /
round number / topological index. `strict` is the defining property every real height has
(a block is strictly higher than its causal past). -/
structure HeightMap (B : Lace) where
  /-- The height of each block. -/
  h : Frontier → Nat
  /-- Strict monotonicity along the lace order: the causal past sits strictly below. -/
  strict : ∀ {x y : Frontier}, precedes B x y → h x < h y

/-- **`causal_deadline_implies_height_gate` — heights are a SOUND projection.** A MET
`causalAfter E` deadline implies, along ANY `HeightMap`, the admission of the height atom
`afterHeight (h E + 1)` at the frontier's height: every causal deadline is over-approximated by a
vesting gate. (The frame/registry parameters are phantom on the causal face —
`causalAfter_no_frame_dependency`.) -/
theorem causal_deadline_implies_height_gate {Stmt Wit : Type} {B : Lace}
    {reg : Registry Stmt Wit} {stmtOf : FrameStatement → Stmt} (hm : HeightMap B)
    (E now : Frontier) (rec : Value)
    (hmet : (Deadline.causalAfter (B := B) (reg := reg) (stmtOf := stmtOf) E).Met now) :
    (TemporalAtom.afterHeight (hm.h E + 1)).eval (hm.h now) rec = true := by
  have hlt : hm.h E < hm.h now := hm.strict hmet
  simp only [TemporalAtom.eval, decide_eq_true_eq]
  omega

/-- In the demo lace nothing precedes INTO genesis: every `≺`-chain's right end carries an ack
edge, and `g0` acks nothing. (The aux fact the height-map witness needs.) -/
theorem demo_precedes_ne_g0 {x y : Block} (h : precedes demoLace x y) : y ≠ g0 := by
  induction h with
  | base hp =>
      intro hyg0
      obtain ⟨hmem, -, -⟩ := hp
      rw [hyg0] at hmem
      exact absurd hmem (by simp [g0])
  | trans _ _ _ ih₂ => exact ih₂

/-- A right endpoint of `precedes` resolves in the lace (the ack edge carries the lookup). -/
theorem demo_precedes_lookup_right {B : Lace} {x y : Block} (h : precedes B x y) :
    B.lookup y.id = some y := by
  induction h with
  | base hp => exact hp.2.2
  | trans _ _ _ ih₂ => exact ih₂

/-- A concrete `HeightMap` on the demo lace: genesis at 0, the honest successor at 2, the two
fork blocks at 1 (heights by block id — fully computable). -/
def demoHm : HeightMap demoLace where
  h := fun b => if b.id = 0 then 0 else if b.id = 1 then 2 else 1
  strict := by
    intro x y hxy
    have hx : x = g0 := demo_precedes_left_g0 hxy
    have hyne : y ≠ g0 := demo_precedes_ne_g0 hxy
    have hylk : demoLace.lookup y.id = some y := demo_precedes_lookup_right hxy
    have hymem : y ∈ demoLace := List.mem_of_find?_eq_some hylk
    subst hx
    have hcases : y = g0 ∨ y = g1 ∨ y = f1 ∨ y = f2 := by
      simpa [demoLace] using hymem
    rcases hcases with rfl | rfl | rfl | rfl
    · exact absurd rfl hyne
    · decide
    · decide
    · decide

/-- **`height_cannot_recover_causal` — THE LIGHTCONE PART (where causal exceeds height).** On the
demo lace's INCOMPARABLE fork there is a height map under which the `afterHeight` gate ADMITS
(`h f1 + 1 ≤ h g1`) while the causal deadline `causalAfter f1` is FALSE at `g1` (`f1 ⊀ g1` — the
fork never entered `g1`'s causal past). Height clocks are LINEAR; the lace is a PARTIAL order; the
exact excess of causal deadlines over EVERY height window is incomparability — the
anti-frontrunning content (`Time/Causal.lean §4`) that no `TemporalAtom` can express. -/
theorem height_cannot_recover_causal :
    ∃ (hm : HeightMap demoLace) (E now : Frontier) (rec : Value),
      (TemporalAtom.afterHeight (hm.h E + 1)).eval (hm.h now) rec = true
        ∧ ¬ CausalAfter demoLace E now := by
  refine ⟨demoHm, f1, g1, .record [], by decide, ?_⟩
  intro hca
  have hf1 : f1 = g0 := demo_precedes_left_g0 hca
  exact absurd (congrArg Block.id hf1) (by decide)

/-- **`frame_deadline_embeds_afterHeight` — the frame face DENOTES a height atom.** A MET
`frameWithin` deadline, under the §8 honesty carrier read at the chain height
(`FrameHonesty fs ht` — the SAME carrier the commit-wait bridge consumes), admits the height atom
`afterHeight (T − δ)⁺` at that height: the attested frame fact and the vesting gate are one
admission. (Acceptance alone concludes nothing physical — exactly as in `Deadline.lean §6` the
carrier is load-bearing.) -/
theorem frame_deadline_embeds_afterHeight {Stmt Wit : Type} {B : Lace}
    {reg : Registry Stmt Wit} {stmtOf : FrameStatement → Stmt}
    (fs : FrameStatement) (att : Wit) (now : Frontier) (ht : Nat) (rec : Value)
    (_hmet : (Deadline.frameWithin (B := B) (reg := reg) (stmtOf := stmtOf) fs att).Met now)
    (hhon : FrameHonesty fs (ht : Time)) :
    (TemporalAtom.afterHeight (fs.T - fs.δ).toNat).eval ht rec = true := by
  simp only [TemporalAtom.eval, decide_eq_true_eq]
  exact Int.toNat_le.mpr hhon

/-- The chain-clock REGISTRY: the `temporal` authority whose attestation IS the chain height —
the verifier accepts a height reading iff it has reached the statement's bound. (The degenerate
self-frame of the chain: its "clock" is the receipt-chain length, exact by construction.) -/
def chainClockReg : Registry Nat Nat :=
  fun k => if k = .temporal then some (fun stmt att => decide (stmt ≤ att)) else none

/-- The statement encoder of the chain-clock frame: the height bound `(T − δ)⁺` the attestation
must clear (the same bound the honesty carrier pins). -/
def heightStmtOf : FrameStatement → Nat := fun fs => (fs.T - fs.δ).toNat

/-- **`afterHeight_is_chain_frame_deadline` — the CONVERSE embedding (an iff).** EVERY
`afterHeight` admission IS a met `frameWithin` deadline against the chain-clock registry, with the
height itself as the attestation — and vice versa. With `frame_deadline_embeds_afterHeight` this
closes the unification: **frame deadlines ≅ height atoms** (one ontology, two readings); only the
CAUSAL face exceeds them (`height_cannot_recover_causal`). -/
theorem afterHeight_is_chain_frame_deadline {B : Lace} (fs : FrameStatement) (ht : Nat)
    (rec : Value) (now : Frontier) :
    (TemporalAtom.afterHeight (heightStmtOf fs)).eval ht rec = true
      ↔ (Deadline.frameWithin (B := B) (reg := chainClockReg)
            (stmtOf := heightStmtOf) fs ht).Met now := by
  show _ ↔ FrameWithin chainClockReg heightStmtOf fs ht
  unfold FrameWithin registryVerify chainClockReg
  simp [TemporalAtom.eval]

-- ### §2 non-vacuity: the chain-clock frame deadline flips with the height.
#guard (registryVerify chainClockReg .temporal 100 150)           -- true  (height reached)
#guard (registryVerify chainClockReg .temporal 100 50) == false   -- false (not yet)
#guard ((TemporalAtom.afterHeight (heightStmtOf
          { authority := { issuer := 0 }, T := 100, δ := 25 })).eval 80 tRec)  -- true (75 ≤ 80)
#guard (demoHm.h g0 == 0 && demoHm.h g1 == 2 && demoHm.h f1 == 1)  -- the witness heights

/-! ## §3 — SCHEDULING THEOREMS. -/

/-! ### §3.V — k-tranche VESTING: the gate admits exactly the cumulative-unlock prefix. -/

/-- Tranche `i`'s gate: `afterHeight (unlocks i)` — the vesting atom at the tranche's unlock
height. A vesting SCHEDULE is the monotone family `unlocks : ℕ → ℕ`. -/
def trancheGate (unlocks : Nat → Nat) (i : Nat) : TemporalAtom :=
  .afterHeight (unlocks i)

/-- The CUMULATIVE UNLOCK count of a `k`-tranche schedule at height `ht`: how many of the `k`
tranches have reached their unlock height. -/
def unlockedCount (unlocks : Nat → Nat) (k ht : Nat) : Nat :=
  ((List.range k).filter (fun i => decide (unlocks i ≤ ht))).length

/-- The unlock count never exceeds the tranche count. -/
theorem unlockedCount_le (unlocks : Nat → Nat) (k ht : Nat) :
    unlockedCount unlocks k ht ≤ k := by
  unfold unlockedCount
  have h := List.length_filter_le (fun i => decide (unlocks i ≤ ht)) (List.range k)
  simpa using h

/-- If every tranche below `k` has unlocked, the count is full. -/
theorem unlockedCount_all (unlocks : Nat → Nat) (k ht : Nat)
    (hall : ∀ i, i < k → unlocks i ≤ ht) : unlockedCount unlocks k ht = k := by
  unfold unlockedCount
  rw [List.filter_eq_self.mpr ?_, List.length_range]
  intro a ha
  rw [List.mem_range] at ha
  simpa using hall a ha

/-- **`vesting_admits_iff_prefix` — THE k-TRANCHE THEOREM.** For a MONOTONE unlock schedule, at
every height the admitted tranches are EXACTLY the cumulative-unlock prefix: tranche `i` (of `k`)
admits iff `i < unlockedCount unlocks k ht`. The vesting program admits the prefix, the whole
prefix, and nothing but the prefix. -/
theorem vesting_admits_iff_prefix {unlocks : Nat → Nat} (hmono : Monotone unlocks)
    (rec : Value) :
    ∀ (k i ht : Nat), i < k →
      ((trancheGate unlocks i).eval ht rec = true ↔ i < unlockedCount unlocks k ht) := by
  intro k
  induction k with
  | zero => intro i ht h; exact absurd h (Nat.not_lt_zero i)
  | succ m ih =>
      intro i ht hik
      have hsplit : unlockedCount unlocks (m + 1) ht
          = unlockedCount unlocks m ht + (if unlocks m ≤ ht then 1 else 0) := by
        unfold unlockedCount
        rw [List.range_succ, List.filter_append, List.length_append]
        by_cases hm : unlocks m ≤ ht <;> simp [hm]
      by_cases hm : unlocks m ≤ ht
      · have hall : ∀ j, j < m + 1 → unlocks j ≤ ht :=
          fun j hj => le_trans (hmono (Nat.lt_succ_iff.mp hj)) hm
        rw [unlockedCount_all unlocks (m + 1) ht hall]
        simp only [trancheGate, TemporalAtom.eval, decide_eq_true_eq]
        exact ⟨fun _ => hik, fun _ => hall i hik⟩
      · have hcount : unlockedCount unlocks (m + 1) ht = unlockedCount unlocks m ht := by
          rw [hsplit, if_neg hm, Nat.add_zero]
        rw [hcount]
        rcases Nat.lt_or_ge i m with him | him
        · exact ih i ht him
        · have hi : i = m := Nat.le_antisymm (Nat.lt_succ_iff.mp hik) him
          subst hi
          have hle : unlockedCount unlocks i ht ≤ i := unlockedCount_le unlocks i ht
          simp only [trancheGate, TemporalAtom.eval, decide_eq_true_eq]
          exact ⟨fun h => absurd h hm, fun h => by omega⟩

/-- The PREFIX property itself: an admitted tranche pulls every earlier tranche with it (the
admitted set is downward-closed in the tranche index — no gaps in a vesting unlock). -/
theorem vesting_prefix_closed {unlocks : Nat → Nat} (hmono : Monotone unlocks)
    {i j ht : Nat} (hij : i ≤ j) (rec rec' : Value)
    (hj : (trancheGate unlocks j).eval ht rec = true) :
    (trancheGate unlocks i).eval ht rec' = true := by
  simp only [trancheGate, TemporalAtom.eval, decide_eq_true_eq] at *
  exact le_trans (hmono hij) hj

/-- The demo 3-tranche schedule: unlocks at heights 100/200/300. -/
def vest3 : Nat → Nat := fun i => 100 * (i + 1)

theorem vest3_mono : Monotone vest3 := by
  intro a b h
  simp only [vest3]
  omega

-- At height 250 exactly the first two tranches are unlocked — count and gates agree, executed.
#guard unlockedCount vest3 3 250 == 2
#guard (trancheGate vest3 0).eval 250 tRec                       -- true  (tranche 0 vested)
#guard (trancheGate vest3 1).eval 250 tRec                       -- true  (tranche 1 vested)
#guard ((trancheGate vest3 2).eval 250 tRec) == false            -- false (tranche 2 locked)
-- the tranche-1 unlock write COMMITS at 250 and is REJECTED at 150 (the guarded write, executed):
#guard (temporalStateStepGuarded ssTemp [trancheGate vest3 1] 250 "unlocked" 0 0 2).isSome
#guard (temporalStateStepGuarded ssTemp [trancheGate vest3 1] 150 "unlocked" 0 0 2).isSome
        == false

/-- The k-tranche theorem, executed on the demo schedule (the `iff`, instantiated). -/
example : (trancheGate vest3 1).eval 250 tRec = true ↔ 1 < unlockedCount vest3 3 250 :=
  vesting_admits_iff_prefix vest3_mono tRec 3 1 250 (by omega)

/-! ### §3.A — the AUCTION LIFECYCLE: bid / reveal / settle, phase-exclusive, settle sees all. -/

/-- A three-phase auction schedule: the bid window, the reveal window, the settle boundary —
with the phase ORDERING carried as fields (constructing a misordered schedule is impossible). -/
structure AuctionSchedule where
  bidLo : Nat
  bidHi : Nat
  revealLo : Nat
  revealHi : Nat
  settleAt : Nat
  /-- Bidding closes strictly before revealing opens. -/
  bid_lt_reveal : bidHi < revealLo
  /-- The reveal window is non-degenerate (it opens no later than it closes) — without this the
  bid and settle phases could overlap THROUGH an empty reveal window. -/
  reveal_wf : revealLo ≤ revealHi
  /-- Revealing closes strictly before settlement opens. -/
  reveal_lt_settle : revealHi < settleAt

/-- The BID gate: `withinWindow [bidLo, bidHi]`. -/
def bidGate (a : AuctionSchedule) : TemporalAtom := .withinWindow a.bidLo a.bidHi

/-- The REVEAL gate (height face): `withinWindow [revealLo, revealHi]`. The full reveal admission
composes this with the in-tree PREIMAGE gate (`revealAdmits` below). -/
def revealGate (a : AuctionSchedule) : TemporalAtom := .withinWindow a.revealLo a.revealHi

/-- The SETTLE gate: `afterHeight settleAt` (upward-closed — settlement, once open, stays open). -/
def settleGate (a : AuctionSchedule) : TemporalAtom := .afterHeight a.settleAt

/-- **`auction_phases_exclusive` — PHASE EXCLUSIVITY.** At every height at most ONE of the three
phase gates admits: no bid during reveal, no reveal during settlement, no overlap anywhere. The
ordering fields make this a pure window computation. -/
theorem auction_phases_exclusive (a : AuctionSchedule) (ht : Nat) (rb rr rs : Value) :
    ¬((bidGate a).eval ht rb = true ∧ (revealGate a).eval ht rr = true)
      ∧ ¬((bidGate a).eval ht rb = true ∧ (settleGate a).eval ht rs = true)
      ∧ ¬((revealGate a).eval ht rr = true ∧ (settleGate a).eval ht rs = true) := by
  have h1 := a.bid_lt_reveal
  have h2 := a.reveal_lt_settle
  have h3 := a.reveal_wf
  simp only [bidGate, revealGate, settleGate, TemporalAtom.eval, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

/-- **`settle_sees_all_reveals`.** Every height at which a reveal is admissible lies STRICTLY
below — and is `heightClock`-REACHABLE from — every height at which settlement is admissible: the
settling turn's clock has every valid reveal in its committed past. (With
`committed_write_advances_clock`, a committed reveal's receipt is a strict log-prefix of the
settling state's.) -/
theorem settle_sees_all_reveals (a : AuctionSchedule) {hr hs : Nat} (rr rs : Value)
    (hrev : (revealGate a).eval hr rr = true) (hset : (settleGate a).eval hs rs = true) :
    hr < hs ∧ Reachable heightClock hr hs := by
  have h2 := a.reveal_lt_settle
  simp only [revealGate, settleGate, TemporalAtom.eval, Bool.and_eq_true,
    decide_eq_true_eq] at hrev hset
  have hlt : hr < hs := by omega
  exact ⟨hlt, heightClock_run_of_le (Nat.le_of_lt hlt)⟩

section PreimageWeld

variable {Digest : Type} [K : Blake3Kernel Digest]

/-- **`revealAdmits` — the FULL reveal admission: the height window COMPOSED with the in-tree
preimage/commitment gate.** `validReveal` (`Intent/SealedAuction.lean`) is the hash-preimage
check: the auction is in its reveal phase AND the revealed bid's Blake3 seal is among the
committed seals — the PreimageGate face, riding the REAL CR carrier. -/
def revealAdmits [DecidableEq Digest] (a : AuctionSchedule) (auc : Auction Digest) (b : Bid)
    (ht : Nat) (rec : Value) : Bool :=
  (revealGate a).eval ht rec && validReveal auc b

/-- The composed gate decomposes as the meet of its two faces (window ∧ preimage). -/
theorem revealAdmits_decomposes [DecidableEq Digest] (a : AuctionSchedule)
    (auc : Auction Digest) (b : Bid) (ht : Nat) (rec : Value) :
    revealAdmits a auc b ht rec = true
      ↔ ((revealGate a).eval ht rec = true ∧ validReveal auc b = true) := by
  simp [revealAdmits]

/-- **`reveal_no_late_switching`.** An in-window admitted reveal that opens a committed seal opens
it to EXACTLY the bid that sealed it (under the CR carrier): the temporal window cannot be used to
swap bids — the preimage face binds, the height face only schedules. (Inherited from the proven
`reveal_binds_committed`; weld, not re-derivation.) -/
theorem reveal_no_late_switching [DecidableEq Digest] (hcr : K.collisionHard)
    (a : AuctionSchedule) (auc : Auction Digest) (b b₀ : Bid) (ht : Nat) (rec : Value)
    (hadm : revealAdmits a auc b ht rec = true)
    (hopen : sealOf (Digest := Digest) b = sealOf b₀) :
    b = b₀ := by
  have hvalid : validReveal auc b = true := ((revealAdmits_decomposes a auc b ht rec).mp hadm).2
  exact reveal_binds_committed hcr auc b b₀ hvalid hopen

/-- **`settle_sees_valid_reveals` — the lifecycle keystone, assembled.** Every reveal admitted by
the FULL gate (window + preimage) at height `hr` is strictly below and `heightClock`-reachable
from every admissible settle height — AND its bid genuinely opened a committed seal
(`validReveal`). Settlement sees all valid reveals; nothing else got in. -/
theorem settle_sees_valid_reveals [DecidableEq Digest] (a : AuctionSchedule)
    (auc : Auction Digest) (b : Bid) {hr hs : Nat} (rr rs : Value)
    (hrev : revealAdmits a auc b hr rr = true)
    (hset : (settleGate a).eval hs rs = true) :
    hr < hs ∧ Reachable heightClock hr hs ∧ validReveal auc b = true := by
  obtain ⟨hwin, hvalid⟩ := (revealAdmits_decomposes a auc b hr rr).mp hrev
  obtain ⟨hlt, hreach⟩ := settle_sees_all_reveals a rr rs hwin hset
  exact ⟨hlt, hreach, hvalid⟩

end PreimageWeld

/-- The demo schedule: bid [10,20], reveal [30,40], settle from 50. -/
def aucSched : AuctionSchedule :=
  { bidLo := 10, bidHi := 20, revealLo := 30, revealHi := 40, settleAt := 50
    bid_lt_reveal := by omega, reveal_wf := by omega, reveal_lt_settle := by omega }

-- phase gates, executed at sample heights — each height admits AT MOST one phase:
#guard (bidGate aucSched).eval 15 tRec                          -- true  (bid phase)
#guard ((revealGate aucSched).eval 15 tRec) == false
#guard ((settleGate aucSched).eval 15 tRec) == false
#guard (revealGate aucSched).eval 35 tRec                       -- true  (reveal phase)
#guard ((bidGate aucSched).eval 35 tRec) == false
#guard (settleGate aucSched).eval 55 tRec                       -- true  (settle phase)
#guard ((revealGate aucSched).eval 55 tRec) == false
-- the dead zone between windows admits NOTHING (gaps fail closed):
#guard (((bidGate aucSched).eval 25 tRec || (revealGate aucSched).eval 25 tRec
          || (settleGate aucSched).eval 25 tRec)) == false

/-! ### §3.R — RATE-LIMIT COMPOSITION over nested windows. -/

/-- **`rateBound_meet` — composition is the MIN bound.** Installing two rate bounds on the same
counter is exactly installing the tighter one: the meet law of the rate algebra. -/
theorem rateBound_meet (c : FieldName) (k k' : Int) (ht : Nat) (rec : Value) :
    ((TemporalAtom.rateBound c k).eval ht rec && (TemporalAtom.rateBound c k').eval ht rec)
      = (TemporalAtom.rateBound c (min k k')).eval ht rec := by
  simp only [TemporalAtom.eval]
  by_cases h : fieldOf c rec < k <;> by_cases h' : fieldOf c rec < k' <;>
    simp [h, h']

/-- A looser bound admits whatever a tighter one does (refinement direction). -/
theorem rateBound_mono {c : FieldName} {k k' : Int} (hkk' : k ≤ k') (ht : Nat) (rec : Value)
    (h : (TemporalAtom.rateBound c k).eval ht rec = true) :
    (TemporalAtom.rateBound c k').eval ht rec = true := by
  simp only [TemporalAtom.eval, decide_eq_true_eq] at *
  omega

/-- A wider window admits whatever a nested one does (refinement direction). -/
theorem withinWindow_widen {lo hi lo' hi' ht : Nat} (hlo : lo ≤ lo') (hhi : hi' ≤ hi)
    (rec rec' : Value) (h : (TemporalAtom.withinWindow lo' hi').eval ht rec = true) :
    (TemporalAtom.withinWindow lo hi).eval ht rec' = true := by
  simp only [TemporalAtom.eval, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

/-- **`nested_rate_gate_refines`.** A NESTED rate gate (a sub-window with a tighter bound on the
same counter) REFINES the enclosing gate: every admission of the inner gate is an admission of
the outer. Rate policies compose by nesting without re-verification. -/
theorem nested_rate_gate_refines {c : FieldName} {lo hi lo' hi' : Nat} {k k' : Int}
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi) (hk : k' ≤ k) (ht : Nat) (rec : Value)
    (h : temporalAtomsAdmit [.withinWindow lo' hi', .rateBound c k'] ht rec = true) :
    temporalAtomsAdmit [.withinWindow lo hi, .rateBound c k] ht rec = true := by
  simp only [temporalAtomsAdmit, List.all_cons, List.all_nil, Bool.and_eq_true,
    TemporalAtom.eval, decide_eq_true_eq] at *
  refine ⟨⟨?_, ?_⟩, ?_, trivial⟩ <;> omega

/-- **`withinWindow_split` — the rotation boundary.** A window splits EXACTLY into two adjacent
sub-windows: an admission of the enclosing window is an admission of precisely one half. This is
the per-window counter ROTATION seam: split the outer window at each boundary, give each
sub-window its own `rateBound` counter slot, and the meet/refinement laws above compose the
per-window policies. (The obligation that the counter register actually counts — bumped on each
admission, reset at each boundary — remains PROGRAM WIRING, exactly as `TemporalAlgebra`'s
`rateBound` doc pins; the algebra here is the window/bound composition itself.) -/
theorem withinWindow_split {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) (ht : Nat)
    (rec : Value) :
    (TemporalAtom.withinWindow lo hi).eval ht rec = true
      ↔ ((TemporalAtom.withinWindow lo mid).eval ht rec = true
          ∨ (TemporalAtom.withinWindow (mid + 1) hi).eval ht rec = true) := by
  simp only [TemporalAtom.eval, Bool.and_eq_true, decide_eq_true_eq]
  omega

-- rate meet/split, executed (the counter register reads 3 in `tRec`):
#guard ((TemporalAtom.rateBound "bids_count" 5).eval 0 tRec
          && (TemporalAtom.rateBound "bids_count" 4).eval 0 tRec)   -- true  (3 < min 5 4)
#guard ((TemporalAtom.rateBound "bids_count" 5).eval 0 tRec
          && (TemporalAtom.rateBound "bids_count" 3).eval 0 tRec) == false  -- false (3 ≮ 3)
#guard (TemporalAtom.withinWindow 10 20).eval 15 tRec               -- in the outer window …
#guard (TemporalAtom.withinWindow 10 15).eval 15 tRec               -- … exactly the LEFT half
#guard ((TemporalAtom.withinWindow 16 20).eval 15 tRec) == false    -- … and not the right

/-! ## §4 — THE JUSTNESS WELD: the liveness face of cooling (Track-D = JUSTNESS).

`flip_not_inevitable` (§1) and `Proof/CTL.lean`'s deferred-`AF` note both say the same thing: pure
branching logic cannot force progress — the eternal stutter is a real path. The Track-D decision
supplies the missing hypothesis: van Glabbeek JUSTNESS. Here the cooled gate's "persistently
enabled" is the `JustProgress` package (`Proof/Fairness.lean`): the schedule is B-just AND at
every pre-boundary state some committing, non-blocking forest is enabled whose interfering
continuations tick the receipt-chain clock. Under that package the gate's boundary ARRIVES. -/

/-- **`cooledSince_eventually_admits_of_just` — THE LIVENESS FACE OF COOLING.** A persistently-
enabled `cooledSince` gate EVENTUALLY ADMITS under just scheduling: from any `JustProgress`
package driving the receipt-chain clock to the cooling boundary (`stagedAt + period ≤ log`),
`just_progress` (the genuine ◇ of the justness layer) yields an index where the gate admits —
and by `cooledSince_upward_closed` it admits at every later index too. The dual of
`cooledSince_refuses_inside`: the gate refuses the whole period, then justness delivers it. -/
theorem cooledSince_eventually_admits_of_just {B : ConservingForest → Prop}
    {s : RecChainedState} {sched : SchedA} (stagedAt period : Nat) (rec : Value)
    (jp : JustProgress B (fun x => stagedAt + period ≤ x.log.length) s sched) :
    Eventually (fun x => (TemporalAtom.cooledSince stagedAt period).eval x.log.length rec = true)
      s sched := by
  obtain ⟨n, hn⟩ := just_progress jp
  exact ⟨n, cooledSince_admits_after hn rec⟩

/-- The vesting form of the same weld (`cooledSince ≡ afterHeight` transfers it): a persistently-
enabled vesting gate eventually opens under just scheduling. -/
theorem afterHeight_eventually_admits_of_just {B : ConservingForest → Prop}
    {s : RecChainedState} {sched : SchedA} (h : Nat) (rec : Value)
    (jp : JustProgress B (fun x => h ≤ x.log.length) s sched) :
    Eventually (fun x => (TemporalAtom.afterHeight h).eval x.log.length rec = true) s sched := by
  obtain ⟨n, hn⟩ := just_progress jp
  refine ⟨n, ?_⟩
  simp only [TemporalAtom.eval, decide_eq_true_eq]
  exact hn

/-! ### §4.D — the CONCRETE inhabitant (the package is buildable on the REAL executor). -/

/-- The clock-ticking schedule: fire the independent authority-free emit (`Fairness.emitFar`,
which COMMITS — no stutter) every tick. Each commit appends one receipt: the chain clock advances. -/
def emitSched : SchedA := fun _ => emitFar

/-- One emit tick lands one receipt (executed). -/
theorem emit_traj1_log : (trajA fma0 emitSched 1).log.length = 1 := by decide

/-- Two emit ticks land two receipts (executed). -/
theorem emit_traj2_log : (trajA fma0 emitSched 2).log.length = 2 := by decide

/-- The demo NonBlocking partition: forests that necessarily participate in the emitting cell `1`
(the active region). The principled modelling choice, instantiated concretely (cf. `BReg`). -/
def Bcool : ConservingForest → Prop := fun cf => (1 : CellId) ∈ npcA cf

/-- `emitFar` affects cell `1`. -/
theorem emitFar_afc : (1 : CellId) ∈ afcA emitFar := by decide

/-- Every `Bcool` forest is interfered by an `emitFar` step (its needed cell `1` is affected) —
the interference engine of the demo's justness. -/
theorem Bcool_interferes_emitFar (cf : ConservingForest) (hB : Bcool cf) :
    interferes cf emitFar := by
  intro hconc
  exact (Finset.disjoint_left.mp hconc) hB emitFar_afc

/-- **`coolDemo` — the inhabited `JustProgress` for a cooling gate `cooledSince 0 2`** (staged at
genesis, two-tick period) on the REAL executor: the B-just `emitSched` path from `fma0`, goal "the
clock has reached the cooling boundary", measure "ticks remaining". All four fields PROVED —
`just` by the interference engine, the commit facts by `decide` against `execFullForestA`. The
"persistently-enabled" of the headline theorem, made concrete. -/
def coolDemo : JustProgress Bcool (fun x => 0 + 2 ≤ x.log.length) fma0 emitSched where
  just := fun k cf hB _ => ⟨k, Nat.le_refl k, Bcool_interferes_emitFar cf hB⟩
  μ := fun x => 2 - x.log.length
  zero := by
    intro x hx
    have hx' : 2 - x.log.length = 0 := hx
    show 0 + 2 ≤ x.log.length
    -- careful: Nat truncated subtraction — `2 - L = 0` forces `2 ≤ L` only with the omega view.
    omega
  enabled := by
    intro k hnP
    have hnP' : ¬ (2 ≤ (trajA fma0 emitSched k).log.length) := hnP
    have hk2 : k < 2 := by
      rcases Nat.lt_or_ge k 2 with h | h
      · exact h
      · exfalso
        have hmono := trajA_logMono_le fma0 emitSched 2 k h
        rw [emit_traj2_log] at hmono
        exact hnP' (by omega)
    match k, hk2 with
    | 0, _ =>
        refine ⟨emitFar, ?_, ?_, ?_⟩
        · show (1 : CellId) ∈ npcA emitFar
          decide
        · show (execFullForestA (trajA fma0 emitSched 0) emitFar.1).isSome = true
          decide
        · intro n _ _
          show 2 - (trajA fma0 emitSched (n + 1)).log.length
                < 2 - (trajA fma0 emitSched 0).log.length
          have h1 := trajA_logMono_le fma0 emitSched 1 (n + 1) (by omega)
          rw [emit_traj1_log] at h1
          have h0 : (trajA fma0 emitSched 0).log.length = 0 := by decide
          omega
    | 1, _ =>
        refine ⟨emitFar, ?_, ?_, ?_⟩
        · show (1 : CellId) ∈ npcA emitFar
          decide
        · show (execFullForestA (trajA fma0 emitSched 1) emitFar.1).isSome = true
          decide
        · intro n hkn _
          show 2 - (trajA fma0 emitSched (n + 1)).log.length
                < 2 - (trajA fma0 emitSched 1).log.length
          have h2 := trajA_logMono_le fma0 emitSched 2 (n + 1) (by omega)
          rw [emit_traj2_log] at h2
          have h1 := emit_traj1_log
          omega
  frame := by
    intro k
    show 2 - (trajA fma0 emitSched (k + 1)).log.length
          ≤ 2 - (trajA fma0 emitSched k).log.length
    have := trajA_logMono_le fma0 emitSched k (k + 1) (Nat.le_succ k)
    omega

/-- **`cooling_liveness_demo` — UNCONDITIONAL liveness on the real executor.** The cooling gate
`cooledSince 0 2` EVENTUALLY ADMITS along the just `emitSched` path from `fma0` — no hypotheses:
the package is inhabited (`coolDemo`) and the weld theorem fires. The polis cooling machinery's
liveness face, machine-checked end-to-end. -/
theorem cooling_liveness_demo (rec : Value) :
    Eventually (fun x => (TemporalAtom.cooledSince 0 2).eval x.log.length rec = true)
      fma0 emitSched :=
  cooledSince_eventually_admits_of_just 0 2 rec coolDemo

/-- **`cooling_starves_without_justness` — the separating negative.** Under the STARVING stutter
schedule (`Fairness.badSched`, which fires only a rejected forest forever — the trajectory never
leaves `fma0`), the SAME cooling gate NEVER admits: justness is exactly the hypothesis separating
the cooled future from the eternal stutter. (The temporal face of `badSched_not_just`.) -/
theorem cooling_starves_without_justness (rec : Value) :
    ¬ Eventually (fun x => (TemporalAtom.cooledSince 0 2).eval x.log.length rec = true)
        fma0 badSched := by
  rintro ⟨n, hn⟩
  rw [badSched_traj_const n] at hn
  rw [cooledSince_refuses_inside (by decide) rec] at hn
  exact Bool.false_ne_true hn

-- §4 non-vacuity, executed: the clock genuinely ticks, the gate genuinely flips along the path.
#guard ((trajA fma0 emitSched 0).log.length == 0)
#guard ((trajA fma0 emitSched 2).log.length == 2)
#guard ((TemporalAtom.cooledSince 0 2).eval (trajA fma0 emitSched 0).log.length tRec) == false
#guard (TemporalAtom.cooledSince 0 2).eval (trajA fma0 emitSched 2).log.length tRec

/-! ## §5 — Axiom-hygiene tripwires (every keystone pinned to the three kernel axioms). -/

#assert_axioms until_since_complement
#assert_axioms flagClock_flag_mono
#assert_axioms sinceEvent_iff_AG
#assert_axioms until_holds_EU_flip
#assert_axioms untilEvent_admits_to_EU
#assert_axioms until_mu_formula
#assert_axioms flip_not_inevitable
#assert_axioms since_flip_in_past
#assert_axioms close_write_flips_gates
#assert_axioms committed_flip_write_steps_flagClock
#assert_axioms eventStateStepGuarded_eq
#assert_axioms eventStateStepGuarded_nil_eq
#assert_axioms eventStateStepGuarded_violation_fails
#assert_axioms event_state_conserves
#assert_axioms causal_deadline_implies_height_gate
#assert_axioms demo_precedes_ne_g0
#assert_axioms demo_precedes_lookup_right
#assert_axioms height_cannot_recover_causal
#assert_axioms frame_deadline_embeds_afterHeight
#assert_axioms afterHeight_is_chain_frame_deadline
#assert_axioms unlockedCount_le
#assert_axioms unlockedCount_all
#assert_axioms vesting_admits_iff_prefix
#assert_axioms vesting_prefix_closed
#assert_axioms auction_phases_exclusive
#assert_axioms settle_sees_all_reveals
#assert_axioms revealAdmits_decomposes
#assert_axioms reveal_no_late_switching
#assert_axioms settle_sees_valid_reveals
#assert_axioms rateBound_meet
#assert_axioms rateBound_mono
#assert_axioms withinWindow_widen
#assert_axioms nested_rate_gate_refines
#assert_axioms withinWindow_split
#assert_axioms cooledSince_eventually_admits_of_just
#assert_axioms afterHeight_eventually_admits_of_just
#assert_axioms emit_traj1_log
#assert_axioms emit_traj2_log
#assert_axioms Bcool_interferes_emitFar
#assert_axioms cooling_liveness_demo
#assert_axioms cooling_starves_without_justness

end Dregg2.Authority.TemporalAlgebra2
