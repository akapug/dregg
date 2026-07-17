/-
# Metatheory.PolisStreamCarrier — the StreamProp carrier bound to the DEPLOYED adversary stream.

`Metatheory.PolisCrossCell` built the *generic* shared-carrier framework (gpt5.5's answer to Q6,
`docs/POLIS-HYPERPROPERTY-FRONTIER.md`): the polis anti-capture floor and circuit cross-cell
soundness are NOT the same property, but they share a CARRIER — properties of public interleaved
adversary STREAMS. This file makes that carrier CONCRETE by binding it to the deployed object:
`Dregg2.Proof.CoinductiveAdversary.obsStream`, the observation trajectory the live `TurnCoalg`
emits as the coinductive unbounded-interleaving adversary drives it along a `Sched`.

We then define TWO SEPARATE `StreamProp`-style predicates over that one carrier:

  * **`circuitSoundnessProp`** — the deployed circuit guarantee: the implementation's observation
    stream coincides, tick-for-tick, with the golden oracle's stream (confluence-up-to-bisimulation,
    `obsStream_eq_of_bisim`). A property of the observable trace alone.
  * **`polisFloorProp`** — the polis anti-capture floor: an exported, public, decidable floor on
    observations holds at EVERY tick of the stream (the trace-shape bar, never the interior).

These are kept **DISTINCT defs over the same carrier** — they are NEVER identified. This is the
load-bearing caution (gpt5.5's): collapsing them would let circuit confluence (an implementation
matches its oracle) masquerade as anti-tyranny (a subject's floor is never foreclosed), a false
claim. `same_carrier_distinct_predicates` records that they range over the same `Nat → Obs`
carrier and reuse the same `Monitorable` decision machinery, while `not_identified` exhibits a
model where one holds and the other fails — they are genuinely different stream properties.

## HONESTY FRAMING

This is a **BOUNDED / PUBLIC / DECIDABLE** binding: each predicate is a property of the public
observation stream `obsStream`, and the shared decision fragment is the finite-prefix
`Monitorable` witness (`violation_has_finite_witness`) — a finite public bad-prefix governs a
violation. It is NOT "full politics solved", but the temporal monitor IS now built: a `Monitorable`
witness for the polis floor over the deployed `Obs` is `Metatheory.PolisMonitor.polisFloorMonitor`,
and the flow floor's bad-prefix is decided by the Büchi game `FlowRefine.decideRefines`
(`PolisMonitor.flowBad_iff_decide`). The only TERMINAL item is unbounded liveness, *proven*
non-monitorable (`PolisMonitor.liveness_not_prefix_refutable`). What is delivered here is the
binding — the two distinct predicates over the deployed
carrier, plus a non-vacuity model and the shared-machinery / non-collapse record.

On the polis floor's non-vacuity specifically: the `∀ Impl x s`-shaped inhabitation is available ONLY
at the trivial floor `fun _ => True`, and §5a PROVES that no stronger floor exists at that shape
(`polisFloorProp_forall_shape_iff_trivial` — such a statement carries exactly the information of
`True`). The load-bearing non-vacuity is therefore the existential, concrete-carrier one:
`polisFloorProp_inhabited_nontrivial` (§5b) inhabits the floor at a predicate that genuinely fails on
some observation, and exhibits a captured cell that VIOLATES it — so the floor is a real bar over the
deployed carrier, refutable as well as satisfiable.

Imports the deployed `Dregg2.Proof.CoinductiveAdversary` and the framework
`Metatheory.PolisCrossCell`; no `:= True` load-bearing (the one `fun _ => True` present is *named* as
trivial and proven to be the shape's ceiling, not passed off as content).
-/
import Dregg2.Proof.CoinductiveAdversary
import Polis.PolisCrossCell

namespace Metatheory.PolisStreamCarrier

open Dregg2.Boundary (TurnCoalg IsBisim bisim_eq)
open Dregg2.Proof.CoinductiveAdversary
open Metatheory.PolisCrossCell (StreamProp Monitorable violation_has_finite_witness)

-- `PolisCrossCell.StreamProp` is defined at universe 0 (`variable {Event : Type}`), so the
-- carrier type `Obs` lives at `Type` (universe 0). `AdmissibleTurn` matches the deployed
-- `CoinductiveAdversary` signatures at the same level.
variable {Obs AdmissibleTurn : Type}

/-! ## §1 — The shared carrier IS the deployed `obsStream`.

`PolisCrossCell.StreamProp Event := (Nat → Event) → Prop`. The deployed
`CoinductiveAdversary.obsStream Impl x s : ℕ → Obs` is exactly an `Event = Obs` carrier: the
public observation trajectory the live cell emits as the coinductive adversary drives it along the
schedule `s`. Both frontiers (circuit soundness, polis floor) are predicates of THIS object. -/

/-- **`carrier Impl x s`** — the shared carrier as the DEPLOYED observation stream. This is the one
`Nat → Obs` object both `circuitSoundnessProp` and `polisFloorProp` are predicates of; it is
literally `CoinductiveAdversary.obsStream` (the badge the `TurnCoalg` emits per adversary tick). -/
def carrier (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier)
    (s : Sched AdmissibleTurn) : Nat → Obs :=
  obsStream Impl x s

@[simp] theorem carrier_eq_obsStream (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier)
    (s : Sched AdmissibleTurn) : carrier Impl x s = obsStream Impl x s := rfl

/-! ## §2 — Predicate ONE: circuit cross-cell soundness over the carrier.

A `StreamProp Obs` (= `(Nat → Obs) → Prop`). The deployed circuit guarantee is
`obsStream_eq_of_bisim`: the implementation's observation stream EQUALS the golden oracle's stream
at every tick along the unbounded adversarial schedule. We express that as a stream property
parameterised by the oracle's reference stream `golden`. -/

/-- **`circuitSoundnessProp golden`** — the circuit cross-cell soundness predicate, over the shared
carrier. `circuitSoundnessProp golden σ` holds iff the stream `σ` coincides tick-for-tick with the
golden-oracle reference stream `golden`: confluence-up-to-bisimulation made observable. This is a
property of the *trace*, never the interior — the vat boundary cannot tell `σ` from the oracle. -/
def circuitSoundnessProp (golden : Nat → Obs) : StreamProp Obs :=
  fun σ => ∀ n, σ n = golden n

/-- The deployed `obsStream_eq_of_bisim` discharges `circuitSoundnessProp` for the live carrier:
if a `Boundary.IsBisim` relates the implementation cell `x` to the oracle cell `y`, then the
deployed `carrier`/`obsStream` satisfies `circuitSoundnessProp` against the oracle's own stream. -/
theorem circuitSoundnessProp_of_bisim
    {Impl Spec : TurnCoalg Obs AdmissibleTurn} {R : Impl.Carrier → Spec.Carrier → Prop}
    (hR : IsBisim Impl Spec R) {x : Impl.Carrier} {y : Spec.Carrier} (hxy : R x y)
    (s : Sched AdmissibleTurn) :
    circuitSoundnessProp (obsStream Spec y s) (carrier Impl x s) := by
  intro n
  have h := obsStream_eq_of_bisim hR hxy s
  simp only [carrier]
  exact congrFun h n

/-! ## §3 — Predicate TWO: the polis anti-capture floor over the carrier.

A SEPARATE `StreamProp Obs`. The polis floor is a public, exported, decidable predicate on
*observations* (`floor : Obs → Prop`, the trace-shape bar of `Metatheory.Polis` — never the
interior) that must hold at EVERY tick of the stream. The politician lives in the trace: a captured
subject is one whose floor is foreclosed at some tick. -/

/-- **`polisFloorProp floor`** — the polis anti-capture floor predicate, over the shared carrier.
`polisFloorProp floor σ` holds iff the public floor `floor` holds at EVERY tick of `σ`. This is the
trace-shape bar (a subject's exported floor over public observations) lifted to the unbounded
adversarial stream: anti-foreclosure forever. Distinct from `circuitSoundnessProp` — it speaks of a
subject-owned floor on each observation, not of agreement with an oracle. -/
def polisFloorProp (floor : Obs → Prop) : StreamProp Obs :=
  fun σ => ∀ n, floor (σ n)

/-- The deployed coinductive carrier carries a tick-local floor along the WHOLE unbounded schedule
when the floor is preserved by the live step (the safety face). This reuses the deployed
`stepComplete_carries_infinite` shape: a floor that holds at the start and is re-established each
tick holds at every `obsStream` tick. Here we take the direct route over `obsStream`/`traj`: if the
floor on observations holds at every trajectory point, it holds at every carrier tick. -/
theorem polisFloorProp_of_pointwise
    (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier) (s : Sched AdmissibleTurn)
    (floor : Obs → Prop)
    (hpt : ∀ n, floor (Impl.obs (traj Impl x s n))) :
    polisFloorProp floor (carrier Impl x s) := by
  intro n
  simp only [carrier, obsStream]
  exact hpt n

/-- The polis floor as a stream property is exactly the per-tick floor over the deployed
`obsStream` — the binding is definitional (no interior, public observations only). -/
theorem polisFloorProp_carrier_unfold
    (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier) (s : Sched AdmissibleTurn)
    (floor : Obs → Prop) :
    polisFloorProp floor (carrier Impl x s) ↔ ∀ n, floor (Impl.obs (traj Impl x s n)) :=
  Iff.rfl

/-! ## §4 — SAME carrier, SEPARATE predicates — the non-collapse record (gpt5.5's caution).

The two predicates above range over the SAME carrier type `Nat → Obs` (and, when instantiated, the
SAME deployed `carrier`/`obsStream` object) and reuse the SAME `Monitorable` finite-prefix decision
machinery. They are NEVER identified. Collapsing them would let circuit confluence (an impl matches
its oracle) masquerade as anti-tyranny (a subject's floor is never foreclosed). We record both
facts: shared carrier/machinery, and a model that distinguishes them. -/

/-- The two predicates have the SAME carrier type: both are `StreamProp Obs = (Nat → Obs) → Prop`.
A trivial-but-load-bearing type-level witness that they are predicates of one carrier. -/
theorem same_carrier_distinct_predicates (golden : Nat → Obs) (floor : Obs → Prop) :
    (circuitSoundnessProp golden : StreamProp Obs) = circuitSoundnessProp golden ∧
    (polisFloorProp floor : StreamProp Obs) = polisFloorProp floor :=
  ⟨rfl, rfl⟩

/-- Both predicates plug into the SAME shared decision fragment: given a `Monitorable` witness for
either, a violation has a finite public bad prefix (`violation_has_finite_witness`). The decision
machinery is shared; the predicates are not. -/
theorem shared_decision_machinery {P : StreamProp Obs} (M : Monitorable P)
    (σ : Nat → Obs) (h : ¬ P σ) : ∃ n, M.bad σ n :=
  violation_has_finite_witness M σ h

/-- **`not_identified` — the two predicates are GENUINELY DIFFERENT.** Over `Obs = Bool` we exhibit
one carrier and floors where `circuitSoundnessProp` HOLDS but `polisFloorProp` FAILS: the impl
stream equals the oracle (circuit-sound) yet every tick violates the polis floor (the subject is
fully foreclosed). So `circuitSoundnessProp golden = polisFloorProp floor` is FALSE — collapsing
them is unsound, exactly the over-claim gpt5.5 warned against (confluence ≠ anti-tyranny). -/
theorem not_identified :
    ∃ (golden : Nat → Bool) (floor : Bool → Prop),
      (circuitSoundnessProp golden ≠ polisFloorProp floor) := by
  -- golden = all-false; floor = "is true". The all-false stream is circuit-sound vs golden
  -- (it equals it), but violates the floor at every tick. So one holds where the other fails.
  refine ⟨(fun _ => false), (fun b => b = true), ?_⟩
  intro heq
  -- `circuitSoundnessProp (fun _ => false) (fun _ => false)` holds (the stream equals golden).
  have hsound : circuitSoundnessProp (fun _ => false) (fun _ : Nat => false) := fun _ => rfl
  -- but rewriting by the (assumed) equality of the *predicates* gives the floor at every tick.
  have hfloor : polisFloorProp (fun b => b = true) (fun _ : Nat => false) := by
    rw [← heq]; exact hsound
  -- contradiction: floor at tick 0 says `false = true`.
  exact absurd (hfloor 0) (by decide)

/-! ## §5 — Non-vacuity on the deployed carrier (both predicates inhabited).

So this is not a "beautiful but empty" binding: each predicate genuinely holds for the deployed
carrier in a concrete model.

⚑ The two legs are NOT equally strong, and the difference is worth stating plainly.
`circuitSoundnessProp_inhabited` is real: it discharges the predicate through the deployed
`obsStream_eq_of_bisim` at the `∀`-shape. Its sibling `polisFloorProp_inhabited_trivial_floor` is
inhabited only at `fun _ => True` — and §5a *proves* that this is not a shortfall of effort but of
SHAPE: over an abstract `Obs`, the `∀ Impl x s` quantifier admits no non-trivial floor whatsoever
(`polisFloorProp_forall_shape_iff_trivial`). §5b then supplies the honest leg the `∀`-shape cannot:
an EXISTENTIAL, concrete-carrier inhabitation at a floor that genuinely discriminates, with both
polarities — the same move `not_identified` (§4) already makes. -/

/-- `circuitSoundnessProp` is inhabited on the deployed carrier: by reflexivity of bisimulation
(`bisim_eq`), the live cell's `obsStream` is circuit-sound against its OWN stream (the impl is its
own oracle — the diagonal). Uses the deployed `obsStream_eq_of_bisim` via `circuitSoundnessProp_of_bisim`. -/
theorem circuitSoundnessProp_inhabited (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier)
    (s : Sched AdmissibleTurn) :
    circuitSoundnessProp (obsStream Impl x s) (carrier Impl x s) :=
  circuitSoundnessProp_of_bisim (bisim_eq Impl) rfl s

/-- `polisFloorProp` is inhabited on the deployed carrier **at the TRIVIAL floor** `fun _ => True`,
which holds at every tick of any `obsStream`. Read the statement, not the name: this says almost
nothing — and `polisFloorProp_forall_shape_forces_trivial` below proves that it *cannot* say more,
because the `∀ Impl x s` shape admits NO non-trivial floor at all. The honest inhabitation, at a floor
that genuinely discriminates, is `polisFloorProp_inhabited_nontrivial` (§5b); the general non-vacuity
route for a real floor is `polisFloorProp_of_pointwise`, and its monitor is
`PolisMonitor.polisFloorMonitor` (§6). -/
theorem polisFloorProp_inhabited_trivial_floor (Impl : TurnCoalg Obs AdmissibleTurn)
    (x : Impl.Carrier) (s : Sched AdmissibleTurn) :
    polisFloorProp (fun _ => True) (carrier Impl x s) :=
  fun _ => trivial

/-! ### §5a — WHY the `∀`-shape is stuck at `fun _ => True` (the triviality is PROVEN, not pleaded).

It would be easy to excuse the `fun _ => True` above as an unavoidable consequence of `Obs` being
abstract. That excuse is checkable, so we check it: `echoCell` is a legitimate `TurnCoalg` whose
tick-`0` observation is *any* chosen `o : Obs`, so a floor that holds on every deployed carrier must
hold on every observation whatsoever — i.e. it is `True` up to `Iff`. The `∀`-shape is therefore
UNSTRENGTHENABLE: it is not that we did not try, it is that there is nothing there.

That is an indictment of the SHAPE, not a licence. The fix is the one `not_identified` (§4) already
uses: quantify EXISTENTIALLY over a concrete carrier. §5b does exactly that. -/

/-- The **echo cell** — a legitimate deployed `TurnCoalg` that emits its own state and is driven along
any schedule. Its tick-`0` observation is whatever start state it is handed, which is what makes the
`∀`-shape collapse. -/
def echoCell : TurnCoalg Obs AdmissibleTurn where
  Carrier := Obs
  step := fun w => (w, fun _ => w)

/-- **`polisFloorProp_forall_shape_forces_trivial`** — the `∀ Impl x s` shape admits ONLY the trivial
floor. If a floor holds at every tick of EVERY deployed carrier, then it holds of EVERY observation:
instantiate at `echoCell` started at `o` and read tick `0`. So `polisFloorProp_inhabited_trivial_floor`
is not merely stated at `fun _ => True` — at that shape, no other floor is available, and any
"`∀`-inhabitation" result is exactly as strong as `True`. (Needs one inhabitant `t` of
`AdmissibleTurn`, to have a schedule to run.) -/
theorem polisFloorProp_forall_shape_forces_trivial (t : AdmissibleTurn) (floor : Obs → Prop)
    (h : ∀ (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier) (s : Sched AdmissibleTurn),
        polisFloorProp floor (carrier Impl x s)) :
    ∀ o, floor o :=
  fun o => h echoCell o (fun _ => t) 0

/-- The collapse as an `Iff`: at the `∀`-shape, "the floor is inhabited on every deployed carrier" is
EQUIVALENT to "the floor is trivially true everywhere". No information is carried by such a statement.
-/
theorem polisFloorProp_forall_shape_iff_trivial (t : AdmissibleTurn) (floor : Obs → Prop) :
    (∀ (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier) (s : Sched AdmissibleTurn),
        polisFloorProp floor (carrier Impl x s)) ↔ (∀ o, floor o) :=
  ⟨polisFloorProp_forall_shape_forces_trivial t floor, fun h _ _ _ n => h _⟩

/-! ### §5b — The HONEST inhabitation: a non-trivial floor, on a concrete deployed carrier.

Following `not_identified`'s pattern (§4), we drop to a concrete `Obs = Bool` where a floor can
actually discriminate. `boolFloor b := (b = true)` reads "the subject is NOT foreclosed at this tick";
it genuinely FAILS at `false`, so it is not `True` in disguise. We then exhibit BOTH polarities on the
deployed `obsStream`, driven along an ARBITRARY unbounded adversarial schedule:

  * a COMPLIANT cell whose stream satisfies the floor at every tick — real inhabitation;
  * a CAPTURED cell whose stream VIOLATES it — so the predicate is refutable on the deployed carrier,
    i.e. it is a genuine bar and not a tautology.

Both cells count schedule ticks in their state, so the adversary really drives them. -/

section NonTrivialFloor

/-- The polis floor over a concrete `Obs = Bool`: the subject is not foreclosed at this tick. -/
def boolFloor : Bool → Prop := fun b => b = true

/-- The floor is NON-TRIVIAL: it genuinely fails at an observation. Not `True` in disguise. -/
theorem boolFloor_nontrivial : ∃ b, ¬ boolFloor b := ⟨false, by simp [boolFloor]⟩

/-- A **COMPLIANT** deployed cell: its state counts adversary ticks (so the schedule really drives
it), and it never forecloses the subject — it emits `true` at every tick. -/
def compliantCell : TurnCoalg Bool Unit where
  Carrier := Nat
  step := fun n => (true, fun _ => n + 1)

/-- A **CAPTURED** deployed cell: same shape, same adversary, but the subject is foreclosed — it
emits `false`. -/
def capturedCell : TurnCoalg Bool Unit where
  Carrier := Nat
  step := fun n => (false, fun _ => n + 1)

/-- Start states (the cells' carriers are `Nat`; named so numerals elaborate against the field). -/
def compliantStart : compliantCell.Carrier := (0 : Nat)
/-- The captured cell's start state. -/
def capturedStart : capturedCell.Carrier := (0 : Nat)

/-- **`polisFloorProp_inhabited_nontrivial`** — the honest replacement for the `fun _ => True`
inhabitation. On a CONCRETE deployed carrier the polis floor is inhabited at a floor that genuinely
discriminates, and it is REFUTABLE there too:

  1. `boolFloor` fails at some observation (it is not `True` in disguise);
  2. the compliant cell's deployed `obsStream` satisfies it at EVERY tick, along ANY unbounded
     adversarial schedule;
  3. the captured cell's deployed `obsStream` VIOLATES it — the floor is a real bar, and
     `polisFloorProp` is not a tautology over the carrier.

Together (2)+(3) say `polisFloorProp boolFloor` separates deployed cells: exactly the content the
`∀`-shape provably cannot carry (§5a). -/
theorem polisFloorProp_inhabited_nontrivial :
    (∃ b, ¬ boolFloor b)
    ∧ (∀ s : Sched Unit, polisFloorProp boolFloor (carrier compliantCell compliantStart s))
    ∧ (∀ s : Sched Unit, ¬ polisFloorProp boolFloor (carrier capturedCell capturedStart s)) := by
  refine ⟨boolFloor_nontrivial, fun s n => rfl, fun s hcap => ?_⟩
  -- The captured cell emits `false` at tick 0, so its floor obligation there IS `false = true`.
  have h0 : boolFloor (carrier capturedCell capturedStart s 0) := hcap 0
  exact Bool.noConfusion (h0 : (false : Bool) = true)

end NonTrivialFloor

/-! ## §6 — Carrier bound; the monitor is CLOSED.

What is BOUND here: the carrier (deployed `obsStream`), and the two distinct stream predicates over
it, with their deployed discharge lemmas (`circuitSoundnessProp_of_bisim` from
`obsStream_eq_of_bisim`; `polisFloorProp_of_pointwise` from the per-tick observation floor), the
non-collapse record (`not_identified`), and the shared decision fragment
(`shared_decision_machinery`).

What WAS the frontier, now CLOSED (`Metatheory.PolisMonitor`): `polisFloorMonitor floor :
Monitorable (polisFloorProp floor)` — every violation of the temporal floor over the deployed
`obsStream` has a FINITE public bad-prefix witness (`polisFloor_violation_has_finite_witness`); and
the flow-policy floor's bad-prefix is DECIDED by the deployed Büchi game `FlowRefine.decideRefines`
(`PolisMonitor.flowBad_iff_decide`). The ONLY thing left is genuinely TERMINAL, not a TODO:
unbounded liveness is *proven* non-monitorable (`PolisMonitor.liveness_not_prefix_refutable`) and
belongs to charters/appeal, not the kernel. -/

/-! ## Axiom hygiene — the carrier's non-vacuity keystones. -/

#print axioms not_identified
#print axioms polisFloorProp_inhabited_nontrivial
#print axioms polisFloorProp_forall_shape_forces_trivial
#print axioms polisFloorProp_forall_shape_iff_trivial
#print axioms circuitSoundnessProp_inhabited

end Metatheory.PolisStreamCarrier
