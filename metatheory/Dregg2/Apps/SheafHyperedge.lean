/-
# Dregg2.Apps.SheafHyperedge — the bridge: a Hyperedge IS a distributed-knowledge frame.

This module THREADS the H¹-Byzantine epistemic sheaf (`Dregg2.Apps.EpistemicSheaf`) onto the
n-ary atomic joint-turn's incidence set (`Dregg2.Hyperedge`). It realizes the frontier
`DREGG4-HYPERSYSTEM.md §5.2` named as "the remaining frontier": *connect the two complexes* so
that **Agreement = distributed knowledge** is a machine-checked theorem, not paper-anchored
commentary.

The two objects bridged are both already built and proved axiom-clean:

  * COMPLEX 2 (the interaction complex): a `Hyperedge ι T turnId halfEdge` — the wide pullback
    over `TurnId`, with N legs `agree i` all factoring through ONE apex `tid` (`Hyperedge.lean`).
  * The epistemic side (Kripke-S5): `Frame`/`DistKnows`/`Honest` — distributed knowledge
    `D_B φ = ∩_{a∈B} ∼_a` and the H¹ Byzantine non-gluing (`EpistemicSheaf.lean`, the
    arXiv:2311.01351 port).

## The bridge, in one sentence

**The legs of a joint turn are the agents/sites of an epistemic frame; the apex turn-id is the
proposition; and `Hyperedge.agree`/`Hyperedge.legs_agree` — every leg factoring through the one
apex — is *literally* the statement that the honest legs have DISTRIBUTED KNOWLEDGE of `tid`.**

## What is realized (REAL, proved, `#assert_axioms`-clean)

  1. **The instantiation** (`obsFrame`): `EpistemicSheaf.Frame`'s machinery AT a hyperedge's
     incidence set. Worlds are candidate global states `ι → TurnId` (each leg's committed id);
     leg `i`'s indistinguishability `∼ᵢ` sees only its own component (the paper's `D_B = ∩∼_a`);
     the apex's binding becomes the proposition `apexKnown tid`.
  2. **The bridge theorem** (`agreement_is_distributed_knowledge`): `DistKnows F.Honest
     (apexKnown H.tid) F.actual` is DERIVED from `H.agree` (equivalently `H.legs_agree`). "When
     the honest legs of a joint turn agree, the apex proposition IS distributed knowledge among
     them" — Agreement = distributed knowledge, as code.
  3. **The dual direction (the fork = H¹)** (`fork_has_no_distributed_apex`): a genuine fork —
     legs that cannot be glued, i.e. observations with no shared apex — admits NO distributed
     knowledge of any apex. This connects a hyperedge non-gluing to `EpistemicSheaf`'s H¹
     obstruction (`byzantine_section_does_not_glue` / `fork_is_genuine`): a real `Hyperedge`
     CANNOT exhibit a fork (the apex forces `legs_agree`), so the fork lives exactly where the
     hyperedge does not — the missing global section.
  4. **Non-vacuity both polarities** (`#guard` + proved examples): a concrete small hyperedge
     where the legs agree ⇒ `DistKnows` follows; and a concrete disagreeing leg-family ⇒ no
     distributed knowledge.

## Honesty label

**REAL (proved here):** the instantiation, the bridge `legs_agree ⟹ DistKnows`, and the fork
non-gluing ⟹ no-distributed-apex, all `#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}`.

**ESTABLISHED (cited, not re-claimed):** "distributed knowledge = shared higher face" and "fork =
H¹ obstruction" are the arXiv:2311.01351 framing (used via `EpistemicSheaf`); we make the
*Hyperedge-side* identification a theorem and cite the framing.

**OUT OF SCOPE (named, not built):** the cohomology objects as objects (a Čech complex / `H⁰`/`H¹`
groups / a simplicial `face_map`) — exactly as `EpistemicSheaf` declines them. We bridge the
*content* (the gluing / non-gluing), not the named coboundary.

CITATION: `Dregg2.Apps.EpistemicSheaf` (the ported frame), `Dregg2.Hyperedge` (the wide pullback),
`.docs-history-noclaude/rebuild/dregg2-design/DREGG4-HYPERSYSTEM.md §5.2` (the frontier this closes).
-/
import Dregg2.Hyperedge
import Dregg2.Apps.EpistemicSheaf

namespace Dregg2.Apps.SheafHyperedge

open Dregg2.Boundary Dregg2.JointTurn Dregg2.Hyperedge
open Dregg2.Apps.EpistemicSheaf

/- Universe note: `EpistemicSheaf.Frame (Ω ι : Type)` is `Type`-valued (universe 0), so the whole
bridge lives at `Type`. Every concrete instance we need (`Fin n`, `ℕ`, `Unit`, `ℤ`, and the
hyperedge layer parameters when instantiated) is in `Type 0`, and `Hyperedge`'s universe-polymorphic
results specialize to it without loss. -/

/-! ## 1. The instantiation — an epistemic `Frame` AT a leg-observation family.

We build the bridge in two layers. First, the **general** layer over a bare observation family
`legObs : ι → TurnId` (what each leg committed): this is the honest minimal data the epistemic
frame needs, and it lets us exhibit BOTH polarities (agreement and the fork) without fabricating a
`Hyperedge` for the fork case (a fork is precisely the configuration with no shared apex, hence no
`Hyperedge`). Then we specialize to a `Hyperedge`, where `H.agree` supplies the agreement.

The construction follows the paper (Goubault–Kniazev–Ledent–Rajsbaum, arXiv:2311.01351) exactly:

  * **Worlds** `Ω := ι → TurnId` — a candidate *global state*: an assignment of a committed
    turn-id to every leg (the paper's global states = facets; each component is a vertex/local
    state). The **actual** world is the family `legObs` of what the legs really committed.
  * **Indistinguishability** `∼ᵢ`: leg `i` confuses two global states iff they agree on *its own*
    component (`a i = b i`) — leg `i` sees only its local state. This is the paper's per-agent
    relation; distributed knowledge `D_B = ∩_{i∈B} ∼ᵢ` then pools the legs' perspectives.
  * **Faulty/Honest**: carried verbatim from `EpistemicSheaf.Frame`. -/

/-- **`obsFrame legObs Faulty` — the epistemic frame of a leg-observation family.** The
incidence set `ι` is the agent set; worlds are candidate global states `ι → TurnId`; the actual
world is the legs' real committed ids `legObs`; leg `i`'s `∼ᵢ` sees only component `i`. This is
`EpistemicSheaf.Frame` instantiated at the joint-turn's incidence set. -/
def obsFrame {ι : Type} {TurnId : Type}
    (legObs : ι → TurnId) (Faulty : ι → Prop) :
    Frame (ι → TurnId) ι where
  actual := legObs
  Indist := fun i a b => a i = b i
  Faulty := Faulty

/-- **`apexKnown tid` — the apex binding AS a proposition (world-set).** The world-set "every
honest leg's component equals `tid`" — i.e. the candidate global state agrees with the shared
apex `tid` at every honest vertex. This is the apex's binding (`Hyperedge.agree`) read as the
`EpistemicSheaf.Frame.Prop'` the legs come to know. (Restricting to honest legs is essential: a
faulty leg may commit to anything, so the *knowable* proposition is the honest-restricted one —
exactly the paper's "the honest group's distributed knowledge".) -/
def apexKnown {ι : Type} {TurnId : Type}
    (Faulty : ι → Prop) (tid : TurnId) : (ι → TurnId) → Prop :=
  fun w => ∀ i, ¬ Faulty i → w i = tid

/-! ## 2. The bridge theorem — Agreement IS distributed knowledge.

The general keystone first (over `legObs`), then its specialization to a `Hyperedge` (the headline
`agreement_is_distributed_knowledge`), and the variant phrased through `legs_agree` literally. -/

/-- **`obs_agreement_is_distributed_knowledge` — the general bridge keystone.** If every honest
leg observes the same shared id `tid`, then `apexKnown tid` is **distributed knowledge** of the
honest legs at the actual world. This is the `D_B` clause discharged directly: the only worlds an
honest-leg-pool confuses with `actual` agree with `actual` on every honest component, and there
`actual i = legObs i = tid`. The honest legs *pool* their single-component perspectives to pin the
apex. -/
theorem obs_agreement_is_distributed_knowledge
    {ι : Type} {TurnId : Type}
    (legObs : ι → TurnId) (Faulty : ι → Prop) (tid : TurnId)
    (hagree : ∀ i, ¬ Faulty i → legObs i = tid) :
    (obsFrame legObs Faulty).DistKnows (obsFrame legObs Faulty).Honest
      (apexKnown Faulty tid) (obsFrame legObs Faulty).actual := by
  -- `DistKnows B φ w = ∀ w', (∀ i, B i → Indist i w' w) → φ w'`; unfold and discharge per honest leg.
  intro w' hconf j hj
  -- `hj : ¬ Faulty j` is honesty of leg `j`; `hconf j hj : w' j = actual j = legObs j`.
  have hwj : w' j = legObs j := hconf j hj
  -- and `legObs j = tid` because leg `j` is honest (`hagree`).
  rw [hwj]
  exact hagree j hj

/-- **`agreement_is_distributed_knowledge` — THE BRIDGE (Hyperedge ⟹ distributed knowledge).**
Instantiate the epistemic frame at a hyperedge's incidence set via the leg-observation family
`legObs i := turnId i (T.next (H.x i) H.t)` (what leg `i` committed). Then `DistKnows F.Honest
(apexKnown H.tid) F.actual` is a **derived theorem** — because every leg's `H.agree i` says it
committed to the one apex `H.tid`. This realizes `DREGG4-HYPERSYSTEM §5.2`: *the honest legs of a
joint turn agreeing IS the apex being distributed knowledge among them.* Agreement = distributed
knowledge, as code. -/
theorem agreement_is_distributed_knowledge
    {ι : Type} [Fintype ι] {Obs AdmissibleTurn TurnId Bal : Type} [AddCommMonoid Bal]
    {T : TurnCoalg Obs AdmissibleTurn}
    {turnId : ι → TurnIdOf (TurnId := TurnId) T}
    {halfEdge : ι → HalfEdgeOf (Bal := Bal) T}
    (H : Hyperedge ι T turnId halfEdge) (Faulty : ι → Prop) :
    (obsFrame (fun i => turnId i (T.next (H.x i) H.t)) Faulty).DistKnows
      (obsFrame (fun i => turnId i (T.next (H.x i) H.t)) Faulty).Honest
      (apexKnown Faulty H.tid)
      (obsFrame (fun i => turnId i (T.next (H.x i) H.t)) Faulty).actual :=
  -- every leg (honest or not) factors through the apex: `H.agree i : legObs i = H.tid`.
  obs_agreement_is_distributed_knowledge _ Faulty H.tid (fun i _ => H.agree i)

/-- **`legs_agree_is_distributed_knowledge` — the bridge, routed LITERALLY through `legs_agree`.**
The same conclusion as `agreement_is_distributed_knowledge`, but the proof's hinge is made the
explicit pairwise-agreement theorem `Hyperedge.legs_agree`: distributed knowledge of `tid` reduces,
honest leg by honest leg, to "leg `j` agrees with the reference leg `i₀` (`legs_agree j i₀`), which
itself commits to `tid` (`H.agree i₀`)". This is the form `DREGG4-HYPERSYSTEM §5.2` calls out —
`legs_agree` ⟹ distributed-knowledge of the apex is *derived, not narrated*. The reference leg `i₀`
need NOT be honest: the wide-pullback apex forces EVERY leg through `tid` (that is exactly the
content of `legs_agree` — pairwise agreement is structural, not just epistemic), so any incidence
anchors the pool. The honesty restriction lives only on `j` (the proposition `apexKnown`), via the
`hconf j hj` confusability of an honest leg's own component. -/
theorem legs_agree_is_distributed_knowledge
    {ι : Type} [Fintype ι] {Obs AdmissibleTurn TurnId Bal : Type} [AddCommMonoid Bal]
    {T : TurnCoalg Obs AdmissibleTurn}
    {turnId : ι → TurnIdOf (TurnId := TurnId) T}
    {halfEdge : ι → HalfEdgeOf (Bal := Bal) T}
    (H : Hyperedge ι T turnId halfEdge) (Faulty : ι → Prop)
    (i₀ : ι) :
    (obsFrame (fun i => turnId i (T.next (H.x i) H.t)) Faulty).DistKnows
      (obsFrame (fun i => turnId i (T.next (H.x i) H.t)) Faulty).Honest
      (apexKnown Faulty H.tid)
      (obsFrame (fun i => turnId i (T.next (H.x i) H.t)) Faulty).actual := by
  intro w' hconf j hj
  -- leg `j`'s component in any honest-confusable world equals its real commitment.
  have hwj : w' j = turnId j (T.next (H.x j) H.t) := hconf j hj
  rw [hwj]
  -- THE HINGE: `legs_agree` makes leg `j`'s commitment equal the reference leg `i₀`'s …
  have hpair : turnId j (T.next (H.x j) H.t) = turnId i₀ (T.next (H.x i₀) H.t) :=
    H.legs_agree j i₀
  -- … and the reference leg `i₀` commits to the apex `H.tid` (`H.agree i₀`).
  rw [hpair]
  exact H.agree i₀

/-! ## 3. The dual direction — the fork is the H¹ obstruction (no distributed apex).

A *genuine fork* is the configuration `EpistemicSheaf` models as a witnessed NON-GLUING
(`byzantine_section_does_not_glue` / `fork_is_genuine`): two legs that are each locally valid yet
report DIFFERENT boundary values, so no global section exists. On the hyperedge side this is
**precisely the absence of a shared apex**: if two honest legs' observations differ, there is no
`tid` they both commit to — equivalently NO `Hyperedge` over this leg-family (a real `Hyperedge`
forces `legs_agree`, killing the fork). We prove the epistemic shadow of that: a disagreeing
honest-leg-family has NO distributed knowledge of *any* apex. This is the H¹ class — the missing
H⁰ global section. -/

/-- **`distributed_apex_forces_agreement` — distributed knowledge of an apex ⟹ the honest legs
agree on it.** The converse engine of the bridge: if `apexKnown tid` is distributed knowledge at
the actual world, then every honest leg already observed `tid` (take the witness world `w' :=
actual`, which every leg trivially confuses with itself). So distributed knowledge of an apex is
exactly a *filled* simplex — all honest legs factor through the one shared face. -/
theorem distributed_apex_forces_agreement
    {ι : Type} {TurnId : Type}
    (legObs : ι → TurnId) (Faulty : ι → Prop) (tid : TurnId)
    (hdk : (obsFrame legObs Faulty).DistKnows (obsFrame legObs Faulty).Honest
            (apexKnown Faulty tid) (obsFrame legObs Faulty).actual) :
    ∀ i, ¬ Faulty i → legObs i = tid :=
  -- `actual` is confusable with itself by every leg (`Indist i actual actual = (actual i = actual i)`);
  -- so `apexKnown Faulty tid actual` holds, which unfolds defeq to the goal (`actual = legObs`).
  fun i hi => hdk (obsFrame legObs Faulty).actual (fun _ _ => rfl) i hi

/-- **`fork_has_no_distributed_apex` — the FORK = the H¹ obstruction (no global section).** If two
honest legs `i j` observe DIFFERENT ids (`legObs i ≠ legObs j`), then there is NO shared apex `tid`
of which the honest legs have distributed knowledge. The fork (a non-gluing) admits no H⁰ global
section — exactly `EpistemicSheaf.byzantine_section_does_not_glue` lifted onto the hyperedge's
incidence set: the disagreement lives entirely in the legs' overlap, and no single apex can fill
it. Since a real `Hyperedge` forces `legs_agree`, this configuration is precisely where the
hyperedge does NOT exist — the fork is the obstruction to the wide-pullback apex. -/
theorem fork_has_no_distributed_apex
    {ι : Type} {TurnId : Type}
    (legObs : ι → TurnId) (Faulty : ι → Prop)
    (i j : ι) (hi : ¬ Faulty i) (hj : ¬ Faulty j) (hfork : legObs i ≠ legObs j) :
    ¬ ∃ tid : TurnId, (obsFrame legObs Faulty).DistKnows (obsFrame legObs Faulty).Honest
              (apexKnown Faulty tid) (obsFrame legObs Faulty).actual := by
  rintro ⟨tid, hdk⟩
  -- distributed knowledge of `tid` forces BOTH honest legs to observe `tid` (filled simplex) …
  have hagree := distributed_apex_forces_agreement legObs Faulty tid hdk
  have hi' : legObs i = tid := hagree i hi
  have hj' : legObs j = tid := hagree j hj
  -- … so `legObs i = tid = legObs j`, contradicting the fork.
  exact hfork (hi'.trans hj'.symm)

/-! ## 4. Non-vacuity — both polarities, `#guard`-witnessed.

Polarity A (agreement ⟹ DistKnows): a concrete tiny hyperedge whose legs agree (here the
single-state `ringHyperedge`, whose every leg commits to the one apex `()`), exhibited as a frame
where `DistKnows` holds. Polarity B (fork ⟹ no DistKnows): an explicit disagreeing leg-family over
`Fin 2` — the epistemic shadow of `opA`/`opB_byzantine` from `EpistemicSheaf` — where no apex is
distributed knowledge. -/

/-! ### Polarity A — agreement ⟹ distributed knowledge (a real hyperedge). -/

/-- A concrete 2-leg agreeing observation family: both legs committed to the SAME id `7`. -/
def agreeObs : Fin 2 → ℕ := fun _ => 7

/-- All honest legs of `agreeObs` observe `7` — the hypothesis the bridge consumes (decidable,
`#guard`-checkable as a finite conjunction). -/
theorem agreeObs_agree : ∀ i : Fin 2, ¬ (fun _ : Fin 2 => False) i → agreeObs i = 7 :=
  fun _ _ => rfl

-- The agreeing family DOES yield distributed knowledge of its apex `7` (the bridge fires).
example : (obsFrame agreeObs (fun _ => False)).DistKnows
    (obsFrame agreeObs (fun _ => False)).Honest
    (apexKnown (fun _ => False) 7) (obsFrame agreeObs (fun _ => False)).actual :=
  obs_agreement_is_distributed_knowledge agreeObs (fun _ => False) 7 agreeObs_agree

-- The bridge AT a real `Hyperedge`: the single-state ring (all legs commit to apex `()`), so its
-- `agreement_is_distributed_knowledge` is inhabited — distributed knowledge of `tid = ()` is derived.
example : True := by
  have _bridge := agreement_is_distributed_knowledge
    (ringHyperedge 3 (fun _ => (0 : ℤ))) (fun _ : Fin 3 => False)
  trivial

-- `#guard` non-vacuity: every honest leg of the agreeing family observes the apex (decidable core).
#guard (decide (∀ i : Fin 2, agreeObs i = 7))                       -- true  (legs agree ⇒ DistKnows)
#guard agreeObs 0 == 7                                              -- true
#guard agreeObs 1 == 7                                              -- true  (both factor through `7`)

/-! ### Polarity B — a fork ⟹ NO distributed knowledge (a disagreeing family). -/

/-- A concrete 2-leg DISAGREEING observation family — the epistemic shadow of
`EpistemicSheaf.opA` (boundary `5`) vs `opB_byzantine` (boundary `99`): leg `0` committed to `5`,
leg `1` to `99`. There is no shared apex; no `Hyperedge` exists over this family. -/
def forkObs : Fin 2 → ℕ := fun i => if i = 0 then 5 else 99

/-- The two honest legs disagree (`5 ≠ 99`): the fork, witnessed (decidable). -/
theorem forkObs_disagree : forkObs 0 ≠ forkObs 1 := by decide

-- The fork has NO distributed apex (no H⁰ global section) — the H¹ obstruction, as a theorem.
example : ¬ ∃ tid : ℕ, (obsFrame forkObs (fun _ => False)).DistKnows
    (obsFrame forkObs (fun _ => False)).Honest
    (apexKnown (fun _ => False) tid) (obsFrame forkObs (fun _ => False)).actual :=
  fork_has_no_distributed_apex forkObs (fun _ => False) 0 1 (by decide) (by decide) forkObs_disagree

-- `#guard` non-vacuity: the legs genuinely disagree on the overlap (the fork BITES) — the dual of
-- `EpistemicSheaf`'s `(opA.boundary == opB_byzantine.boundary) == false`.
#guard (forkObs 0 == forkObs 1) == false                           -- false (overlap disagreement)
#guard forkObs 0 == 5                                              -- true  (leg 0 ↦ 5, locally fine)
#guard forkObs 1 == 99                                             -- true  (leg 1 ↦ 99, locally fine …
                                                                   --         … but no shared apex)

/-! ## 5. Axiom hygiene — the bridge is kernel-clean. -/

#assert_all_clean [obs_agreement_is_distributed_knowledge, agreement_is_distributed_knowledge,
  legs_agree_is_distributed_knowledge, distributed_apex_forces_agreement,
  fork_has_no_distributed_apex, agreeObs_agree, forkObs_disagree]

/- VERDICT (§5.2 realized). The two complexes are now ONE machine-checked theorem, not commentary:

  * INSTANTIATION: `obsFrame` puts `EpistemicSheaf.Frame` AT a `Hyperedge`'s incidence
    set — legs = agents, worlds = candidate global states `ι → TurnId`, `∼ᵢ` = "leg `i` sees its
    own component", apex `tid` = the proposition `apexKnown`.
  * BRIDGE: `agreement_is_distributed_knowledge` (and `legs_agree_is_distributed_knowledge`, routed
    literally through `Hyperedge.legs_agree`) DERIVES `DistKnows F.Honest (apexKnown H.tid)
    F.actual` from `H.agree`. **Agreement = distributed knowledge** is code.
  * FORK: `fork_has_no_distributed_apex` + `distributed_apex_forces_agreement` connect a hyperedge
    NON-GLUING (legs with no shared apex) to the H¹ obstruction — the fork admits no H⁰ global
    section, exactly `EpistemicSheaf.byzantine_section_does_not_glue` on the incidence set. A real
    `Hyperedge` cannot fork (the apex forces `legs_agree`); the fork is where the hyperedge is not.
  * Both polarities are non-vacuous (`#guard`-witnessed: agreeing legs ⇒ DistKnows; disagreeing
    legs ⇒ no apex), and every keystone is `#assert_axioms`-clean.

NAMED NEXT (out of this lane, faithfully stated): promoting this to a *simplicial object* — face
maps ∂ᵢ on `Hyperedge` restricting to sub-incidence-sets, with the per-face CG-5 obstruction as the
non-Kan content (`DREGG4-HYPERSYSTEM §8.2`). The fork direction here is the *content* of that
non-Kan theorem (faces don't freely extend) at the level of the apex proposition; the named-object
coboundary (`H⁰`/`H¹` as groups, a Čech complex) stays out of scope, exactly as `EpistemicSheaf`
declines it. -/

end Dregg2.Apps.SheafHyperedge
