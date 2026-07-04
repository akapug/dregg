/-
# Metatheory.CommonSecret — the COMMON SECRET: threshold-graded distributed knowledge.

A `K`-of-`N` Shamir secret sharing (SSS) scheme is usually framed weakly — *"`K` shares
RECONSTRUCT the secret"* — a single-point, operational reading. This module REFRAMES it as a
new **epistemic object**: a value the committee `G` *collectively holds as DISTRIBUTED
KNOWLEDGE* (the `D_G` modality of `Metatheory.EpistemicConsensus`) but that NO sub-threshold
subset, and no individual, knows. The secret becomes group-knowable **exactly at the threshold
`K`**, and below `K` it is **information-theoretically NOTHING**. We call this graded modality
`D_G^{≥K}` — *threshold distributed knowledge* — and the object it holds a **common secret**.

This is the epistemic DUAL of common knowledge: `C_G φ` is *"everyone knows that everyone knows
… φ"* — the supremum of the iterated-`E_G` tower (a fixpoint, limit-side); a common secret is
*"the group COULD know `φ` if it pooled `≥K` shares, but no proper sub-threshold part can"* — a
single `D`-style pooling, gated by a coalition-size THRESHOLD. Common knowledge climbs UP an
iteration to a binding ceiling; a common secret reaches ACROSS a coalition to a threshold floor.

It EXTENDS `Metatheory.EpistemicConsensus.Frame` (`Indist`, `Knows`, `DistKnows`,
`distKnows_mono_group`) — `D_G^{≥K}` is `DistKnows` evaluated at the threshold gate, NOT a new
Kripke primitive. The "Varieties of Distributed Knowledge" (Galimullin–Kuijer, AiML 2024) reading
is the right one: distributed knowledge is *hypothetical* — *"`φ` is `D_G` if the members COULD,
by combining their information, learn `φ`."* SSS is precisely the case where that pooling
SUCCEEDS at coalition size `≥K` and is information-theoretically VACUOUS below it.

DISCIPLINE: faithful Props, candidate-independent. The PROVED keystones are pinned
`#assert_axioms` (kernel-clean: only `propext`/`Classical.choice`/`Quot.sound`). The ONE
cryptographic obligation — that "a sub-threshold coalition's indistinguishability is TOTAL on the
secret-fiber" reflects an ACTUAL information-theoretic security (perfect privacy of the SSS scheme
below `K`) — enters ONLY as the `ThresholdFrame.subThreshold_blind` structural field, never as an
`axiom` or `admit`. It is the EXACT analogue of the `Disclosure` separation parameter in
`ConstructiveKnowledge`/`EpistemicDial` (the crypto layer discharges the antecedent; the
metatheory says *if* the scheme is perfectly private below `K`, *then* the cliff holds). A
DISCRIMINATING concrete model (§5) certifies every keystone non-vacuous: a real 2-of-2 scheme
where neither share knows the secret yet the pair does.
-/
import Metatheory.EpistemicConsensus
import Mathlib.Order.Lattice

namespace Metatheory.CommonSecret

open Dregg2.Laws Metatheory Metatheory.EpistemicConsensus

universe u v

/-! # §1. The threshold frame — a coalition-size gate over the epistemic frame

A `ThresholdFrame` is an epistemic `Frame` together with the committee `G`, the threshold `K`
(as a predicate `ReachesThreshold` on coalitions — "this coalition has `≥K` shares"), and the
two structural facts that make SSS what it is:

  * **monotone threshold** — a SUPERSET of a threshold coalition is still threshold (more shares
    never un-reaches the cliff); and
  * **sub-threshold blindness** — the *load-bearing crypto floor*: a coalition that does NOT
    reach threshold has its pooled indistinguishability TOTAL on the secret-fiber (it cannot
    rule out ANY value of the secret) — the information-theoretic security of the scheme below
    `K`, carried as a hypothesis, never an axiom.

We do not bake `K` as a `Nat`: `ReachesThreshold` is the abstract "is this coalition large
enough", so a richer monotone access structure (weighted shares, general monotone span programs)
instantiates the same laws. The `Nat`/cardinality reading is recovered by the concrete model §5. -/

/-- A **threshold frame**: an epistemic frame with a committee, a coalition-size gate, and the
SSS structural facts. The `secret : Ω → S` valuation reads each world's secret value (`S` = the
secret space); a proposition *about the secret* is `φ ∘ secret`-shaped, and "knowing the secret"
is distinguishing worlds with different `secret`-values. -/
structure ThresholdFrame (Ω : Type u) (ι : Type v) (S : Type u) where
  /-- The underlying epistemic frame (worlds, indistinguishability, faulty subset). -/
  base : Frame Ω ι
  /-- The committee `G` over whom the secret is shared (a coalition predicate). -/
  committee : ι → Prop
  /-- **`ReachesThreshold B`** — coalition `B` holds `≥K` shares (the access predicate). -/
  ReachesThreshold : (ι → Prop) → Prop
  /-- The threshold is MONOTONE: a superset of a threshold coalition is still threshold
  (`B ⊆ B' → ReachesThreshold B → ReachesThreshold B'`). More shares never un-reach the cliff —
  the access structure is monotone (every real SSS / monotone span program). -/
  threshold_mono : ∀ (B B' : ι → Prop), (∀ i, B i → B' i) →
    ReachesThreshold B → ReachesThreshold B'
  /-- **The whole committee reaches threshold** (`N ≥ K`): the scheme is realizable — pooling
  ALL shares determines the secret. (Without this the common secret would be unrecoverable.) -/
  committee_reaches : ReachesThreshold committee
  /-- The secret valuation: each world's secret value. -/
  secret : Ω → S
  /-- **SUB-THRESHOLD BLINDNESS — the information-theoretic floor (THE crypto hypothesis).** A
  coalition `B` that does NOT reach threshold cannot distinguish the actual world from a world
  with a DIFFERENT secret value: for every alternative value `s`, there is a world `w'` that `B`
  jointly confuses with `actual` and whose secret is `s`. The pooled view of a sub-threshold
  coalition is consistent with EVERY secret — perfect privacy below `K`. This is carried as a
  STRUCTURAL FIELD (the scheme's perfect-secrecy guarantee), the exact analogue of the
  `Disclosure` separation parameter; the crypto layer discharges it, the metatheory consumes it. -/
  subThreshold_blind : ∀ (B : ι → Prop), (∀ i, B i → committee i) → ¬ ReachesThreshold B →
    ∀ s : S, ∃ w' : Ω, (∀ i, B i → base.Indist i w' base.actual) ∧ secret w' = s

namespace ThresholdFrame

variable {Ω : Type u} {ι : Type v} {S : Type u} (TF : ThresholdFrame Ω ι S)

/-- **`DistKnowsGeK B φ` — threshold distributed knowledge `D_G^{≥K}` at the actual world.** The
group `B` distributedly knows `φ` AT THE THRESHOLD: `B` reaches threshold AND has distributed
knowledge of `φ`. This is the graded modality: `DistKnowsGeK B φ ≜ ReachesThreshold B ∧
DistKnows B φ actual`. Below threshold (the gate fails) the modality is `False` — the cliff. -/
def DistKnowsGeK (B : ι → Prop) (φ : Frame.Prop' Ω) : Prop :=
  TF.ReachesThreshold B ∧ TF.base.DistKnows B φ TF.base.actual

/-- **`KnowsSecret B`** — coalition `B` KNOWS THE SECRET: it can pin the secret value, i.e. its
pooled indistinguishability rules out every world with a different secret. Formally: every world
`B` confuses with `actual` has the SAME secret value as `actual`. This is "`B` distributedly
knows the proposition *the secret is `secret actual`*". -/
def KnowsSecret (B : ι → Prop) : Prop :=
  TF.base.DistKnows B (fun w => TF.secret w = TF.secret TF.base.actual) TF.base.actual

/-! # §2. The threshold laws — monotone-in-K, the cliff, and the dual to common knowledge -/

/-- **`distKnowsGeK_mono_group` — `D_G^{≥K}` is MONOTONE in the coalition (more shares ⇒ ≥
knowledge), PROVED, kernel-clean.** If `B ⊆ B'` and `B` has threshold distributed knowledge of
`φ`, so does `B'`: enlarging a threshold coalition keeps it above threshold (`threshold_mono`)
and only sharpens its distributed knowledge (`distKnows_mono_group`). This is the "monotone in
K" law — adding a share never loses what the smaller coalition could pool. -/
theorem distKnowsGeK_mono_group (B B' : ι → Prop) (hsub : ∀ i, B i → B' i)
    (φ : Frame.Prop' Ω) (h : TF.DistKnowsGeK B φ) : TF.DistKnowsGeK B' φ :=
  ⟨TF.threshold_mono B B' hsub h.1,
   TF.base.distKnows_mono_group B B' hsub φ TF.base.actual h.2⟩

/-- **`subThreshold_secret_blind` — THE THRESHOLD CLIFF / non-amplification tooth, PROVED,
kernel-clean.** A sub-threshold committee coalition does NOT know the secret: if `B ⊆ committee`
and `¬ ReachesThreshold B`, then `¬ KnowsSecret B`. The secret is information-theoretically
NOTHING below `K`. The proof is the heart of the common-secret object: `subThreshold_blind` hands
us, for ANY alternative secret value `s ≠ secret actual`, a world `w'` that `B` confuses with
`actual` whose secret is `s` — so `B`'s pooled view cannot pin the secret. This is the EPISTEMIC
shadow of perfect SSS privacy: below threshold, every secret value remains possible.

It is the non-amplification tooth in epistemic clothes — the dual of `ConstructiveKnowledge`'s
`no_forge_step` (no authority appears below its production): here NO knowledge of the secret
appears below the production threshold `K`. -/
theorem subThreshold_secret_blind (B : ι → Prop) (hsub : ∀ i, B i → TF.committee i)
    (hbelow : ¬ TF.ReachesThreshold B)
    -- non-degeneracy: the secret space has at least two values (else "knowing it" is vacuous).
    (s₀ : S) (hs₀ : s₀ ≠ TF.secret TF.base.actual) :
    ¬ TF.KnowsSecret B := by
  intro hknows
  -- `subThreshold_blind` gives a confusable world `w'` whose secret is the alternative `s₀`.
  obtain ⟨w', hconf, hsec⟩ := TF.subThreshold_blind B hsub hbelow s₀
  -- `KnowsSecret` forces `secret w' = secret actual`, but `secret w' = s₀ ≠ secret actual`.
  have : TF.secret w' = TF.secret TF.base.actual := hknows w' hconf
  exact hs₀ (hsec ▸ this)

/-- **`committee_knows_secret_of_recoverable` — THRESHOLD SUFFICIENCY (the `≥K` side of the
cliff).** If the WHOLE committee's pooled view determines the secret (`recoverable` — the scheme's
correctness: `N` shares reconstruct), then the committee `KnowsSecret`. This is the dual face of
the cliff: AT threshold (here, the full committee, which `committee_reaches`), the secret IS
group-known. Together with `subThreshold_secret_blind` this is the information-theoretic JUMP:
nothing below `K`, everything at `K`. `recoverable` is the scheme-correctness hypothesis (the
analogue of `committee_reaches` on the indistinguishability side). -/
theorem committee_knows_secret_of_recoverable
    (recoverable : ∀ w', (∀ i, TF.committee i → TF.base.Indist i w' TF.base.actual) →
        TF.secret w' = TF.secret TF.base.actual) :
    TF.KnowsSecret TF.committee :=
  fun w' hconf => recoverable w' hconf

/-- **`distKnowsGeK_iff_dist_and_threshold` — the gate factorisation.** `D_G^{≥K}` is exactly
"reaches threshold AND distributed-knows" — the graded modality splits cleanly into the
size-gate and the ordinary `D_G`. This makes `D_G^{≥K}` a genuine REFINEMENT of `DistKnows`: it
adds the threshold conjunct and nothing else, so every `DistKnows` law transports through. -/
theorem distKnowsGeK_iff_dist_and_threshold (B : ι → Prop) (φ : Frame.Prop' Ω) :
    TF.DistKnowsGeK B φ ↔
      (TF.ReachesThreshold B ∧ TF.base.DistKnows B φ TF.base.actual) :=
  Iff.rfl

/-! # §3. The duality to common knowledge — order-theoretic placement

`C_G` (common knowledge) is the GREATEST fixpoint of `E_G` (everyone-knows) — a LIMIT-side
ceiling reached by climbing an iteration UP. `D_G` (distributed knowledge) is, dually, the
group's pooled MEET — a single reach ACROSS the coalition. The common secret lives on the `D_G`
side, GATED by a threshold. The placement law: threshold distributed knowledge entails ordinary
distributed knowledge (the gate only removes the sub-threshold floor; it never adds beyond `D_G`)
— so `D_G^{≥K} ⊑ D_G ⊑ (no E_G/C_G of the secret below threshold)`. -/

/-- **`distKnowsGeK_imp_distKnows` — `D_G^{≥K}` is BELOW `D_G` in the knowledge order.** Threshold
distributed knowledge implies ordinary distributed knowledge: the threshold gate is a
RESTRICTION (it can only fail to fire), never an amplification past `D_G`. This places the common
secret strictly inside the `D` modality — it is a `D`-style object, not an `E`/`C` one. -/
theorem distKnowsGeK_imp_distKnows (B : ι → Prop) (φ : Frame.Prop' Ω)
    (h : TF.DistKnowsGeK B φ) : TF.base.DistKnows B φ TF.base.actual :=
  h.2

/-- **`secret_not_everyone_knows` — the DUAL-TO-`C_G` content: a common secret is the OPPOSITE of
common knowledge.** No individual committee member (a singleton coalition, assumed sub-threshold —
the SSS non-degeneracy `K ≥ 2`) knows the secret. Where common knowledge `C_G φ` requires every
member to know `φ` (and to know that they know, …), a common secret requires every member to NOT
know it. This is the sharp epistemic duality: `C_G` is built from `E_G` (ALL members know);
the common secret guarantees `¬ Kᵢ secret` for each member — the anti-`E_G`, hence anti-`C_G`,
floor. -/
theorem secret_not_everyone_knows (i : ι) (hi : TF.committee i)
    (hsingleton_below : ¬ TF.ReachesThreshold (fun j => j = i))
    (s₀ : S) (hs₀ : s₀ ≠ TF.secret TF.base.actual) :
    ¬ TF.KnowsSecret (fun j => j = i) :=
  TF.subThreshold_secret_blind (fun j => j = i) (fun _ hj => hj ▸ hi) hsingleton_below s₀ hs₀

end ThresholdFrame

#assert_axioms ThresholdFrame.distKnowsGeK_mono_group
#assert_axioms ThresholdFrame.subThreshold_secret_blind
#assert_axioms ThresholdFrame.committee_knows_secret_of_recoverable
#assert_axioms ThresholdFrame.distKnowsGeK_iff_dist_and_threshold
#assert_axioms ThresholdFrame.distKnowsGeK_imp_distKnows
#assert_axioms ThresholdFrame.secret_not_everyone_knows

/-! # §4. The non-amplification BRIDGE — the common secret as the dual of `no_forge_step`

The cliff (`subThreshold_secret_blind`) is the epistemic dual of the authority
non-amplification of `ConstructiveKnowledge` (`no_forge_step`: no authority appears below its
production). We make the duality precise: in BOTH cases a quantity (authority / secret-knowledge)
is `⊥` below a production gate (held-rights / threshold) and present above it. The shared shape
is "nothing below the gate" — the information-theoretic / non-forgeability floor. -/

/-- **`threshold_jump` — the information-theoretic JUMP stated as one proposition, PROVED.** For a
sub-threshold committee coalition `B` (with the SSS non-degeneracy: a real alternative secret
exists), the secret is BOTH not-known by `B` AND known by the whole committee (given
recoverability). The conjunction IS the cliff: a single coalition-size step (`B` ⊊ committee, `B`
below threshold) flips secret-knowledge from `⊥` to `⊤`. This is the non-amplification tooth: the
secret is `information-theoretically NOTHING` at `K−1` and `everything` at `K`. -/
theorem ThresholdFrame.threshold_jump {Ω : Type u} {ι : Type v} {S : Type u}
    (TF : ThresholdFrame Ω ι S) (B : ι → Prop)
    (hsub : ∀ i, B i → TF.committee i) (hbelow : ¬ TF.ReachesThreshold B)
    (s₀ : S) (hs₀ : s₀ ≠ TF.secret TF.base.actual)
    (recoverable : ∀ w', (∀ i, TF.committee i → TF.base.Indist i w' TF.base.actual) →
        TF.secret w' = TF.secret TF.base.actual) :
    ¬ TF.KnowsSecret B ∧ TF.KnowsSecret TF.committee :=
  ⟨TF.subThreshold_secret_blind B hsub hbelow s₀ hs₀,
   TF.committee_knows_secret_of_recoverable recoverable⟩

#assert_axioms ThresholdFrame.threshold_jump

/-! # §5. A DISCRIMINATING model — non-vacuity certificate (a real 2-of-2 common secret)

Every keystone above is over an abstract `ThresholdFrame`; a `∀`-quantified theorem can be
vacuously true. We rule that out with a CONCRETE 2-of-2 scheme over `GF(2)`-flavoured data:

  * the secret is a bit `s ∈ Bool`; two shares `a, b ∈ Bool` with `a ⊕ b = s` (the XOR/1-degree
    Shamir line over `𝔽₂`); a WORLD is a pair `(a, b)`, its secret `a ⊕ b`.
  * agent `0` sees only `a`; agent `1` sees only `b`. So agent `0` confuses `(a,b)` with `(a,b')`
    for ANY `b'` (it cannot see `b`), and dually agent `1`.
  * the coalition `{0,1}` (size 2) reaches threshold; any singleton (size 1) does not.

Then: NEITHER agent alone knows the secret (each confuses it with the world of opposite secret),
but the PAIR does (pooling `a` and `b` fixes `a ⊕ b`). This is a genuine common secret: held by
`{0,1}` as distributed knowledge, information-theoretically nothing to either share. -/

namespace TwoOfTwo

/-- A world: the two share values `(a, b)`; the secret is `a ⊕ b` (xor). -/
abbrev World := Bool × Bool

/-- The secret read from a world: `a ⊕ b`. -/
def secretOf : World → Bool := fun w => xor w.1 w.2

/-- The underlying epistemic frame: agent `false` sees only `a` (`.1`), agent `true` only `b`
(`.2`); each confuses worlds agreeing on its OWN share. Actual world `(true, false)` (secret
`true`). No faults. -/
def baseF : Frame World Bool where
  actual := (true, false)
  -- agent `false` (share a) confuses worlds with the same `.1`; agent `true` (share b) the same `.2`.
  Indist := fun i w w' => if i = false then w.1 = w'.1 else w.2 = w'.2
  indist_refl := by intro i w; cases i <;> simp
  Alive := fun _ _ => True
  Faulty := fun _ => False

/-- The 2-of-2 threshold frame. Committee = both agents. A coalition reaches threshold iff it
contains BOTH agents (size 2). Sub-threshold blindness is PROVED below from the share structure. -/
def TF : ThresholdFrame World Bool Bool where
  base := baseF
  committee := fun _ => True
  -- reaches threshold iff both agents are in: the access structure of 2-of-2.
  ReachesThreshold := fun B => B false ∧ B true
  threshold_mono := by intro B B' hsub h; exact ⟨hsub false h.1, hsub true h.2⟩
  committee_reaches := ⟨trivial, trivial⟩
  secret := secretOf
  subThreshold_blind := by
    -- A coalition missing at least one agent cannot pin the secret: flip the unseen share.
    intro B _ hbelow s
    -- hbelow : ¬ (B false ∧ B true), so some agent is absent.
    by_cases hf : B false
    · -- agent `false` present ⇒ agent `true` absent (else threshold). Hold `.1`, set `.2` to
      -- realise secret `s`: choose `b` with `actual.1 ⊕ b = s`, i.e. `b = actual.1 ⊕ s`.
      have htabsent : ¬ B true := fun ht => hbelow ⟨hf, ht⟩
      refine ⟨(true, xor true s), ?_, ?_⟩
      · intro i hi
        -- only agent `false` can be in B (true is absent); its edge needs `.1` equal: `true = true`.
        cases i with
        | false => show (true, xor true s).1 = baseF.actual.1; rfl
        | true => exact absurd hi htabsent
      · show secretOf (true, xor true s) = s
        unfold secretOf; simp
    · -- agent `false` absent. Hold `.2 = false`, set `.1` to realise secret `s`: `a ⊕ false = s`
      -- ⇒ `a = s`.
      refine ⟨(s, false), ?_, ?_⟩
      · intro i hi
        cases i with
        | false => exact absurd hi hf
        | true => show (s, false).2 = baseF.actual.2; rfl
      · show secretOf (s, false) = s
        unfold secretOf; simp

/-- **agent `false` alone does NOT know the secret** — a singleton is below the 2-of-2 threshold.
Concrete witness that `subThreshold_secret_blind` is non-vacuous: the alternative secret `false`
(≠ actual `true`) is realisable by flipping the unseen share `b`. -/
theorem agent0_not_knows_secret :
    ¬ TF.KnowsSecret (fun j => j = false) := by
  refine TF.subThreshold_secret_blind (fun j => j = false) (fun _ _ => trivial) ?_ false ?_
  · -- singleton {false} does not reach threshold (lacks `true`).
    intro h; exact (by simp : ¬ ((fun j => j = false) true)) h.2
  · -- alternative secret `false ≠ secretOf actual = secretOf (true,false) = true`.
    show false ≠ secretOf (true, false); unfold secretOf; simp

/-- **The PAIR `{false,true}` DOES know the secret** — both shares pin `a ⊕ b`. Any world the pair
confuses with `actual` must agree on BOTH `.1` and `.2`, hence equal `actual`, hence have the same
secret. So `DistKnows` of "the secret is `secretOf actual`" holds — a real common secret recovered
at threshold. -/
theorem pair_knows_secret :
    TF.KnowsSecret (fun _ => True) := by
  intro w' hall
  -- agent false's edge: w'.1 = actual.1 ; agent true's edge: w'.2 = actual.2.
  have h1 : w'.1 = baseF.actual.1 := by
    have := hall false trivial; simpa [baseF] using this
  have h2 : w'.2 = baseF.actual.2 := by
    have := hall true trivial; simpa [baseF] using this
  show secretOf w' = secretOf baseF.actual
  unfold secretOf; rw [h1, h2]

/-- **Therefore `{false,true}` is a genuine COMMON SECRET** — held by the pair, unknown to either
share: `KnowsSecret pair ∧ ¬ KnowsSecret {false}`. The sharp non-vacuity certificate for the whole
module: the threshold modality `D_G^{≥K}` separates the pair from the singleton, exactly the
information-theoretic cliff of a real 2-of-2 SSS. -/
theorem genuine_common_secret :
    TF.KnowsSecret (fun _ => True) ∧ ¬ TF.KnowsSecret (fun j => j = false) :=
  ⟨pair_knows_secret, agent0_not_knows_secret⟩

/-- **The pair reaches threshold AND knows it — `D_G^{≥K}` fires.** The full threshold modality
holds for the pair on the secret-proposition: it is above threshold and distributedly knows the
secret. The common secret is `D_G^{≥K}`-held by the committee. -/
theorem pair_distKnowsGeK_secret :
    TF.DistKnowsGeK (fun _ => True)
      (fun w => TF.secret w = TF.secret TF.base.actual) :=
  ⟨⟨trivial, trivial⟩, pair_knows_secret⟩

end TwoOfTwo

#assert_axioms TwoOfTwo.agent0_not_knows_secret
#assert_axioms TwoOfTwo.pair_knows_secret
#assert_axioms TwoOfTwo.genuine_common_secret
#assert_axioms TwoOfTwo.pair_distKnowsGeK_secret

/-! # Coda

The common secret is `D_G^{≥K}` — distributed knowledge `D_G` (`EpistemicConsensus`) GATED by a
monotone coalition-size threshold. The threshold laws hold (§2): monotone-in-coalition
(`distKnowsGeK_mono_group`), the CLIFF (`subThreshold_secret_blind` — info-theoretically nothing
below `K`, the non-amplification tooth) and its dual face (`committee_knows_secret_of_recoverable`
— everything at `K`), assembled as the `threshold_jump` (§4). The duality to common knowledge is
placed (§3): the common secret is a `D`-side object BELOW `D_G` and is the anti-`E_G`/anti-`C_G`
floor (`secret_not_everyone_knows`). A real 2-of-2 XOR scheme (§5) certifies every keystone
non-vacuous: a secret held by the pair as distributed knowledge, information-theoretically nothing
to either share. The single cryptographic obligation — perfect SSS privacy below `K` — lives,
faithfully, as the `subThreshold_blind` structural field, the exact analogue of the `Disclosure`
separation parameter, NEVER an axiom. -/

end Metatheory.CommonSecret
