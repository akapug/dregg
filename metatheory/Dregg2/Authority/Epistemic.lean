/-
# Dregg2.Authority.Epistemic — the EPISTEMIC MODALITY TOWER over the constructive witness semantics.

THE THESIS. In dregg, knowledge is constructive: `K_a φ` means *"agent `a` can exhibit a verifying
witness of `φ`"* — the BHK/realizability reading already implemented by the `Predicate ⊣ Witness`
seam (`Dregg2.Laws.Discharged`, `Metatheory.ConstructiveKnowledge.Holds`). Every classical epistemic
modality therefore has an EXISTING mechanism in this tree, and this module proves the welds:

  * **K_a (knowledge)** = exhibitable witness — the caveat/third-party-discharge surface
    (`Authority.MacaroonDischarge`: a discharge IS a witness one must exhibit and the verifier
    re-checks; `Authority.CaveatChain`). `Knows pocket a φ := ∃ w, pocket a w ∧ Discharged φ w`.
  * **E_G (everyone knows)** = per-member witnesses — the actor-bound approval slots of
    `Exec.Program` (`anyOf [immutable f, senderIs k]`, the polis council machinery): §4 proves a
    council certificate IS an E_G certificate, because each approval's witness is PINNED to its
    member's sender identity (`approval_witness_pins_sender`).
  * **D_G (distributed knowledge: pooled info entails φ, no member alone knows)** = threshold
    constructions — `Distributed.ThresholdDecrypt`'s Shamir/GF(256) algebra: §5 proves the 2-of-3
    golden quorum constructs a pooled witness (`threshold_gate_is_D`) while NO single member can
    exhibit one (`no_single_member_knows`) — the D-without-K separation, witnessed.
  * **C_G (common knowledge)** = FINALITY — a witness in a finalized block verified by every
    member's light client (`Distributed.FinalizedLightClient.CertValid` over the node's REAL
    super-ratification rule): §6 proves a valid finality cert constructs `CommonAt`
    (`finality_is_common`), the cert is ONE shared witness visible to every member (the constructive
    content of common knowledge), and there are no conflicting common knowledges per wave
    (`no_conflicting_common_per_wave`). The honesty caveat is stated, not hidden: C_G holds
    RELATIVE to the finality floor (the `FinalityFloor.finalized_visible` law = "finalized ⇒ every
    light client sees it"), and at n = 1 it collapses onto K_a (`knows_to_common_single`,
    the single-machine principle).
  * **non-transferable K_a** = the `Authority.DesignatedVerifier` machinery: §7 proves DV
    knowledge does NOT lift to E_G under witness forwarding (`dv_forwarding_no_E`) — possession of
    the transcript is not knowledge when the discharge relation is verifier-indexed — while a
    `Transferable` (public-endpoint) witness DOES lift (`transferable_forwarding_lifts`).

THE TOWER (where it holds constructively): `C_G ⊆ E_G ⊆ K_a (a ∈ G) ⊆ D_G` — §2/§3. Note the
constructive direction of the last inclusion: D_G is the WEAKEST (the pool contains every member's
pocket), yet D_G is NOT below any single K_a — the threshold separation. Where the classical tower
FAILS constructively: E_G ⇏ C_G (`no_common_for_private_pockets` — private witnesses give E with no
possible finality floor yielding C), D_G ⇏ K_a (the threshold separation), and DV-K_a ⇏ E_G on
forwarding (§7).

THE ADJOINT STRUCTURE (§8): the graded triple `∃_a ⊣ q_a* ⊣ ∀_a` over the witness fibration — the
"holding" span `Holding pocket = {(a, w) // pocket a w}` projecting to agents — is PROVED by
instantiating `Dregg2.Metatheory.Lawvere.PartA.lawvere_triple` (both Galois connections, with unit,
counit, and Frobenius). The Knows operator is pinned to the LEFT-adjoint composite:
`Knows = ∃_a ∘ q_a*` (`mem_knowsSet_iff`) — the constructive-knowledge correction (knowledge is
PRODUCTION of a witness, an ∃, not descent, a ∀). The carried open core "faithful ∀_a = Knows" is
resolved PRECISELY: `KnowsSet = BoxSet` holds iff the holding relation is FUNCTIONAL (one credential
per agent, `knowsSet_eq_boxSet_of_functional`), the D-axiom direction `□ ⇒ ◇` needs only
inhabitation (`box_to_knows_of_inhabited`), and the obstruction for general pockets is the
non-invertible `◇ ⇒ □` comparison at MIXED pockets — witnessed FALSE (`MixedPocket.knows_ne_box`),
never faked with a Unit carrier. The unit/counit laws of the triple itself all HOLD (§8a).

GUARD-ATOM DESIGNS (§9, design ONLY — installation belongs to the temporal-algebra lane, which owns
the guard surface): `knownBy / distributedAmong / commonAt / privateTo` atom signatures with their
coordination-cost classification (K and DV-K are FREE — a local witness check; D costs QUORUM
latency — one threshold round; C costs FINALITY latency — wait for super-ratification), plus the
killer example AS A THEOREM: bridge settlement guarded on `commonAt` is partition-safe
(`commonAt_guard_partition_safe` — two partition sides can never BOTH reach the super-majority the
C_G constructor demands, by `superMajority_gt_half`), against the explicit double-settlement
counterexample that breaks the unguarded version (`unguarded_double_settles`).

NON-VACUITY: every operator carries a TRUE and a FALSE witness (§3 Demo + the mechanism sections).
No `:= True` carriers; `#assert_axioms`-clean (⊆ {propext, Classical.choice,
Quot.sound}). The crypto floor enters ONLY through the modules this one consumes (named there:
`Blake3Prf`, the BLS/SNARK contracts, the DV simulator law) — nothing new is assumed here.
-/
import Dregg2.Laws
import Dregg2.Tactics
import Dregg2.Authority.DesignatedVerifier
import Dregg2.Exec.Program
import Dregg2.Distributed.ThresholdDecrypt
import Dregg2.Distributed.FinalizedLightClient
import Dregg2.Metatheory.Lawvere

namespace Dregg2.Authority.Epistemic

open Dregg2.Laws

universe u v w

/-! ## §1 — The witness-pocket semantics.

An agent's epistemic state is WHAT IT CAN EXHIBIT: a `Pocket` assigns to each agent the set of
witnesses it can produce on demand (held credentials, received discharges, locally-computed
openings). All modality operators are defined over a pocket and the `Verifiable`/`Discharged`
seam of `Dregg2.Laws` — knowledge never floats free of a verifying witness.
(`Metatheory.ConstructiveKnowledge.Holds` is the full-pocket special case: `Holds X` =
`Knows (fun _ _ => True) a X.stmt` for any `a` — global exhibitability.) -/

/-- **`Pocket Agent W`** — which witnesses each agent can exhibit. The epistemic accessibility
data of the constructive semantics: not a relation between worlds, a relation between an agent and
the witnesses it can PRODUCE. -/
def Pocket (Agent : Type u) (W : Type w) := Agent → W → Prop

variable {Agent : Type u} {P : Type v} {W : Type w}

/-! ## §2 — The tower operators. -/

/-- **`Knows pocket a φ`** (constructive K_a) — agent `a` can exhibit a verifying witness of `φ`.
The BHK clause over the `Predicate ⊣ Witness` seam: knowledge IS the ability to produce a realizer
that the (decidable, verifier-local) `Verify` accepts. -/
def Knows [Verifiable P W] (pocket : Pocket Agent W) (a : Agent) (φ : P) : Prop :=
  ∃ w : W, pocket a w ∧ Discharged φ w

/-- **`EveryoneKnows pocket G φ`** (constructive E_G) — every member of `G` can exhibit a
verifying witness (each possibly its OWN, distinct witness — that is what separates E from C). -/
def EveryoneKnows [Verifiable P W] (pocket : Pocket Agent W) (G : List Agent) (φ : P) : Prop :=
  ∀ a ∈ G, Knows pocket a φ

/-- **`PoolOps W`** — the pooling structure for distributed knowledge: how a coalition COMBINES
the witnesses its members exhibit into one candidate witness (Lagrange interpolation for Shamir
shares, signature aggregation for BLS, concatenation for multi-sig). -/
structure PoolOps (W : Type w) where
  /-- Combine a list of exhibited witnesses into one pooled candidate. -/
  combine : List W → W

/-- **`Pooled combine base`** — the closure of a base witness set under pooling: everything a
coalition can DERIVE from what its members exhibit. `seed` = any member's own witness; `mix` =
combining already-derivable witnesses. This is the constructive content of "pooled information":
not a union of facts, a closure under an explicit combining computation. -/
inductive Pooled (combine : List W → W) (base : W → Prop) : W → Prop where
  /-- A witness some member exhibits directly is pooled. -/
  | seed {w : W} : base w → Pooled combine base w
  /-- Combining pooled witnesses yields a pooled witness. -/
  | mix {ws : List W} : (∀ w ∈ ws, Pooled combine base w) → Pooled combine base (combine ws)

/-- **`pooled_invariant`** — the induction principle in invariant form: any property preserved by
the base and by combining holds of every pooled witness. The "no conjuring" law: pooling cannot
produce witnesses outside the closure (used for the FALSE witnesses of D_G). -/
theorem pooled_invariant {combine : List W → W} {base : W → Prop} {Q : W → Prop}
    (hbase : ∀ w, base w → Q w)
    (hmix : ∀ ws : List W, (∀ w ∈ ws, Q w) → Q (combine ws)) :
    ∀ {w : W}, Pooled combine base w → Q w := by
  intro w h
  induction h with
  | seed hb => exact hbase _ hb
  | mix _ ih => exact hmix _ ih

/-- The group pocket: a witness some member of `G` can exhibit. -/
def groupPocket (pocket : Pocket Agent W) (G : List Agent) : W → Prop :=
  fun w => ∃ a, a ∈ G ∧ pocket a w

/-- **`DistributedKnows pool pocket G φ`** (constructive D_G) — the group's POOLED witnesses
(closure of the members' pockets under combining) contain a verifying witness of `φ`. "Pooled
information entails φ": the coalition, cooperating, can construct a realizer — even when no member
alone can (the threshold separation, §5). -/
def DistributedKnows [Verifiable P W] (pool : PoolOps W) (pocket : Pocket Agent W)
    (G : List Agent) (φ : P) : Prop :=
  ∃ w : W, Pooled pool.combine (groupPocket pocket G) w ∧ Discharged φ w

/-- **`ThresholdKnows pool pocket G k φ`** (the THRESHOLD shape of D_G) — some `k` distinct members
of `G` each exhibit one witness (their SHARE) and the single combine of exactly those shares
verifies `φ`. This is the `t`-of-`n` gate shape (`ThresholdDecrypt.combineAdmits`): the quorum leg
(`k ≤ length`), distinctness (`Nodup`), membership, possession, and the verifying reconstruction. -/
def ThresholdKnows [Verifiable P W] (pool : PoolOps W) (pocket : Pocket Agent W)
    (G : List Agent) (k : Nat) (φ : P) : Prop :=
  ∃ (members : List Agent) (sel : Agent → W),
    (∀ a ∈ members, a ∈ G) ∧ members.Nodup ∧ k ≤ members.length ∧
    (∀ a ∈ members, pocket a (sel a)) ∧
    Discharged φ (pool.combine (members.map sel))

/-- **`FinalityFloor Agent W`** — the C_G constructor's substrate: which witnesses are FINALIZED
at each depth, which witnesses each agent's light client makes VISIBLE to it, and THE FLOOR LAW —
a finalized witness is visible to EVERY agent. The floor law is the honest carrier of the finality
assumption (a BFT quorum super-ratified the block and every light client checks the same
verifier-index-free certificate); it is exactly what a network partition suspends, which is why
the `commonAt` guard is partition-safe (§9) and why C_G is "relative to the finality floor". -/
structure FinalityFloor (Agent : Type u) (W : Type w) where
  /-- `Finalized d w` — witness `w` is finalized at depth/wave `d`. -/
  Finalized : Nat → W → Prop
  /-- `visible a w` — agent `a`'s light client makes `w` exhibitable by `a`. -/
  visible : Agent → W → Prop
  /-- THE FLOOR: finalized ⇒ visible to every agent. -/
  finalized_visible : ∀ d w, Finalized d w → ∀ a, visible a w

/-- **`CommonAt floor d φ`** (constructive C_G) — a verifying witness of `φ` is FINALIZED at depth
`d`. By the floor law this single witness is visible to every agent, and — because finality and
light-client verification are agent-INDEPENDENT — every agent can also verify that every other
agent can locate the same witness: the infinite E^k tower collapses onto the ONE shared finalized
witness (`common_gives_mutual_witness`). -/
def CommonAt [Verifiable P W] (floor : FinalityFloor Agent W) (d : Nat) (φ : P) : Prop :=
  ∃ w : W, floor.Finalized d w ∧ Discharged φ w

/-! ## §3 — The inclusion tower (where it holds), and the separations (where it fails).

Constructive inclusions, each proved: `CommonAt → EveryoneKnows → Knows → DistributedKnows`,
`ThresholdKnows → DistributedKnows`. Constructive FAILURES, each witnessed: `EveryoneKnows ⇏
CommonAt` (private pockets), `DistributedKnows ⇏ Knows` (the threshold separation, §5), DV-`Knows`
⇏ `EveryoneKnows` on forwarding (§7). -/

section Tower

variable [Verifiable P W]

/-- E_G restricts to each member: `EveryoneKnows → Knows` (a ∈ G). -/
theorem everyone_to_knows {pocket : Pocket Agent W} {G : List Agent} {φ : P}
    (h : EveryoneKnows pocket G φ) {a : Agent} (ha : a ∈ G) : Knows pocket a φ :=
  h a ha

/-- A single member's knowledge pools: `Knows → DistributedKnows` (a ∈ G). The pooled pocket
contains every member's own pocket (`Pooled.seed`) — D_G is the WEAKEST rung. -/
theorem knows_to_distributed (pool : PoolOps W) {pocket : Pocket Agent W} {G : List Agent}
    {a : Agent} (ha : a ∈ G) {φ : P} (h : Knows pocket a φ) :
    DistributedKnows pool pocket G φ := by
  obtain ⟨w, hw, hdis⟩ := h
  exact ⟨w, Pooled.seed ⟨a, ha, hw⟩, hdis⟩

/-- `EveryoneKnows → DistributedKnows` for inhabited groups (any member's witness pools). -/
theorem everyone_to_distributed (pool : PoolOps W) {pocket : Pocket Agent W} {G : List Agent}
    {φ : P} (hne : G ≠ []) (h : EveryoneKnows pocket G φ) :
    DistributedKnows pool pocket G φ := by
  cases G with
  | nil => exact absurd rfl hne
  | cons a t => exact knows_to_distributed pool (List.mem_cons_self ..) (h a (List.mem_cons_self ..))

/-- The threshold shape is a distributed-knowledge constructor: `ThresholdKnows →
DistributedKnows`. The selected shares are seeds; their combine is one `mix`. -/
theorem threshold_to_distributed (pool : PoolOps W) {pocket : Pocket Agent W} {G : List Agent}
    {k : Nat} {φ : P} (h : ThresholdKnows pool pocket G k φ) :
    DistributedKnows pool pocket G φ := by
  obtain ⟨ms, sel, hsub, _, _, hpock, hdis⟩ := h
  refine ⟨pool.combine (ms.map sel), Pooled.mix ?_, hdis⟩
  intro w hw
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hw
  exact Pooled.seed ⟨a, hsub a ha, hpock a ha⟩

/-- `CommonAt → EveryoneKnows` (over the floor's visibility pocket, for ANY group): the finalized
witness is in every agent's light-client pocket. -/
theorem common_to_everyone (floor : FinalityFloor Agent W) (G : List Agent) {d : Nat} {φ : P}
    (h : CommonAt floor d φ) : EveryoneKnows floor.visible G φ := by
  obtain ⟨w, hfin, hdis⟩ := h
  exact fun a _ => ⟨w, floor.finalized_visible d w hfin a, hdis⟩

/-- `CommonAt → Knows` for every agent (not only group members — finality is global). -/
theorem common_to_knows (floor : FinalityFloor Agent W) (a : Agent) {d : Nat} {φ : P}
    (h : CommonAt floor d φ) : Knows floor.visible a φ := by
  obtain ⟨w, hfin, hdis⟩ := h
  exact ⟨w, floor.finalized_visible d w hfin a, hdis⟩

/-- **The shared-witness strengthening — what separates C from mere E.** Common knowledge yields
ONE witness that verifies `φ` and sits in EVERY agent's visibility pocket. Mere E_G gives each
member its own (possibly private, mutually invisible) witness; C gives a single public one. -/
theorem common_shared_witness (floor : FinalityFloor Agent W) {d : Nat} {φ : P}
    (h : CommonAt floor d φ) :
    ∃ w : W, Discharged φ w ∧ ∀ a : Agent, floor.visible a w := by
  obtain ⟨w, hfin, hdis⟩ := h
  exact ⟨w, hdis, floor.finalized_visible d w hfin⟩

/-- **The E^k collapse.** For any two agents, common knowledge exhibits one witness visible to
BOTH — so `a` can exhibit the very witness that establishes `b`'s knowledge, and vice versa, at
every iteration depth: the infinite mutual-knowledge tower collapses onto the one finalized
witness. (Stated at depth 2; the same witness serves every depth, uniformly in the agents.) -/
theorem common_gives_mutual_witness (floor : FinalityFloor Agent W) {d : Nat} {φ : P}
    (h : CommonAt floor d φ) (a b : Agent) :
    ∃ w : W, floor.visible a w ∧ floor.visible b w ∧ Discharged φ w := by
  obtain ⟨w, hfin, hdis⟩ := h
  exact ⟨w, floor.finalized_visible d w hfin a, floor.finalized_visible d w hfin b, hdis⟩

/-- **The n = 1 collapse (single-machine principle), stated honestly as a hypothesis.** If an
agent's visible witnesses are all finalized at depth `d` — TRUE on a single machine, where local
commitment IS finality, FALSE in general at n > 1 (a partition makes witnesses visible-but-not-
finalized) — then its private knowledge already IS common knowledge. The hypothesis `hloc` is the
exact content of "n = 1 collapses the distributed bounds". -/
theorem knows_to_common_single (floor : FinalityFloor Agent W) (a : Agent) {d : Nat} {φ : P}
    (hloc : ∀ w, floor.visible a w → floor.Finalized d w)
    (h : Knows floor.visible a φ) : CommonAt floor d φ := by
  obtain ⟨w, hv, hdis⟩ := h
  exact ⟨w, hloc w hv, hdis⟩

/-- FALSE witness shape for ThresholdKnows: an empty group can never reach a positive threshold
(the quorum leg is unsatisfiable). -/
theorem threshold_false_on_empty (pool : PoolOps W) (pocket : Pocket Agent W) {k : Nat}
    (hk : 1 ≤ k) (φ : P) : ¬ ThresholdKnows pool pocket ([] : List Agent) k φ := by
  rintro ⟨ms, sel, hsub, _, hlen, _, _⟩
  cases ms with
  | nil => simp at hlen; omega
  | cons a t => exact absurd (hsub a (List.mem_cons_self ..)) (List.not_mem_nil)

end Tower

/-! ### §3b — Demo: TRUE and FALSE witnesses for every tower operator, and the E ⇏ C separation.

A two-agent toy: agent 0 exhibits only `7`, agent 1 exhibits only `8`; the statement `⟨lo⟩` is
discharged by any witness `≥ lo` (so DISTINCT witnesses can discharge the same statement —
exactly the situation where E holds with nothing shared). -/

namespace Demo

/-- Toy statement: "some witness ≥ lo exists". -/
structure Stmt where
  lo : Nat
  deriving DecidableEq, Repr

instance : Verifiable Stmt Nat := ⟨fun s w => decide (s.lo ≤ w)⟩

/-- Agent 0 holds exactly `7`; agent 1 holds exactly `8` — private, non-shared witnesses. -/
def pock : Pocket Nat Nat := fun a w => (a = 0 ∧ w = 7) ∨ (a = 1 ∧ w = 8)

/-- K TRUE: agent 0 knows `⟨5⟩` (exhibits 7, and 5 ≤ 7). -/
theorem knows_true : Knows pock 0 (⟨5⟩ : Stmt) := ⟨7, Or.inl ⟨rfl, rfl⟩, by decide⟩

/-- K FALSE: agent 0 does not know `⟨9⟩` (its only witness is 7 < 9). -/
theorem knows_false : ¬ Knows pock 0 (⟨9⟩ : Stmt) := by
  rintro ⟨w, hp, hd⟩
  rcases hp with ⟨_, rfl⟩ | ⟨h0, _⟩
  · exact absurd hd (by decide)
  · exact absurd h0 (by decide)

/-- E TRUE: both agents know `⟨5⟩` — each with its OWN witness. -/
theorem everyone_true : EveryoneKnows pock [0, 1] (⟨5⟩ : Stmt) := by
  intro a ha
  rcases (by simpa using ha : a = 0 ∨ a = 1) with rfl | rfl
  · exact ⟨7, Or.inl ⟨rfl, rfl⟩, by decide⟩
  · exact ⟨8, Or.inr ⟨rfl, rfl⟩, by decide⟩

/-- E FALSE: not everyone knows `⟨8⟩` (agent 0's best witness is 7). -/
theorem everyone_false : ¬ EveryoneKnows pock [0, 1] (⟨8⟩ : Stmt) := by
  intro h
  rcases h 0 (by simp) with ⟨w, hp, hd⟩
  rcases hp with ⟨_, rfl⟩ | ⟨h0, _⟩
  · exact absurd hd (by decide)
  · exact absurd h0 (by decide)

/-- A degenerate pool (combining always yields 0) for the D FALSE witness. -/
def zeroPool : PoolOps Nat := { combine := fun _ => 0 }

/-- D TRUE: distributed knowledge of `⟨5⟩` (any member's witness pools — here via agent 0). -/
theorem distributed_true : DistributedKnows zeroPool pock [0, 1] (⟨5⟩ : Stmt) :=
  knows_to_distributed zeroPool (by simp) knows_true

/-- D FALSE — via the no-conjuring invariant: every pooled witness of this toy is ≤ 8 (the seeds
are 7 and 8; combining yields 0), so `⟨9⟩` is not distributedly known. Pooling cannot conjure
witnesses the closure does not contain. -/
theorem distributed_false : ¬ DistributedKnows zeroPool pock [0, 1] (⟨9⟩ : Stmt) := by
  rintro ⟨w, hp, hd⟩
  have hle : w ≤ 8 := by
    refine pooled_invariant (Q := fun w => w ≤ 8) ?_ ?_ hp
    · rintro w ⟨a, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ <;> omega
    · intro ws _; exact Nat.zero_le 8
  have : (9 : Nat) ≤ w := of_decide_eq_true hd
  omega

/-- A toy finality floor: exactly the witness `9` is finalized, at depth 0 only. -/
def toyFloor : FinalityFloor Nat Nat where
  Finalized := fun d w => d = 0 ∧ w = 9
  visible := fun _ w => w = 9
  finalized_visible := fun _ _ h _ => h.2

/-- C TRUE: `⟨5⟩` is common at depth 0 (the finalized witness 9 verifies it). -/
theorem common_true : CommonAt toyFloor 0 (⟨5⟩ : Stmt) := ⟨9, ⟨rfl, rfl⟩, by decide⟩

/-- C FALSE: nothing is common at depth 1 (no witness finalized there). -/
theorem common_false : ¬ CommonAt toyFloor 1 (⟨5⟩ : Stmt) := by
  rintro ⟨w, ⟨h0, _⟩, _⟩
  exact absurd h0 (by decide)

/-- **THE E ⇏ C SEPARATION (constructive).** Over the private pockets `pock`, E_G holds
(`everyone_true`) yet NO finality floor whose visibility respects the pockets (members cannot see
witnesses they do not hold) can make `⟨5⟩` common at ANY depth: common knowledge needs ONE witness
visible to both agents (`common_shared_witness`), and pockets `{7}` and `{8}` share nothing. The
classical inclusion E ⊇ C is strict, and constructively the gap is exactly the missing SHARED
finalized witness — what the finality mechanism manufactures. -/
theorem no_common_for_private_pockets (floor : FinalityFloor Nat Nat)
    (hvis : ∀ a w, floor.visible a w → pock a w) (d : Nat) :
    ¬ CommonAt floor d (⟨5⟩ : Stmt) := by
  rintro ⟨w, hfin, _⟩
  have h0 := hvis 0 w (floor.finalized_visible d w hfin 0)
  have h1 := hvis 1 w (floor.finalized_visible d w hfin 1)
  rcases h0 with ⟨_, rfl⟩ | ⟨h, _⟩
  · rcases h1 with ⟨h, _⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)
  · exact absurd h (by decide)

end Demo

/-! ## §4 — MECHANISM INSTANCE: the council certification IS E_G.

Against the REAL actor-bound approval machinery of `Dregg2.Exec.Program` (`anyOf [immutable f,
senderIs k]`, the polis council's per-member slot binding, mirrored by the Rust e2e
`approval_slots_are_actor_bound`). The weld: an approval witness — a turn context under which the
member's slot-flip is ADMITTED — is necessarily SENT BY that member (`approval_witness_pins_sender`,
riding `actorBound_flip_requires_sender`). So a full certificate (every slot admitted-flipped) is
literally a tuple of per-member witnesses, each in its own member's pocket and in NO other's
(`approval_not_exhibitable_by_other`): the council certificate IS the E_G certificate, in the
indexed-family form (member `k` knows the approval-of-`k` statement). -/

section Council

open Dregg2.Exec

/-- The per-member approval binding (`Exec.Program.councilBound`, generalized): leaving slot `f`
alone is open to all; flipping it demands `sender = k`. -/
def approvalConstraint (slot : FieldName) (member : Int) : StateConstraint :=
  .anyOf [.immutable slot, .senderIs member]

/-- The approval STATEMENT: "member `member`'s slot `slot` was flipped (old → new) by an admitted
turn". Its witness is the turn context; `Verify` demands the binding admits AND the slot actually
flipped (an untouched slot is a ceremony turn, not an approval). -/
structure ApprovalStmt where
  slot : FieldName
  member : Int
  old : Value
  new : Value

/-- The approval verifier: admitted under the actor binding, and the slot genuinely flipped. -/
def approvalVerify (s : ApprovalStmt) (ctx : TurnCtx) : Bool :=
  evalConstraintCtx ctx (approvalConstraint s.slot s.member) s.old s.new
    && !(evalSimple (.immutable s.slot) s.old s.new)

instance : Verifiable ApprovalStmt TurnCtx := ⟨approvalVerify⟩

/-- Each member's pocket: the turn contexts it can author — exactly those bearing ITS sender
identity. (Capability possession alone does not move a context into another member's pocket;
sender identity is bound by the executor, not carried by the witness.) -/
def senderPocket : Pocket Int TurnCtx := fun a ctx => ctx.sender = some a

/-- **THE PIN — an approval witness is necessarily the member's own turn.** Any context
discharging member `k`'s approval statement has `sender = k`: the slot flipped (second conjunct),
so by `actorBound_flip_requires_sender` a non-`k` sender would have been REJECTED. The witness
for "k approved" can exist only in `k`'s pocket. -/
theorem approval_witness_pins_sender (s : ApprovalStmt) (ctx : TurnCtx)
    (h : Discharged s ctx) : ctx.sender = some s.member := by
  by_contra hne
  have h' : approvalVerify s ctx = true := h
  rw [approvalVerify, Bool.and_eq_true, Bool.not_eq_true'] at h'
  obtain ⟨hadm, hflip⟩ := h'
  have hrej := actorBound_flip_requires_sender s.member s.slot ctx s.old s.new hflip hne
  rw [approvalConstraint] at hadm
  rw [hrej] at hadm
  exact Bool.false_ne_true hadm

/-- **The council certification IS E_G (the mechanism-instance theorem).** If the certificate
exhibits, for every member `k` of the council `G`, an admitted flip of `k`'s slot (a discharging
context exists), then every member KNOWS its approval statement — the witness lands in `k`'s own
pocket automatically, by the pin. The certificate is per-member witnesses: E_G in the indexed
family form `(approval-of-k)_{k ∈ G}` (each member's discharge of the shared ceremony). -/
theorem council_certification_is_E (slotOf : Int → FieldName) (o n : Value) (G : List Int)
    (cert : ∀ k ∈ G, ∃ ctx : TurnCtx, Discharged (ApprovalStmt.mk (slotOf k) k o n) ctx) :
    ∀ k ∈ G, Knows senderPocket k (ApprovalStmt.mk (slotOf k) k o n) := by
  intro k hk
  obtain ⟨ctx, hctx⟩ := cert k hk
  exact ⟨ctx, approval_witness_pins_sender _ ctx hctx, hctx⟩

/-- **The per-member tooth — no other member can exhibit `k`'s approval.** The E_G certificate is
genuinely DISTRIBUTED over the members: agent `b ≠ k` holds no witness of `k`'s approval (its
pocket carries only `sender = b` contexts, and the pin demands `sender = k`). A stolen capability
cannot vote; neither can it CLAIM another's vote. -/
theorem approval_not_exhibitable_by_other (s : ApprovalStmt) (b : Int) (hb : b ≠ s.member) :
    ¬ Knows senderPocket b s := by
  rintro ⟨ctx, hp, hd⟩
  have hpin := approval_witness_pins_sender s ctx hd
  rw [hp] at hpin
  exact hb (Option.some.inj hpin)

/-- The concrete polis binding (slot `approve_a`, member 17), over a genuine flip. -/
def demoApproval : ApprovalStmt :=
  ⟨"approve_a", 17, .record [("approve_a", .int 0)], .record [("approve_a", .int 1)]⟩

/-- E-instance TRUE witness: member 17 knows its own approval (its turn is the witness). -/
theorem council_knows_true : Knows senderPocket 17 demoApproval :=
  ⟨{ sender := some 17 }, rfl, by decide⟩

/-- E-instance FALSE witness: member 99 — a real identity with a real capability — cannot exhibit
member 17's approval. -/
theorem council_knows_false : ¬ Knows senderPocket 99 demoApproval :=
  approval_not_exhibitable_by_other demoApproval 99 (by decide)

end Council

/-! ## §5 — MECHANISM INSTANCE: the threshold gate IS D_G.

Against the REAL Shamir/GF(256) algebra of `Dregg2.Distributed.ThresholdDecrypt` (the federation's
t-of-n threshold decryption). The weld: the pooled witness is the LAGRANGE RECONSTRUCTION at x = 0
(`reconstructByte`), each member's pocket holds exactly its SHARE (a point at x = i ≠ 0), and:

  * **D holds** — any 2 of the 3 golden share-holders combine to a verifying witness of the secret
    (`threshold_gate_is_D`, executing the real `reconstructByte`); the general any-t law is
    `quorum_pool_determines_secret` (= `shamir_any_t_reconstruct`, Mathlib-Lagrange).
  * **no K holds** — NO single member can exhibit a verifying witness: its share sits at x ≠ 0 and
    the secret lives at x = 0 (`no_single_member_knows`); the information-theoretic floor is
    `subthreshold_pool_blind` (= `shamir_below_t_undetermined`: < t shares are consistent with
    EVERY secret).

This is the precise sense in which D_G is "weaker than E_G but stronger than any single K_a":
WEAKER as a rung (E_G pools trivially, `everyone_to_distributed`), but its witness is one NO
single K_a possesses — `distributed_without_individual` packages the separation. -/

section Threshold

open Dregg2.Distributed.ThresholdDecrypt

/-- The secret statement: "the shared secret byte is `val`". -/
structure SecretStmt where
  val : Nat
  deriving DecidableEq, Repr

/-- A Shamir share point `(x, y)`; the secret is the point at `x = 0`. -/
structure SharePoint where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

/-- The secret verifier: a witness verifies iff it is the point AT ZERO carrying the secret —
exactly the protocol's "evaluation points are 1..n, point 0 is the secret" discipline. -/
def secretVerify (s : SecretStmt) (w : SharePoint) : Bool :=
  w.x == 0 && w.y == s.val

instance : Verifiable SecretStmt SharePoint := ⟨secretVerify⟩

/-- The Lagrange pool: combining shares = interpolating at x = 0 with the REAL `reconstructByte`
(the executable transcription of `shamir_reconstruct_byte`, pinned byte-for-byte to the Rust). -/
def lagrangePool : PoolOps SharePoint where
  combine := fun ws => ⟨0, reconstructByte (ws.map fun w => (w.x, w.y))⟩

/-- The golden sharing (`test_shamir_single_byte_roundtrip`): secret `0x42`, polynomial
`f(x) = 0x42 + 0xAB·x`, member `i` holds the point `(i, f(i))`. -/
def shareOf (i : Nat) : SharePoint := ⟨i, 0x42 ^^^ gf256Mul 0xAB i⟩

/-- Each validator's pocket: exactly its own share. -/
def goldenPocket : Pocket Nat SharePoint := fun i w => w = shareOf i

/-- A share at `x ≠ 0` NEVER verifies the secret statement — the verifier demands the point at
zero. (The structural half of "no member alone knows"; the information-theoretic half is
`subthreshold_pool_blind`.) -/
theorem share_alone_never_verifies (s : SecretStmt) (w : SharePoint) (hx : w.x ≠ 0) :
    ¬ Discharged s w := by
  intro h
  have h' : secretVerify s w = true := h
  rw [secretVerify, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h'
  exact hx h'.1

set_option maxRecDepth 8192 in
/-- The 2-of-3 reconstruction verifies: combining members 1 and 2's shares with the REAL Lagrange
interpolation recovers `(0, 0x42)` — executed by `decide` through `gf256Mul`/`gf256Inv` (the
recursion-depth bump pays for the 8-round carry-less multiplies under kernel reduction). -/
theorem two_shares_reconstruct :
    Discharged (⟨0x42⟩ : SecretStmt) (lagrangePool.combine [shareOf 1, shareOf 2]) := by
  decide

/-- **The threshold gate IS the threshold rung of D_G**: members {1, 2} of the federation {1, 2, 3}
satisfy `ThresholdKnows` at threshold 2 — distinct quorum members, each exhibiting its own share,
whose single combine verifies the secret. -/
theorem threshold_knows_secret :
    ThresholdKnows lagrangePool goldenPocket [1, 2, 3] 2 (⟨0x42⟩ : SecretStmt) := by
  refine ⟨[1, 2], shareOf, ?_, by decide, by decide, ?_, two_shares_reconstruct⟩
  · intro a ha; fin_cases ha <;> simp
  · intro a _; rfl

/-- **The threshold gate IS D_G (the mechanism-instance theorem).** -/
theorem threshold_gate_is_D :
    DistributedKnows lagrangePool goldenPocket [1, 2, 3] (⟨0x42⟩ : SecretStmt) :=
  threshold_to_distributed lagrangePool threshold_knows_secret

/-- **No member alone knows**: each validator's pocket holds only its own share, at `x ∈ {1,2,3}`,
never at zero — no single K_a. -/
theorem no_single_member_knows :
    ∀ i ∈ [1, 2, 3], ¬ Knows goldenPocket i (⟨0x42⟩ : SecretStmt) := by
  intro i hi
  rintro ⟨w, rfl, hd⟩
  refine share_alone_never_verifies _ _ ?_ hd
  rcases (by simpa using hi : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl <;> decide

/-- **THE D-WITHOUT-K SEPARATION, packaged**: the group distributedly knows the secret while no
member individually does — "pooled info entails φ, no member alone knows", witnessed on the real
threshold-decryption algebra. -/
theorem distributed_without_individual :
    DistributedKnows lagrangePool goldenPocket [1, 2, 3] (⟨0x42⟩ : SecretStmt)
      ∧ ∀ i ∈ [1, 2, 3], ¬ Knows goldenPocket i (⟨0x42⟩ : SecretStmt) :=
  ⟨threshold_gate_is_D, no_single_member_knows⟩

/-- The gate's admission IS the quorum leg of `ThresholdKnows`: `combineAdmits shares t = true`
yields the threshold cardinality, the no-reserved-index discipline, and distinctness — the three
side conditions of the threshold rung (delegates to `combine_admits_iff`, the gate's exact
characterization). -/
theorem gate_admission_gives_quorum_leg (shares : List Share) (t : Nat)
    (h : combineAdmits shares t = true) :
    t ≤ shares.length ∧ (∀ s ∈ shares, s.idx ≠ 0) ∧ (shares.map (·.idx)).Nodup :=
  (combine_admits_iff shares t).mp h

/-- **The general any-t entailment (D_G's positive face, abstract field).** Any `t` distinct
share-holders' pooled shares determine the secret — Lagrange interpolation at 0 of a degree-< t
sharing polynomial recovers `f(0)`. Delegates to `shamir_any_t_reconstruct` (proved via Mathlib's
`Lagrange.eq_interpolate`); restated here under its epistemic reading: the QUORUM's pooled
information ENTAILS the secret, constructively (the interpolation is the pooling computation). -/
theorem quorum_pool_determines_secret {F : Type*} [Field F]
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → F)
    (hinj : Set.InjOn x S) (f : Polynomial F)
    (hdeg : f.degree < S.card) (s : F) (hsecret : f.eval 0 = s) :
    (Lagrange.interpolate S x (fun i => f.eval (x i))).eval 0 = s :=
  shamir_any_t_reconstruct S x hinj f hdeg s hsecret

/-- **The sub-threshold blindness (D_G's negative face, abstract field).** A sub-quorum's pooled
shares are consistent with EVERY secret (two sharings agreeing on all observed points whose
secrets differ by any prescribed gap) — so below threshold not even the COALITION knows, let alone
a member. Delegates to `shamir_below_t_undetermined`; the epistemic reading: pooled information
below the threshold entails NOTHING about the secret (information-theoretic, not computational). -/
theorem subthreshold_pool_blind {F : Type*} [Field F]
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → F)
    (hinj : Set.InjOn x S) (h0 : ∀ i ∈ S, x i ≠ 0)
    (vals : ι → F) (s₀ s₁ : F) :
    ∃ f₀ f₁ : Polynomial F,
      (∀ i ∈ S, f₀.eval (x i) = vals i) ∧ (∀ i ∈ S, f₁.eval (x i) = vals i)
        ∧ f₀.eval 0 - f₁.eval 0 = s₀ - s₁ :=
  shamir_below_t_undetermined S x hinj h0 vals s₀ s₁

end Threshold

/-! ## §6 — MECHANISM INSTANCE: finality-at-depth IS the C_G constructor.

Against the REAL light-client finality of `Dregg2.Distributed.FinalizedLightClient`: the witness
is the `FinalityCert` itself (the super-ratification evidence over the node's REAL
`ordering.rs::tau` rule), `Finalized d cert := CertValid cert ∧ cert.wave = d`, and visibility is
the light-client check — which is verifier-INDEX-FREE (`cert_visibility_uniform`): the same cert
verdict for every agent. That index-freeness is exactly the `Transferable` (public) endpoint of
the DV dial (`Authority.DesignatedVerifier.publicMode_collapses_to_universal`) — and it is WHY
finality can manufacture common knowledge at all: one transferable witness, identically checkable
by every member, is the shared witness C_G demands. A DESIGNATED-verifier witness could never
seed C_G (§7).

Honesty: the floor law here says a `CertValid` cert is visible to all — i.e. the cert has been
DELIVERED and every light client runs the same check. Delivery under partition is exactly what
fails, which is the §9 killer example; and at n = 1 the constructor collapses per
`knows_to_common_single`. Non-vacuity of `CertValid` itself is witnessed executably in
`FinalizedLightClient` §5b (`realCert` over `trace3`, `#guard`-evaluated through the node's real
finality rule); `finality_is_common` is parametric in the cert exactly as
`finalized_light_client_fires_for` is. -/

section Finality

open Dregg2.Distributed.FinalizedLightClient
open Dregg2.Distributed.BlocklaceFinality (superMajority)

/-- The root statement: "the finalized state root is `root`". -/
structure RootStmt where
  root : Int
  deriving DecidableEq

/-- The light-client verifier of a root statement: the cert exhibits the super-ratification
quorum (`CertQuorum`, the node's real counting rule) and binds this root. NOTE: no verifier
index — every agent computes the same verdict. -/
def rootVerify (s : RootStmt) (cert : FinalityCert) : Bool :=
  CertQuorum cert && (cert.finalizedRoot == s.root)

instance : Verifiable RootStmt FinalityCert := ⟨rootVerify⟩

variable (Agent : Type u)

/-- The REAL finality floor: a cert is finalized at depth `d` iff it is `CertValid` (its anchor IS
the unique final leader the node's tau rule anchors) for wave `d`; visibility is the (agent-
independent) validity check itself. The floor law is definitional BECAUSE the check is
index-free — the honest content is that validity does not depend on who verifies. -/
def certFloor : FinalityFloor Agent FinalityCert where
  Finalized := fun d cert => CertValid cert ∧ cert.wave = d
  visible := fun _ cert => CertValid cert
  finalized_visible := fun _ _ h _ => h.1

/-- **Finality IS the C_G constructor (the mechanism-instance theorem).** A genuine finality
certificate — `CertValid`, i.e. the node's real super-ratification rule anchored its leader —
makes its finalized root COMMON knowledge at its wave: the cert is the one shared witness, its
quorum leg holds by `certValid_has_quorum`, and it binds its own root. -/
theorem finality_is_common (cert : FinalityCert) (hv : CertValid cert) :
    CommonAt (certFloor Agent) cert.wave (⟨cert.finalizedRoot⟩ : RootStmt) := by
  refine ⟨cert, ⟨hv, rfl⟩, ?_⟩
  show rootVerify ⟨cert.finalizedRoot⟩ cert = true
  rw [rootVerify, certValid_has_quorum cert hv]
  simp

/-- The C → E instance over the real floor: a finalized root is known to EVERY member of any
group, each exhibiting the SAME cert. -/
theorem finalized_root_known_to_all (cert : FinalityCert) (hv : CertValid cert) (G : List Agent) :
    EveryoneKnows (certFloor Agent).visible G (⟨cert.finalizedRoot⟩ : RootStmt) :=
  common_to_everyone (certFloor Agent) G (finality_is_common Agent cert hv)

/-- **Light-client visibility is verifier-uniform** — the same cert verdict for every agent
(definitionally: the check takes no agent). This is the `Transferable`/public endpoint of the DV
dial, and the precondition for finality to seed COMMON knowledge: a designated-verifier witness
(§7) has no such uniformity and cannot. -/
theorem cert_visibility_uniform (a b : Agent) (cert : FinalityCert) :
    (certFloor Agent).visible a cert ↔ (certFloor Agent).visible b cert :=
  Iff.rfl

/-- **No conflicting common knowledge per wave (the uniqueness tooth).** Two valid certs over the
same view (lace, participants, wave, wavelength) anchor the SAME leader — `CertValid` pins the
anchor to the deterministic `finalLeaderAt`, so common knowledge at a wave is unique: the C_G
constructor can never be run twice with conflicting content on one view. (Cross-view conflicts
are excluded by the quorum-overlap theorems of `BlsQuorumCert` /
`BlocklaceFinality.finalLeaders_one_per_wave`.) -/
theorem no_conflicting_common_per_wave (c₁ c₂ : FinalityCert)
    (h₁ : CertValid c₁) (h₂ : CertValid c₂)
    (hl : c₁.lace = c₂.lace) (hp : c₁.participants = c₂.participants)
    (hw : c₁.wave = c₂.wave) (hwl : c₁.wavelength = c₂.wavelength) :
    c₁.anchor = c₂.anchor := by
  unfold CertValid at h₁ h₂
  rw [hl, hp, hw, hwl] at h₁
  rw [h₁] at h₂
  exact Option.some.inj h₂

end Finality

/-! ## §7 — MECHANISM INSTANCE: non-transferable K_a (the DesignatedVerifier machinery).

The separation the DV dial creates at the TOWER level: with a verifier-INDEXED discharge
(`DV.DischargedFor`), forwarding the witness moves the TRANSCRIPT but not the KNOWLEDGE. Over the
reference DV kernel: `v0`'s designated transcript is in EVERYONE's pocket (forwarded), `v0` knows,
yet `vOther` — holding the very same witness — does NOT know: `DischargedFor vOther` rejects it.
So DV-K_a does not lift to E_G on forwarding (`dv_forwarding_no_E`), while a `Transferable`
(public-endpoint) witness lifts along ANY pocket (`transferable_forwarding_lifts`). Possession of
a witness is knowledge ONLY at the transferable endpoint of the dial — the formal content of
"privateTo" (§9). -/

section DV

open Dregg2.Authority.DV
open Dregg2.Authority.DV.Reference

/-- Verifier-indexed knowledge — `Knows` with the DV-indexed discharge: agent `a` can exhibit a
transcript that discharges `stmt` FOR `a`. The index is the whole point: the same transcript can
discharge for one verifier and not another. -/
def KnowsFor {Verifier Statement Proof VSecret : Type}
    [DVKernel Verifier Statement Proof VSecret]
    (pocket : Pocket Verifier Proof) (a : Verifier) (stmt : Statement) : Prop :=
  ∃ p : Proof, pocket a p ∧ DischargedFor (VSecret := VSecret) a stmt p

/-- The FORWARDED pocket: `v0`'s designated transcript has been handed to every verifier — total
possession, the strongest forwarding scenario. -/
def forwardedPocket : Pocket V Prf := fun _ p => p = designatedProof

/-- The designated verifier KNOWS: its own transcript discharges for it. -/
theorem dv_designated_knows : KnowsFor (VSecret := VSec) forwardedPocket V.v0 7 := by
  refine ⟨designatedProof, rfl, ?_⟩
  unfold DischargedFor designatedProof
  simp [DVKernel.verifyFor, vrfy, sim, secretOf]

/-- **The forwarding separation**: `vOther` HOLDS the forwarded transcript yet does NOT know —
the transcript does not discharge for it (it could have been `v0`'s own simulation; the DV
deniability). Possession ≠ knowledge off the transferable endpoint. -/
theorem dv_forwarding_fails : ¬ KnowsFor (VSecret := VSec) forwardedPocket V.vOther 7 := by
  rintro ⟨p, rfl, h⟩
  unfold DischargedFor designatedProof at h
  simp [DVKernel.verifyFor, vrfy, sim, secretOf] at h

/-- **DV knowledge does not lift to E_G on forwarding (the separation, packaged).** The designated
verifier knows, the witness is universally forwarded, and STILL not everyone knows. The witnessed
failure of the classical "hand over the proof, transfer the knowledge" — exactly what the
`privateTo` atom (§9) buys. -/
theorem dv_forwarding_no_E :
    KnowsFor (VSecret := VSec) forwardedPocket V.v0 7
      ∧ ¬ (∀ a : V, KnowsFor (VSecret := VSec) forwardedPocket a 7) :=
  ⟨dv_designated_knows, fun h => dv_forwarding_fails (h V.vOther)⟩

/-- **The contrast: a TRANSFERABLE witness lifts along any pocket.** At the public endpoint of the
DV dial (`Transferable`: the transcript convinces every verifier), forwarding the witness DOES
transfer the knowledge — whoever holds it, knows. The two endpoints of the dial are exactly
"forwarding lifts" vs "forwarding fails": transferability is the dial-position of K_a. -/
theorem transferable_forwarding_lifts {Verifier Statement Proof VSecret : Type}
    [DVKernel Verifier Statement Proof VSecret]
    (pocket : Pocket Verifier Proof) (stmt : Statement) (p : Proof)
    (htr : Transferable Verifier (VSecret := VSecret) stmt p)
    (a : Verifier) (hp : pocket a p) :
    KnowsFor (VSecret := VSecret) pocket a stmt :=
  ⟨p, hp, htr a⟩

end DV

/-! ## §8 — THE ADJOINT STRUCTURE: the graded triple `∃_a ⊣ q_a* ⊣ ∀_a` over the witness fibration.

The fibration: the HOLDING span `Holding pocket = {(a, w) // pocket a w}` with `agentOf` (the
grading projection to agents) and `witOf` (the projection to witnesses). Predicates over witnesses
pull back along `witOf` (`q* = reindex`), then quantify along `agentOf`:

  * `KnowsSet φ = ∃_{agentOf} (witOf* (Truth φ))` — and §8a PINS `Knows` to this LEFT-adjoint
    composite (`mem_knowsSet_iff`): constructive knowledge IS the ∃ of the doctrine. This is the
    constructive-knowledge correction made formal: authority/knowledge = PRODUCTION of a witness
    (∃, image), never descent (∀).
  * `BoxSet φ = ∀_{agentOf} (witOf* (Truth φ))` — the right-adjoint modality: "EVERY witness the
    agent can exhibit verifies φ" (the agent's pocket is φ-homogeneous).

STATUS of the carried open core "faithful ∀_a = Knows" — resolved precisely, not faked:

  * the TRIPLE ITSELF: **PROVED** — both Galois connections (`epistemic_triple`, instantiating
    `Lawvere.PartA.lawvere_triple` at the holding projection), with unit (`exists_unit`), counit
    (`box_counit`), and Frobenius (`frobenius_for_knowledge`). All adjunction laws hold.
  * `∀_a = Knows` **HOLDS iff the holding relation is functional**: with exactly one credential
    per agent the diamond and box composites COINCIDE (`knowsSet_eq_boxSet_of_functional`) — on
    single-witness pockets the constructive Knows IS the right adjoint ∀_a, faithfully.
  * the D-axiom direction `□ ⊆ ◇` needs only pocket inhabitation (`box_to_knows_of_inhabited`).
  * **THE NAMED OBSTRUCTION** (for general pockets): the comparison `◇ ⊆ □` — equivalently the
    invertibility of the canonical `∃_a ⇒ ∀_a` map — FAILS at MIXED pockets (an agent holding
    both a verifying and a non-verifying witness): witnessed FALSE in `MixedPocket.knows_ne_box`.
    This is NOT a failure of any unit/counit of the triple (those are proved); it is the
    modal collapse ◇=□ demanding a functional fibration. The general `Knows` is irreducibly the
    LEFT adjoint — which is the thesis, not a defect. -/

section Hyperdoctrine

open Dregg2.Metatheory.Lawvere.PartA

/-- The HOLDING fibration's total space: pairs `(a, w)` with `w` in `a`'s pocket. -/
def Holding (pocket : Pocket Agent W) := { p : Agent × W // pocket p.1 p.2 }

/-- The grading projection to agents (the base of the graded modality). -/
def agentOf (pocket : Pocket Agent W) : Holding pocket → Agent := fun h => h.val.1

/-- The witness projection (the substitution leg `q_a`). -/
def witOf (pocket : Pocket Agent W) : Holding pocket → W := fun h => h.val.2

/-- The EXTENSION of a predicate: its verifying witnesses (the `Truth` functor of the doctrine —
the image of the `Predicate ⊣ Witness` seam in `Set W`). -/
def Truth [Verifiable P W] (φ : P) : Set W := { w | Discharged φ w }

/-- `◇_a` — the agents that can EXHIBIT a verifying witness: `∃_{agentOf} ∘ witOf*`. -/
def KnowsSet [Verifiable P W] (pocket : Pocket Agent W) (φ : P) : Set Agent :=
  existsAlong (agentOf pocket) (reindex (witOf pocket) (Truth (W := W) φ))

/-- `□_a` — the agents whose EVERY exhibitable witness verifies: `∀_{agentOf} ∘ witOf*`. -/
def BoxSet [Verifiable P W] (pocket : Pocket Agent W) (φ : P) : Set Agent :=
  forallAlong (agentOf pocket) (reindex (witOf pocket) (Truth (W := W) φ))

/-- **`Knows` IS the left-adjoint composite** — the operator of §2 is pointwise the doctrine's
`∃_{agentOf} ∘ witOf*`. The constructive K_a is the ∃ of the hyperdoctrine, pinned. -/
theorem mem_knowsSet_iff [Verifiable P W] (pocket : Pocket Agent W) (φ : P) (a : Agent) :
    a ∈ KnowsSet pocket φ ↔ Knows pocket a φ := by
  simp only [KnowsSet, existsAlong, reindex, Set.mem_image, Set.mem_preimage, Truth,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, hT, rfl⟩
    exact ⟨h.val.2, h.property, hT⟩
  · rintro ⟨w, hpw, hdis⟩
    exact ⟨⟨(a, w), hpw⟩, hdis, rfl⟩

/-- `□_a` membership characterization: every pocketed witness verifies. -/
theorem mem_boxSet_iff [Verifiable P W] (pocket : Pocket Agent W) (φ : P) (a : Agent) :
    a ∈ BoxSet pocket φ ↔ ∀ w : W, pocket a w → Discharged φ w := by
  simp only [BoxSet, forallAlong, Set.kernImage, reindex, Set.mem_setOf_eq, Set.mem_preimage,
    Truth]
  constructor
  · intro h w hpw
    exact h (show agentOf pocket ⟨(a, w), hpw⟩ = a from rfl)
  · rintro h ⟨⟨a', w⟩, hp⟩ rfl
    exact h w hp

/-- **THE TRIPLE `∃_a ⊣ q_a* ⊣ ∀_a`, PROVED** — both Galois connections, instantiated at the
holding fibration's grading projection (delegating to the proven `Lawvere.PartA.lawvere_triple`).
The adjoint structure of the epistemic modalities EXISTS over the witness semantics. -/
theorem epistemic_triple (pocket : Pocket Agent W) :
    GaloisConnection (existsAlong (agentOf pocket)) (reindex (agentOf pocket))
      ∧ GaloisConnection (reindex (agentOf pocket)) (forallAlong (agentOf pocket)) :=
  lawvere_triple (agentOf pocket)

/-- The unit of `∃_a ⊣ q_a*` over the fibration: every holding lands in the reindexed image of its
own quantification. -/
theorem exists_unit (pocket : Pocket Agent W) (S : Set (Holding pocket)) :
    S ⊆ reindex (agentOf pocket) (existsAlong (agentOf pocket) S) :=
  reindex_existsAlong_unit (agentOf pocket) S

/-- The counit of `q_a* ⊣ ∀_a` over the fibration (the ∀-right-adjoint law against the holding
data): reindexing the box back into the total space lands inside the original predicate. -/
theorem box_counit (pocket : Pocket Agent W) (T : Set (Holding pocket)) :
    reindex (agentOf pocket) (forallAlong (agentOf pocket) T) ⊆ T :=
  reindex_forallAlong_counit (agentOf pocket) T

/-- Frobenius reciprocity for knowledge: `∃_a` is a module map over reindexing — quantifying a
conjunction with a reindexed agent-predicate exports the agent-predicate. -/
theorem frobenius_for_knowledge (pocket : Pocket Agent W)
    (S : Set (Holding pocket)) (T : Set Agent) :
    existsAlong (agentOf pocket) (S ∩ reindex (agentOf pocket) T)
      = existsAlong (agentOf pocket) S ∩ T :=
  frobenius (agentOf pocket) S T

/-- The D-axiom direction `□ ⊆ ◇` under SERIALITY (an inhabited pocket): an agent whose every
witness verifies, and who holds at least one, can exhibit one. -/
theorem box_to_knows_of_inhabited [Verifiable P W] (pocket : Pocket Agent W) (a : Agent) (φ : P)
    (hser : ∃ w : W, pocket a w) (h : a ∈ BoxSet pocket φ) : a ∈ KnowsSet pocket φ := by
  obtain ⟨w, hw⟩ := hser
  rw [mem_boxSet_iff] at h
  rw [mem_knowsSet_iff]
  exact ⟨w, hw, h w hw⟩

/-- **The FAITHFUL `∀_a = Knows` — proved exactly where it holds.** On a FUNCTIONAL holding
relation (each agent holds exactly one credential), the left- and right-adjoint composites
COINCIDE: `KnowsSet = BoxSet`, i.e. the constructive Knows IS the right adjoint `∀_a`. The
single-credential discipline is the precise hypothesis under which the classical box reading of
knowledge is constructively faithful. -/
theorem knowsSet_eq_boxSet_of_functional [Verifiable P W] (pocket : Pocket Agent W)
    (hfun : ∀ a : Agent, ∃! w : W, pocket a w) (φ : P) :
    KnowsSet pocket φ = BoxSet pocket φ := by
  ext a
  rw [mem_knowsSet_iff, mem_boxSet_iff]
  obtain ⟨w₀, hw₀, huniq⟩ := hfun a
  constructor
  · rintro ⟨w, hpw, hdis⟩ w' hpw'
    rw [huniq w' hpw']
    rw [huniq w hpw] at hdis
    exact hdis
  · intro h
    exact ⟨w₀, hw₀, h w₀ hw₀⟩

/-! **THE OBSTRUCTION, WITNESSED** — at a MIXED pocket (one agent, two witnesses: one verifying,
one not), the comparison `◇ ⊆ □` fails: `KnowsSet ≠ BoxSet`. The faithful `∀_a = Knows` is NOT a
theorem for relational pockets; the failing law is precisely the modal collapse `∃_a ⇒ ∀_a` (NOT
any unit/counit of the triple, which are proved above). Knowledge-as-production survives mixture;
knowledge-as-descent does not. -/
namespace MixedPocket

/-- A statement verified exactly by the witness `true`. -/
structure S where

instance : Verifiable S Bool := ⟨fun _ w => w⟩

/-- The mixed pocket: the one agent holds BOTH Boolean witnesses. -/
def allPocket : Pocket Unit Bool := fun _ _ => True

theorem knows_holds : () ∈ KnowsSet allPocket (⟨⟩ : S) := by
  rw [mem_knowsSet_iff]
  exact ⟨true, trivial, by rfl⟩

theorem box_fails : () ∉ BoxSet allPocket (⟨⟩ : S) := by
  rw [mem_boxSet_iff]
  intro h
  exact Bool.false_ne_true (h false trivial)

/-- `◇ ≠ □` at the mixed pocket — the named obstruction to the unconditional faithful triple. -/
theorem knows_ne_box : KnowsSet allPocket (⟨⟩ : S) ≠ BoxSet allPocket (⟨⟩ : S) := by
  intro h
  exact box_fails (h ▸ knows_holds)

end MixedPocket

end Hyperdoctrine

/-! ## §9 — GUARD-ATOM DESIGNS (design ONLY — the temporal-algebra lane owns the install point).

The four epistemic guard atoms, with their COORDINATION-COST classification:

  * **`knownBy a`** (K_a) — admits iff `a` exhibits a verifying witness. Cost: **FREE** — a local
    witness check at evaluation time (one `Verify` call against the presented witness; the
    macaroon-discharge shape: present + re-check).
  * **`privateTo v`** (DV-K_v) — admits iff `v` exhibits a witness that discharges FOR `v`, with
    the transcript non-transferable. Cost: **FREE** (the same local check, verifier-indexed); its
    price is paid in EXPRESSIVITY, not latency: the witness cannot seed E/C (§7).
  * **`distributedAmong G k`** (D_G, threshold shape) — admits iff `k` distinct members of `G`
    exhibit shares whose combine verifies. Cost: **QUORUM LATENCY** — one threshold round
    (collect k shares + one reconstruction; the `combineAdmits` gate of `ThresholdDecrypt`).
  * **`commonAt d`** (C_G) — admits iff a verifying witness is finalized at depth `d`. Cost:
    **FINALITY LATENCY** — wait for the wave's super-ratification (the `CertValid` rule); the
    price of partition-safety, by the killer theorem below.

Install-point contract (for the temporal lane): these denote into the §2 operators via
`EpistemicAtom.denotes`; an installation should mirror the `evalSimpleCtx` fail-closed discipline
(absent witness/cert ⇒ reject) and the `TurnCtx` shape (the cert/share evidence rides the turn
context the way `revealedHash` does). NOT installed here — `Exec.Program` is untouched. -/

section Atoms

/-- The coordination-cost ladder of the epistemic atoms. -/
inductive CoordCost where
  /-- A local witness check — no coordination. -/
  | free
  /-- One threshold round — collect k shares and combine. -/
  | quorumLatency
  /-- Wait for finality — the wave's super-ratification. -/
  | finalityLatency
  deriving DecidableEq, Repr

/-- The epistemic guard atoms (DESIGN — signatures + denotation; installation owned by the
temporal-algebra lane). Agent identities follow the `senderIs` convention (`Int` sender ids). -/
inductive EpistemicAtom where
  /-- K: admit iff `agent` exhibits a verifying witness. -/
  | knownBy (agent : Int)
  /-- D (threshold shape): admit iff `k` distinct members of `group` pool a verifying witness. -/
  | distributedAmong (group : List Int) (k : Nat)
  /-- C: admit iff a verifying witness is finalized at `depth`. -/
  | commonAt (depth : Nat)
  /-- DV: admit iff `verifier` exhibits a designated (non-transferable) witness. -/
  | privateTo (verifier : Int)
  deriving DecidableEq, Repr

/-- The cost classification: K and DV-K are free; D pays one quorum round; C pays finality. -/
def EpistemicAtom.cost : EpistemicAtom → CoordCost
  | .knownBy _           => .free
  | .privateTo _         => .free
  | .distributedAmong .. => .quorumLatency
  | .commonAt _          => .finalityLatency

example : (EpistemicAtom.knownBy 17).cost = .free := rfl
example : (EpistemicAtom.distributedAmong [1, 2, 3] 2).cost = .quorumLatency := rfl
example : (EpistemicAtom.commonAt 0).cost = .finalityLatency := rfl
example : (EpistemicAtom.privateTo 5).cost = .free := rfl

/-- The denotation of each atom into the §2 tower operators — the semantics an installation must
realize. `privateTo` denotes the designated shape: the verifier knows AND the witness does not
universally lift (the `DesignatedFor` conjunction at tower level). -/
def EpistemicAtom.denotes [Verifiable P W] (pocket : Pocket Int W) (pool : PoolOps W)
    (floor : FinalityFloor Int W) : EpistemicAtom → P → Prop
  | .knownBy a,             φ => Knows pocket a φ
  | .distributedAmong G k,  φ => ThresholdKnows pool pocket G k φ
  | .commonAt d,            φ => CommonAt floor d φ
  | .privateTo v,           φ => Knows pocket v φ ∧ ¬ ∀ a : Int, Knows pocket a φ

/-! ### §9b — THE KILLER EXAMPLE, AS THEOREMS: `commonAt`-guarded bridge settlement is
partition-safe; the unguarded version double-settles.

The scenario: a bridge cell settles a cross-chain transfer when its guard admits. A network
partition splits the `n` validators into two sides (`sideA + sideB = n`); each side sees only its
own members' approvals/ratifications.

  * **UNGUARDED** (settle on any locally-visible approval — the K/E shape): BOTH sides settle —
    the double-settlement that mints the bridged asset twice. `unguarded_double_settles` exhibits
    the counterexample (n = 4 split 2/2).
  * **`commonAt`-GUARDED** (settle only with the C_G constructor's evidence — `superMajority n`
    distinct ratifiers, the cert quorum leg of `CertValid`/`isSuperRatified`): the two sides can
    NEVER both settle, for ANY partition of ANY committee size — because two disjoint
    super-majorities cannot coexist (`superMajority_gt_half`). At most one side (the one holding a
    quorum, if any) settles; safety is unconditional, liveness waits for the partition to heal —
    the finality latency of `CoordCost.finalityLatency`, priced exactly here. -/

open Dregg2.Distributed.BlocklaceFinality (superMajority)

/-- A super-majority is a strict majority: `2 · superMajority n > n` — two disjoint
super-majorities cannot fit in one committee. (The counting heart of the partition-safety; the
full no-conflicting-finality story adds the honest-overlap theorems of `BlsQuorumCert`.) -/
theorem superMajority_gt_half (n : Nat) : n < 2 * superMajority n := by
  show n < 2 * (n * 2 / 3 + 1)
  omega

/-- A partition of the committee: two sides covering the `total` validators. Each side can count
at most its own members as visible approvals/ratifiers. -/
structure Partition where
  total : Nat
  sideA : Nat
  sideB : Nat
  covers : sideA + sideB = total

/-- The UNGUARDED settlement rule: settle on any locally-visible approval. -/
def UnguardedSettles (visibleApprovals : Nat) : Prop := 1 ≤ visibleApprovals

/-- The `commonAt`-GUARDED settlement rule: settle only with the C_G constructor's quorum —
`superMajority total` distinct ratifiers (the counting leg of `isSuperRatified`, which `CertValid`
demands). -/
def CommonAtGuardSettles (total visibleRatifiers : Nat) : Prop :=
  superMajority total ≤ visibleRatifiers

/-- **The unguarded bridge DOUBLE-SETTLES under partition** — the counterexample: 4 validators
split 2/2, each side sees an approval, both settle. The bridged asset is minted twice. -/
theorem unguarded_double_settles :
    ∃ pt : Partition, UnguardedSettles pt.sideA ∧ UnguardedSettles pt.sideB :=
  ⟨⟨4, 2, 2, rfl⟩, by unfold UnguardedSettles; decide, by unfold UnguardedSettles; decide⟩

/-- **`commonAt`-guarded settlement is PARTITION-SAFE** — for EVERY partition of EVERY committee
size, the two sides cannot both satisfy the C_G quorum: two disjoint super-majorities cannot
coexist. The guard converts the double-settlement counterexample into at-most-one-side settlement
unconditionally; the price is finality latency, never safety. -/
theorem commonAt_guard_partition_safe (pt : Partition) :
    ¬ (CommonAtGuardSettles pt.total pt.sideA ∧ CommonAtGuardSettles pt.total pt.sideB) := by
  rintro ⟨ha, hb⟩
  have hgt := superMajority_gt_half pt.total
  have hc := pt.covers
  unfold CommonAtGuardSettles at ha hb
  omega

/-- The guarded rule is non-vacuous on the POSITIVE side too: an unpartitioned committee (one side
holding everyone) settles — 4 of 4 meets `superMajority 4 = 3`. Safety did not buy deadness. -/
theorem commonAt_guard_settles_when_healed : CommonAtGuardSettles 4 4 := by
  unfold CommonAtGuardSettles; decide

end Atoms

/-! ## §10 — Axiom hygiene: the whole tower is kernel-clean
(⊆ {propext, Classical.choice, Quot.sound}; the crypto floor lives in the consumed modules, named
there). -/

-- the tower
#assert_axioms pooled_invariant
#assert_axioms knows_to_distributed
#assert_axioms everyone_to_distributed
#assert_axioms threshold_to_distributed
#assert_axioms common_to_everyone
#assert_axioms common_shared_witness
#assert_axioms common_gives_mutual_witness
#assert_axioms knows_to_common_single
-- the separations
#assert_axioms Demo.no_common_for_private_pockets
#assert_axioms Demo.distributed_false
-- mechanism instances
#assert_axioms approval_witness_pins_sender
#assert_axioms council_certification_is_E
#assert_axioms approval_not_exhibitable_by_other
#assert_axioms threshold_gate_is_D
#assert_axioms no_single_member_knows
#assert_axioms distributed_without_individual
#assert_axioms quorum_pool_determines_secret
#assert_axioms subthreshold_pool_blind
#assert_axioms finality_is_common
#assert_axioms finalized_root_known_to_all
#assert_axioms no_conflicting_common_per_wave
#assert_axioms dv_forwarding_no_E
#assert_axioms transferable_forwarding_lifts
-- the adjoint structure
#assert_axioms mem_knowsSet_iff
#assert_axioms mem_boxSet_iff
#assert_axioms epistemic_triple
#assert_axioms box_counit
#assert_axioms frobenius_for_knowledge
#assert_axioms box_to_knows_of_inhabited
#assert_axioms knowsSet_eq_boxSet_of_functional
#assert_axioms MixedPocket.knows_ne_box
-- the killer example
#assert_axioms superMajority_gt_half
#assert_axioms unguarded_double_settles
#assert_axioms commonAt_guard_partition_safe

end Dregg2.Authority.Epistemic
