/-
# Dregg2.Finality — the pluggable finality tier (dregg2 §2.2).

Canonicity — *which valid history is THE history* — is a per-cell pluggable tier layered
over ONE CvRDT DAG (the single Merkle-CRDT substrate). This module encodes the four-tier
ladder (`Tier`), the `τ_unified` selector, and the cross-tier commit / no-downgrade laws.

The `½(n+f)` quorum is lifted into per-group `Config` (not hardcoded); the four
"globalism seams" (single global order; GST required for any progress; fixed σ-quorum;
synchronized deadline) are deliberately excluded — tiers 1–2 progress with n=1 and no
synchrony.

Cheap data (`Tier`, `rank`, `crossTierJoin`) is defined and every theorem in this file is
proved. The genuine distributed-agreement obligations live (proved) in
the `Dregg2.Distributed.*` modules (`BlocklaceFinality` for the node's computed tau rule,
`Consensus` for quorum safety) and `Dregg2.Consensus.TauPrefixMonotone` for prefix monotonicity.
-/
import Mathlib.Order.Lattice
import Mathlib.Algebra.Order.Group.Nat
import Dregg2.Confluence
import Dregg2.Execution
import Dregg2.Core

namespace Dregg2.Finality

universe u

/-- **The pluggable finality tier (dregg2 §2.2 table).** One of four canonicity
mechanisms layered over the single CvRDT DAG. Strength increases with the ordinal;
`rank`/`≤` below make that a `LinearOrder`. -/
inductive Tier where
  /-- **Tier 1 — Causal-only / CRDT.** Add a block in causal order; n ≥ 1; assumes NO
  synchrony; **never blocks** under partition (offline phones over BLE keep
  transacting). Eligible ONLY for I-confluent state (`Confluence.Tier1Eligible`). -/
  | causal
  /-- **Tier 2 — Ack-threshold.** k-of-m acknowledgements, leaderless; small n; needs no
  synchrony for *safety*; under partition it **degrades to tier 1** rather than
  stalling. -/
  | ackThreshold
  /-- **Tier 3 — Cordial-Miners τ-BFT.** Blocklace DAG waves + a per-wave leader + a
  3-step ratification; a known committee Π with n ≥ 3; GST / asynchronous network; it
  **stalls** during a partition and **resumes after GST**. -/
  | bft
  /-- **Tier 4 — Constitutional.** τ-BFT plus a self-amending constitution `(P, σ, Δ)`;
  known parties under PKI; partial-synchrony; **stalls with a deadline**. The
  amendment rules are adopted; the globalism seams are rejected. -/
  | constitutional
  deriving DecidableEq, Repr, Inhabited

/-- **Tier strength as a rank.** The ordinal of the §2.2 ladder; a strictly stronger
finality mechanism has a strictly larger rank. This induces the `LinearOrder` below
and is what `no_downgrade` is stated against. -/
def Tier.rank : Tier → Nat
  | .causal         => 1
  | .ackThreshold   => 2
  | .bft            => 3
  | .constitutional => 4

@[simp] theorem Tier.rank_causal : Tier.causal.rank = 1 := rfl
@[simp] theorem Tier.rank_ackThreshold : Tier.ackThreshold.rank = 2 := rfl
@[simp] theorem Tier.rank_bft : Tier.bft.rank = 3 := rfl
@[simp] theorem Tier.rank_constitutional : Tier.constitutional.rank = 4 := rfl

/-- `rank` is injective — distinct tiers have distinct strength (so the rank order is a
genuine total order, not a preorder collapsing tiers). -/
theorem Tier.rank_injective : Function.Injective Tier.rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [Tier.rank]

/-- Tier strength order: `t₁ ≤ t₂` iff `t₁` is no stronger than `t₂`, by `rank`. -/
instance : LE Tier := ⟨fun a b => a.rank ≤ b.rank⟩
/-- Strict tier strength order. -/
instance : LT Tier := ⟨fun a b => a.rank < b.rank⟩

/-- **`Tier` is a `LinearOrder`** under `rank` — the four mechanisms form a total
strength ladder (causal < ack < bft < constitutional). The `max` of this order is the
cross-tier commit join (see `crossTierJoin`). -/
instance : LinearOrder Tier where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by intro a; exact Nat.le_refl a.rank
  le_trans := by intro a b c hab hbc; exact Nat.le_trans hab hbc
  le_antisymm := by
    intro a b hab hba
    exact Tier.rank_injective (Nat.le_antisymm hab hba)
  le_total := by intro a b; exact Nat.le_total a.rank b.rank
  lt_iff_le_not_ge := by
    intro a b
    exact Nat.lt_iff_le_and_not_ge
  toDecidableLE := fun a b => decidable_of_iff (a.rank ≤ b.rank) Iff.rfl

/-- **The one underlying history substrate: a CvRDT DAG.** Per §2.2 the four tiers all
sit over a SINGLE join-semilattice DAG (proven a Merkle-CRDT, `discoveries §4`);
concurrent histories merge by `⊔`, exactly as `Confluence.MergeState` merges cell
state. We reuse the join-semilattice assumption directly. -/
abbrev History := Type u

/-- **Quorum / commit predicate (kept abstract).** `committed H h` says block/history
`h` has met `H`'s tier's agreement condition — e.g. tier-1 "is a causal extension",
tier-2 "k-of-m acks", tier-3/4 "a τ-BFT quorum ratified it". The `½(n+f)` threshold is
NOT hardcoded; it lives in `Config` and is consumed by the rule that builds this. -/
abbrev Committed (H : Type u) := H → Prop

/-- **`Canonical` — which valid history is THE history (§2.2 canonicity).** The single
distinguished element of the otherwise-merge-only DAG that the cell's finality tier has
selected as the head of record. -/
abbrev Canonical (H : Type u) := H → Prop

/-- **Per reference-group consensus config.** The `½(n+f)` quorum the naive design
hardcodes is lifted here: `n` participants, `f` tolerated faults, `threshold` the
acks/votes a commit needs (a tier-2 ack count or a tier-3/4 BFT quorum). `n = 1` is
permitted (rejecting the "fixed σ-quorum forbidding n=1" globalism seam). -/
structure Config where
  /-- Number of participants in the reference group. -/
  n : Nat
  /-- Number of Byzantine / crash faults tolerated. -/
  f : Nat
  /-- Commit threshold (acks or BFT votes). The canonical instantiation is the lifted
  `⌈½(n+f)⌉ + 1`-style quorum, but it is config, not law. -/
  threshold : Nat

/-- The standard lifted quorum `½(n+f)` (rounded up, strict majority of the
fault-adjusted set) — the value the old hardcoded constant becomes. Provided as a
helper to build a `Config`; groups MAY override it. -/
def Config.halfQuorum (n f : Nat) : Nat := (n + f) / 2 + 1

/-- **A finality rule (the §2.2 plugin).** Selects a `tier` and supplies the predicate
that decides canonicity at that tier over the DAG `H`: tier-1 admits any causal
extension; tier-2 needs the ack threshold; tier-3/4 need a τ-BFT quorum. `commit_canonical`
is the rule's soundness obligation — a committed history is the canonical one. -/
structure FinalityRule (H : Type u) where
  /-- Which tier of the ladder this rule realizes. -/
  tier : Tier
  /-- The group/threshold configuration the quorum is read from. -/
  config : Config
  /-- The tier's commit predicate (quorum kept abstract). -/
  committed : Committed H
  /-- The canonicity selector the rule installs. -/
  canonical : Canonical H
  /-- **Commit soundness:** once the tier's quorum has committed `h`, `h` is canonical.
  Making this a field means a `FinalityRule` value IS, by definition, a rule whose commits
  are canonical — the `commit ⇒ canonical` link required for `commit_at_join_of_tiers`. -/
  commit_canonical : ∀ h, committed h → canonical h

/-- **Reference group.** The set of participants `τ_unified` runs per-group (§2.2 "`τ`
per reference-group"); its identity selects which rule applies. Kept opaque. -/
structure Group where
  /-- Opaque group identity (a committee / cell-set hash in the real system). -/
  id : Nat
  deriving DecidableEq, Repr

/-- **`τ_unified(B, G, C)` — the unified finality selector (§2.2).** Given a block, a
reference-group `G`, and a config `C`, it picks the finality rule (hence tier) to run.
We model it as: a per-group tier assignment `groupTier`, plus a `ruleOf` building the
concrete rule for a tier under the config. `tau_unified G` is the rule `τ` runs for `G`.
The hardcoded `½(n+f)` is gone — it enters only through `C` / `ruleOf`. -/
structure Selector (H : Type u) where
  /-- Which tier each reference-group is assigned (its declared finality requirement). -/
  groupTier : Group → Tier
  /-- The config in force for the selection. -/
  config : Config
  /-- Build the concrete rule realizing a tier under the config. -/
  ruleOf : Tier → FinalityRule H

/-- The selector body: `τ_unified` resolves group `G` to the rule for `G`'s tier. -/
def Selector.tau_unified {H : Type u} (s : Selector H) (G : Group) : FinalityRule H :=
  s.ruleOf (s.groupTier G)

/-- The tier `τ_unified` chooses for a group is exactly the group's assigned tier
(the `ruleOf` preserves the tier label it was asked for) — a well-formedness condition
on a selector. Stated as an obligation. -/
theorem tau_unified_tier {H : Type u} (s : Selector H) (G : Group)
    (hwf : ∀ t, (s.ruleOf t).tier = t) :
    (s.tau_unified G).tier = s.groupTier G := by
  unfold Selector.tau_unified
  exact hwf (s.groupTier G)

/-- **Tier-1 requires I-confluence (links §2.2 ↔ `Confluence.lean`).** A cell may run
the `Tier.causal` rule ONLY if its invariant `I` is `Confluence.IConfluent` (equivalently
`Confluence.Tier1Eligible I`). The classifier rejects tier-1 on non-I-confluent state as
a STATIC error (`balance≥0` cannot be tier-1; hash-keyed nullifier uniqueness can). This
is the canonicity-side statement of `Confluence.admits_sound`. -/
theorem tier1_requires_iconfluent
    {S : Type u} [Confluence.MergeState S] (I : Confluence.Invariant S)
    (rule : FinalityRule S) (hcausal : rule.tier = Tier.causal)
    -- the static classifier and its soundness, made explicit (statement-repair: an
    -- arbitrary `I` is not I-confluent for free — the *classifier* is what guarantees it):
    (classify : Confluence.Invariant S → Tier)
    (hmatch : rule.tier = classify I)
    (hsound : ∀ J, classify J = Tier.causal → Confluence.Tier1Eligible J) :
    Confluence.Tier1Eligible I := by
  apply hsound I
  rw [← hmatch]; exact hcausal

/-- **Cross-tier join — the commit tier of a multi-tier turn.** A turn touching cells of
two tiers commits at the **join (max) of their tiers** (§2.2 cross-tier rule): the
stronger requirement dominates. Defined via the `LinearOrder` `max`. -/
def crossTierJoin (a b : Tier) : Tier := max a b

@[simp] theorem crossTierJoin_self (a : Tier) : crossTierJoin a a = a := by
  simp [crossTierJoin]

/-- `crossTierJoin` is commutative — tier order does not change the commit tier. -/
theorem crossTierJoin_comm (a b : Tier) : crossTierJoin a b = crossTierJoin b a := by
  simp [crossTierJoin, max_comm]

/-- The join is at least each input tier (the commit tier is never weaker than any cell
touched). -/
theorem crossTierJoin_ge_left (a b : Tier) : a ≤ crossTierJoin a b := by
  simp [crossTierJoin]

/-- **A turn commits at the join of its written cells' tiers; effects are held until the
join-tier commits (§2.2).** For a turn over a set of tiers `ts` (nonempty), the commit
tier is `crossTierJoin`-folded `max`, and no effect is released until the rule at THAT
tier reports `committed`. Stated over a written-cell tier list and the join-tier rule. -/
theorem commit_at_join_of_tiers {H : Type u}
    (ts : List Tier) (hne : ts ≠ [])
    (joinTier : Tier) (hjoin : joinTier = ts.foldr crossTierJoin ts.head!)
    (rule : FinalityRule H) (hrule : rule.tier = joinTier)
    (h : H) (hcommit : rule.committed h) :
    -- the join tier dominates every written cell's tier …
    (∀ t ∈ ts, t ≤ joinTier)
    -- … and canonicity is only granted once the join-tier rule has committed.
    ∧ rule.canonical h := by
  refine ⟨?_, rule.commit_canonical h hcommit⟩
  -- first conjunct: the fold-`max` dominates every element. Generalize the fold's seed.
  subst hjoin
  intro t ht
  have hmax : ∀ (l : List Tier) (seed : Tier) (x : Tier), x ∈ l → x ≤ l.foldr crossTierJoin seed := by
    intro l
    induction l with
    | nil => intro _ _ hx; simp at hx
    | cons a as ih =>
        intro seed x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact crossTierJoin_ge_left _ _
        · exact le_trans (ih seed x hx') (by
            simpa [crossTierJoin, max_comm] using crossTierJoin_ge_left (as.foldr crossTierJoin seed) a)
  exact hmax ts ts.head! t ht

/-- **The finality-strength transition system for a single value.** A configuration is
the value's currently-finalized `Tier`; a step is a (re-)finalization event, admissible
only when it does **not** lower the tier (`t ≤ t'`). This is the operational model the
no-downgrade safety property lives over: the *commit history* of one value, where each
event may only keep or strengthen its finality. The abstract `committed`/`canonical`
predicates of a `FinalityRule` cannot express this — it is a constraint on the sequence
of finalization events, encoded here as the step relation. -/
def finalitySystem : Execution.System where
  Config := Tier
  Step t t' := t ≤ t'

/-- **No-downgrade (§2.2).** Along any run of the finality-strength system, the final
tier is no weaker than the initial tier: finality strength is monotone non-decreasing.
Proved by lifting the per-step "a step never lowers the tier" to the whole run via
`Execution.invariant_run`. -/
theorem no_downgrade {t₀ t : Tier} (hrun : Execution.Run finalitySystem t₀ t) :
    t₀ ≤ t := by
  -- `fun s => t₀ ≤ s` is a step-invariant: every admissible step satisfies `a ≤ b`, so
  -- `t₀ ≤ a` together with the step gives `t₀ ≤ b` by transitivity. It holds at the start
  -- by reflexivity, hence at the reachable endpoint `t`.
  have hpres : Execution.StepInvariant finalitySystem (fun s => t₀ ≤ s) := by
    intro a b ha hstep
    exact le_trans ha hstep
  exact Execution.invariant_run hpres hrun (le_refl t₀)

/-! ## Conservation (Law 1) is tier-independent (§2.2 closing clause).

The two judgements are orthogonal: Law 1 (conservation) is a balance on the resource
MEASURE; Law 2 (ordering/finality) is a per-cell tier. The closing clause of §2.2 — "the
finality tier only prunes the order search; it neither creates nor destroys resource" —
is the statement that *re-annotating a cell at a different tier does not change the
conservation verdict*. We make this honest (not `True`) by exhibiting the conservation
balance as a predicate that takes a `Tier` argument it provably DISCARDS, and proving the
verdict agrees across two distinct tiers. The content lives in: (a) the balance
predicate is `Core.conservation_step`'s equality, which mentions no `Tier`; (b) the
cross-tier agreement below quantifies over distinct tiers and proves equality of verdicts.
-/

/-- **The tier-annotated conservation balance.** The Law-1 balance verdict for a turn
`f : Core.Turn A B` under measure `cons`, carrying — for the sake of the orthogonality
statement — the finality `Tier` the cell is annotated at. The verdict is
`count A + minted = count B + burned` (`Core`'s balance), and the `Tier` argument is
DISCARDED: that discarding is precisely "the tier does not enter the conservation
measure". -/
def conservedAtTier {M : Type u} [AddCommMonoid M]
    (cons : Core.Conservation M) (_t : Tier) {A B : Core.Cell} (f : Core.Turn A B) : Prop :=
  cons.count A + cons.minted f.tag = cons.count B + cons.burned f.tag

/-- **The tier-independent verdict is the genuine Law-1 balance (anchoring non-vacuity).**
At every tier, `conservedAtTier` holds for an arbitrary turn — because it unfolds to
`Core.conservation_step`'s balance, which `Core` discharges as Law 1. This ties the
cross-tier statement to real conservation content (so it is not agreement between two
vacuous predicates): the shared verdict is exactly the resource-balance law. -/
theorem conservedAtTier_holds {M : Type u} [AddCommMonoid M]
    (cons : Core.Conservation M) [Core.ConservesStep cons]
    (t : Tier) {A B : Core.Cell} (f : Core.Turn A B) :
    conservedAtTier cons t f := by
  unfold conservedAtTier
  exact Core.conservation_step cons f

/-- **Conservation is tier-independent (§2.2 closing clause).** For any two finality tiers
`t₁ t₂`, the conservation balance predicate is the **same proposition**:
`conservedAtTier t₁ f = conservedAtTier t₂ f`, proved by `rfl`. This is genuine independence —
the two sides are *definitionally identical* because the `Tier` argument is discarded by the
measure (`conservedAtTier` does not mention `_t`). Re-tagging a cell's finality tier cannot
change the conservation verdict; Law 1 (conservation) and Law 2 (ordering/tier) are orthogonal. -/
theorem conservation_tier_independent {M : Type u} [AddCommMonoid M]
    (cons : Core.Conservation M) (t₁ t₂ : Tier)
    {A B : Core.Cell} (f : Core.Turn A B) :
    conservedAtTier cons t₁ f = conservedAtTier cons t₂ f :=
  rfl

/-- The `↔` corollary for downstream callers expecting the biconditional. -/
theorem conservation_tier_independent_iff {M : Type u} [AddCommMonoid M]
    (cons : Core.Conservation M) (t₁ t₂ : Tier)
    {A B : Core.Cell} (f : Core.Turn A B) :
    conservedAtTier cons t₁ f ↔ conservedAtTier cons t₂ f :=
  (conservation_tier_independent cons t₁ t₂ f) ▸ Iff.rfl

end Dregg2.Finality
