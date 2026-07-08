/-
# `Dregg2.Distributed.FinalizationQuorum` — the verified finalization-vote quorum decision.

The node's `node/src/finalization_votes.rs` adds an explicit signed-vote agreement layer on top of the
blocklace: each committee member gossips a signed [FinalizationVote] over a finalized `(block, root)`, and
a block is **consensus-attested** once `≥ superMajority(n)` DISTINCT committee members have signed the
SAME `root`. That `VoteCollector` decision — group by root, count distinct signers, gate at the
supermajority — is security-critical (a subtle equivocation-counting bug lets a minority forge finality),
and it was hand-written in Rust with no verified counterpart.

This is the verified counterpart (tier-2: the DECISION is Lean, exported to Rust). It models the
already-deduplicated tally the collector holds (first-write-wins upstream guarantees at most one recorded
`(signer, root)` per signer) and proves the two properties that make the gate SOUND:

* `quorumRoot_sound` — if the decision returns a root, a genuine supermajority of distinct signers
  attested it (never a fabricated quorum a restart would reject).
* `quorum_no_conflict` — **the safety property**: at most one root can reach quorum, because two
  supermajorities of distinct signers would need `2·superMajority(n) > n` distinct signers, which cannot
  fit in an `n`-member committee. So the gate can never consensus-attest two conflicting finalized roots.
-/
import Dregg2.Distributed.BlocklaceFinality
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Count

namespace Dregg2.Distributed.FinalizationQuorum

open Dregg2.Distributed.BlocklaceFinality (superMajority)
open List (Disjoint)

variable {Sig Root : Type*} [DecidableEq Sig] [DecidableEq Root]

/-- The distinct signers who attested `root` in a tally `votes` (a list of `(signer, root)` pairs, one
per distinct signer — the collector's first-write-wins invariant). -/
def signersFor (votes : List (Sig × Root)) (root : Root) : List Sig :=
  ((votes.filter (fun v => v.2 = root)).map (·.1)).dedup

/-- The finalization-quorum decision: the root attested by a supermajority of DISTINCT committee signers,
if one exists. `n` is the committee size. Returns the first such root in the tally's root order. -/
def quorumRoot (votes : List (Sig × Root)) (n : Nat) : Option Root :=
  (votes.map (·.2)).dedup.find? (fun r => superMajority n ≤ (signersFor votes r).length)

/-- **SOUNDNESS.** A returned root is genuinely attested by `≥ superMajority(n)` distinct signers. -/
theorem quorumRoot_sound {votes : List (Sig × Root)} {n : Nat} {r : Root}
    (h : quorumRoot votes n = some r) :
    superMajority n ≤ (signersFor votes r).length := by
  have := List.find?_some h
  simpa using this

/-- The tally is *well-formed* for a committee of size `n`: every recorded signer is distinct (the
collector keys votes by signer, first-write-wins) and there are at most `n` of them. -/
def WellFormed (votes : List (Sig × Root)) (n : Nat) : Prop :=
  (votes.map (·.1)).Nodup ∧ (votes.map (·.1)).length ≤ n

/-- Signers attesting DIFFERENT roots are disjoint: a well-formed tally records each signer once, so a
signer counted for `r₁` is not counted for `r₂ ≠ r₁`. -/
theorem signersFor_disjoint {votes : List (Sig × Root)} {n : Nat} (hwf : WellFormed votes n)
    {r₁ r₂ : Root} (hne : r₁ ≠ r₂) :
    Disjoint (signersFor votes r₁) (signersFor votes r₂) := by
  rw [List.disjoint_left]
  intro s hs1 hs2
  simp only [signersFor, List.mem_dedup, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hs1 hs2
  obtain ⟨v1, ⟨hv1mem, hv1r⟩, hv1s⟩ := hs1
  obtain ⟨v2, ⟨hv2mem, hv2r⟩, hv2s⟩ := hs2
  -- same signer s ⟹ same recorded vote (Nodup on signers) ⟹ same root, contradicting r₁ ≠ r₂
  have hsig : v1.1 = v2.1 := by rw [hv1s, hv2s]
  have : v1 = v2 := by
    have hnd := hwf.1
    exact List.inj_on_of_nodup_map hnd hv1mem hv2mem hsig
  rw [this] at hv1r
  exact hne (hv1r.symm.trans hv2r)

/-- **THE SAFETY PROPERTY.** At most one root reaches quorum. If two distinct roots both had a
supermajority of distinct signers, their disjoint signer sets would total `2·superMajority(n) > n`
distinct signers — impossible in an `n`-member committee. So the gate never consensus-attests two
conflicting finalized roots. -/
theorem quorum_no_conflict {votes : List (Sig × Root)} {n : Nat} (hwf : WellFormed votes n)
    {r₁ r₂ : Root} (hne : r₁ ≠ r₂)
    (h1 : superMajority n ≤ (signersFor votes r₁).length)
    (h2 : superMajority n ≤ (signersFor votes r₂).length) : False := by
  -- both signer sets are sublists of the (Nodup) recorded signers, and are disjoint
  have hsub1 : (signersFor votes r₁) ⊆ (votes.map (·.1)) := by
    intro s hs; simp only [signersFor, List.mem_dedup, List.mem_map, List.mem_filter] at hs
    obtain ⟨v, ⟨hv, _⟩, hvs⟩ := hs; exact List.mem_map.mpr ⟨v, hv, hvs⟩
  have hsub2 : (signersFor votes r₂) ⊆ (votes.map (·.1)) := by
    intro s hs; simp only [signersFor, List.mem_dedup, List.mem_map, List.mem_filter] at hs
    obtain ⟨v, ⟨hv, _⟩, hvs⟩ := hs; exact List.mem_map.mpr ⟨v, hv, hvs⟩
  have hnd1 : (signersFor votes r₁).Nodup := List.nodup_dedup _
  have hnd2 : (signersFor votes r₂).Nodup := List.nodup_dedup _
  have hdisj := signersFor_disjoint hwf hne
  -- the concatenation is Nodup and a sub-multiset of the ≤ n recorded signers
  have hcard : (signersFor votes r₁).length + (signersFor votes r₂).length ≤ n := by
    have hun : ((signersFor votes r₁) ++ (signersFor votes r₂)).Nodup :=
      List.Nodup.append hnd1 hnd2 hdisj
    have hsubun : ((signersFor votes r₁) ++ (signersFor votes r₂)) ⊆ (votes.map (·.1)) := by
      intro s hs; rcases List.mem_append.mp hs with h | h
      · exact hsub1 h
      · exact hsub2 h
    have := (List.subperm_of_subset hun hsubun).length_le
    simpa [List.length_append] using this.trans hwf.2
  -- but superMajority n = 2n/3 + 1, so 2·superMajority n > n
  have hsm : n < superMajority n + superMajority n := by
    unfold superMajority; omega
  omega

#assert_axioms quorumRoot_sound
#assert_axioms quorum_no_conflict

end Dregg2.Distributed.FinalizationQuorum
