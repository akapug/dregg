/-
# `Dregg2.Distributed.HybridFinalizationQuorum` — the node's finalization quorum is HYBRID-unforgeable.

This file COMPOSES the two already-verified pieces so the *actual running consensus decision* is tied
to the hybrid (classical + post-quantum) security guarantee — not merely each in isolation:

* `Dregg2.Distributed.FinalizationQuorum` — the distinct-signer supermajority DECISION (`quorumRoot`,
  `quorumRoot_sound`, `quorum_no_conflict`, `WellFormed`, `signersFor`). It knows nothing about crypto:
  it counts distinct signers over an already-admitted tally.
* `Dregg2.Crypto.HybridQuorum` — the per-certificate HYBRID unforgeability (`hybridVerify = classical ∧
  pq`, `Unforgeable`, `hybrid_survives_classical_break`: PQ-`Unforgeable` ⟹ the AND-composite survives a
  TOTAL classical break). It knows nothing about quorums: it reasons about ONE signature.

## The bridge

A real finalization vote carries the signer AND both signature halves over the finalized root. The node's
`VoteCollector.record` admits a vote only if it passes `verify_hybrid` (classical AND pq), and only then is
it counted toward the quorum. We mirror that exactly: `admittedTally` FILTERS the raw votes by the hybrid
admission predicate `hybridAdmit` BEFORE handing the `(signer, root)` pairs to `quorumRoot`. So the counted
signers are exactly the ones whose hybrid certificate verified.

## What is PROVEN

1. `hybrid_quorum_needs_supermajority_hybrid_votes` — a `quorumRoot`-accepted root has `≥ superMajority n`
   DISTINCT signers, each of whom produced a vote for that root whose hybrid check (`classical ∧ pq`)
   passed. (Transfers `quorumRoot_sound` onto the admitted tally.)
2. **THE HEADLINE — `hybrid_quorum_survives_classical_break`.** If the PQ half is `Unforgeable`, then even
   with the classical verifier a TOTAL rubber stamp (ed25519 → Shor), an accepted quorum for `r` implies
   `r` was genuinely signed (`Signed r`) — so no adversary can assemble a finalization quorum for a root
   the honest committee did not sign. Each admitted vote's PQ half is fed through
   `HybridQuorum.hybrid_survives_classical_break`; the supermajority (`≥ 1`) forces at least one such vote
   to exist, and PQ-`Unforgeable` turns it into `Signed r`. `hybrid_no_forged_quorum_under_classical_break`
   is the contrapositive: `¬ Signed r ⟹` no quorum for `r`, classical break notwithstanding.
3. `hybrid_quorum_no_conflict_under_break` — transfers `quorum_no_conflict`: at most one root reaches a
   hybrid quorum. The proof never touches the classical verifier, which is exactly why safety SURVIVES the
   classical break.

Non-vacuity `#guard`s exhibit a quorum reached under all-hybrid-valid votes, and a would-be member whose PQ
half is invalid being EXCLUDED so the quorum fails — the teeth that show the admission filter is load-bearing.

`#assert_axioms` on every theorem (⊆ `{propext, Classical.choice, Quot.sound}`; no fresh axiom — the PQ
hardness enters ONLY as the explicit `Unforgeable` hypothesis at the stated boundary).
-/
import Dregg2.Distributed.FinalizationQuorum
import Dregg2.Crypto.HybridQuorum

namespace Dregg2.Distributed.HybridFinalizationQuorum

open Dregg2.Distributed.FinalizationQuorum (quorumRoot quorumRoot_sound quorum_no_conflict WellFormed
  signersFor)
open Dregg2.Distributed.BlocklaceFinality (superMajority)
open Dregg2.Crypto.HybridQuorum (hybridVerify Unforgeable HybridUnforgeable
  hybrid_survives_classical_break)

set_option linter.unusedSectionVars false

variable {Sig Root Sc Sp : Type*} [DecidableEq Sig] [DecidableEq Root]

/-! ## §1 — The hybrid finalization vote and the admission-gated tally. -/

/-- A finalization vote as the node actually holds it: the `signer`, the finalized `root` being voted for,
and BOTH signature halves — the classical `sigC` (FROST/ed25519) and the post-quantum `sigP` (ML-DSA) over
`root`. -/
structure HybridVote (Sig Root Sc Sp : Type*) where
  signer : Sig
  root : Root
  sigC : Sc
  sigP : Sp

/-- The hybrid admission check on a single vote: BOTH halves must verify over the voted root. This is the
executable mirror of the Rust `verify_hybrid` gate that `VoteCollector.record` runs before counting a vote.
`Vc`/`Vp` are the classical/PQ verifiers (Bool-valued so the tally is executable for the `#guard`s). -/
def hybridAdmit (Vc : Root → Sc → Bool) (Vp : Root → Sp → Bool)
    (v : HybridVote Sig Root Sc Sp) : Bool :=
  Vc v.root v.sigC && Vp v.root v.sigP

/-- The tally handed to `quorumRoot`: only the hybrid-admitted votes contribute their `(signer, root)`
pair. Filtering BEFORE `quorumRoot` is the whole composition — a forged/invalid vote never reaches the
distinct-signer count. -/
def admittedTally (Vc : Root → Sc → Bool) (Vp : Root → Sp → Bool)
    (votes : List (HybridVote Sig Root Sc Sp)) : List (Sig × Root) :=
  (votes.filter (hybridAdmit Vc Vp)).map (fun v => (v.signer, v.root))

/-- The hybrid finalization decision: the root a supermajority of DISTINCT signers HYBRID-attested. It is
`FinalizationQuorum.quorumRoot` over the admission-gated tally — the composition, packaged as one decision. -/
def hybridQuorumRoot (Vc : Root → Sc → Bool) (Vp : Root → Sp → Bool)
    (votes : List (HybridVote Sig Root Sc Sp)) (n : Nat) : Option Root :=
  quorumRoot (admittedTally Vc Vp votes) n

/-! ## §2 — Bridge lemmas: admission ⟺ hybrid verification, and who is counted. -/

/-- The Bool admission check equals the `Prop` hybrid verification (`classical ∧ pq`) — the coercion that
lets the executable tally talk to `HybridQuorum`'s `Prop`-level unforgeability. -/
theorem hybridAdmit_true_iff (Vc : Root → Sc → Bool) (Vp : Root → Sp → Bool)
    (v : HybridVote Sig Root Sc Sp) :
    hybridAdmit Vc Vp v = true ↔ (Vc v.root v.sigC = true ∧ Vp v.root v.sigP = true) := by
  unfold hybridAdmit; rw [Bool.and_eq_true]

/-- A signer is counted for `root` iff it produced an ADMITTED (hybrid-verifying) vote for that root. This
is the characterization that makes the counted-signer set exactly the hybrid-verified set. -/
theorem mem_admittedSignersFor (Vc : Root → Sc → Bool) (Vp : Root → Sp → Bool)
    (votes : List (HybridVote Sig Root Sc Sp)) (r : Root) (s : Sig) :
    s ∈ signersFor (admittedTally Vc Vp votes) r ↔
      ∃ v ∈ votes, hybridAdmit Vc Vp v = true ∧ v.signer = s ∧ v.root = r := by
  unfold signersFor admittedTally
  simp only [List.mem_dedup, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨⟨v, hvmem, hvp⟩, hpr⟩, hps⟩
    subst hvp
    exact ⟨v, hvmem.1, hvmem.2, hps, hpr⟩
  · rintro ⟨v, hv, hadm, hvs, hvr⟩
    exact ⟨(v.signer, v.root), ⟨⟨v, ⟨hv, hadm⟩, rfl⟩, hvr⟩, hvs⟩

/-! ## §3 — Theorem 1: a quorum is a supermajority of DISTINCT hybrid-verified votes. -/

/-- **THEOREM 1 — `hybrid_quorum_needs_supermajority_hybrid_votes`.** If the hybrid decision returns `r`,
then `≥ superMajority n` DISTINCT signers each produced a vote for `r` whose hybrid check
(`classical ∧ pq`) passed. Transfers `FinalizationQuorum.quorumRoot_sound` onto the admission-gated tally,
then reads back through `mem_admittedSignersFor` that each counted signer's certificate verified. -/
theorem hybrid_quorum_needs_supermajority_hybrid_votes (Vc : Root → Sc → Bool) (Vp : Root → Sp → Bool)
    (votes : List (HybridVote Sig Root Sc Sp)) (n : Nat) (r : Root)
    (h : hybridQuorumRoot Vc Vp votes n = some r) :
    superMajority n ≤ (signersFor (admittedTally Vc Vp votes) r).length ∧
      ∀ s ∈ signersFor (admittedTally Vc Vp votes) r,
        ∃ v ∈ votes, v.signer = s ∧ v.root = r ∧
          hybridVerify (fun rr ss => Vc rr ss = true) (fun rr ss => Vp rr ss = true)
            v.root v.sigC v.sigP := by
  have h' : quorumRoot (admittedTally Vc Vp votes) n = some r := h
  refine ⟨quorumRoot_sound h', ?_⟩
  intro s hs
  rw [mem_admittedSignersFor] at hs
  obtain ⟨v, hv, hadm, hvs, hvr⟩ := hs
  exact ⟨v, hv, hvs, hvr, (hybridAdmit_true_iff Vc Vp v).mp hadm⟩

/-! ## §4 — THE HEADLINE: the hybrid quorum survives a TOTAL classical break. -/

/-- **THEOREM 2 (THE HEADLINE) — `hybrid_quorum_survives_classical_break`.** With the classical verifier
replaced by the always-accepting rubber stamp (`fun _ _ => true` — discrete log fell to Shor, every
classical "signature" verifies), a hybrid quorum for `r` STILL implies `r` was genuinely signed
(`Signed r`), provided the PQ half is `Unforgeable`. No adversary can assemble a finalization quorum for a
root the honest committee never signed.

The composition of the two files: `FinalizationQuorum.quorumRoot_sound` forces `≥ superMajority n ≥ 1`
DISTINCT admitted signers, hence at least one admitted vote exists; its PQ half is fed to
`HybridQuorum.hybrid_survives_classical_break` (PQ-`Unforgeable` ⟹ the AND-composite rejects forgeries even
under a total classical break), yielding `Signed r`. Every one of the `≥ superMajority n` distinct
members would have to forge its PQ half — impossible under PQ-`Unforgeable`. -/
theorem hybrid_quorum_survives_classical_break (Vp : Root → Sp → Bool) (Signed : Root → Prop)
    (hpq : Unforgeable (fun r s => Vp r s = true) Signed)
    (votes : List (HybridVote Sig Root Sc Sp)) (n : Nat) (r : Root)
    (h : hybridQuorumRoot (fun _ _ => true) Vp votes n = some r) :
    Signed r ∧ superMajority n ≤ (signersFor (admittedTally (fun _ _ => true) Vp votes) r).length := by
  have h' : quorumRoot (admittedTally (fun (_ : Root) (_ : Sc) => true) Vp votes) n = some r := h
  have hlen := quorumRoot_sound h'
  refine ⟨?_, hlen⟩
  -- the supermajority is ≥ 1, so the admitted-signer set is nonempty: at least one hybrid vote exists.
  have hne : signersFor (admittedTally (fun (_ : Root) (_ : Sc) => true) Vp votes) r ≠ [] := by
    intro hnil
    rw [hnil, List.length_nil] at hlen
    have : 0 < superMajority n := by unfold superMajority; omega
    omega
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hne
  rw [mem_admittedSignersFor] at hs
  obtain ⟨v, _, hadm, _, hvr⟩ := hs
  have hVp : Vp v.root v.sigP = true := ((hybridAdmit_true_iff _ Vp v).mp hadm).2
  -- COMPOSE with HybridQuorum: the PQ half of this admitted vote defeats the total classical break.
  have hHU : HybridUnforgeable (fun (_ : Root) (_ : Sc) => True) (fun r s => Vp r s = true) Signed :=
    hybrid_survives_classical_break hpq
  have hSigned : Signed v.root := hHU v.root v.sigC v.sigP ⟨trivial, hVp⟩
  rwa [hvr] at hSigned

/-- **THE CONTRAPOSITIVE — `hybrid_no_forged_quorum_under_classical_break`.** Under PQ-`Unforgeable`, if the
honest committee never signed `r` (`¬ Signed r`), then NO quorum for `r` can be assembled — even with the
classical half a total rubber stamp. The forged finalization quorum is refuted outright. -/
theorem hybrid_no_forged_quorum_under_classical_break (Vp : Root → Sp → Bool) (Signed : Root → Prop)
    (hpq : Unforgeable (fun r s => Vp r s = true) Signed)
    (votes : List (HybridVote Sig Root Sc Sp)) (n : Nat) (r : Root)
    (hforge : ¬ Signed r) :
    hybridQuorumRoot (fun (_ : Root) (_ : Sc) => true) Vp votes n ≠ some r := by
  intro h
  exact hforge (hybrid_quorum_survives_classical_break Vp Signed hpq votes n r h).1

/-! ## §5 — Theorem 3: safety (no two conflicting hybrid quorums) survives the classical break. -/

/-- **THEOREM 3 — `hybrid_quorum_no_conflict_under_break`.** At most one root reaches a hybrid quorum: two
distinct roots each with a supermajority of distinct admitted signers would need `2·superMajority n > n`
distinct committee members. Transfers `FinalizationQuorum.quorum_no_conflict`. The proof NEVER inspects the
classical verifier `Vc` — which is exactly why safety survives an arbitrary (including totally broken)
classical half. -/
theorem hybrid_quorum_no_conflict_under_break (Vc : Root → Sc → Bool) (Vp : Root → Sp → Bool)
    (votes : List (HybridVote Sig Root Sc Sp)) (n : Nat)
    (hwf : WellFormed (admittedTally Vc Vp votes) n)
    {r₁ r₂ : Root} (hne : r₁ ≠ r₂)
    (h1 : superMajority n ≤ (signersFor (admittedTally Vc Vp votes) r₁).length)
    (h2 : superMajority n ≤ (signersFor (admittedTally Vc Vp votes) r₂).length) : False :=
  quorum_no_conflict hwf hne h1 h2

/-! ## §6 — Non-vacuity teeth: the hybrid admission filter is LOAD-BEARING.

Classical half broken (`demoVc = fun _ _ => true`), PQ half a toy verifier accepting a signature only when
it equals the voted root (`demoVp r s = (s == r)`). `superMajority 4 = 3`. -/

namespace Demo

/-- Broken classical verifier: a rubber stamp accepting everything (ed25519 → Shor). -/
def demoVc (_ : Nat) (_ : Nat) : Bool := true
/-- Toy PQ verifier: the PQ "signature" is valid only when it equals the voted root. -/
def demoVp (r : Nat) (s : Nat) : Bool := s == r

/-- Three distinct signers, each hybrid-valid for root `7` (PQ sig = 7). Reaches the supermajority. -/
def goodVotes : List (HybridVote Nat Nat Nat Nat) :=
  [⟨1, 7, 0, 7⟩, ⟨2, 7, 0, 7⟩, ⟨3, 7, 0, 7⟩]

/-- Same three, but signer 3's PQ half is FORGED (sig `99 ≠ 7`): the teeth. -/
def forgedVotes : List (HybridVote Nat Nat Nat Nat) :=
  [⟨1, 7, 0, 7⟩, ⟨2, 7, 0, 7⟩, ⟨3, 7, 0, 99⟩]

-- POSITIVE: all-hybrid-valid votes reach a quorum for root 7.
#guard hybridQuorumRoot demoVc demoVp goodVotes 4 = some 7
-- TEETH: the forged-PQ member is EXCLUDED, dropping the count below supermajority ⟹ NO quorum.
#guard hybridQuorumRoot demoVc demoVp forgedVotes 4 = none
-- A hybrid-valid vote is admitted; a forged-PQ vote is not (even though classical rubber-stamps it).
#guard hybridAdmit demoVc demoVp ⟨3, 7, 0, 7⟩ = true
#guard hybridAdmit demoVc demoVp ⟨3, 7, 0, 99⟩ = false
-- The forged vote never reaches the tally: only the two genuine signers are counted.
#guard admittedTally demoVc demoVp forgedVotes = [(1, 7), (2, 7)]

end Demo

/-! ## §7 — Axiom-hygiene tripwires. -/

#assert_axioms hybridAdmit_true_iff
#assert_axioms mem_admittedSignersFor
#assert_axioms hybrid_quorum_needs_supermajority_hybrid_votes
#assert_axioms hybrid_quorum_survives_classical_break
#assert_axioms hybrid_no_forged_quorum_under_classical_break
#assert_axioms hybrid_quorum_no_conflict_under_break

end Dregg2.Distributed.HybridFinalizationQuorum
