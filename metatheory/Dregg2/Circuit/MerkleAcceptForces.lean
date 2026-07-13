import Dregg2.Circuit.FriVerifier
import Dregg2.Tactics

/-!
# The Merkle recompute is ENFORCED by acceptance (not carried)

Attacking the commitment-binding floor: `verifyAlgo`'s per-query check (`foldConsistent → friQueryCheck`)
runs a real `merkleVerify` of the opened leaf against the committed trace root. So the Merkle recompute
is a CONSEQUENCE of acceptance, not an assumption a bundle must carry. This file lands the query-level
brick: `friQueryCheck` acceptance forces the first-layer leaf to Merkle-recompute (over `core.compress`)
to the committed root — the anti-forgery binding, derived. The residual is then only the honest hash
floor (`CompressInjective`/Poseidon2 CR), via `merkleRecompute_binds`.
-/

namespace Dregg2.Circuit.MerkleAcceptForces

open Dregg2.Circuit.FriVerifier

/-- **`friQueryCheck` acceptance FORCES the first-layer Merkle recompute.** If `friQueryCheck` accepts a
query with a nonempty layer list, the first layer's leaf recomputes over `core.compress` to the committed
trace root `traceCom`. Enforced by the verifier's own `merkleVerify`, not assumed. -/
theorem friQueryCheck_forces_merkleRecompute {F : Type} [DecidableEq F] (core : FriCore F)
    (traceCom : List F) (fcs : List (List F)) (fc : F) (q : QueryOpening F)
    (l0 : LayerOpening F) (ls : List (LayerOpening F)) (hq : q.layers = l0 :: ls)
    (hok : friQueryCheck core traceCom fcs fc q = true) :
    merkleRecompute core.compress q.index l0.leaf l0.siblings = traceCom := by
  obtain ⟨idx, layers⟩ := q
  simp only at hq
  subst hq
  rcases hfc : friChainGo core (idx / 2)
      (core.foldCombine l0.beta l0.x l0.e0 l0.e1) (fcs.zip ls) with ⟨okRest, fin⟩
  simp only [friQueryCheck, merkleVerify, hfc, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok.1.1

#assert_axioms friQueryCheck_forces_merkleRecompute

/-- **`verifyAlgo` acceptance FORCES the concrete per-query FRI check.** If the full verifier
(`fullChecks` bundle) accepts, then the concrete fold-consistency check — every query's Merkle recompute
+ fold-chain + final-poly constant, positions bound to the transcript-derived indices — held on exactly
the challenges `verifyAlgo` itself derived. The second conjunct of acceptance, peeled: the FRI query core
is load-bearing inside acceptance, not carried. -/
theorem verifyAlgo_accept_forces_foldConsistent {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
      initState logN proof pub = true) :
    (concreteFriChecks core).foldConsistent proof
      (deriveFri perm RATE params proof (Challenger.init initState)).1
      (deriveQueryIndices perm RATE toNat params logN
        (deriveFri perm RATE params proof (Challenger.init initState)).2).1 = true := by
  unfold verifyAlgo at hacc
  simp only [Bool.and_eq_true] at hacc
  exact hacc.1.1.1.1.2

#assert_axioms verifyAlgo_accept_forces_foldConsistent

end Dregg2.Circuit.MerkleAcceptForces
