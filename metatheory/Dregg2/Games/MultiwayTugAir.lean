/-
# Dregg2.Games.MultiwayTugAir — the ABSTRACT play-leaf AIR relation, refining `applyAction`.

⚠ RESOLUTION (see `docs/audit/SEMANTIC-LEAN-BOUNDARY.md`, Class B — UPDATED). The deployed tug
play-teeth `CellProgram::Cases` (over register counters + `SumEquals==21`) is now LEAN-SOURCED:
authored in `Dregg2.Games.MultiwayTugProgram` (`multiwayTugProgram`), emitted to a checked-in JSON
artifact, and loaded by `dregg-multiway-tug/src/state.rs::Deployment::program()`. That file also
CLOSES the counter↔multiset refinement: `Prog.program_admits_legal_play` proves the DEPLOYED
counter program admits the abstraction (`Prog.abstract`) of every legal `applyAction` move —
conservation reads `totalCards`, the write-once flags/monotone scores/strict sequencing/win-gate
each pinned to a PROVEN model invariant. So the deployed program IS this Lean model at the
COUNTER (cardinality) granularity it operates on — machine-checked, not prose.

What THIS file proves is the OTHER layer: the membership play-leaf `airPlay` over the abstract
`MerkleScheme`, which pins the CARD IDENTITY the counters abstract away (many `GState`s share a
counter image; the leaf fixes WHICH card moved under the committed hand root). The two referees
agree on every legal play and compose: `Prog.play_admitted_by_both` proves a membership-proven
play is admitted by BOTH the counter program AND the leaf, together refining `applyAction`. The
HONEST remainders are now narrow and named: (1) the abstract `MerkleScheme`'s `MerkleSound` (the
deployed Poseidon2 STARK soundness — CARRIED, not re-proven), and (2) the full IVC fold
composition over an arbitrary chain (§below). In the prose that follows, "CONNECTED"/"concrete"
mean connected to the fold-leaf SHAPE; the counter-program connection to the deployed referee is
the machine-checked one in `MultiwayTugProgram.lean`.

`MultiwayTug.lean` states the game-level refinement obligation abstractly:
`AirSpec air` says a HYPOTHESIZED transition AIR admits `(o, p, a, n)` iff
`n = applyAction o p a`, and `multiwayTug_air_refines_applyAction` is the empty-carrier
version (the AIR predicate is a bare hypothesis). This file CONNECTS that obligation to the
CONCRETE Phase-3 fold structure (`dregg-multiway-tug/src/{hidden_hand,fold}.rs`,
`game-turn-slice/src/compiler.rs::lower_witnessed_merkle_membership`): a play in the fold is a
`Custom` leaf carrying a `Witnessed { MerkleMembership }` tooth — the played card is proven a
member of the committed hand root, public inputs `[leaf, root]`, the remaining root updates.

## The mapping (fold.rs / hidden_hand.rs / compiler.rs → this file)

  * **The committed hand root** (`HandTree::root`, a 4-ary Poseidon2 Merkle root over the
    dealt cards) ↦ `M.commit (o.hand p)` — an ABSTRACT commitment to the acting player's
    current (remaining) hand multiset. `M.Root` / `M.commit` are opaque here because the
    hash's collision-resistance is the STARK-soundness remainder, not re-proven (see below).
  * **The membership-proven play** (`check_play` / `HandMembershipVerifier::verify` /
    `lower_witnessed_merkle_membership` — a Poseidon2 path from the played leaf climbing to the
    committed root) ↦ `M.Member (M.commit (o.hand p)) (actionCards a)` — the play's cards are
    proven under the committed hand root. The distinct-leaf-per-copy deck (`deck_guild`) makes
    the played multiset `actionCards a` the sub-multiset admitted under the root.
  * **The public inputs `[leaf, root]`** ↦ the `(M.commit (o.hand p), M.Member …)` pair; the
    played card ids are NOT in the relation (private-in-fold), only the commitment + the
    membership fact.
  * **The remaining-root update** (`HandTree::without` recommits `hand − played`) ↦
    `M.commit (n.hand p) = M.commit (o.hand p − actionCards a)` (`remaining_root_updates`).
  * **The win as a bound public output** ↦ `winBound s p winPI` — the leaf's public win bit is
    pinned to the model predicate `Won` (`winBound_pins`).

## What is PROVEN here (the play-leaf refinement — real, non-vacuous, `#assert_axioms`-clean)

`airPlay_iff_applyAction`: the concrete fold-leaf's admission relation IS the graph of
`applyAction` RESTRICTED to a legal, membership-proven play — the game-level analogue of
`Exec.Program`'s `evalSimpleCtx_*_iff` admit-characterizations, now for the membership leaf.
The `MerkleSound` bridge is LOAD-BEARING (membership ⇒ the card is in the hand ⇒ the play is
legal ⇒ `applyAction = applyLegal`); the correspondence is not a `P → P` tautology.
`airPlay_refines_airSpec` shows the concrete leaf refines the abstract `AirSpec` obligation on
the play class; `airPlay_functional` inherits determinism; `airPlay_chain_are_applySteps` is
the two-turn compositional step toward the whole match fold.

## The OBLIGATION remaining (STATED, honestly, NOT discharged here)

  1. **The deployed STARK's soundness** — that the emitted Poseidon2 `MerkleAir` (the same
     `compute_parent_poseidon2` recurrence `check_play` walks) ACCEPTS a leaf only if the card
     is genuinely under the committed root. Modelled as `MerkleSound M` and CARRIED as a
     hypothesis (like `AirSpec air` upstream), NOT an axiom — so `#assert_axioms` stays clean.
     Discharging it is the deployed circuit's job (Poseidon2 collision-resistance + the STARK
     soundness of the linking tower), not re-proven in this pure model.
  2. **The full match-fold refinement** — that `prove_turn_chain_recursive` composing the
     per-play leaves into one `WholeChainProof` refines the whole `applyAction` run.
     `airPlay_chain_are_applySteps` proves the inductive step for two consecutive play leaves;
     the IVC's soundness (the deployed fold) composing an arbitrary chain is the remainder.
-/
import Dregg2.Games.MultiwayTug

namespace Dregg2.Games.MultiwayTug

/-! ## 1. The abstract Merkle-commitment scheme + its soundness bridge (the STARK remainder) -/

/-- An abstract Poseidon2 hand-commitment scheme: an opaque root type, a `commit` over a hand
multiset, and a `Member` relation ("this sub-multiset is proven under the root" — the
executor-checked `Witnessed { MerkleMembership }` tooth / the `MerkleAir`'s acceptance). The
deployed side is the concrete 4-ary Poseidon2 Merkle root (`hidden_hand::HandTree`); it is
OPAQUE here because the hash's collision-resistance is the STARK-soundness remainder. -/
structure MerkleScheme where
  /-- The commitment (root) type — the concrete `BabyBear` Poseidon2 root, abstract here. -/
  Root : Type
  /-- Commit a hand multiset to its root (`HandTree::commit`). -/
  commit : Multiset Geisha → Root
  /-- "This sub-multiset is membership-proven under the root" (the accepted tooth / leaf). -/
  Member : Root → Multiset Geisha → Prop

/-- **`MerkleSound M` — the deployed STARK's soundness (the honest remainder, a HYPOTHESIS).**
A membership proof accepted under `commit h` implies the sub-multiset is GENUINELY in `h`. This
is exactly what the deployed Poseidon2 `MerkleAir` + collision-resistance give — it is NOT
re-proven in this pure model; it is carried like `AirSpec air` is carried upstream, so
`#assert_axioms` never sees it as an axiom. -/
def MerkleSound (M : MerkleScheme) : Prop :=
  ∀ (h sub : Multiset Geisha), M.Member (M.commit h) sub → sub ≤ h

/-! ## 2. `legalB` as a proposition, and the legal ⇒ `applyLegal` collapse -/

/-- `legalB` unpacked: a legal action is the acting player's, kind unused, cards in hand. -/
theorem legalB_iff (s : GState) (p : Player) (a : Action) :
    legalB s p a = true ↔
      (s.current = p ∧ s.used p a.kind = false ∧ actionCards a ≤ s.hand p) := by
  simp only [legalB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', and_assoc]

/-- On a legal action, `applyAction` IS `applyLegal` (the `bif` selects the update branch). -/
theorem applyAction_of_legal (s : GState) (p : Player) (a : Action) (h : legalB s p a = true) :
    applyAction s p a = applyLegal s p a := by
  simp only [applyAction, h, cond_true]

/-! ## 3. The concrete fold-leaf AIR predicate (the membership play-leaf) -/

/-- **`airPlay M o p a n` — the CONCRETE Phase-3 fold-leaf admission relation.** A membership
play leaf admits `(o, p, a, n)` when: it is the acting player's turn, the play's cards are
membership-proven under the committed hand root `M.commit (o.hand p)`, the action-kind is unused
this round, and the witnessed next state `n` is the model update `applyLegal o p a`. This is the
Lean shadow of `fold.rs::membership_leaf_for_play` + `mint_turn` (a `Custom` leaf bound to
`[leaf, root]`, the next state computed off-circuit and re-checked). -/
def airPlay (M : MerkleScheme) (o : GState) (p : Player) (a : Action) (n : GState) : Prop :=
  o.current = p ∧
  M.Member (M.commit (o.hand p)) (actionCards a) ∧
  o.used p a.kind = false ∧
  n = applyLegal o p a

/-- **`airPlay_iff_applyAction` (THE ABSTRACT PLAY-LEAF REFINEMENT — ⚠ NOT connected to the deployed
Rust fold; see the resolution note atop this file).** The abstract play-leaf's admission
relation is EXACTLY the graph of `applyAction` restricted to a legal, membership-proven play —
the game-level analogue of `evalSimpleCtx_*_iff`, for the membership leaf. `MerkleSound` is
load-bearing: membership under the committed root ⇒ the card is in the hand ⇒ the play is legal
⇒ `applyAction = applyLegal`. NON-vacuous — the RHS carries a real `legalB`/membership content,
not `P → P`. -/
theorem airPlay_iff_applyAction (M : MerkleScheme) (hsound : MerkleSound M)
    (o : GState) (p : Player) (a : Action) (n : GState) :
    airPlay M o p a n ↔
      (legalB o p a = true ∧ M.Member (M.commit (o.hand p)) (actionCards a)
        ∧ n = applyAction o p a) := by
  constructor
  · rintro ⟨hcur, hmem, hused, hn⟩
    have hle : actionCards a ≤ o.hand p := hsound _ _ hmem
    have hleg : legalB o p a = true := (legalB_iff o p a).mpr ⟨hcur, hused, hle⟩
    refine ⟨hleg, hmem, ?_⟩
    rw [applyAction_of_legal o p a hleg]; exact hn
  · rintro ⟨hleg, hmem, hn⟩
    obtain ⟨hcur, hused, _hle⟩ := (legalB_iff o p a).mp hleg
    rw [applyAction_of_legal o p a hleg] at hn
    exact ⟨hcur, hmem, hused, hn⟩

/-- **`airPlay_refines_airSpec` (concrete leaf ⇒ abstract obligation).** Given ANY AIR meeting
the abstract `AirSpec` obligation, the concrete fold-leaf's admission relation coincides with
that AIR's on the legal membership-proven play class. The concrete leaf REFINES the hypothesized
abstract AIR — it is the emitted realization of the contract `MultiwayTug.AirSpec` states. -/
theorem airPlay_refines_airSpec (M : MerkleScheme) (hsound : MerkleSound M)
    (air : GState → Player → Action → GState → Prop) (hair : AirSpec air)
    (o : GState) (p : Player) (a : Action) (n : GState) :
    airPlay M o p a n ↔
      (legalB o p a = true ∧ M.Member (M.commit (o.hand p)) (actionCards a) ∧ air o p a n) := by
  rw [airPlay_iff_applyAction M hsound, hair o p a n]

/-- **`airPlay_functional` (the leaf inherits `applyAction`'s determinism).** A membership leaf
admits at most one successor per `(o, p, a)` — the emitted circuit is functional. -/
theorem airPlay_functional (M : MerkleScheme) (hsound : MerkleSound M)
    {o : GState} {p : Player} {a : Action} {n₁ n₂ : GState}
    (h₁ : airPlay M o p a n₁) (h₂ : airPlay M o p a n₂) : n₁ = n₂ :=
  (((airPlay_iff_applyAction M hsound o p a n₁).mp h₁).2.2).trans
    (((airPlay_iff_applyAction M hsound o p a n₂).mp h₂).2.2).symm

/-- **`remaining_root_updates` (the fold's remaining-hand recommit).** After a membership play,
the committed root of the acting player's remaining hand is the commitment of `hand − played` —
the Lean shadow of `HandTree::without`. A re-play of the same card fails membership under this
new root (it is no longer in `n.hand p`), the crypto no-double-play tooth. -/
theorem remaining_root_updates (M : MerkleScheme) (o : GState) (p : Player) (a : Action)
    (n : GState) (h : airPlay M o p a n) :
    M.commit (n.hand p) = M.commit (o.hand p - actionCards a) := by
  rcases h with ⟨_, _, _, hn⟩
  rw [hn]
  simp only [applyLegal, Function.update_self]

/-- **`airPlay_chain_are_applySteps` (the two-turn compositional step).** Two consecutive fold
leaves compose as two consecutive `applyAction` steps — the inductive step of the whole
match-fold refinement (the deployed `prove_turn_chain_recursive` chaining the per-play leaves;
its full IVC soundness over an arbitrary chain is the STATED remainder). -/
theorem airPlay_chain_are_applySteps (M : MerkleScheme) (hsound : MerkleSound M)
    {o₁ o₂ o₃ : GState} {p₁ p₂ : Player} {a₁ a₂ : Action}
    (h₁ : airPlay M o₁ p₁ a₁ o₂) (h₂ : airPlay M o₂ p₂ a₂ o₃) :
    o₂ = applyAction o₁ p₁ a₁ ∧ o₃ = applyAction o₂ p₂ a₂ :=
  ⟨((airPlay_iff_applyAction M hsound _ _ _ _).mp h₁).2.2,
   ((airPlay_iff_applyAction M hsound _ _ _ _).mp h₂).2.2⟩

/-! ## 4. The win as a bound public output -/

/-- **`winBound s p winPI`** — the terminal win/score leaf's public win bit `winPI` pinned to
the model win predicate `Won` (the `game-turn-slice` range-gadget leaf's public output). -/
def winBound (s : GState) (p : Player) (winPI : Bool) : Prop := winPI = true ↔ Won s p

/-- The public win bit IS the model win fact (the PI binding). -/
theorem winBound_pins (s : GState) (p : Player) (winPI : Bool) (h : winBound s p winPI) :
    winPI = true ↔ Won s p := h

/-- Non-vacuity of the win binding (a real win): `winState` binds `winPI = true`. -/
theorem winBound_winState : winBound winState .p1 true :=
  ⟨fun _ => winState_wins, fun _ => rfl⟩

/-- Teeth of the win binding (a non-win): the blank state binds `winPI = false`. -/
theorem winBound_blank (p : Player) : winBound blankState p false :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (not_won_blank p)⟩

/-! ## 5. The IDEAL (perfect-binding) scheme + the correspondence witnesses -/

/-- The IDEAL Merkle scheme: the committed hand IS its own root (`commit = id`) and membership
is genuine sub-multiset containment. This is the perfect-binding limit the deployed Poseidon2
scheme approximates — its `MerkleSound` holds unconditionally, so the correspondence witnesses
below are concrete (no carried hypothesis). -/
def idealScheme : MerkleScheme where
  Root := Multiset Geisha
  commit := id
  Member := fun root sub => sub ≤ root

/-- The ideal scheme is sound by construction (containment ⇒ containment). -/
theorem idealScheme_sound : MerkleSound idealScheme := fun _ _ hmem => hmem

/-- **`demo_play_is_applyStep` (THE CORRESPONDENCE WITNESS).** A membership-proven play IS an
`applyAction` step: P1's legal Gift `3 3 5` out of `demo`'s hand is admitted by the concrete
fold-leaf `airPlay` and its next state is exactly `applyAction demo .p1 (gift 3 3 5)`. -/
theorem demo_play_is_applyStep :
    airPlay idealScheme demo .p1 (Action.gift 3 3 5)
      (applyAction demo .p1 (Action.gift 3 3 5)) := by
  refine (airPlay_iff_applyAction idealScheme idealScheme_sound demo .p1 (Action.gift 3 3 5)
    (applyAction demo .p1 (Action.gift 3 3 5))).mpr ⟨?_, ?_, rfl⟩
  · decide
  · show actionCards (Action.gift 3 3 5) ≤ demo.hand .p1
    decide

/-- **`demo_fabricated_refused` (teeth — a fabricated play is NOT admitted).** A play of a card
NOT in the hand (`secret 4`, no 4 in `demo`'s hand) has no membership proof under the committed
root, so the fold-leaf refuses it. -/
theorem demo_fabricated_refused :
    ¬ airPlay idealScheme demo .p1 (Action.secret 4)
        (applyAction demo .p1 (Action.secret 4)) := by
  rintro ⟨_, hmem, _, _⟩
  have hmem' : actionCards (Action.secret 4) ≤ demo.hand .p1 := hmem
  revert hmem'; decide

/-! ### `#guard` smoke — the decidable core of the correspondence -/

-- The Gift's cards ARE members of P1's committed hand (membership under the ideal root holds).
#guard actionCards (Action.gift 3 3 5) ≤ demo.hand .p1
-- A fabricated card is NOT a member (the refusal is real, not vacuous).
#guard ¬ (actionCards (Action.secret 4) ≤ demo.hand .p1)

/-! ## 6. Axiom hygiene — the connected refinement pinned to the standard kernel triple.

`MerkleSound` (the deployed STARK's soundness) and `AirSpec` are CARRIED hypotheses, not axioms,
so `#assert_axioms` (which is blind to hypotheses) stays clean on `{propext, Classical.choice,
Quot.sound}`. -/

#assert_axioms legalB_iff
#assert_axioms applyAction_of_legal
#assert_axioms airPlay_iff_applyAction
#assert_axioms airPlay_refines_airSpec
#assert_axioms airPlay_functional
#assert_axioms remaining_root_updates
#assert_axioms airPlay_chain_are_applySteps
#assert_axioms winBound_pins
#assert_axioms winBound_winState
#assert_axioms winBound_blank
#assert_axioms idealScheme_sound
#assert_axioms demo_play_is_applyStep
#assert_axioms demo_fabricated_refused

end Dregg2.Games.MultiwayTug
