/-!
# `CapMerkleGeneric` — the width-AGNOSTIC cap-Merkle recompose + its anti-ghost spine.

This is the Option-A abstraction for the `cap_root` native-8-felt weld (Phase H-CAP-8): the
sorted-binary-Merkle membership recompose, parameterized over an ABSTRACT digest type `D` and an
internal-node function `node : D → D → D`. The ONE soundness lemma the whole cap-open corpus rests
on — `recomposeG` is injective in its starting leaf digest along a FIXED path, under the node's
collision-resistance — is proved ONCE here, generically, and INSTANTIATED twice:

  * `D := ℤ`, `node := DeployedCapTree.nodeOf` (the deployed 1-felt `cap_root.rs::cap_node`), with
    `node_inj := DeployedCapTree.nodeOf_injective` — RECOVERS the existing 1-felt proof.
  * `D := Fin 8 → ℤ` (or any 8-felt digest carrier), `node := nodeOf8` (the `node8` chip
    compression `cap_root.rs::cap_node8`), with `node_inj` from the arity-16 chip's CR — the NEW
    8-felt instance, with NO re-proof of the recompose spine.

The point (per the grind methodology): REUSE the 1-felt proof effort. `recomposeG_inj_of_path` only
ever calls `node_inj` (peeling one level per `node`-injectivity step) and the `recomposeG` unfold —
nothing width-specific — so the 1→8 migration of the membership soundness is a re-INSTANTIATION, not
a re-proof. The mix convention matches `cap_root.rs::recompose_membership` / `DeployedCapTree.recomposeUp`
byte-for-byte: `dir = false` ⇒ `cur` is the LEFT child (`node cur sib`), `dir = true` ⇒ RIGHT child
(`node sib cur`).
-/

namespace Dregg2.Circuit.CapMerkleGeneric

variable {D : Type}

/-- One Merkle path step over an abstract digest type `D`: the sibling digest at this level plus the
direction bit. The 1-felt `DeployedCapTree.Step` is `StepG ℤ`; the 8-felt tree uses `StepG (Fin 8 → ℤ)`. -/
structure StepG (D : Type) where
  /-- The sibling digest at this level (`cap_root.rs` `siblings[level]`). -/
  sib : D
  /-- `false` ⇒ `cur` is the LEFT child (sibling on the right); `true` ⇒ RIGHT child. -/
  dir : Bool

/-- **`recomposeG node cur path`** — fold the held digest up the sibling/direction path through the
abstract node `node`, mixing `(cur, sib)` by the direction bit. Width-agnostic twin of
`DeployedCapTree.recomposeUp` and `cap_root.rs::recompose_membership`. -/
def recomposeG (node : D → D → D) (cur : D) : List (StepG D) → D
  | [] => cur
  | s :: rest =>
    recomposeG node (if s.dir then node s.sib cur else node cur s.sib) rest

/-- **THE width-agnostic anti-ghost spine.** Under the node's collision-resistance (`node` injective
in BOTH children), `recomposeG` is injective in its STARTING digest along any FIXED path: equal
recomposed roots from the same path force equal starting leaf digests. A prover cannot keep the
published root while swapping the opened leaf along a fixed path — at ANY digest width.

This is the SINGLE proof the 1-felt (`nodeOf`) and 8-felt (`nodeOf8`) cap trees both instantiate; it
calls ONLY `node_inj` and the `recomposeG` unfold (nothing width-specific). -/
theorem recomposeG_inj_of_path
    (node : D → D → D)
    (node_inj : ∀ {l₁ r₁ l₂ r₂ : D}, node l₁ r₁ = node l₂ r₂ → l₁ = l₂ ∧ r₁ = r₂)
    (path : List (StepG D)) :
    ∀ {a b : D}, recomposeG node a path = recomposeG node b path → a = b := by
  induction path with
  | nil => intro a b h; simpa [recomposeG] using h
  | cons s rest ih =>
    intro a b h
    simp only [recomposeG] at h
    have hstep := ih h
    cases hd : s.dir with
    | false =>
      rw [hd] at hstep
      simp only [Bool.false_eq_true, if_false] at hstep
      exact (node_inj hstep).1
    | true =>
      rw [hd] at hstep
      simp only [if_true] at hstep
      exact (node_inj hstep).2

/-! ## The EXTRACTION-AS-DATA spine — the sound form for a DEPLOYED keystone.

`recomposeG_inj_of_path` CONSUMES a node-injectivity hypothesis. At any deployed digest width that
hypothesis is FALSE: the node is a compressing hash into bounded lanes, so it collides by pigeonhole
(`VacuitySweepTeeth.compress8CR_false_babyBear` proves exactly this for the arity-16 `node8` chip). A
keystone that CARRIES that hypothesis therefore says nothing about the deployed system, and a
STRUCTURE FIELD carrying it makes the structure uninhabitable and every theorem over it vacuous.

The walk below is the SAME peel written as a TOTAL FUNCTION. Given two starting digests and a fixed
path it either proves them equal or LANDS on the specific level whose two child-pairs are a genuine
`node` collision, and hands that pair back as DATA. Consumers then carry `a = b ∨ NodeColl …` — a
disjunction that is TRUE of the deployed node, where the injective form was empty.

Note what `NodeColl` is NOT: it is not `∃ p q, node-collides p q`, which pigeonhole makes
unconditionally true at deployed parameters and which therefore binds nothing. It is a predicate about
the SPECIFIC pair the extractor RETURNS, and it is REFUTABLE (see `nodeColl_refutable_of_injective`). -/

/-- `NodeColl node pq` — the pair of child-pairs `pq = (p, q)` is a GENUINE collision of the
internal-node function: DISTINCT children with the SAME node image. -/
def NodeColl (node : D → D → D) (pq : (D × D) × (D × D)) : Prop :=
  pq.1 ≠ pq.2 ∧ node pq.1.1 pq.1.2 = node pq.2.1 pq.2.2

/-- "Is this pair of child-pairs a genuine collision?" is DECIDABLE at any decidable digest type — so
the extractor may branch on it and remain a TOTAL function, with no `Classical.choice` in the walk. -/
instance decidableNodeColl [DecidableEq D] (node : D → D → D) (pq : (D × D) × (D × D)) :
    Decidable (NodeColl node pq) := by
  unfold NodeColl
  infer_instance

/-- The child pair one path step forms around the held digest: `dir = false` ⇒ `cur` LEFT, `dir = true`
⇒ `cur` RIGHT. The `recomposeG` mix, as data. -/
def mixG (s : StepG D) (cur : D) : D × D :=
  if s.dir then (s.sib, cur) else (cur, s.sib)

/-- One `recomposeG` step, factored through `mixG` (definitional; both branches of the direction bit). -/
theorem recomposeG_cons (node : D → D → D) (s : StepG D) (cur : D) (rest : List (StepG D)) :
    recomposeG node cur (s :: rest)
      = recomposeG node (node (mixG s cur).1 (mixG s cur).2) rest := by
  cases hd : s.dir <;> simp [recomposeG, mixG, hd]

/-- **⚑ THE PATH WALK.** Step the two recomposes up together. At each level the two child-pairs are
`mixG s a` and `mixG s b`; if they COLLIDE (distinct pairs, equal node images) return them, else carry
on with the two new folded digests. If the path runs out, return a trivially non-colliding pair — the
spec's `nil` case delivers `a = b` outright and never needs the returned value.

Note the case the `else` absorbs and `recomposeGFind_spec` handles: the two levels may have DIFFERENT
node images here and the folds still re-converge higher up. That is why the walk continues rather than
concluding — the case a "peel from the outside" proof gets for free, but a FUNCTION must survive. -/
def recomposeGFind [DecidableEq D] (node : D → D → D) :
    D → D → List (StepG D) → (D × D) × (D × D)
  | a, _, [] => ((a, a), (a, a))
  | a, b, s :: rest =>
      if NodeColl node (mixG s a, mixG s b) then (mixG s a, mixG s b)
      else
        recomposeGFind node (node (mixG s a).1 (mixG s a).2) (node (mixG s b).1 (mixG s b).2) rest

/-- **⚑ THE WALK IS CORRECT — this is the sound replacement for `recomposeG_inj_of_path`.** Equal
recomposed roots along a FIXED path EITHER force equal starting digests, OR the walk lands on a genuine
`node` collision, handed back by name. The old theorem's peel, restated so the failure branch produces
a WITNESS instead of consuming an injectivity hypothesis the deployed node refutes. -/
theorem recomposeGFind_spec [DecidableEq D] (node : D → D → D) :
    ∀ (path : List (StepG D)) {a b : D},
      recomposeG node a path = recomposeG node b path →
      a = b ∨ NodeColl node (recomposeGFind node a b path) := by
  intro path
  induction path with
  | nil =>
    intro a b h
    exact Or.inl (by simpa [recomposeG] using h)
  | cons s rest ih =>
    intro a b h
    by_cases hif : NodeColl node (mixG s a, mixG s b)
    · refine Or.inr ?_
      show NodeColl node (recomposeGFind node a b (s :: rest))
      rw [recomposeGFind, if_pos hif]
      exact hif
    · rw [recomposeG_cons, recomposeG_cons] at h
      rcases ih h with heq | hcoll
      · -- the folded digests agree; with the failed collision test that forces the CHILD PAIRS equal.
        refine Or.inl ?_
        have hpq : mixG s a = mixG s b :=
          Decidable.byContradiction (fun hne => hif ⟨hne, heq⟩)
        cases hd : s.dir with
        | false => simpa [mixG, hd] using congrArg Prod.fst hpq
        | true => simpa [mixG, hd] using congrArg Prod.snd hpq
      · refine Or.inr ?_
        show NodeColl node (recomposeGFind node a b (s :: rest))
        rw [recomposeGFind, if_neg hif]
        exact hcoll

/-- **THE STRENGTH RELATION (`_of_injective`).** The old `recomposeG_inj_of_path` conclusion is EXACTLY
the injective special case of the walk: assume the node injectivity the deleted carriers asserted and
the collision disjunct is impossible, so the bare equality falls straight out. Nothing genuinely proved
was given up — what was given up is the pretence that a deployed compressing hash satisfies it. -/
theorem recomposeGFind_inj_of_nodeInj [DecidableEq D] (node : D → D → D)
    (node_inj : ∀ {l₁ r₁ l₂ r₂ : D}, node l₁ r₁ = node l₂ r₂ → l₁ = l₂ ∧ r₁ = r₂)
    (path : List (StepG D)) {a b : D} (h : recomposeG node a path = recomposeG node b path) :
    a = b := by
  rcases recomposeGFind_spec node path h with heq | ⟨hne, himg⟩
  · exact heq
  · exact absurd (Prod.ext (node_inj himg).1 (node_inj himg).2) hne

/-- **(CANARY — the collision disjunct is REFUTABLE, so the disjunction is not a free pass.)** At an
injective node the extracted pair is NOT a collision, so `recomposeGFind_spec` cannot discharge itself
by taking the right branch: the binding half has to do the work. A disjunction whose right side were
always available would carry no more content than `True`. -/
theorem nodeColl_refutable_of_nodeInj (node : D → D → D)
    (node_inj : ∀ {l₁ r₁ l₂ r₂ : D}, node l₁ r₁ = node l₂ r₂ → l₁ = l₂ ∧ r₁ = r₂)
    (pq : (D × D) × (D × D)) : ¬ NodeColl node pq := by
  rintro ⟨hne, himg⟩
  exact hne (Prod.ext (node_inj himg).1 (node_inj himg).2)

-- (This module is deliberately IMPORT-FREE — no `#assert_axioms` command is in scope here. The
-- axiom-hygiene tripwires for the walk are pinned at its 8-felt instantiation in
-- `DeployedCapTree` §5b, which imports the tripwire.)

end Dregg2.Circuit.CapMerkleGeneric
