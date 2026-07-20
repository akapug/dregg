/-
# `Dregg2.Circuit.FriColumnLogExtract` — THE STRAIGHT-LINE QUERY-LOG EXTRACTOR
(commitment → total column), and the REFUTATION of the seam it was supposed to close.

## What this file is

`FriColumnDecode.ColumnDecodeBridge` (`FriColumnDecode.lean:341`) is the residual behind
`accept_folds`, and its module docstring decomposes that residual into four verifier-side
sub-seams. Sub-seam **(a)** reads:

> **commitment → total column**: `BatchProofData` carries per-QUERY Merkle openings; the total
> committed column function is the extractor's object under Poseidon2 Merkle binding
> (`merkleRecompute_binds` is the proven tooth; turning openings into a committed FUNCTION is
> knowledge-extraction, not algebra);

Nothing in-tree implemented that extractor. This file builds it — BCS16-style, **straight-line**
(no rewinding, no forking): the extractor is a PURE FUNCTION of the adversary's own query log
(`RomQueryLog.OracleComp.log`), reading the Merkle tree out of the `(preimage, answer)` pairs the
adversary produced. `treeExtractComp_queryBounded` records the straight-line property formally —
the extractor is `QueryBounded 0`, it never touches the oracle.

And then it REFUTES the seam's premise.

## ⚑ THE FINDING — Merkle binding does NOT yield a committed TOTAL column

`partial_commitment_verifies_but_no_total_column` (§5) exhibits, for EVERY node oracle `H` and
every `x2 x3 w` in general position (three explicit disequalities, each failing on an `O(1/|α|)`
slice of oracles), a `QueryBounded 2` adversary that

  * publishes a root `root = H (w, H (x2, x3))`,
  * carries an authenticated opening `merkleRecO H 2 x2 [x3, w] = root` that the DEPLOYED verifier
    check accepts verbatim (this is `FriVerifierMerkle.merkleRecO`, the deployed recompute), and
  * whose COMPLETE query log admits NO depth-2 total column: `treeExtract … = none`.

It pays no `1/|α|`, exhibits no collision, and is not a lucky guess: it verifies for EVERY oracle
agreeing with its two logged answers. The reason is structural. A Merkle root commits to exactly
the part of the tree the prover actually HASHED; a prover may invent an interior node `w` out of
thin air, never query below it, and hash upward. Every leaf under `w` is then simply not committed
to anything. Positional binding at OPENED positions (`merkleRecompute_binds`,
`findCollisionZ_none_binds`) is all that Merkle gives, and positional binding is not a function.

**Consequence for the seam.** Sub-seam (a) does not precede sub-seam (b) — it REDUCES to it. The
gap between "the openings the verifier checked" and "a total column at every domain position" is
the same spot-check gap (b) names, with the same shape: a prover leaving a `μ`-fraction of leaves
un-hashed survives `k` spot checks with probability `(1 − μ)^k`. So `ColumnDecodeBridge`'s
`accept_chains`, which quantifies over ALL `y : Fin 2` (full domain), CANNOT be discharged by
extraction under Merkle binding. Extraction supplies the column only on the hashed part; the rest
is (b). The four sub-seams are three.

## What IS proved here (the extractor is real and it works on the hashed part)

  1. **`treeExtract` (§1)** — the straight-line extractor: `treeExtract L d root` walks the log `L`
     top-down from `root`, at each interior node picking a logged pair whose ANSWER is the current
     node and recursing on its two arguments. Computable, log-only, `QueryBounded 0`.
  2. **SOUNDNESS (`treeExtract_isTree`, `treeExtract_log_isTree`)** — whatever it returns is a
     GENUINE `H`-preimage tree of the root (`IsTree`), and its length is exactly `2^d`. The
     faithfulness hypothesis is not floating: `OracleComp.mem_log_answer` discharges it for every
     real log, so `treeExtract_log_isTree` has NO hypothesis beyond "the extraction succeeded".
  3. **BINDING (`isTree_unique_or_collision`)** — two total columns under ONE root force an
     `H`-collision. So the extracted column is THE committed one, up to the collision event
     `birthday_cond` already bounds (`FriVerifierMerkle.merkle_path_collision_prob_le`).
  4. **OPENING AGREEMENT (`isTree_opening_agrees`, `log_column_total_and_binds`)** — the payoff
     shape of (a): every authenticated opening the DEPLOYED verifier accepts
     (`merkleRecO H i v sibs = root`, deployed sibling order, deployed `pnode` index bits) agrees
     with the extracted column at position `i % 2^d`, or exhibits an `H`-collision. This is the
     real content: extraction and the verifier's own path check cannot disagree for free.
  5. **THE ε OVER A Q-BOUNDED ADVERSARY (§4)** — `freshHit_prob_le`: for ANY `Q`-query adversary
     `M`, conditioned on everything it learned (the cylinder over its own `queriedFinset`, of size
     `≤ Q`), the probability that its published root is `H` of a preimage it NEVER QUERIED is
     `≤ 1/|α|` — and `freshHit_prob_eq_of_fresh` shows this is EXACT, not slack. The `n`-node union
     bound `anyFreshHit_prob_le` gives `n/|α|`; `deployed_freshHit_prob_le` instantiates at the
     shipped BabyBear node oracle `|α| = |F| = 2013265921`.

## What is REFUTED (§5), with witnesses

  * **`no_deterministic_extraction`** — "the node check passes ⟹ the extractor recovers the
    subtree" is FALSE. Witness: a `QueryBounded 0` adversary over `α = Bool` that guesses a root
    (`guesser`), with the empty log. Deterministic extraction is impossible in principle; the
    honest form is the §4 probability, whose value is EXACTLY `1/|α|` (not `0`).
  * **`partial_commitment_verifies_but_no_total_column`** — the finding above. Not probabilistic,
    not a collision: a verifying opening + the complete log + no total column.

## What remains NAMED (not papered)

  * **(a1) the leaf-digest layer.** `IsTree` bottoms out at depth-0 DIGESTS. The deployed leaves
    are `Int` felt values entering a leaf hash; the felt↔leaf-digest step (and its injectivity) is
    NOT proved here.
  * **(a2) the `α`-pin.** `H : α × α → α` finite node oracle vs. the deployed list sponge — the
    permanent ROM instantiation carrier already named by
    `FriVerifierMerkle.sponge_pair_oracle_bridge`. Unchanged, still a carrier.
  * **(a3) root ↔ `verifyAlgo`.** Tying the `root` this file extracts from to the commitment an
    accepting `verifyAlgo` run actually pins is `verifyAlgoO`-level plumbing; not done here.
  * **(a4) ⚑ the un-hashed remainder.** THE finding: the residual is (b), and it is probabilistic.
  * **(b) proximity.** Untouched. Extraction gives the committed FUNCTION, never its DEGREE.

## Discipline

Sorry-free; no `axiom`; no `native_decide`; no `def …Sound` carrier. `#assert_all_clean` ⊆
`{propext, Classical.choice, Quot.sound}`. ADDITIVE: `FriVerifierMerkle`, `FriVerifierFS`,
`RomOracle`, `RomQueryLog`, `RomCounting`, `FriColumnDecode` imported read-only / untouched. The
deployed `pnode`/`merkleRecO` are REUSED from `FriVerifierMerkle`, not forked.
-/
import Dregg2.Circuit.FriVerifierMerkle
import Dregg2.Circuit.FriVerifierFS

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.FriColumnLogExtract

open Dregg2.Crypto.RomOracle
open Dregg2.Crypto.RomCounting
open Dregg2.Circuit.FriVerifierMerkle (pnode merkleRecO merkleRecO_cons queriedFinset
  mem_queriedFinset_iff queriedFinset_card_le)
open Dregg2.Circuit.FriVerifierFS (condProb_or_le)

/-! ## §0 — Nat scaffolding for the deployed index bits.

The deployed path check `merkleRecO` consumes siblings DEEPEST-FIRST and halves the index at each
level (`FriVerifierMerkle.merkleRecO_cons`), while a tree is naturally read TOP-DOWN. The two meet
through `merkleRecO_concat` (peel the LAST sibling = the top level, whose side bit is
`(i / 2^d) % 2`) and `nat_mod_pow_succ` (the leaf index splits as low bits + that same top bit). -/

/-- The leaf index splits at level `d`: the low `d` bits, plus `2^d` times the level-`d` side bit.
This is the arithmetic that makes "top-down tree" and "bottom-up path" the same object. -/
theorem nat_mod_pow_succ (i d : ℕ) : i % 2 ^ (d + 1) = i % 2 ^ d + 2 ^ d * (i / 2 ^ d % 2) := by
  have h1 : i % 2 ^ (d + 1) % 2 ^ d = i % 2 ^ d :=
    Nat.mod_mod_of_dvd i (pow_dvd_pow 2 (Nat.le_succ d))
  have h2 : i % 2 ^ (d + 1) / 2 ^ d = i / 2 ^ d % 2 := by
    rw [pow_succ]; exact Nat.mod_mul_right_div_self i (2 ^ d) 2
  have h3 := Nat.div_add_mod (i % 2 ^ (d + 1)) (2 ^ d)
  rw [h1, h2] at h3
  omega

/-- `merkleRecO` with the empty sibling list is the identity on the accumulator. -/
theorem merkleRecO_nil {α : Type} (H : α × α → α) (i : ℕ) (v : α) :
    merkleRecO H i v [] = v := rfl

/-- The deployed node preimage at an EVEN index bit: accumulator on the left. -/
theorem pnode_even {α : Type} {idx : ℕ} (h : idx % 2 = 0) (a s : α) :
    pnode idx a s = (a, s) := by
  unfold pnode; rw [if_pos h]

/-- The deployed node preimage at an ODD index bit: accumulator on the right. -/
theorem pnode_odd {α : Type} {idx : ℕ} (h : idx % 2 = 1) (a s : α) :
    pnode idx a s = (s, a) := by
  unfold pnode; rw [if_neg (by omega)]

/-- `getD` through an append, left half. -/
theorem getD_append_left {α : Type} (ls rs : List α) (n : ℕ) (dflt : α) (h : n < ls.length) :
    (ls ++ rs).getD n dflt = ls.getD n dflt := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- `getD` through an append, right half. -/
theorem getD_append_right {α : Type} (ls rs : List α) (k : ℕ) (dflt : α) :
    (ls ++ rs).getD (ls.length + k) dflt = rs.getD k dflt := by
  simp [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right ls.length k)]

/-- **PEEL THE TOP LEVEL.** The deployed recompute over `sibs ++ [s]` is the recompute over `sibs`
followed by ONE more level whose side bit is `(i / 2^|sibs|) % 2` — the level the top of a
depth-`|sibs|+1` tree sits at. This is the bridge between the verifier's bottom-up path walk and a
top-down tree. -/
theorem merkleRecO_concat {α : Type} (H : α × α → α) (s : α) :
    ∀ (sibs : List α) (i : ℕ) (v : α),
      merkleRecO H i v (sibs ++ [s])
        = H (pnode (i / 2 ^ sibs.length) (merkleRecO H i v sibs) s) := by
  intro sibs
  induction sibs with
  | nil =>
      intro i v
      show merkleRecO H i v [s] = H (pnode (i / 2 ^ 0) v s)
      rw [merkleRecO_cons, merkleRecO_nil, pow_zero, Nat.div_one]
  | cons t rest ih =>
      intro i v
      show merkleRecO H i v (t :: (rest ++ [s]))
        = H (pnode (i / 2 ^ (rest.length + 1)) (merkleRecO H i v (t :: rest)) s)
      rw [merkleRecO_cons, merkleRecO_cons, ih (i / 2) (H (pnode i v t))]
      have hdiv : i / 2 / 2 ^ rest.length = i / 2 ^ (rest.length + 1) := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
      rw [hdiv]

section Extractor

variable {α : Type} [DecidableEq α]

/-! ## §1 — The tree relation, the straight-line extractor, and its soundness. -/

/-- **A FULL BINARY MERKLE TREE OF DEPTH `d`.** `IsTree H d root xs` says: `xs` is the leaf list
(left-to-right) of a depth-`d` tree whose every interior node is a genuine `H`-application and
whose root is `root`. The root of a `node` is carried as an EQUATION so the relation inverts
cleanly (`cases`) — the index stays a variable. -/
inductive IsTree (H : α × α → α) : ℕ → α → List α → Prop where
  /-- A depth-`0` tree is a single leaf, and it IS its own root. -/
  | leaf (x : α) : IsTree H 0 x [x]
  /-- Two depth-`d` trees joined by one genuine `H`-application. -/
  | node {d : ℕ} {l r root : α} {ls rs : List α} :
      IsTree H d l ls → IsTree H d r rs → H (l, r) = root → IsTree H (d + 1) root (ls ++ rs)

/-- Inversion at depth `0`: the tree IS its root. -/
theorem IsTree.zero_inv {H : α × α → α} {root : α} {xs : List α} (h : IsTree H 0 root xs) :
    xs = [root] := by
  cases h with | leaf x => rfl

/-- Inversion at depth `d+1`: two depth-`d` subtrees joined by one genuine `H`-application. Stated
as an existential so the implicit indices are ACCESSIBLE at every use site. -/
theorem IsTree.succ_inv {H : α × α → α} {d : ℕ} {root : α} {xs : List α}
    (h : IsTree H (d + 1) root xs) :
    ∃ (l r : α) (ls rs : List α),
      IsTree H d l ls ∧ IsTree H d r rs ∧ H (l, r) = root ∧ xs = ls ++ rs := by
  cases h with
  | node hl hr heq => exact ⟨_, _, _, _, hl, hr, heq, rfl⟩

/-- A depth-`d` tree has exactly `2^d` leaves — the extracted column is TOTAL on its domain. -/
theorem IsTree.length_eq {H : α × α → α} :
    ∀ {d : ℕ} {root : α} {xs : List α}, IsTree H d root xs → xs.length = 2 ^ d := by
  intro d root xs h
  induction h with
  | leaf x => simp
  | node _ _ _ ihl ihr =>
      rw [List.length_append, ihl, ihr, pow_succ]
      ring

/-- **AN `H`-COLLISION**, as the one thing binding can fail by. -/
def HasCollision (H : α × α → α) : Prop := ∃ a b : α × α, a ≠ b ∧ H a = H b

/-- **⚑ THE STRAIGHT-LINE QUERY-LOG EXTRACTOR.** `treeExtract L d root` reconstructs the depth-`d`
committed column from the query log `L` alone: at an interior node it looks for a logged pair whose
ANSWER is the current node value, and recurses on that pair's two arguments; at depth `0` the node
IS the leaf. `none` means the log does not contain the tree.

NOTE what it does not do: it never queries the oracle, never rewinds, never forks. It is a pure
function of `(L, d, root)` — BCS16's straight-line extractor, on our own `RomQueryLog` substrate.
NOTE also `List.find?`: if the adversary logged TWO preimages of one node value, the extractor takes
the first. `isTree_unique_or_collision` is exactly why that costs nothing beyond a collision. -/
def treeExtract (L : List ((α × α) × α)) : ℕ → α → Option (List α)
  | 0,     root => some [root]
  | d + 1, root =>
      (L.find? (fun e => decide (e.2 = root))).bind (fun e =>
        (treeExtract L d e.1.1).bind (fun ls =>
          (treeExtract L d e.1.2).map (fun rs => ls ++ rs)))

theorem treeExtract_zero (L : List ((α × α) × α)) (root : α) :
    treeExtract L 0 root = some [root] := rfl

theorem treeExtract_succ (L : List ((α × α) × α)) (d : ℕ) (root : α) :
    treeExtract L (d + 1) root
      = (L.find? (fun e => decide (e.2 = root))).bind (fun e =>
          (treeExtract L d e.1.1).bind (fun ls =>
            (treeExtract L d e.1.2).map (fun rs => ls ++ rs))) := rfl

/-- **THE EXTRACTOR IS STRAIGHT-LINE**, formally: packaged as an oracle computation it is
`QueryBounded 0` — it makes ZERO oracle queries. Everything it knows, it read off the log. (Contrast
a rewinding extractor, which would have to re-run the adversary and is not expressible as a single
`QueryBounded Q` computation at all.) -/
def treeExtractComp (L : List ((α × α) × α)) (d : ℕ) (root : α) :
    OracleComp (α × α) α (Option (List α)) := .pure (treeExtract L d root)

theorem treeExtractComp_queryBounded (L : List ((α × α) × α)) (d : ℕ) (root : α) :
    QueryBounded 0 (treeExtractComp L d root) := QueryBounded.pure 0 _

/-- **SOUNDNESS OF THE EXTRACTOR.** Against a FAITHFUL log (every logged pair really is
`(point, H point)`), whatever `treeExtract` returns is a genuine depth-`d` `H`-preimage tree of the
root. Nothing is invented: every interior node of the returned column is an actual `H`-application
the adversary performed. -/
theorem treeExtract_isTree {H : α × α → α} {L : List ((α × α) × α)}
    (hL : ∀ e ∈ L, H e.1 = e.2) :
    ∀ (d : ℕ) (root : α) (xs : List α), treeExtract L d root = some xs → IsTree H d root xs := by
  intro d
  induction d with
  | zero =>
      intro root xs hx
      rw [treeExtract_zero] at hx
      obtain rfl := (Option.some.inj hx).symm
      exact IsTree.leaf root
  | succ d ih =>
      intro root xs hx
      rw [treeExtract_succ] at hx
      cases hfind : L.find? (fun e => decide (e.2 = root)) with
      | none => rw [hfind] at hx; exact absurd hx (by simp)
      | some e =>
          rw [hfind] at hx
          simp only [Option.bind_some] at hx
          cases hls : treeExtract L d e.1.1 with
          | none => rw [hls] at hx; exact absurd hx (by simp)
          | some ls =>
              rw [hls] at hx
              simp only [Option.bind_some] at hx
              cases hrs : treeExtract L d e.1.2 with
              | none => rw [hrs] at hx; exact absurd hx (by simp)
              | some rs =>
                  rw [hrs] at hx
                  simp only [Option.map_some] at hx
                  obtain rfl := (Option.some.inj hx).symm
                  have hmem : e ∈ L := List.mem_of_find?_eq_some hfind
                  have hroot : e.2 = root :=
                    of_decide_eq_true
                      (List.find?_some (p := fun e : (α × α) × α => decide (e.2 = root)) hfind)
                  have hfaith : H e.1 = e.2 := hL e hmem
                  refine IsTree.node (ih e.1.1 ls hls) (ih e.1.2 rs hrs) ?_
                  rw [show ((e.1.1, e.1.2) : α × α) = e.1 from rfl, hfaith, hroot]

/-- **SOUNDNESS WITH NO FLOATING HYPOTHESIS.** For a REAL query log the faithfulness premise is
discharged by `RomQueryLog.OracleComp.mem_log_answer` — the log records `H` on the queried set and
records nothing false. So: whatever the extractor pulls out of a `Q`-bounded adversary's own log is
a genuine `H`-tree of the root, unconditionally. -/
theorem treeExtract_log_isTree {A : Type} (M : OracleComp (α × α) α A) (H : α × α → α)
    (d : ℕ) (root : α) (xs : List α) (hx : treeExtract (M.log H) d root = some xs) :
    IsTree H d root xs := by
  refine treeExtract_isTree (H := H) (L := M.log H) (fun e he => ?_) d root xs hx
  exact M.mem_log_answer H (show (e.1, e.2) ∈ M.log H from he)

/-- The extractor's read set is the adversary's own log, so a `Q`-query budget bounds the data the
extractor consumed: at most `Q` logged pairs. (`RomQueryLog.QueryBounded.log_length_le`.) -/
theorem extractor_reads_at_most_Q {A : Type} {M : OracleComp (α × α) α A} {Q : ℕ}
    (hM : QueryBounded Q M) (H : α × α → α) : (M.log H).length ≤ Q :=
  hM.log_length_le H

/-! ## §2 — BINDING: two total columns under one root force a collision. -/

/-- **⚑ MERKLE BINDING FOR THE EXTRACTED COLUMN.** If two leaf lists are both genuine depth-`d`
`H`-trees of the SAME root, they are EQUAL — or `H` has a collision. So the extractor's choice of
`List.find?` witness costs nothing: the extracted column is THE committed one, except on the
collision event `FriVerifierMerkle.merkle_path_collision_prob_le` already bounds. -/
theorem isTree_unique_or_collision {H : α × α → α} :
    ∀ (d : ℕ) (root : α) (xs ys : List α),
      IsTree H d root xs → IsTree H d root ys → xs = ys ∨ HasCollision H := by
  intro d
  induction d with
  | zero =>
      intro root xs ys hx hy
      rw [hx.zero_inv, hy.zero_inv]
      exact Or.inl rfl
  | succ d ih =>
      intro root xs ys hx hy
      obtain ⟨l, r, ls, rs, hl, hr, heq, rfl⟩ := hx.succ_inv
      obtain ⟨l', r', ls', rs', hl', hr', heq', rfl⟩ := hy.succ_inv
      by_cases hpair : ((l, r) : α × α) = (l', r')
      · have hll : l = l' := congrArg Prod.fst hpair
        have hrr : r = r' := congrArg Prod.snd hpair
        subst hll; subst hrr
        rcases ih l ls ls' hl hl' with hls | hc
        · rcases ih r rs rs' hr hr' with hrs | hc
          · exact Or.inl (by rw [hls, hrs])
          · exact Or.inr hc
        · exact Or.inr hc
      · exact Or.inr ⟨(l, r), (l', r'), hpair, heq.trans heq'.symm⟩

/-! ## §3 — OPENING AGREEMENT: the deployed path check cannot disagree with the extracted column. -/

/-- **⚑ THE SUB-SEAM (a) PAYOFF, ON THE HASHED PART.** Let `xs` be a genuine depth-`d` tree of
`root`. Then EVERY authenticated opening the DEPLOYED verifier accepts — a leaf value `v`, a
sibling list `sibs` of length `d`, and `merkleRecO H i v sibs = root`, i.e. `FriVerifierMerkle`'s
recompute against the node oracle, deepest-sibling-first with `pnode`'s index bits — reads back the
extracted column's own entry at position `i % 2^d`, unless `H` has a collision.

This is the real content of "commitment → column": extraction and the verifier's path check are
forced to agree. (It says NOTHING about positions the prover never hashed — see §5.) -/
theorem isTree_opening_agrees {H : α × α → α} :
    ∀ (d : ℕ) (root : α) (xs : List α), IsTree H d root xs →
      ∀ (i : ℕ) (v : α) (sibs : List α), sibs.length = d → merkleRecO H i v sibs = root →
        ∀ dflt : α, xs.getD (i % 2 ^ d) dflt = v ∨ HasCollision H := by
  intro d
  induction d with
  | zero =>
      intro root xs hx i v sibs hlen hrec dflt
      obtain rfl : xs = [root] := hx.zero_inv
      obtain rfl : sibs = [] := List.length_eq_zero_iff.mp hlen
      rw [merkleRecO_nil] at hrec
      left
      rw [pow_zero, Nat.mod_one, List.getD_cons_zero]
      exact hrec.symm
  | succ d ih =>
      intro root xs hx i v sibs hlen hrec dflt
      obtain ⟨l, r, ls, rs, hl, hr, heq, rfl⟩ := hx.succ_inv
      -- peel the LAST sibling: it is the TOP level of the tree
      obtain ⟨init, s, rfl⟩ : ∃ (init : List α) (s : α), sibs = init ++ [s] := by
        rcases List.eq_nil_or_concat sibs with rfl | ⟨init, s, rfl⟩
        · simp at hlen
        · exact ⟨init, s, List.concat_eq_append⟩
      have hinit : init.length = d := by
        rw [List.length_append, List.length_singleton] at hlen; omega
      rw [merkleRecO_concat H s init i v, hinit] at hrec
      by_cases hp : pnode (i / 2 ^ d) (merkleRecO H i v init) s = (l, r)
      · -- the top node agrees; descend into the correct half
        have hlsLen : ls.length = 2 ^ d := hl.length_eq
        have hpow : 0 < 2 ^ d := pow_pos (by norm_num) d
        have hlow : i % 2 ^ d < 2 ^ d := Nat.mod_lt _ hpow
        have hb2 : i / 2 ^ d % 2 = 0 ∨ i / 2 ^ d % 2 = 1 := by omega
        rcases hb2 with hbit | hbit
        · -- LEFT half: side bit `0`, so the recompute bottoms out at `l`
          rw [pnode_even hbit] at hp
          have hAl : merkleRecO H i v init = l := congrArg Prod.fst hp
          have hidx : i % 2 ^ (d + 1) = i % 2 ^ d := by
            rw [nat_mod_pow_succ, hbit]; ring
          have hget : (ls ++ rs).getD (i % 2 ^ (d + 1)) dflt = ls.getD (i % 2 ^ d) dflt := by
            rw [hidx]
            exact getD_append_left ls rs _ dflt (by rw [hlsLen]; exact hlow)
          rw [hget]
          exact ih l ls hl i v init hinit hAl dflt
        · -- RIGHT half: side bit `1`, so the recompute bottoms out at `r`
          rw [pnode_odd hbit] at hp
          have hAr : merkleRecO H i v init = r := congrArg Prod.snd hp
          have hidx : i % 2 ^ (d + 1) = ls.length + i % 2 ^ d := by
            rw [nat_mod_pow_succ, hbit, hlsLen]; ring
          have hget : (ls ++ rs).getD (i % 2 ^ (d + 1)) dflt = rs.getD (i % 2 ^ d) dflt := by
            rw [hidx]
            exact getD_append_right ls rs _ dflt
          rw [hget]
          exact ih r rs hr i v init hinit hAr dflt
      · -- the top node DISAGREES: two distinct preimages of `root` — a collision
        right
        exact ⟨pnode (i / 2 ^ d) (merkleRecO H i v init) s, (l, r), hp, hrec.trans heq.symm⟩

/-- **⚑ THE BUNDLED (a)-PAYOFF OVER A REAL QUERY LOG.** On any run whose log yields an extraction at
`root`, the extracted list IS a total column on `Fin (2^d)`'s worth of positions — `2^d` entries,
every interior node a genuine `H`-application — and every opening the deployed verifier accepts
reads back one of its entries, unless `H` collides. No hypothesis beyond "the extraction succeeded":
faithfulness comes free from the log.

(The `getD`-with-default reading is EXACTLY the shape `FriColumnDecode.decodeColumn` consumes —
that decoder is `fun i => ((col.getD i 0 : Int) : BabyBear)` — so the object produced here is the
one `ColumnDecodeBridge.column` names, modulo the leaf-digest layer (a1).) -/
theorem log_column_total_and_binds {A : Type} (M : OracleComp (α × α) α A) (H : α × α → α)
    (d : ℕ) (root : α) (xs : List α) (dflt : α)
    (hex : treeExtract (M.log H) d root = some xs) :
    xs.length = 2 ^ d
      ∧ IsTree H d root xs
      ∧ (∀ (i : ℕ) (v : α) (sibs : List α), sibs.length = d →
          merkleRecO H i v sibs = root → xs.getD (i % 2 ^ d) dflt = v ∨ HasCollision H) := by
  have htree : IsTree H d root xs := treeExtract_log_isTree M H d root xs hex
  exact ⟨htree.length_eq, htree,
    fun i v sibs hlen hrec => isTree_opening_agrees d root xs htree i v sibs hlen hrec dflt⟩

end Extractor

/-! ## §4 — THE ε: extraction failure against a `Q`-BOUNDED adversary.

The extractor fails at an interior node exactly when the adversary published a node value it never
obtained from the oracle. Conditioned on EVERYTHING the adversary learned — the cylinder over its
own `queriedFinset`, whose card is `≤ Q` — that value is a FRESH coordinate, so it matches the
published root with probability exactly `1/|α|` (`RomCounting.condProb_fresh_eq`). No independence
is assumed anywhere: this is one adversary against one shared oracle. -/

section Epsilon

variable {α : Type} [Fintype α] [DecidableEq α]

/-- **THE FRESH-HIT EVENT.** The adversary outputs a claimed interior node `(u, z)`: a preimage `u`
and the value `z` it publishes for it. The event is "the verifier's recompute at that node succeeds
(`H u = z`) although `u` is NOT in the adversary's own query set" — precisely the case in which the
straight-line extractor has nothing to read. -/
def freshHit (M : OracleComp (α × α) α ((α × α) × α)) (H : α × α → α) : Bool :=
  decide (H (M.eval H).1 = (M.eval H).2) && decide ((M.eval H).1 ∉ queriedFinset M H)

/-- Inside the cylinder over its OWN query set, a computation's output and query set are CONSTANT —
it cannot tell those oracles apart (`RomOracle.eval_congr_of_agree_on_queried`). This is what lets
the fresh-coordinate lemma see a FIXED target. -/
theorem eval_const_on_own_cylinder {A : Type} (M : OracleComp (α × α) α A) (σ H : α × α → α)
    (hH : H ∈ cyl (queriedFinset M σ) σ) :
    M.eval H = M.eval σ ∧ queriedFinset M H = queriedFinset M σ := by
  have hag : ∀ d ∈ M.queried σ, σ d = H d := by
    intro d hd
    exact ((mem_cyl.1 hH) d ((mem_queriedFinset_iff M σ d).2 hd)).symm
  obtain ⟨hev, hq⟩ := M.eval_congr_of_agree_on_queried σ H hag
  refine ⟨hev.symm, ?_⟩
  unfold queriedFinset
  rw [hq]

/-- **⚑ THE ε — AGAINST ANY `Q`-QUERY ADVERSARY, WITH AN EXPLICIT VALUE.** Conditioned on the whole
of what a `Q`-query adversary learned (`|queriedFinset| ≤ Q` by `queriedFinset_card_le`), the
probability that its published node value is `H` of a preimage it never queried — i.e. the
probability the straight-line extractor has nothing to read at that node — is at most `1/|α|`.

Quantified over ADVERSARIES, not over words; the bound is a number, not a shape. -/
theorem freshHit_prob_le (M : OracleComp (α × α) α ((α × α) × α)) (σ : α × α → α) :
    condProb (cyl (queriedFinset M σ) σ) (freshHit M) ≤ 1 / (Fintype.card α : ℝ) := by
  by_cases hu : (M.eval σ).1 ∈ queriedFinset M σ
  · -- the node WAS queried: the event is impossible, not merely improbable
    refine le_of_eq_of_le (condProb_eq_zero (fun H hH => ?_)) (by positivity)
    obtain ⟨hev, hq⟩ := eval_const_on_own_cylinder M σ H hH
    unfold freshHit
    rw [hev, hq]
    simp [hu]
  · -- the node was NOT queried: a fresh coordinate hitting a FIXED target
    have hcongr : condProb (cyl (queriedFinset M σ) σ) (freshHit M)
        = condProb (cyl (queriedFinset M σ) σ)
            (fun H => decide (H (M.eval σ).1 = (M.eval σ).2)) := by
      refine condProb_congr (fun H hH => ?_)
      obtain ⟨hev, hq⟩ := eval_const_on_own_cylinder M σ H hH
      unfold freshHit
      rw [hev, hq]
      simp [hu]
    rw [hcongr]
    exact le_of_eq (condProb_fresh_eq (queriedFinset M σ) σ (M.eval σ).1 hu (M.eval σ).2)

/-- **THE BOUND IS EXACT — extraction failure is not a slack term.** When the published node really
was never queried, the fresh-hit probability is EQUAL to `1/|α|`. There is therefore no route to a
deterministic extraction theorem by sharpening the analysis: the failure event has strictly positive
probability at every finite `|α|`. -/
theorem freshHit_prob_eq_of_fresh (M : OracleComp (α × α) α ((α × α) × α)) (σ : α × α → α)
    (hu : (M.eval σ).1 ∉ queriedFinset M σ) :
    condProb (cyl (queriedFinset M σ) σ) (freshHit M) = 1 / (Fintype.card α : ℝ) := by
  have hcongr : condProb (cyl (queriedFinset M σ) σ) (freshHit M)
      = condProb (cyl (queriedFinset M σ) σ)
          (fun H => decide (H (M.eval σ).1 = (M.eval σ).2)) := by
    refine condProb_congr (fun H hH => ?_)
    obtain ⟨hev, hq⟩ := eval_const_on_own_cylinder M σ H hH
    unfold freshHit
    rw [hev, hq]
    simp [hu]
  rw [hcongr, condProb_fresh_eq (queriedFinset M σ) σ (M.eval σ).1 hu (M.eval σ).2]

/-- **THE `n`-NODE UNION BOUND, as pure counting.** For any fixed list of `n` claimed
`(preimage, value)` nodes, the chance that ANY of them is a fresh hit against a conditioning set `S`
is at most `n/|α|`. Built from `RomCounting.condProb_fresh_eq` and `FriVerifierFS.condProb_or_le` —
a REAL union bound over ONE shared oracle, no independence assumed. -/
theorem condProb_anyFresh_le (S : Finset (α × α)) (σ : α × α → α) :
    ∀ ps : List ((α × α) × α),
      condProb (cyl S σ) (fun H => ps.any (fun p => decide (H p.1 = p.2) && decide (p.1 ∉ S)))
        ≤ (ps.length : ℝ) / (Fintype.card α : ℝ) := by
  intro ps
  induction ps with
  | nil =>
      rw [condProb_eq_zero (fun H _ => by simp)]
      simp
  | cons p ps ih =>
      have hstep : condProb (cyl S σ)
          (fun H => (decide (H p.1 = p.2) && decide (p.1 ∉ S))
              || ps.any (fun q => decide (H q.1 = q.2) && decide (q.1 ∉ S)))
          ≤ condProb (cyl S σ) (fun H => decide (H p.1 = p.2) && decide (p.1 ∉ S))
            + condProb (cyl S σ)
                (fun H => ps.any (fun q => decide (H q.1 = q.2) && decide (q.1 ∉ S))) :=
        condProb_or_le _ _ _
      have hhead : condProb (cyl S σ) (fun H => decide (H p.1 = p.2) && decide (p.1 ∉ S))
          ≤ 1 / (Fintype.card α : ℝ) := by
        by_cases hp : p.1 ∈ S
        · refine le_of_eq_of_le (condProb_eq_zero (fun H _ => by simp [hp])) (by positivity)
        · refine le_of_eq ?_
          rw [condProb_congr (win' := fun H => decide (H p.1 = p.2)) (fun H _ => by simp [hp])]
          exact condProb_fresh_eq S σ p.1 hp p.2
      have hrw : (fun H : α × α → α =>
          (p :: ps).any (fun q => decide (H q.1 = q.2) && decide (q.1 ∉ S)))
          = (fun H : α × α → α => (decide (H p.1 = p.2) && decide (p.1 ∉ S))
              || ps.any (fun q => decide (H q.1 = q.2) && decide (q.1 ∉ S))) := by
        funext H; simp [List.any_cons]
      rw [hrw]
      refine hstep.trans ?_
      have : (1 : ℝ) / (Fintype.card α : ℝ) + (ps.length : ℝ) / (Fintype.card α : ℝ)
          = ((p :: ps).length : ℝ) / (Fintype.card α : ℝ) := by
        rw [List.length_cons]; push_cast; ring
      linarith [hhead, ih]

/-- **⚑ THE DEPLOYED NUMBER — for the FORGERY failure mode only.** At the shipped BabyBear node
oracle (`|α| = |F| = 2013265921`, `FriVerifierMerkle.sponge_pair_oracle_bridge`'s width-pinned
sponge), a depth-`d` column has `2^d − 1` interior nodes, so the probability that a `Q`-query
adversary's published tree contains ANY node it VERIFIED-BUT-NEVER-QUERIED (a forged hash the
straight-line extractor cannot read) is at most `(2^d − 1)/2013265921`.

⚑ READ THIS HONESTLY, TWO WAYS.
  * The number is NOT a cryptographic margin. At a shipped `logN = 21` it is
    `2097151/2013265921 ≈ 2^-9.9`. That is the union bound over every interior node of a tree the
    verifier only ever spot-checks `k` paths of.
  * More important: this ε bounds ONLY the forgery mode (guess a hash without querying,
    `no_deterministic_extraction`'s witness). It does NOT bound the mode of
    `partial_commitment_verifies_but_no_total_column`, which is DETERMINISTIC — the prover leaves a
    subtree un-hashed, pays no `1/|α|`, and still passes every opening that avoids it. That mode
    has NO ε at all here; its cost is `(1 − μ)^k` in the spot-check parameter — sub-seam (b),
    `FriQuerySamplingBias.epsQueryBias`'s exponent. So the total column is not obtainable by
    bounding this term; the finding stands. -/
theorem deployed_freshHit_prob_le (hcard : Fintype.card α = 2013265921)
    (S : Finset (α × α)) (σ : α × α → α) (ps : List ((α × α) × α)) (d : ℕ)
    (hps : ps.length = 2 ^ d - 1) :
    condProb (cyl S σ) (fun H => ps.any (fun p => decide (H p.1 = p.2) && decide (p.1 ∉ S)))
      ≤ ((2 ^ d - 1 : ℕ) : ℝ) / (2013265921 : ℝ) := by
  have h := condProb_anyFresh_le S σ ps
  rw [hps, hcard] at h
  exact h

end Epsilon

/-! ## §5 — ⚑ THE REFUTATIONS. Two, of increasing force. -/

section Refutation

/-- A `QueryBounded 0` adversary over `α = Bool` that simply GUESSES: it publishes the interior node
`(true, true)` with value `false`, having queried nothing. -/
def guesser : OracleComp (Bool × Bool) Bool ((Bool × Bool) × Bool) :=
  .pure ((true, true), false)

theorem guesser_bounded : QueryBounded 0 guesser := QueryBounded.pure 0 _

/-- The guesser's log is EMPTY and yet, against the constant-`false` oracle, its published node
check PASSES. -/
theorem guesser_verifies_with_empty_log :
    (fun _ => false : Bool × Bool → Bool) (guesser.eval (fun _ => false)).1
        = (guesser.eval (fun _ => false)).2
      ∧ guesser.log (fun _ => false) = [] := ⟨rfl, rfl⟩

/-- **⚑ REFUTATION 1 — DETERMINISTIC EXTRACTION IS IMPOSSIBLE.** There is no theorem of the shape
"the published node's oracle check passes ⟹ the straight-line extractor recovers its subtree",
not even for a ZERO-query adversary. The witness is `guesser` against the constant oracle: the check
passes, the log is empty, and `treeExtract` returns `none` at depth `1`.

So the honest form of sub-seam (a) is necessarily the §4 PROBABILITY, whose value
(`freshHit_prob_eq_of_fresh`) is exactly `1/|α|` — positive at every finite `|α|`. This is the same
species of claim as "every accepting proof yields a codeword": false by counting, and the fix is an
ε, not a sharper proof. -/
theorem no_deterministic_extraction :
    ¬ (∀ (M : OracleComp (Bool × Bool) Bool ((Bool × Bool) × Bool)) (H : Bool × Bool → Bool),
        QueryBounded 0 M → H (M.eval H).1 = (M.eval H).2 →
        (treeExtract (M.log H) 1 (M.eval H).2).isSome = true) := by
  intro h
  have := h guesser (fun _ => false) guesser_bounded rfl
  simp [treeExtract, guesser, OracleComp.log, OracleComp.eval] at this

section Partial

variable {α : Type} [DecidableEq α]

/-- **THE PARTIAL-COMMITMENT ADVERSARY.** It hashes the RIGHT half honestly (`(x2, x3) ↦ n1`) but
INVENTS the left interior node `w` out of thin air — it never queries below `w` — and hashes upward
to a root. Exactly `2` queries. This is what a Merkle prover is actually free to do: a root commits
only to the part of the tree the prover HASHED. -/
def partialCommit (x2 x3 w : α) : OracleComp (α × α) α (α × α) :=
  .query (x2, x3) (fun n1 => .query (w, n1) (fun root => .pure (n1, root)))

theorem partialCommit_bounded (x2 x3 w : α) : QueryBounded 2 (partialCommit x2 x3 w) :=
  QueryBounded.query 1 _ _ (fun _ => QueryBounded.query 0 _ _ (fun _ => QueryBounded.pure 0 _))

/-- Its COMPLETE query log: two pairs, both faithful. Nothing is hidden from the extractor. -/
theorem partialCommit_log (H : α × α → α) (x2 x3 w : α) :
    (partialCommit x2 x3 w).log H
      = [((x2, x3), H (x2, x3)), ((w, H (x2, x3)), H (w, H (x2, x3)))] := rfl

/-- **⚑⚑ REFUTATION 2 — MERKLE BINDING DOES NOT YIELD A COMMITTED TOTAL COLUMN.**

For EVERY node oracle `H` and every `x2 x3 w` in general position (the three disequalities below,
each of which fails only on an `O(1/|α|)` slice of oracles), the `QueryBounded 2` partial-commitment
adversary simultaneously:

  * carries an authenticated opening at leaf index `2` that the DEPLOYED verifier check accepts —
    `merkleRecO H 2 x2 [x3, w] = root`, deployed sibling order, deployed `pnode` index bits; and
  * admits NO depth-`2` total column from its COMPLETE query log: `treeExtract … = none`.

It pays no `1/|α|`: the opening verifies for EVERY oracle agreeing with those two logged answers.
It exhibits no collision: `H` may be injective. It is not a knowledge-extraction failure that a
better extractor could repair — the information simply is not there, because the prover never
computed it.

⚑ THEREFORE sub-seam (a) as stated in `FriColumnDecode`'s docstring is not closable as stated. A
Merkle commitment gives POSITIONAL binding at OPENED positions (`merkleRecompute_binds`,
`findCollisionZ_none_binds` — both true, both proved), and positional binding is not a function.
The gap between "the `k` openings the verifier checked" and `ColumnDecodeBridge.accept_chains`'s
"at EVERY domain position" is not extraction: it is the spot-check gap of sub-seam (b), with the
same `(1 − μ)^k` shape. (a) reduces to (b); it does not precede it. -/
theorem partial_commitment_verifies_but_no_total_column
    (H : α × α → α) (x2 x3 w : α)
    (h1 : H (x2, x3) ≠ w)
    (h2 : H (w, H (x2, x3)) ≠ w)
    (h3 : H (x2, x3) ≠ H (w, H (x2, x3))) :
    merkleRecO H 2 x2 [x3, w] = H (w, H (x2, x3))
      ∧ treeExtract ((partialCommit x2 x3 w).log H) 2 (H (w, H (x2, x3))) = none := by
  constructor
  · show merkleRecO H 2 x2 [x3, w] = H (w, H (x2, x3))
    rw [merkleRecO_cons, merkleRecO_cons, merkleRecO_nil]
    rw [show pnode 2 x2 x3 = (x2, x3) from by simp [pnode]]
    rw [show pnode 1 (H (x2, x3)) w = (w, H (x2, x3)) from by simp [pnode]]
  · rw [partialCommit_log, treeExtract_succ]
    -- the top node IS in the log (the adversary really hashed it) …
    rw [show ([((x2, x3), H (x2, x3)), ((w, H (x2, x3)), H (w, H (x2, x3)))] :
          List ((α × α) × α)).find?
            (fun e => decide (e.2 = H (w, H (x2, x3))))
          = some ((w, H (x2, x3)), H (w, H (x2, x3))) from by
      simp [List.find?, h3]]
    -- … but its LEFT child `w` is not: the prover invented it, so extraction dies there.
    simp only [Option.bind_some]
    rw [show treeExtract ([((x2, x3), H (x2, x3)), ((w, H (x2, x3)), H (w, H (x2, x3)))] :
          List ((α × α) × α)) 1 w = none from by
      rw [treeExtract_succ]
      rw [show ([((x2, x3), H (x2, x3)), ((w, H (x2, x3)), H (w, H (x2, x3)))] :
            List ((α × α) × α)).find? (fun e => decide (e.2 = w)) = none from by
        simp [List.find?, h1, h2]]
      rfl]
    rfl

end Partial

end Refutation

/-! ## §6 — The honest verdict, in Lean vocabulary.

`log_column_total_and_binds` is what extraction DELIVERS: on the hashed part, the committed column
is total, unique-up-to-collision, and forced to agree with every accepted opening. That is a real
discharge of the algebraic content of sub-seam (a).

`partial_commitment_verifies_but_no_total_column` is what it does NOT deliver, and cannot: the
hashed part need not be the whole tree, and acceptance does not make it so.

`freshHit_prob_le` / `deployed_freshHit_prob_le` price the one failure mode that IS probabilistic
(a published node with no preimage in the log) at `1/|α|` per node — exactly, not slackly
(`freshHit_prob_eq_of_fresh`).

What is NOT priced here, and is now the named residual of (a): the un-hashed remainder. Its cost is
`(1 − μ)^k` in the spot-check parameter, i.e. it belongs to sub-seam (b) and to
`FriQuerySamplingBias.epsQueryBias`'s exponent — NOT to a Merkle-binding argument. -/

#assert_all_clean [
  nat_mod_pow_succ,
  merkleRecO_nil,
  pnode_even,
  pnode_odd,
  getD_append_left,
  getD_append_right,
  merkleRecO_concat,
  IsTree.zero_inv,
  IsTree.succ_inv,
  IsTree.length_eq,
  treeExtract_zero,
  treeExtract_succ,
  treeExtractComp_queryBounded,
  treeExtract_isTree,
  treeExtract_log_isTree,
  extractor_reads_at_most_Q,
  isTree_unique_or_collision,
  isTree_opening_agrees,
  log_column_total_and_binds,
  eval_const_on_own_cylinder,
  freshHit_prob_le,
  freshHit_prob_eq_of_fresh,
  condProb_anyFresh_le,
  deployed_freshHit_prob_le,
  guesser_bounded,
  guesser_verifies_with_empty_log,
  no_deterministic_extraction,
  partialCommit_bounded,
  partialCommit_log,
  partial_commitment_verifies_but_no_total_column
]

end Dregg2.Circuit.FriColumnLogExtract
