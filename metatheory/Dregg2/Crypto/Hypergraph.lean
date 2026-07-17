/-
# Dregg2.Crypto.Hypergraph — arbitrary hypergraph reductions as ZK-checkable certificates.

The generic chain-certificate machinery (`chain`/`Cert`/`bridge`/`Cert.map`/`Cert.foldSound`) lives in
the LEAF module `Crypto/Chain.lean` (in this namespace — `Hypergraph.chain` etc.). This file holds two
INSTANCES of that one bridge: for ANY reduction relation `R : α → α → Prop`, a locally-checkable CHAIN
certificate `[start, …, goal]` exists IFF `start` reduces to `goal` in `ReflTransGen R`.

Instantiating `R` at a hyperedge-replacement relation on HYPERGRAPHS gives
`hypergraph_reduction_bridge` — a ZK-checkable certificate for arbitrary hypergraph reductions (hyperedge
replacement is the hypergraph generalization of a context-free rewrite). Instantiating the SAME bridge at
a grammar's `Produces` recovers CFG parsing (`cfg_parse_via_reduction`): context-free parsing is the
linear/string instance of hypergraph reduction. One verified certificate framework covers both —
`Crypto/Cfg.cfg_bridge` is now literally an alias of `cfg_parse_via_reduction`, not a second induction.

    bridge                      : (∃ c, Cert R start goal c) ↔ ReflTransGen R start goal   (Chain.lean)
    hypergraph_reduction_bridge : … instantiated at hyperedge replacement
    cfg_parse_via_reduction     : … instantiated at `g.Produces` ⇒ `input ∈ g.language`
-/
import Mathlib.Computability.ContextFreeGrammar
import Dregg2.Crypto.Chain
import Dregg2.Tactics

namespace Dregg2.Crypto.Hypergraph

open ContextFreeGrammar

universe u v

/-! ## Hypergraphs + hyperedge-replacement reduction.

(The generic `chain`/`Cert`/`bridge` these instances consume are defined in `Crypto/Chain.lean`,
in this same namespace.) -/

/-- A hyperedge: a `label` together with its ordered attachment `nodes`. -/
abbrev Hyperedge (L V : Type) := L × List V

/-- A hypergraph: a list of hyperedges over a shared node set. -/
structure Hypergraph (L V : Type) where
  /-- The hyperedges. -/
  edges : List (Hyperedge L V)
  deriving Repr

/-- **`Reduces rule g g'`** — one hyperedge-replacement step: an edge `e` occurring in edge-context
`pre`/`post` is replaced by the edges `rhs`, where `rule e rhs` licenses the replacement. This IS the
hyperedge-replacement operation — the hypergraph generalization of a context-free rewrite (a context-free
rewrite is the special case where every hyperedge is a length-2 "string" edge). -/
inductive Reduces {L V : Type} (rule : Hyperedge L V → List (Hyperedge L V) → Prop) :
    Hypergraph L V → Hypergraph L V → Prop where
  /-- Replace edge `e` (between contexts `pre`, `post`) by `rhs`, licensed by `rule`. -/
  | replace (pre post : List (Hyperedge L V)) (e : Hyperedge L V) (rhs : List (Hyperedge L V))
      (h : rule e rhs) :
      Reduces rule ⟨pre ++ e :: post⟩ ⟨pre ++ rhs ++ post⟩

/-- **`hypergraph_reduction_bridge`** — the generic bridge INSTANTIATED at hypergraph reduction: a
reduction certificate (a chain of hypergraphs, each obtained from the previous by ONE hyperedge
replacement) from `g` to `g'` exists IFF `g` reduces to `g'` in the reflexive-transitive reduction
relation. A ZK-checkable proof of an ARBITRARY hypergraph reduction — the same certificate machinery
`Crypto/Cfg` uses for parse certificates. -/
theorem hypergraph_reduction_bridge {L V : Type}
    (rule : Hyperedge L V → List (Hyperedge L V) → Prop) (g g' : Hypergraph L V) :
    (∃ c, Cert (Reduces rule) g g' c) ↔ Relation.ReflTransGen (Reduces rule) g g' :=
  bridge (Reduces rule) g g'

/-- **`cfg_parse_via_reduction`** — the SAME generic bridge INSTANTIATED at a grammar's `Produces`
recovers context-free parsing: a `Produces`-chain from the start symbol to the input word exists IFF the
input is in the grammar's language. So CFG parsing is the linear/string instance of hypergraph reduction:
one verified reduction-certificate framework certifies both. -/
theorem cfg_parse_via_reduction {T : Type} (g : ContextFreeGrammar T) (input : List T) :
    (∃ c, Cert g.Produces [Symbol.nonterminal g.initial] (input.map Symbol.terminal) c)
      ↔ input ∈ g.language := by
  rw [mem_language_iff]
  exact bridge g.Produces _ _

#assert_axioms hypergraph_reduction_bridge
#assert_axioms cfg_parse_via_reduction

/-! ## Non-vacuity — a concrete hypergraph reduction, certified. -/

namespace Reference

/-- Edge labels: a "nonterminal" `A` and two "terminals" `B`, `C`. -/
inductive Lbl | A | B | C
  deriving DecidableEq, Repr

open Lbl

/-- The split rule `A[x,y] ↝ { B[x,y], C[x,y] }`: replace an `A`-edge by a `B`-edge and a `C`-edge on the
same two attachment nodes. A genuine hyperedge replacement. -/
def splitRule : Hyperedge Lbl Nat → List (Hyperedge Lbl Nat) → Prop :=
  fun e rhs => ∃ x y, e = (A, [x, y]) ∧ rhs = [(B, [x, y]), (C, [x, y])]

/-- The one-step reduction certificate `⟨[A 0 1]⟩ ↝ ⟨[B 0 1, C 0 1]⟩`. -/
def redChain : List (Hypergraph Lbl Nat) :=
  [ ⟨[(A, [0, 1])]⟩, ⟨[(B, [0, 1]), (C, [0, 1])]⟩ ]

/-- The certificate is valid: the single step is a genuine `splitRule` hyperedge replacement. -/
theorem red_cert :
    Cert (Reduces splitRule) ⟨[(A, [0, 1])]⟩ ⟨[(B, [0, 1]), (C, [0, 1])]⟩ redChain := by
  refine ⟨rfl, rfl, ?_, trivial⟩
  have h : Reduces splitRule ⟨[] ++ (A, [0, 1]) :: []⟩ ⟨[] ++ [(B, [0, 1]), (C, [0, 1])] ++ []⟩ :=
    Reduces.replace [] [] (A, [0, 1]) [(B, [0, 1]), (C, [0, 1])] ⟨0, 1, rfl, rfl⟩
  simpa using h

/-- **`red_reduces`** — via the bridge, the certificate proves the genuine reflexive-transitive reduction
`⟨[A 0 1]⟩ ↝* ⟨[B 0 1, C 0 1]⟩`. A concrete arbitrary-hypergraph-reduction proof from a checkable chain. -/
theorem red_reduces :
    Relation.ReflTransGen (Reduces splitRule) ⟨[(A, [0, 1])]⟩ ⟨[(B, [0, 1]), (C, [0, 1])]⟩ :=
  (hypergraph_reduction_bridge splitRule _ _).mp ⟨redChain, red_cert⟩

end Reference

end Dregg2.Crypto.Hypergraph
