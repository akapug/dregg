/-
# Dregg2.Crypto.GraphRewrite — match-driven contextual hyperedge replacement.

`Crypto/Hypergraph` reduces hypergraphs by POSITIONAL edge splicing (`⟨pre ++ e :: post⟩ ↝ ⟨pre ++ rhs ++
post⟩`). That is enough to bridge to the generic reduction certificate, but it has no genuine **match**
(an occurrence of a pattern anywhere in a host graph, up to node identification), and the pattern is a
single edge in a fixed position.

This module adds match-driven contextual replacement over arbitrary node/label carriers `V`/`L
(`UInt8` is the concrete example below):

  * **matching** — `IsHom f pat host` (a node map sending every pattern edge to a host edge) and the
    relations `Matches`/`Embeds` (a homomorphism / an injective homomorphism = subgraph embedding). This
    is graph pattern matching / subgraph isomorphism as a first-class relation.
  * **rewrite rules** — `Rule Var L` = a pair of pattern graphs `lhs`/`rhs` over pattern variables `Var`;
  * **rewrite steps** — `RewriteStep rules G H`: there is a rule, a MATCH `σ : Var → V` (embedding the
    pattern `lhs` into `G`), and a preserved CONTEXT, such that `H` replaces the matched `lhs` by the
    instantiated `rhs`: match, delete the matched pattern, glue in the replacement, and keep the
    context (`G.edges ~ ctx ++ σ·lhs`, `H.edges = ctx ++ σ·rhs`).

Feeding `RewriteStep rules` to the generic `Hypergraph.bridge` yields checkable certificates for finite
derivations (`graphRewrite_bridge`), and `step_matches` shows every rewrite step is witnessed by a
genuine graph matching. This is the reusable relation-level substrate beneath a bounded circuit
instance; it does not by itself impose DPO freshness/dangling conditions or prove a circuit encoding.
-/
import Dregg2.Crypto.Hypergraph
import Dregg2.Tactics

namespace Dregg2.Crypto.GraphRewrite

open Dregg2.Crypto.Hypergraph

universe u

/-! ## Graph matching — homomorphisms and embeddings of a pattern into a host. -/

/-- Apply a node map to a hyperedge (relabel its attachment nodes). -/
def mapEdge {Vp Vh L : Type} (f : Vp → Vh) (e : Hyperedge L Vp) : Hyperedge L Vh :=
  (e.1, e.2.map f)

/-- **`IsHom f pat host`** — `f` is a hypergraph homomorphism: every edge of the pattern `pat` maps
(under `f` on nodes, label preserved) to an edge of `host`. This is a MATCH of `pat` into `host`. -/
def IsHom {Vp Vh L : Type} (f : Vp → Vh) (pat : Hypergraph L Vp) (host : Hypergraph L Vh) : Prop :=
  ∀ e ∈ pat.edges, mapEdge f e ∈ host.edges

/-- **`Matches pat host`** — `pat` occurs in `host`: some homomorphism embeds it (graph pattern match). -/
def Matches {Vp Vh L : Type} (pat : Hypergraph L Vp) (host : Hypergraph L Vh) : Prop :=
  ∃ f, IsHom f pat host

/-- **`Embeds pat host`** — an INJECTIVE match: a subgraph embedding (distinct pattern nodes stay
distinct), i.e. subgraph isomorphism onto its image. -/
def Embeds {Vp Vh L : Type} (pat : Hypergraph L Vp) (host : Hypergraph L Vh) : Prop :=
  ∃ f, IsHom f pat host ∧ Function.Injective f

theorem embeds_matches {Vp Vh L : Type} {pat : Hypergraph L Vp} {host : Hypergraph L Vh}
    (h : Embeds pat host) : Matches pat host :=
  ⟨h.choose, h.choose_spec.1⟩

/-! ## Rewrite rules + match-driven contextual replacement. -/

/-- A rewrite rule: a left pattern and a right pattern over pattern variables `Var`. Shared variables
can serve as a preserved interface. This relation does not require RHS-only variables to be fresh;
that is a stronger, explicitly named follow-on condition for a DPO-capable instance. -/
structure Rule (Var L : Type) where
  /-- The pattern to match and delete. -/
  lhs : Hypergraph L Var
  /-- The replacement to glue in. -/
  rhs : Hypergraph L Var

/-- Instantiate a pattern's edges along a match `σ : Var → V`. -/
def instEdges {Var V L : Type} (σ : Var → V) (es : List (Hyperedge L Var)) : List (Hyperedge L V) :=
  es.map (mapEdge σ)

/-- **`RewriteStep rules G H`** — one contextual graph-rewrite step. There is a rule `r ∈ rules`, a
MATCH `σ : Var → V` mapping `r.lhs` into `G`, and a CONTEXT `ctx` of untouched edges, such that `G` is the
context together with the matched pattern (`G.edges ~ ctx ++ σ·lhs`, up to reordering — the pattern may
occur anywhere), and `H` replaces the matched pattern by the instantiated replacement while keeping the
context (`H.edges = ctx ++ σ·rhs`). Injectivity, RHS freshness, and the dangling condition are not
premises of this general relation. -/
inductive RewriteStep {Var V L : Type} (rules : List (Rule Var L)) :
    Hypergraph L V → Hypergraph L V → Prop where
  /-- Rewrite via rule `r`, match `σ`, preserved context `ctx`. -/
  | step (r : Rule Var L) (hr : r ∈ rules) (σ : Var → V) (ctx : List (Hyperedge L V))
      (G H : Hypergraph L V)
      (hG : G.edges.Perm (ctx ++ instEdges σ r.lhs.edges))
      (hH : H.edges = ctx ++ instEdges σ r.rhs.edges) :
      RewriteStep rules G H

/-- **`graphRewrite_bridge`** — the generic reduction bridge instantiated at contextual graph rewriting:
a checkable certificate (a chain of graphs, each obtained from the previous by ONE match-driven rewrite
step) from `G` to `G'` exists IFF `G` rewrites to `G'` in the reflexive-transitive rewrite relation.
Finite match-driven derivations, certified — the same machinery `Crypto/Cfg` uses for parses. -/
theorem graphRewrite_bridge {Var V L : Type} (rules : List (Rule Var L)) (G G' : Hypergraph L V) :
    (∃ c, Cert (RewriteStep rules) G G' c) ↔ Relation.ReflTransGen (RewriteStep rules) G G' :=
  bridge (RewriteStep rules) G G'

/-- **`step_matches`** — every rewrite step is witnessed by a genuine graph matching: if `G` rewrites via
rule `r` and match `σ`, then `r.lhs` MATCHES `G` (the instantiated pattern edges all occur in `G`). So
rewriting is inseparable from subgraph matching. -/
theorem step_matches {Var V L : Type} {rules : List (Rule Var L)} {r : Rule Var L}
    (hr : r ∈ rules) {σ : Var → V} {ctx : List (Hyperedge L V)} {G H : Hypergraph L V}
    (hG : G.edges.Perm (ctx ++ instEdges σ r.lhs.edges))
    (hH : H.edges = ctx ++ instEdges σ r.rhs.edges) :
    Matches r.lhs G := by
  refine ⟨σ, ?_⟩
  intro e he
  have : mapEdge σ e ∈ ctx ++ instEdges σ r.lhs.edges := by
    apply List.mem_append_right
    exact List.mem_map_of_mem he
  exact hG.mem_iff.mpr this

#assert_axioms graphRewrite_bridge
#assert_axioms step_matches

/-! ## Non-vacuity — a concrete graph MATCHING and a concrete rewrite derivation, over BYTES.

Everything is instantiated at `V := UInt8` (host nodes are bytes) and `L := UInt8` (edge labels are
bytes): arbitrary byte-labeled graphs. -/

namespace Reference

/-- A host byte-graph: two labelled edges `A:(10,11)` and `B:(11,12)` — a little labelled path over bytes. -/
def host : Hypergraph UInt8 UInt8 :=
  ⟨[(0x41, [10, 11]), (0x42, [11, 12])]⟩

/-- A pattern with variable nodes `0,1 : Nat`: a single `A`-edge `A:(x,y)`. -/
def patA : Hypergraph UInt8 Nat :=
  ⟨[(0x41, [0, 1])]⟩

/-- The matching substitution: pattern var `0 ↦ 10`, `1 ↦ 11` (and everything else to `0`). -/
def σA : Nat → UInt8 := fun n => if n = 0 then 10 else if n = 1 then 11 else 0

/-- **`patA_matches_host`** — the `A`-pattern MATCHES the host graph: `σA` embeds `A:(x,y)` onto the
host's `A:(10,11)` edge. A concrete graph matching over bytes. -/
theorem patA_matches_host : Matches patA host := by
  refine ⟨σA, ?_⟩
  intro e he
  simp only [patA, List.mem_singleton] at he
  subst he
  decide

/-- A split rule `A:(x,y) ⇒ { B:(x,y), C:(x,y) }` over byte labels (`A=0x41`, `B=0x42`, `C=0x43`). -/
def splitRule : Rule Nat UInt8 :=
  ⟨⟨[(0x41, [0, 1])]⟩, ⟨[(0x42, [0, 1]), (0x43, [0, 1])]⟩⟩

/-- The one-edge host to rewrite: just `A:(10,11)`. -/
def g0 : Hypergraph UInt8 UInt8 := ⟨[(0x41, [10, 11])]⟩

/-- After rewriting: `B:(10,11)` and `C:(10,11)` — the matched `A`-edge replaced. -/
def g1 : Hypergraph UInt8 UInt8 := ⟨[(0x42, [10, 11]), (0x43, [10, 11])]⟩

/-- **`g0_rewrites_g1`** — a genuine match-driven rewrite step over bytes: match `A:(x,y)` at `(10,11)`
via `σA`, empty context, replace by `B`+`C`. -/
theorem g0_rewrites_g1 : RewriteStep [splitRule] g0 g1 := by
  refine RewriteStep.step splitRule (by simp) σA [] g0 g1 ?_ ?_
  · -- g0.edges ~ [] ++ σA·lhs = [A:(10,11)]
    apply List.Perm.refl
  · -- g1.edges = [] ++ σA·rhs = [B:(10,11), C:(10,11)]
    rfl

/-- **`g0_reduces_g1`** — via the bridge, the one-step certificate proves the reflexive-transitive
graph-rewrite reduction `g0 ↝* g1`. A concrete contextual-rewrite proof from a checkable chain. -/
theorem g0_reduces_g1 : Relation.ReflTransGen (RewriteStep [splitRule]) g0 g1 :=
  (graphRewrite_bridge [splitRule] g0 g1).mp
    ⟨[g0, g1], rfl, rfl, g0_rewrites_g1, trivial⟩

end Reference

end Dregg2.Crypto.GraphRewrite
