/-
# Dregg2.Crypto.GraphRewriteHistory — root-linked receipts for semantic rewrite histories.

`Crypto.GraphRewrite` proves the semantic step relation: a licensed rule genuinely matches a host
graph, deletes its instantiated left-hand side, preserves a context, and glues its instantiated
right-hand side.  `Crypto.Chain` proves that a locally checkable `Cert R` chain is equivalent to the
reflexive-transitive closure of any relation `R`.

This file supplies the protocol bridge between those two facts and a public receipt stream.  A
`CertifiedStep` has a public statement `(session, rulesRoot, index, oldRoot, newRoot)` plus hidden
semantic openings `(oldGraph, newGraph)` and a sound `RewriteStep`.  Consecutive receipts must keep
the same session/rules root, increment the index exactly once, and connect `newRoot` to `oldRoot`.

The commitment boundary is deliberately not faked.  Equal graph roots imply equal semantic graphs
only under a supplied binding carrier (`Function.Injective commit` here, the idealized theorem shape
which a deployed hash instantiates computationally).  Without it, a root-linked semantic splice
extracts an explicit collision: two different graphs with the same commitment.  Under binding,
`linked_reduces` and `linked_has_cert` turn any nonempty receipt history into a genuine
`ReflTransGen (RewriteStep rules)` / `Hypergraph.Cert` from its first graph to its last.

This is independent of any particular AIR.  A bounded private graph-rewrite descriptor discharges
each receipt's `sound` field; the existing IVC segment chain carries the public roots.  The theorem
then supplies the semantic meaning of the folded history.
-/
import Dregg2.Crypto.GraphRewrite
import Dregg2.Tactics

namespace Dregg2.Crypto.GraphRewriteHistory

open Dregg2.Crypto.Hypergraph
open Dregg2.Crypto.GraphRewrite

/-- The public statement of one certified rewrite step.  `GraphRoot` is intended to be a faithful
eight-limb graph commitment and `RulesRoot` a faithful ruleset commitment; the theorem is agnostic
to their concrete encoding. -/
structure Statement (Session RulesRoot GraphRoot : Type) where
  session : Session
  rulesRoot : RulesRoot
  index : Nat
  oldRoot : GraphRoot
  newRoot : GraphRoot

/-- A public rewrite statement together with the hidden semantic openings and the proof meaning of
one accepted private leaf.  The graph values are witness-side data; only `stmt` is the receipt ABI. -/
structure CertifiedStep (Session RulesRoot : Type) {Var V L GraphRoot : Type}
    (rules : List (Rule Var L)) (commit : Hypergraph L V → GraphRoot) where
  stmt : Statement Session RulesRoot GraphRoot
  oldGraph : Hypergraph L V
  newGraph : Hypergraph L V
  oldRoot_binds : stmt.oldRoot = commit oldGraph
  newRoot_binds : stmt.newRoot = commit newGraph
  sound : RewriteStep rules oldGraph newGraph

namespace CertifiedStep

variable {Var V L Session RulesRoot GraphRoot : Type}
variable {rules : List (Rule Var L)} {commit : Hypergraph L V → GraphRoot}

/-- The public view of a certified step; witness graphs and the semantic proof do not cross the
receipt boundary. -/
def publicStatement (s : CertifiedStep Session RulesRoot rules commit) :
    Statement Session RulesRoot GraphRoot :=
  s.stmt

end CertifiedStep

/-- Two consecutive receipts form one protocol link exactly when they stay in one session and one
ruleset, advance by one index, and identify the preceding output root with the next input root. -/
structure Link {Var V L Session RulesRoot GraphRoot : Type}
    {rules : List (Rule Var L)} {commit : Hypergraph L V → GraphRoot}
    (a b : CertifiedStep Session RulesRoot rules commit) : Prop where
  sameSession : b.stmt.session = a.stmt.session
  sameRules : b.stmt.rulesRoot = a.stmt.rulesRoot
  nextIndex : b.stmt.index = a.stmt.index + 1
  roots : a.stmt.newRoot = b.stmt.oldRoot

/-- Consecutive-link validity for a receipt list.  This intentionally mirrors
`Hypergraph.chain`; the latter is recovered semantically by `linked_has_cert`. -/
def Linked {Var V L Session RulesRoot GraphRoot : Type}
    {rules : List (Rule Var L)} {commit : Hypergraph L V → GraphRoot} :
    List (CertifiedStep Session RulesRoot rules commit) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Link a b ∧ Linked (b :: rest)

/-- The semantic end graph of a nonempty history represented as its first step and remaining
steps. -/
def endGraph {Var V L Session RulesRoot GraphRoot : Type}
    {rules : List (Rule Var L)} {commit : Hypergraph L V → GraphRoot}
    (head : CertifiedStep Session RulesRoot rules commit) :
    List (CertifiedStep Session RulesRoot rules commit) → Hypergraph L V
  | [] => head.newGraph
  | next :: rest => endGraph next rest

section Refusals

variable {Var V L Session RulesRoot GraphRoot : Type}
variable {rules : List (Rule Var L)} {commit : Hypergraph L V → GraphRoot}
variable {a b : CertifiedStep Session RulesRoot rules commit}

/-- A ruleset substitution cannot be a valid link. -/
theorem wrong_rules_refused (h : b.stmt.rulesRoot ≠ a.stmt.rulesRoot) : ¬ Link a b :=
  fun hlink => h hlink.sameRules

/-- A cross-session splice cannot be a valid link. -/
theorem wrong_session_refused (h : b.stmt.session ≠ a.stmt.session) : ¬ Link a b :=
  fun hlink => h hlink.sameSession

/-- Reordering, replaying, or skipping a receipt cannot be a valid link: the next index is exact. -/
theorem wrong_index_refused (h : b.stmt.index ≠ a.stmt.index + 1) : ¬ Link a b :=
  fun hlink => h hlink.nextIndex

/-- A public endpoint splice with unequal roots cannot be a valid link. -/
theorem wrong_root_refused (h : a.stmt.newRoot ≠ b.stmt.oldRoot) : ¬ Link a b :=
  fun hlink => h hlink.roots

/-- **The honest hash boundary.**  If roots link but the hidden semantic endpoint graphs differ,
the two openings are an explicit collision in `commit`. -/
theorem hidden_splice_extracts_collision (hlink : Link a b)
    (hne : a.newGraph ≠ b.oldGraph) :
    a.newGraph ≠ b.oldGraph ∧ commit a.newGraph = commit b.oldGraph := by
  refine ⟨hne, ?_⟩
  calc
    commit a.newGraph = a.stmt.newRoot := a.newRoot_binds.symm
    _ = b.stmt.oldRoot := hlink.roots
    _ = commit b.oldGraph := b.oldRoot_binds

/-- Under the idealized binding carrier, a public root link identifies the two semantic endpoint
graphs.  A deployed sponge uses this lemma through its collision-resistance/extractability theorem,
not by claiming mathematical injectivity of a finite hash. -/
theorem linked_graph_eq (hcommit : Function.Injective commit) (hlink : Link a b) :
    a.newGraph = b.oldGraph := by
  apply hcommit
  calc
    commit a.newGraph = a.stmt.newRoot := a.newRoot_binds.symm
    _ = b.stmt.oldRoot := hlink.roots
    _ = commit b.oldGraph := b.oldRoot_binds

end Refusals

section HistorySoundness

variable {Var V L Session RulesRoot GraphRoot : Type}
variable {rules : List (Rule Var L)} {commit : Hypergraph L V → GraphRoot}

/-- **A root-linked certified history is a genuine semantic graph-rewrite reduction**, under the
explicit commitment-binding carrier.  Each receipt contributes one real `RewriteStep`; root
binding identifies adjacent hidden endpoint graphs; `ReflTransGen.head` composes the steps. -/
theorem linked_reduces (hcommit : Function.Injective commit) :
    ∀ (head : CertifiedStep Session RulesRoot rules commit)
      (rest : List (CertifiedStep Session RulesRoot rules commit)),
      Linked (head :: rest) →
      Relation.ReflTransGen (RewriteStep rules) head.oldGraph (endGraph head rest) := by
  intro head rest
  induction rest generalizing head with
  | nil =>
      intro _
      exact Relation.ReflTransGen.head head.sound Relation.ReflTransGen.refl
  | cons next rest ih =>
      intro hlinked
      have hpair : Link head next := hlinked.1
      have htail : Linked (next :: rest) := hlinked.2
      have hEq : head.newGraph = next.oldGraph := linked_graph_eq hcommit hpair
      have hrest := ih next htail
      have hsound := head.sound
      rw [hEq] at hsound
      exact Relation.ReflTransGen.head hsound hrest

/-- The same result in the repository's common certificate form: every valid root-linked receipt
history has a locally checkable `Hypergraph.Cert` chain for the semantic rewrite relation. -/
theorem linked_has_cert (hcommit : Function.Injective commit)
    (head : CertifiedStep Session RulesRoot rules commit)
    (rest : List (CertifiedStep Session RulesRoot rules commit))
    (hlinked : Linked (head :: rest)) :
    ∃ c, Cert (RewriteStep rules) head.oldGraph (endGraph head rest) c :=
  (bridge (RewriteStep rules) head.oldGraph (endGraph head rest)).mpr
    (linked_reduces hcommit head rest hlinked)

end HistorySoundness

/-! ## Non-vacuity — the byte-graph rewrite from `GraphRewrite.Reference` as a receipt history. -/

namespace Reference

open Dregg2.Crypto.GraphRewrite.Reference

/-- For the non-vacuity witness only, commit a graph to its complete edge list.  This is genuinely
injective and keeps the example free of a cryptographic assumption; deployed histories use a
faithful root plus the collision theorem above. -/
def edgeCommit (g : Hypergraph UInt8 UInt8) : List (Hyperedge UInt8 UInt8) := g.edges

theorem edgeCommit_injective : Function.Injective edgeCommit := by
  intro a b h
  cases a with
  | mk ae =>
      cases b with
      | mk be =>
          simp only [edgeCommit] at h
          subst h
          rfl

def refStmt : Statement Unit Nat (List (Hyperedge UInt8 UInt8)) where
  session := ()
  rulesRoot := 7
  index := 0
  oldRoot := edgeCommit g0
  newRoot := edgeCommit g1

def refStep : CertifiedStep Unit Nat [splitRule] edgeCommit where
  stmt := refStmt
  oldGraph := g0
  newGraph := g1
  oldRoot_binds := rfl
  newRoot_binds := rfl
  sound := g0_rewrites_g1

theorem reference_history_reduces :
    Relation.ReflTransGen (RewriteStep [splitRule]) g0 g1 := by
  simpa [refStep, endGraph] using
    linked_reduces edgeCommit_injective refStep [] (by trivial)

theorem reference_history_has_cert :
    ∃ c, Cert (RewriteStep [splitRule]) g0 g1 c := by
  simpa [refStep, endGraph] using
    linked_has_cert edgeCommit_injective refStep [] (by trivial)

end Reference

#assert_all_clean [
  wrong_rules_refused,
  wrong_session_refused,
  wrong_index_refused,
  wrong_root_refused,
  hidden_splice_extracts_collision,
  linked_graph_eq,
  linked_reduces,
  linked_has_cert,
  Reference.edgeCommit_injective,
  Reference.reference_history_reduces,
  Reference.reference_history_has_cert
]

end Dregg2.Crypto.GraphRewriteHistory
