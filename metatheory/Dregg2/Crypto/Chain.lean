/-
# Dregg2.Crypto.Chain — the LEAF chain-certificate module: `chain`/`Cert`/`bridge` for ANY relation.

The relation-parametric certificate substrate every instance file rides on: for ANY reduction relation
`R : α → α → Prop`, a locally-checkable CHAIN certificate `[start, …, goal]` (consecutive elements
related by one `R`-step) exists IFF `start` reduces to `goal` in the reflexive-transitive closure
`ReflTransGen R`. The prover exhibits the chain, the verifier checks each step, and `bridge` certifies
the whole reduction.

This module is a LEAF (Mathlib + `Dregg2.Tactics` only) so BOTH the generic instances
(`Crypto/Hypergraph`: hyperedge replacement, `cfg_parse_via_reduction`) AND the per-language modules
(`Crypto/Cfg.producesChain := chain g.Produces`, `Crypto/Dfa.chained := chain delta`) sit ABOVE it —
no instance re-proves the bridge. The declarations live in the `Dregg2.Crypto.Hypergraph` namespace
(their historical home) so every downstream reference (`Hypergraph.chain`, `Hypergraph.Cert`,
`Hypergraph.bridge`, `Hypergraph.Cert.foldSound`, …) resolves unchanged.

    bridge        : (∃ c, Cert R start goal c) ↔ ReflTransGen R start goal   (ANY R)
    Cert.map      : certificates are functorial along relation-preserving maps
    Cert.foldSound: the generic "walk the chain, accumulate output, carry a semantic invariant"
-/
import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic
import Dregg2.Tactics

namespace Dregg2.Crypto.Hypergraph

universe u v

section Generic

variable {α : Type u}

/-- **`chain R c`** — every consecutive pair of the sequence `c` is one `R`-reduction step. The generic
`producesChain`: the locally-checkable heart of a reduction certificate. -/
def chain (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => R a b ∧ chain R (b :: rest)

/-- **`Cert R start goal c`** — a reduction certificate: `c` is a NON-EMPTY chain from `start` to `goal`
with every step a valid `R`-reduction. The verifier checks `chain R c` locally + the two endpoints. -/
def Cert (R : α → α → Prop) (start goal : α) (c : List α) : Prop :=
  c.head? = some start ∧ c.getLast? = some goal ∧ chain R c

/-- A reflexive-transitive reduction unrolls to a certificate chain (prepend at each head-step). -/
theorem to_chain (R : α → α → Prop) {u v : α} (h : Relation.ReflTransGen R u v) :
    ∃ c, c.head? = some u ∧ c.getLast? = some v ∧ chain R c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[v], rfl, rfl, trivial⟩
  | @head a c h' _hcv ih =>
    obtain ⟨cc, hhead, hlast, hpc⟩ := ih
    cases cc with
    | nil => simp at hhead
    | cons c' rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      refine ⟨a :: c' :: rest, rfl, ?_, ?_⟩
      · rw [List.getLast?_cons_cons]; exact hlast
      · exact ⟨h', hpc⟩

/-- A certificate chain from `u` to `v` witnesses `ReflTransGen R u v` (fold each step in at the head). -/
theorem of_chain (R : α → α → Prop) :
    ∀ (c : List α) {u v : α},
      c.head? = some u → c.getLast? = some v → chain R c → Relation.ReflTransGen R u v := by
  intro c
  induction c with
  | nil => intro u v hhead _ _; simp at hhead
  | cons x xs ih =>
    intro u v hhead hlast hpc
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases xs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast; exact Relation.ReflTransGen.refl
    | cons y ys =>
      obtain ⟨hxy, hrest⟩ := hpc
      rw [List.getLast?_cons_cons] at hlast
      exact Relation.ReflTransGen.head hxy (ih rfl hlast hrest)

/-- **`bridge`** — the generic reduction bridge: a chain certificate from `start` to `goal` exists IFF
`start` reduces to `goal` in the reflexive-transitive closure of `R`. This is the ZK-checkable proof of
an ARBITRARY reduction — the verifier checks each local step, the bridge certifies the whole reduction. -/
theorem bridge (R : α → α → Prop) (start goal : α) :
    (∃ c, Cert R start goal c) ↔ Relation.ReflTransGen R start goal := by
  constructor
  · rintro ⟨c, hhead, hlast, hpc⟩; exact of_chain R c hhead hlast hpc
  · intro h; obtain ⟨c, hhead, hlast, hpc⟩ := to_chain R h; exact ⟨c, hhead, hlast, hpc⟩

/-! ### Generic transport + fold — certificates are functorial, and they FOLD into semantics.

Two further relation-parametric lemmas. `Cert.map` transports a certificate along any
relation-preserving map (`R x y → S (f x) (f y)`), so a certificate over one configuration space
yields a certificate over any simulating one. `Cert.foldSound` is the generic "walk the chain,
accumulate an output, carry a semantic invariant" induction: give each configuration an output
segment (`out`) and a semantics (`Sem`) such that every `R`-step PREPENDS its segment soundly, and
any certificate folds to `Sem` of the concatenated output at its start — the shape of every
trace-to-replay assembly (see `ReplayAsCert.mrun_imp_replay_via_fold`). -/

/-- A chain transports pointwise along any relation-preserving map: if every `R`-step maps to an
`S`-step, an `R`-chain maps to an `S`-chain. -/
theorem chain_map {β : Type v} {R : α → α → Prop} {S : β → β → Prop} (f : α → β)
    (hf : ∀ x y, R x y → S (f x) (f y)) :
    ∀ c : List α, chain R c → chain S (c.map f)
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: rest, ⟨hab, hrest⟩ => ⟨hf a b hab, chain_map f hf (b :: rest) hrest⟩

/-- **`Cert.map`** — certificates are functorial along relation-preserving maps: a certificate for
`R` from `x` to `y` maps to a certificate for `S` from `f x` to `f y`, chain mapped pointwise. -/
theorem Cert.map {β : Type v} {R : α → α → Prop} {S : β → β → Prop} (f : α → β)
    (hf : ∀ x y, R x y → S (f x) (f y)) {x y : α} {c : List α}
    (h : Cert R x y c) : Cert S (f x) (f y) (c.map f) := by
  obtain ⟨hhead, hlast, hchain⟩ := h
  refine ⟨?_, ?_, chain_map f hf c hchain⟩
  · simp [hhead]
  · simp [hlast]

/-- **`Cert.foldSound`** — the generic chain-fold induction. Give each configuration an output
segment `out` and a semantics `Sem : List β → α → Prop` such that every `R`-step is SOUND for
prepending (`Sem rs y → Sem (out x ++ rs) x` whenever `R x y`). Then any certificate from `x` to
`y` folds: `Sem` of the whole concatenated output holds at the start, given `Sem` of the final
segment at the goal. This is the one induction behind every "forward trace ⇒ backward replay"
assembly — the trace is the chain, `out` reconstructs the wire object, `Sem` is the replay. -/
theorem Cert.foldSound {β : Type v} {R : α → α → Prop}
    (out : α → List β) (Sem : List β → α → Prop)
    (hstep : ∀ x y, R x y → ∀ rs, Sem rs y → Sem (out x ++ rs) x) :
    ∀ {c : List α} {x y : α}, Cert R x y c → Sem (out y) y → Sem (c.flatMap out) x := by
  intro c
  induction c with
  | nil => intro x y h _; obtain ⟨hhead, -, -⟩ := h; simp at hhead
  | cons a as ih =>
    intro x y h hsem
    obtain ⟨hhead, hlast, hchain⟩ := h
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases as with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      simpa using hsem
    | cons b bs =>
      obtain ⟨hab, hrest⟩ := hchain
      rw [List.getLast?_cons_cons] at hlast
      have hSem := ih ⟨rfl, hlast, hrest⟩ hsem
      simpa [List.flatMap_cons] using hstep _ _ hab _ hSem

end Generic

#assert_axioms bridge
#assert_axioms Cert.map
#assert_axioms Cert.foldSound

/-- Non-vacuity of `Cert.map`: the successor chain `[0, 1]` transports along `(· + 1)` to the
genuine successor certificate `[1, 2]` — the mapped chain's steps are real steps. -/
theorem cert_map_nonvacuous : Cert (fun a b => b = a + 1) 1 2 [1, 2] := by
  have base : Cert (fun a b => b = a + 1) 0 1 [0, 1] := ⟨rfl, rfl, rfl, trivial⟩
  have h := Cert.map (S := fun a b => b = a + 1) (· + 1)
    (fun x y (h : y = x + 1) => by show y + 1 = x + 1 + 1; omega) base
  simpa using h

#assert_axioms cert_map_nonvacuous

end Dregg2.Crypto.Hypergraph
