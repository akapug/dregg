/-
# Dregg2.Crypto.DfaAsCert — the LINCHPIN of the composed-attestation architecture.

`Crypto/Hypergraph` proved a RELATION-PARAMETRIC certificate: for ANY reduction relation
`R : α → α → Prop`, a locally-checkable CHAIN certificate `Cert R start goal c` exists IFF
`ReflTransGen R start goal` (`Hypergraph.bridge`). That one object already unifies CFG parsing
(`cfg_parse_via_reduction`, `R = g.Produces`), hyperedge replacement, and DPO graph rewrite —
they differ ONLY in the relation `R`.

`Crypto/Dfa` proved DFA acceptance (`DfaAccepts δ q₀ accept trace`) via its OWN chain (`Dfa.chained`),
but never expressed it as a `Hypergraph.Cert`. This file closes that seam: a DFA run is EXACTLY a
`Hypergraph` chain certificate over the step-chaining relation `delta`, so regular languages (DFA)
join the SAME certificate substrate as context-free languages (CFG), hypergraphs, and graph rewriting.
Regular vs context-free is then not two machineries but ONE `Hypergraph.Cert`, differing only in `R`:

    DFA :  Cert delta        first last              trace                     (delta := chaining of Steps)
    CFG :  Cert g.Produces   [nt g.initial]  (input.map term)   c              (Produces := grammar rewrite)

The key fact is DEFINITIONAL: `Dfa.chained` and `Hypergraph.chain delta` are the same structural
recursion (`chained_iff_chain`), so `DfaAccepts` is a `Hypergraph.Cert` over `delta` plus the DFA
boundary/validity side-conditions (initial state `q₀`, accepting `last.next`, per-step `δ`-validity)
— the same way `CfgAccepts`'s boundaries are the fixed endpoints of its `Cert`.

    delta                       : Step → Step → Prop  (b.state = a.next — the `Transition` chaining relation)
    chained_iff_chain           : Dfa.chained trace ↔ Hypergraph.chain delta trace  (definitional bridge)
    dfaAccepts_as_cert          : DfaAccepts δ q₀ accept trace ↔ (a Hypergraph.Cert over delta + boundaries)
    dfaAccepts_reduces          : an accepting run ⇒ ReflTransGen delta first last  (via Hypergraph.bridge)
    regular_and_cf_share_substrate : DFA and CFG are BOTH `Hypergraph.bridge` instances, differing only in R
-/
import Dregg2.Crypto.Dfa
import Dregg2.Crypto.Hypergraph
import Dregg2.Tactics

namespace Dregg2.Crypto.DfaAsCert

open Dregg2.Crypto Dregg2.Crypto.Dfa

universe u

variable {State Sym : Type u}

/-! ## `delta` — the DFA step relation, as a `Hypergraph` reduction relation over configs = `Step`.

`Dfa.DfaAccepts` runs its chain over `List (Step State Sym)`: the configuration the chain threads IS a
`Step` (a trace row `[state, byte, next_state]`). The `Transition` constraint — "consecutive steps
chain: `b.state = a.next`" — is exactly `Dfa.chained`. Reading that as a `Hypergraph` reduction relation
`R : Step → Step → Prop`, the relation is `delta a b := b.state = a.next`: one step reduces to the next
iff the next starts where this one ended. This is the SAME shape of `R` `Hypergraph.chain` consumes;
per-step `δ`-validity (`Lookup`) and the boundaries (`PiBinding`s) ride alongside as the DFA-specific
acceptance wrapper, exactly as CFG's start-symbol/goal-word ride as its `Cert`'s fixed endpoints. -/

/-- **`delta`** — the DFA `Transition` relation as a `Hypergraph` reduction relation over `Step` configs:
`a` reduces to `b` iff `b` begins in `a`'s exit state (`b.state = a.next`). This is precisely the relation
whose `Hypergraph.chain` coincides with `Dfa.chained`. -/
def delta (a b : Step State Sym) : Prop := b.state = a.next

/-- **`chained_iff_chain`** — the DEFINITIONAL heart: `Dfa.chained` IS `Hypergraph.chain delta`.
Since the chain-dedup refactor, `Dfa.chained` is DEFINED as `Hypergraph.chain (fun a b => b.state =
a.next)` and `delta` unfolds to that same relation, so the identification is `Iff.rfl` — a DFA
`Transition` chain and a `Hypergraph` reduction chain over `delta` are the same predicate, by
definition. -/
theorem chained_iff_chain :
    ∀ trace : List (Step State Sym), Dfa.chained trace ↔ Hypergraph.chain delta trace :=
  fun _ => Iff.rfl

/-! ## `dfaAccepts_as_cert` — a DFA acceptance IS a `Hypergraph.Cert` over `delta`. -/

/-- **`dfaAccepts_as_cert`** — THE KEYSTONE. `DfaAccepts δ q₀ accept trace` holds IFF there exist endpoint
steps `first`/`last` such that the run is a genuine `Hypergraph.Cert delta first last trace` (the
`head?`/`getLast?` endpoint bindings + the `chain delta` over the whole run) TOGETHER WITH the DFA
acceptance wrapper: `first.state = q₀` (initial `PiBinding`), `accept last.next` (accepting `PiBinding`),
and `∀ s ∈ trace, stepValid δ s` (per-step `Lookup`). The `Cert` conjunct is bit-for-bit the SAME
certificate object `Crypto/Hypergraph` uses for CFG/hypergraph/graph-rewrite reductions — only the
relation is DFA-specific (`delta`). Proof: reassociate `DfaAccepts`'s conjuncts and swap `Dfa.chained`
for `Hypergraph.chain delta` via `chained_iff_chain`. -/
theorem dfaAccepts_as_cert (δ : State → Sym → State → Prop) (q₀ : State) (accept : State → Prop)
    (trace : List (Step State Sym)) :
    DfaAccepts δ q₀ accept trace ↔
      ∃ first last : Step State Sym,
        first.state = q₀ ∧
        accept last.next ∧
        (∀ s ∈ trace, stepValid δ s) ∧
        Hypergraph.Cert delta first last trace := by
  constructor
  · rintro ⟨first, last, hhead, hlast, hq0, hacc, hval, hchain⟩
    exact ⟨first, last, hq0, hacc, hval, hhead, hlast, (chained_iff_chain trace).mp hchain⟩
  · rintro ⟨first, last, hq0, hacc, hval, hhead, hlast, hchain⟩
    exact ⟨first, last, hhead, hlast, hq0, hacc, hval, (chained_iff_chain trace).mpr hchain⟩

/-- **`dfaAccepts_reduces`** — feeding the `Cert` half of `dfaAccepts_as_cert` through the GENERIC
`Hypergraph.bridge`: an accepting DFA run witnesses a reflexive-transitive `delta`-reduction from its
first to its last step. The DFA run is literally a reduction in the shared substrate. -/
theorem dfaAccepts_reduces (δ : State → Sym → State → Prop) (q₀ : State) (accept : State → Prop)
    (trace : List (Step State Sym)) (h : DfaAccepts δ q₀ accept trace) :
    ∃ first last : Step State Sym,
      first.state = q₀ ∧ accept last.next ∧
        Relation.ReflTransGen delta first last := by
  obtain ⟨first, last, hq0, hacc, _hval, hcert⟩ := (dfaAccepts_as_cert δ q₀ accept trace).mp h
  exact ⟨first, last, hq0, hacc, (Hypergraph.bridge delta first last).mp ⟨trace, hcert⟩⟩

#assert_axioms chained_iff_chain
#assert_axioms dfaAccepts_as_cert
#assert_axioms dfaAccepts_reduces

/-! ## `regular_and_cf_share_substrate` — the unification is REAL: DFA and CFG are ONE object.

Side by side, the two acceptance notions are the SAME `Hypergraph.bridge`, applied at two relations:

  * REGULAR (DFA):        `Hypergraph.bridge delta first last`
                          — `∃ c, Cert delta first last c ↔ ReflTransGen delta first last`
  * CONTEXT-FREE (CFG):   `Hypergraph.cfg_parse_via_reduction g input`
                          — `∃ c, Cert g.Produces [nt g.initial] (input.map term) c ↔ input ∈ g.language`

`cfg_parse_via_reduction` is itself `Hypergraph.bridge g.Produces _ _` composed with `mem_language_iff`.
So both regular and context-free acceptance are the reflexive-transitive-closure bridge of the ONE
`Hypergraph.Cert` certificate — they differ ONLY in the reduction relation `R` (`delta` vs `g.Produces`).
The verifier machinery (`chain`, `Cert`, `bridge`) is shared verbatim. -/

/-- **`regular_and_cf_share_substrate`** — DFA acceptance and CFG parsing are BOTH the generic
`Hypergraph.bridge`, instantiated at `delta` and at `g.Produces` respectively. The conjunction exhibits
the two instantiations of the SAME certificate object literally side by side; the only difference is the
relation `R`. -/
theorem regular_and_cf_share_substrate
    (first last : Step State Sym) {T : Type} (g : ContextFreeGrammar T) (input : List T) :
    -- REGULAR: the chain certificate over `delta` bridges to a reflexive-transitive DFA reduction.
    ((∃ c, Hypergraph.Cert delta first last c) ↔ Relation.ReflTransGen delta first last)
    ∧
    -- CONTEXT-FREE: the chain certificate over `g.Produces` bridges to grammar membership.
    ((∃ c, Hypergraph.Cert g.Produces
        [Symbol.nonterminal g.initial] (input.map Symbol.terminal) c) ↔ input ∈ g.language) :=
  ⟨Hypergraph.bridge delta first last, Hypergraph.cfg_parse_via_reduction g input⟩

-- Both projections are, by construction, the SAME `Hypergraph.bridge`/`Cert` object at different `R`:
#check @Hypergraph.bridge          -- the shared substrate: `∀ R start goal, (∃ c, Cert R start goal c) ↔ …`
#check @Hypergraph.Cert            -- the shared certificate: `chain R c` + endpoint bindings
#check @regular_and_cf_share_substrate

#assert_axioms regular_and_cf_share_substrate

/-! ## Non-vacuity — the concrete `a⁺b` DFA of `Crypto/Dfa`, routed through the `Cert` form. -/

namespace Reference

open Dfa.Reference

/-- **`aab_as_cert`** — the reference `"aab"` run (`0 →a 1 →a 1 →b 2` of the `a⁺b` DFA) exercised through
the KEYSTONE: its genuine acceptance (`Dfa.Reference.aab_accepts`) yields, via `dfaAccepts_as_cert`, a
`Hypergraph.Cert delta`-shaped certificate — the DFA acceptance really does go through the shared
`Hypergraph` certificate object, on a concrete automaton, with no crypto and no `sorry`. -/
theorem aab_as_cert :
    ∃ first last : Step Nat Nat,
      first.state = Dfa.Reference.q₀ ∧
      accept last.next ∧
      (∀ s ∈ aabTrace, stepValid Dfa.Reference.δ s) ∧
      Hypergraph.Cert delta first last aabTrace :=
  (dfaAccepts_as_cert Dfa.Reference.δ Dfa.Reference.q₀ accept aabTrace).mp aab_accepts

/-- And the concrete run witnesses a genuine reflexive-transitive `delta`-reduction (the shared
substrate's reduction reading), from the `"aab"` first step to its accepting last step. -/
theorem aab_reduces :
    ∃ first last : Step Nat Nat,
      first.state = Dfa.Reference.q₀ ∧ accept last.next ∧
        Relation.ReflTransGen delta first last :=
  dfaAccepts_reduces Dfa.Reference.δ Dfa.Reference.q₀ accept aabTrace aab_accepts

#assert_axioms aab_as_cert

end Reference

end Dregg2.Crypto.DfaAsCert
