/-
# Dregg2._scratch.ExecRightsLattice — DESIGN + PROTOTYPE for a REAL rights lattice.

The FAITHFULNESS-AUDIT root finding: `Dregg2/Spec/ExecRefinement.lean:210`
`abbrev ExecRights := Unit` makes every `granted.rights ≤ held.rights` attenuation
claim collapse to `() ≤ () = True` — VACUOUS. On `Unit`, `confers parent child`
reduces to `child.target = parent.target` and a trivially-true rights conjunct; no
amplifying grant can ever be rejected, because there is exactly one rights value.

This sidefile PROTOTYPES the real lattice and PROVES non-vacuity, WITHOUT touching
the production `abbrev ExecRights` (which is hardwired as `()`-literals across ~10
files / ~60 sites — see the integration plan in the agent report).

## The carrier

The executable rights are `List Auth` (`Dregg2.Authority.Cap.endpoint target (rights :
List Auth)`, with `capAuthConferred`). The genuine attenuation order is **subset of
conferred authorities** (`granted ⊆ held` — `Caps.attenuate_subset`,
`AuthModes.captp_granted_le_held`). The deduplicated, order-insensitive carrier with a
GENUINE meet-semilattice + top is `Finset Auth`:

  * `≤`  := `⊆`           (attenuation: narrower = fewer authorities)
  * `⊓`  := `∩`           (the largest authority narrower than both — what `attenuate` realizes)
  * `⊤`  := `Finset.univ` (full authority — `Auth` is a `Fintype`)

`Finset Auth` IS a `SemilatticeInf` with `OrderTop` (mathlib instances + `Fintype Auth`),
so it slots DIRECTLY into `Spec.Authority`'s `variable {Rights} [SemilatticeInf Rights]
[OrderTop Rights]` with NO new instance to discharge. This is the faithful replacement
for `ExecRights := Unit`.
-/
import Dregg2.Authority.Positional
import Dregg2.Spec.Authority
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Basic

namespace Dregg2._scratch

open Dregg2.Authority (Auth Label capAuthConferred)
open Dregg2.Spec (Cap confers confers_refl confers_trans Graph)

/-! ## §1 — `Auth` is a `Fintype` (so `Finset Auth` has a top). -/

/-- `Auth` has decidable equality already (`deriving DecidableEq`); give it a `Fintype`
so `Finset.univ : Finset Auth` exists and `⊤` is genuinely the full authority set. -/
instance : Fintype Auth where
  elems := {.read, .write, .grant, .call, .reply, .reset, .control}
  complete := by intro a; cases a <;> decide

/-- Sanity: the full authority set has all 7 kinds. -/
example : (Finset.univ : Finset Auth).card = 7 := by decide

/-! ## §2 — THE LATTICE: `ExecRightsR := Finset Auth`.

This is the genuine rights carrier. `Finset` is a `SemilatticeInf` + `OrderTop`
(via `Fintype`) out of the box — exactly `Spec.Authority`'s required interface. -/

/-- **The real rights lattice** — the deduplicated set of conferred authorities, ordered
by subset (attenuation). Replaces `ExecRights := Unit`. -/
abbrev ExecRightsR := Finset Auth

-- These instances are what `Spec.Authority` demands; confirm they resolve.
example : SemilatticeInf ExecRightsR := inferInstance
example : OrderTop ExecRightsR := inferInstance

/-- The faithful lift of an executable cap's conferred-rights into the lattice. -/
def rightsOf (c : Dregg2.Authority.Cap) : ExecRightsR :=
  (capAuthConferred c).toFinset

/-! ## §3 — NON-VACUITY: `≤` genuinely distinguishes, and `confers` can FAIL.

On `Unit`, `a ≤ b` is ALWAYS true. Here it is a real subset test. We exhibit:

  * a HOLDS witness: a strictly-narrower grant attenuates (`confers` succeeds), AND
  * a FAILS witness: an AMPLIFYING grant (asks for `write` not held) — `confers` is
    FALSE, and the rights `≤` is decidably `false`.

This is the tooth `ExecRights := Unit` cannot grow. -/

/-- read-only authority. -/
def held    : ExecRightsR := {Auth.read}
/-- read+write — STRICTLY MORE than `held` (amplifying). -/
def amplified : ExecRightsR := {Auth.read, Auth.write}
/-- the empty authority — STRICTLY LESS than `held` (a sound attenuation). -/
def narrowed : ExecRightsR := ∅

-- ── The order is NON-TRIVIAL (this is the whole point) ──────────────────────────

/-- HOLDS: narrowing read-only down to nothing IS a valid attenuation. -/
example : narrowed ≤ held := by decide

/-- FAILS: asking for write when you hold only read is NOT `≤` — the amplifying
grant is REJECTED. On `Unit` this would be `() ≤ () = True`; here it is FALSE. -/
example : ¬ (amplified ≤ held) := by decide

-- The same, as decidable `#guard`s. The spec returns `false` on the amplifying input
-- (the tooth `Unit` cannot grow), `true` on the sound attenuation (not constantly-false),
-- and `true` reflexively (sanity).
#guard (decide (amplified ≤ held)) = false
#guard (decide (narrowed ≤ held)) = true
#guard (decide (held ≤ held)) = true

/-! ## §4 — `confers` over the REAL lattice has teeth.

`Spec.confers parent child := child.target = parent.target ∧ child.rights ≤ parent.rights`.
Instantiate it at `Rights = ExecRightsR` and show a TAMPERED (amplifying) child cap makes
`confers` FALSE — the exact claim `ExecRights := Unit` cannot make. -/

/-- A held parent cap to target `7` conferring read-only. -/
def parentCap : Cap Label ExecRightsR := ⟨7, held⟩
/-- A SOUND attenuated child: same target, empty rights. -/
def soundChild : Cap Label ExecRightsR := ⟨7, narrowed⟩
/-- A TAMPERED child: same target, but AMPLIFIED rights (read+write). -/
def amplifyChild : Cap Label ExecRightsR := ⟨7, amplified⟩
/-- A WRONG-TARGET child (the connectivity conjunct also bites). -/
def wrongTargetChild : Cap Label ExecRightsR := ⟨8, narrowed⟩

/-- HOLDS: the sound attenuation confers. -/
theorem sound_confers : confers parentCap soundChild := by
  refine ⟨rfl, ?_⟩
  show narrowed ≤ held
  decide

/-- FAILS (rights tooth): the amplifying child does NOT confer — its rights exceed the
parent's. This is the non-amplification claim that `ExecRights := Unit` makes vacuous. -/
theorem amplify_refused : ¬ confers parentCap amplifyChild := by
  rintro ⟨_, hle⟩
  exact absurd (by decide : ¬ (amplified ≤ held)) (by simpa using hle)

/-- FAILS (connectivity tooth): a different-target child does NOT confer. -/
theorem wrong_target_refused : ¬ confers parentCap wrongTargetChild := by
  rintro ⟨ht, _⟩
  exact absurd ht (by decide)

/-! ## §5 — The conferral discipline still composes (lattice laws survive).

`confers_refl` / `confers_trans` are proved generically in `Spec.Authority` for ANY
`SemilatticeInf`+`OrderTop`, so they transport to `ExecRightsR` for free — the lattice
is a drop-in. We instantiate them to confirm the refinement plumbing keeps working. -/

/-- Reflexivity transports. -/
example : confers parentCap parentCap := confers_refl parentCap

/-- Transitivity transports: chaining `held ⟶ narrowed` (already minimal) stays sound. -/
example (c : Cap Label ExecRightsR) (h1 : confers parentCap soundChild)
    (h2 : confers soundChild c) : confers parentCap c := confers_trans h1 h2

/-! ## §6 — A faithful `execGraphR` keyed on REAL rights (the integration shape).

The production `execGraph` (ExecRefinement.lean:216) abstracts rights to `()`. The faithful
version reads `capAuthConferred` into the lattice, so a Spec edge's `rights` field is the
ACTUAL conferred authority — and `Graph.has` / `confers` over it are non-vacuous. This is the
SHAPE the integration installs (rights-aware, not connectivity-only). -/

/-- Faithful reconstruction: cell `h` holds a Spec edge `⟨t, r⟩` iff it holds an executable
cap to `t` whose conferred rights are exactly `r` (as a `Finset`). Rights are CARRIED, not
abstracted to `()`. -/
def execGraphR (caps : Dregg2.Authority.Caps) : Graph Label ExecRightsR :=
  fun h c => ∃ cap ∈ caps h,
    (match cap with
     | .endpoint t _ => t = c.target
     | .node t       => t = c.target
     | .null         => False) ∧ rightsOf cap = c.rights

/-! NON-VACUITY of the graph: a concrete cap table places a rights-bearing edge, and an
edge with the WRONG (amplified) rights is ABSENT — the rights field genuinely discriminates,
unlike the `()`-skeleton where every same-target edge is present. -/
section GraphWitness

/-- one cell (`0`) holds a read-only endpoint cap to target `7`. -/
def sampleCaps : Dregg2.Authority.Caps :=
  fun h => if h = 0 then [.endpoint 7 [Auth.read]] else []

/-- HOLDS: the read-only edge `0 ⟶ ⟨7, {read}⟩` is in the faithful graph. -/
theorem graph_has_real_edge :
    execGraphR sampleCaps 0 ⟨7, {Auth.read}⟩ := by
  refine ⟨.endpoint 7 [Auth.read], ?_, rfl, ?_⟩
  · show (.endpoint 7 [Auth.read] : Dregg2.Authority.Cap) ∈ sampleCaps 0
    simp [sampleCaps]
  · show rightsOf (.endpoint 7 [Auth.read]) = ({Auth.read} : ExecRightsR)
    decide

/-- FAILS: the AMPLIFIED edge `0 ⟶ ⟨7, {read,write}⟩` is NOT in the graph — the cell only
holds read, so a write-conferring edge cannot be reconstructed. On the `()`-skeleton this
distinction is INVISIBLE (both would be the single edge `⟨7, ()⟩`). -/
theorem graph_lacks_amplified_edge :
    ¬ execGraphR sampleCaps 0 ⟨7, {Auth.read, Auth.write}⟩ := by
  rintro ⟨cap, hmem, _htgt, hr⟩
  -- only `endpoint 7 [read]` is in `sampleCaps 0`; its `rightsOf` is `{read} ≠ {read,write}`.
  simp only [sampleCaps, ite_true, List.mem_singleton] at hmem
  subst hmem
  exact absurd hr (by decide)

end GraphWitness

/-! ## §7 — Summary tooth for the report.

On `ExecRights := Unit` BOTH of the following collapse to `True`; here the first HOLDS and
the second is genuinely FALSE — the audit's vacuity is closed. -/

/-- The grant lattice distinguishes amplification from attenuation: there EXISTS a pair where
`confers` fails. (On `Unit`, `∀ p c, confers p c ↔ c.target = p.target` — no such pair.) -/
theorem rights_lattice_nonvacuous :
    confers parentCap soundChild ∧ ¬ confers parentCap amplifyChild :=
  ⟨sound_confers, amplify_refused⟩

end Dregg2._scratch
