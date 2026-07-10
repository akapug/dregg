/-
# Dregg2.Crypto.ZkHandlebars — SLOT-CONFINEMENT: a `{{`-free player field cannot inject a control token.

The load-bearing input-integrity property of an attested AI dungeon-master. A prompt TEMPLATE is a
list of segments — fixed `Lit` bytes (the DM's system prompt / world-rules, which MAY themselves carry
handlebars control tokens `{{`) and `Slot` holes (where an untrusted player's field is interpolated).
`render` concatenates the template, substituting each `Slot n` with the player's `binding n`.

THE THEOREM (`slot_confinement`): if every player field bound into `T` is `{{`-free — i.e. it UNMATCHES
the zkOracle `injectionTemplate`, the EXACT hypothesis the `Crypto/ZkOracle` injection-free leg already
attests — then the *control-token structure* of the rendered prompt (`controlTokens`, the sublist of
`{{` occurrences) EQUALS that of the template's literal segments alone. The player contributes ZERO
control tokens: it cannot introduce or alter a single `{{`, so the system-prompt / world-rules are
preserved verbatim.

Non-vacuity is pinned in BOTH polarities: a `{{`-free binding PRESERVES the structure (`benign_preserves`
+ `#guard`s), and a `{{`-bearing binding CHANGES it — injects exactly one extra control token
(`malicious_injects`) — so the guard is load-bearing, not decorative.

Rides entirely on the verified derivative matcher (`Crypto/Deriv`): `derives_cat`, `derives_sym`,
`derives_neg`, `derives_star_cons` and the `injectionTemplate` of `Crypto/ZkOracle`. No new axioms.
-/
import Dregg2.Crypto.ZkOracle
import Dregg2.Crypto.Deriv.Correctness
import Dregg2.Tactics

namespace Dregg2.Crypto.ZkHandlebars

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE
open Dregg2.Crypto.ZkOracle

/-! ## The control-token reader.

A control token is a frame whose `"c"` field is the reserved `handlebarsOpen` code — EXACTLY the frame
`injectionTemplate` detects (its middle leaf is `sym (matchCode handlebarsOpen)`). `controlTokens` keeps
only those frames, so it reads off "the `{{` structure" of a token list. -/

/-- **`isControl a`** — is frame `a` the handlebars control token `{{`? The SAME leaf predicate the
zkOracle `injectionTemplate` fires on (`leaf (matchCode handlebarsOpen)`). -/
def isControl (a : Value) : Bool := PredRE.leaf (matchCode handlebarsOpen) a

/-- **`controlTokens w`** — the control-token structure of a token list: the sublist of `{{` frames,
in order. Its equality across two token lists is "they carry the same handlebars control structure." -/
def controlTokens (w : List Value) : List Value := w.filter isControl

/-! ## Prompt templates and rendering. -/

/-- A prompt-template **segment**: fixed template bytes `lit ts` (MAY contain control tokens `{{` — the
DM's own world-rule delimiters), or a `slot n` hole where the untrusted player field `binding n` lands. -/
inductive Seg (Name : Type) where
  | lit  (ts : List Value)
  | slot (n : Name)
  deriving Repr

/-- A **prompt template** is a list of segments. -/
abbrev Template (Name : Type) := List (Seg Name)

variable {Name : Type}

/-- **`render b T`** — the rendered prompt: concatenate the template left-to-right, substituting each
`slot n` with the player's `binding n = b n`. -/
def render (b : Name → List Value) : Template Name → List Value
  | []                 => []
  | Seg.lit ts :: rest => ts ++ render b rest
  | Seg.slot n :: rest => b n ++ render b rest

/-- **`litOnly T`** — the template's LITERAL bytes alone (drop every slot). The committed
system-prompt / world-rules the DM published; the reference the player must not perturb. -/
def litOnly : Template Name → List Value
  | []                 => []
  | Seg.lit ts :: rest => ts ++ litOnly rest
  | Seg.slot _ :: rest => litOnly rest

/-! ## The `{{`-free hypothesis is exactly the zkOracle injection-free leg.

`InjectionFree w` (`Crypto/ZkOracle`) is `derives w (neg injectionTemplate) = true`. We show this holds
iff `w` carries no control token, connecting the ZK guard to `controlTokens`. -/

/-- `star (sym tt)` matches EVERY word — the `.*` wings of `injectionTemplate`. -/
theorem derives_star_tt (w : List Value) : derives w (PredRE.star (PredRE.sym Pred.tt)) = true := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    rw [derives_star_cons, derives_cat]
    refine ⟨[], as, rfl, ?_, ih⟩
    -- der a (sym tt) = ε  (leaf tt a = true), so derives [] (der a (sym tt)) = true
    have hd : der a (PredRE.sym Pred.tt) = PredRE.ε := by simp [der, leaf, Pred.eval]
    rw [hd]; rfl

/-- **`derives_injection_iff`** — the zkOracle injection template fires on `w` IFF `w` contains a
handlebars control token. Peels the `.* ⟨{{⟩ .*` structure through the verified `derives_cat`/
`derives_sym` lemmas. -/
theorem derives_injection_iff (w : List Value) :
    derives w injectionTemplate = true ↔ ∃ a ∈ w, isControl a = true := by
  unfold injectionTemplate
  rw [derives_cat]
  constructor
  · rintro ⟨w1, w2, rfl, -, h2⟩
    rw [derives_cat] at h2
    obtain ⟨u1, u2, rfl, hsym, -⟩ := h2
    rw [derives_sym] at hsym
    obtain ⟨a, rfl, hfire⟩ := hsym
    exact ⟨a, by simp, hfire⟩
  · rintro ⟨a, ha, hfire⟩
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem ha
    refine ⟨pre, a :: post, rfl, derives_star_tt pre, ?_⟩
    rw [derives_cat]
    exact ⟨[a], post, rfl, (derives_sym [a] (matchCode handlebarsOpen)).mpr ⟨a, rfl, hfire⟩,
           derives_star_tt post⟩

/-- **`injection_false_of_free`** — an injection-free field does NOT match the injection template. -/
theorem injection_false_of_free (w : List Value) (h : InjectionFree w) :
    derives w injectionTemplate = false := by
  unfold InjectionFree at h
  rw [derives_neg] at h
  cases hd : derives w injectionTemplate with
  | false => rfl
  | true  => rw [hd] at h; simp at h

/-- **`injectionFree_forall`** — the zkOracle `{{`-free hypothesis IS "no frame is a control token." -/
theorem injectionFree_forall (w : List Value) :
    InjectionFree w ↔ ∀ a ∈ w, isControl a = false := by
  constructor
  · intro h a ha
    have hfalse := injection_false_of_free w h
    by_contra hc
    have htrue : isControl a = true := by
      cases hh : isControl a with
      | true  => rfl
      | false => exact absurd hh hc
    have hcontra : derives w injectionTemplate = true := (derives_injection_iff w).mpr ⟨a, ha, htrue⟩
    rw [hfalse] at hcontra; exact Bool.noConfusion hcontra
  · intro h
    have hfalse : derives w injectionTemplate = false := by
      by_contra hc
      have htrue : derives w injectionTemplate = true := by
        cases hh : derives w injectionTemplate with
        | true  => rfl
        | false => exact absurd hh hc
      obtain ⟨a, ha, hfire⟩ := (derives_injection_iff w).mp htrue
      rw [h a ha] at hfire; exact Bool.noConfusion hfire
    unfold InjectionFree
    rw [derives_neg, hfalse]; rfl

/-- An injection-free field contributes NO control tokens: its `controlTokens` filter is empty. -/
theorem filter_control_nil_of_forall (w : List Value)
    (h : ∀ a ∈ w, isControl a = false) : w.filter isControl = [] := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    have ha0 : isControl a = false := h a (by simp)
    have hrest : as.filter isControl = [] := ih (fun x hx => h x (by simp [hx]))
    simp [ha0, hrest]

/-! ## THE THEOREM — slot confinement. -/

/-- **`slot_confinement`** — the DM's rules are intact. If every player field bound into template `T`
is `{{`-free (`InjectionFree`, the zkOracle injection-free leg), then the control-token structure of the
rendered prompt EQUALS that of the template's literal segments alone. The player contributes ZERO control
tokens: it cannot add or alter a single `{{`. -/
theorem slot_confinement (T : Template Name) (b : Name → List Value)
    (hb : ∀ n, Seg.slot n ∈ T → InjectionFree (b n)) :
    controlTokens (render b T) = controlTokens (litOnly T) := by
  induction T with
  | nil => rfl
  | cons seg rest ih =>
    cases seg with
    | lit ts =>
      have hrec := ih (fun n hn => hb n (List.mem_cons_of_mem _ hn))
      simp only [render, litOnly, controlTokens, List.filter_append] at hrec ⊢
      rw [hrec]
    | slot n =>
      have hrec := ih (fun m hm => hb m (List.mem_cons_of_mem _ hm))
      have hn0 : (b n).filter isControl = [] :=
        filter_control_nil_of_forall (b n)
          ((injectionFree_forall (b n)).mp (hb n (by simp)))
      simp only [render, litOnly, controlTokens, List.filter_append] at hrec ⊢
      rw [hn0, List.nil_append, hrec]

/-- **`slot_confinement_count`** — the sharper counting form: the number of `{{` control tokens in the
rendered prompt equals the number in the template literals. (A corollary of the structural equality;
enough on its own for the security claim — the player cannot change the `{{` count.) -/
theorem slot_confinement_count (T : Template Name) (b : Name → List Value)
    (hb : ∀ n, Seg.slot n ∈ T → InjectionFree (b n)) :
    (render b T).countP isControl = (litOnly T).countP isControl := by
  have h := slot_confinement T b hb
  simp only [controlTokens] at h
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter, h]

/-! ## Corollary — tying slot-confinement to the zkOracle injection-free leg (the DM narrative). -/

/-- **`dm_rules_intact`** — restated for a single player slot between fixed template bytes: a system
prompt (`before`), the player's hole, and more fixed bytes (`after`). If the player field is
injection-free — EXACTLY the property the zkOracle attestation certifies for the player's field — then
the control-token structure of the whole rendered prompt equals that of the template literals alone:
the DM's world-rules survive the player's input verbatim. -/
theorem dm_rules_intact (before after player : List Value) (nm : Name)
    (hSafe : InjectionFree player) :
    controlTokens (render (fun _ => player) [Seg.lit before, Seg.slot nm, Seg.lit after])
      = controlTokens (litOnly [Seg.lit before, Seg.slot nm, Seg.lit after]) := by
  apply slot_confinement
  intro _ _
  exact hSafe

/-! ## Non-vacuity — BOTH polarities, on concrete data.

A concrete DM template whose LITERAL carries one real control token `{{` (a world-rule delimiter), and
a `slot "player"` for the untrusted field. We show: a benign (`{{`-free) player PRESERVES the one
control token, and a malicious (`{{`-bearing) player INJECTS a second — so the guard is load-bearing. -/

namespace Demo

/-- A DM template: one literal control token `{{` (a world-rule delimiter), then the player's slot. -/
def sysTemplate : Template String := [Seg.lit [frame handlebarsOpen], Seg.slot "player"]

/-- A benign player field `"hi"` (codes 104,105) — carries no handlebars delimiter. -/
def benignPlayer : String → List Value := fun _ => [frame 104, frame 105]

/-- A malicious player field `"{{x"` — smuggles the handlebars delimiter `{{` (code 123). -/
def maliciousPlayer : String → List Value := fun _ => [frame handlebarsOpen, frame 120]

/-- **(a) WITNESS** — the benign player field is injection-free (the hypothesis is SATISFIABLE). -/
theorem benign_injection_free : InjectionFree (benignPlayer "player") := by
  unfold InjectionFree benignPlayer injectionTemplate frame matchCode handlebarsOpen
  decide

/-- **(a) WITNESS** — with a `{{`-free player, the rendered prompt has the SAME control structure as
the template literals: `slot_confinement` fires, the conclusion is meaningful (one preserved `{{`). -/
theorem benign_preserves :
    controlTokens (render benignPlayer sysTemplate) = controlTokens (litOnly sysTemplate) := by
  apply slot_confinement
  intro n _
  show InjectionFree (benignPlayer n)
  unfold InjectionFree benignPlayer injectionTemplate frame matchCode handlebarsOpen
  decide

/-- **(b) COUNTER** — the malicious player field is NOT injection-free (the guard rejects it). -/
theorem malicious_not_injection_free : ¬ InjectionFree (maliciousPlayer "player") := by
  unfold InjectionFree maliciousPlayer injectionTemplate frame matchCode handlebarsOpen
  decide

/-- **(b) COUNTER** — WITHOUT the `{{`-free guard the player INJECTS a control token: the rendered
prompt has EXACTLY ONE MORE `{{` than the template literals. The guard is load-bearing, not decorative. -/
theorem malicious_injects :
    (controlTokens (render maliciousPlayer sysTemplate)).length
      = (controlTokens (litOnly sysTemplate)).length + 1 := by decide

/-! ### Runnable `#guard`s (Nat lengths / Bool — `Value` has no `DecidableEq`, so we count). -/

-- The benign field is `{{`-free; the malicious field is not (the zkOracle guard, decided).
#guard derives (benignPlayer "player") (.neg injectionTemplate) = true
#guard derives (maliciousPlayer "player") (.neg injectionTemplate) = false

-- Template literals carry ONE control token `{{`.
#guard (controlTokens (litOnly sysTemplate)).length = 1
-- Benign player PRESERVES it (still 1) — structure unchanged.
#guard (controlTokens (render benignPlayer sysTemplate)).length = 1
-- Malicious player INJECTS one (now 2) — structure changed: the guard is load-bearing.
#guard (controlTokens (render maliciousPlayer sysTemplate)).length = 2

-- Sharper pure-slot form: an empty-literal template has NO control tokens; a benign player keeps it 0,
-- a malicious player forces it to 1 — injection is possible EXACTLY when the guard is dropped.
#guard (controlTokens (litOnly [Seg.slot "p"])).length = 0
#guard (controlTokens (render benignPlayer [Seg.slot "p"])).length = 0
#guard (controlTokens (render maliciousPlayer [Seg.slot "p"])).length = 1

end Demo

/-! ## Axiom hygiene — the slot-confinement tower is kernel-clean. -/

#assert_all_clean [
  derives_star_tt, derives_injection_iff, injection_false_of_free, injectionFree_forall,
  filter_control_nil_of_forall, slot_confinement, slot_confinement_count, dm_rules_intact
]

#print axioms slot_confinement
#print axioms dm_rules_intact

end Dregg2.Crypto.ZkHandlebars
