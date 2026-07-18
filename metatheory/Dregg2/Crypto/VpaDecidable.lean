/-
# Dregg2.Crypto.VpaDecidable — boolean closure on the visibly-pushdown rung: the first slice of
DECIDABLE template equivalence.

`Crypto/VpaAsCert` landed the visibly-pushdown rung of the certificate substrate and proved the ROOT
VPL property (`run_height` / `stack_height_input_determined`): the stack height at every input
position is a function of the INPUT WORD ALONE. Its residual note names the one genuinely new
capability that property opens — decidable template equivalence on the finite visibly-nested
fragment (CFL equivalence is undecidable; VPL equivalence is EXPTIME-decidable, Alur–Madhusudan).
The route is boolean closure: `L(M₁) = L(M₂)` iff both `L(M₁) ∩ ∁L(M₂)` and `L(M₂) ∩ ∁L(M₁)` are
empty, and VPL emptiness is decidable. This file lands the tractable first step of that route.

PROVED here (finite `Sym` grid, no `sorry`):
    Lang                    : the nested-word language of a VPA (words of accepting runs)
    prodVpa / prodVpa_lang  : INTERSECTION — the product VPA recognizes exactly `L(M₁) ∩ L(M₂)`,
                              both directions. The backward (zip) direction is where the
                              visibly-pushdown discipline earns its keep: because the stack ACTION
                              is class-driven, two VPAs reading the SAME word push and pop in
                              lockstep, so their stacks zip into ONE product stack with no height
                              bookkeeping — the constructive face of
                              `stack_height_input_determined`.
    lang_wordDelta_zero     : every accepted word has net height 0 (all calls matched)
    lang_wellMatched        : every accepted word is WELL-MATCHED (net 0 AND every prefix ≥ 0) —
                              pinning the correct universe for relative complement
    lang_not_nil            : the empty word is NEVER accepted (runs are non-empty by
                              `VpaAccepts`) — which is why the complement target below carries a
                              `w ≠ []` guard
    equiv_iff_symmDiff_empty: the (pure-logic) reduction of equivalence to two emptiness checks
    sat / wm_iff_mem_sat    : the COMPUTABLE emptiness decision — reachable-summary saturation
                              over the finite `S × S` grid as a `Finset` fixpoint, proved sound
                              AND complete against `Lang` (`lang_nonempty_iff_wm`), packaged as
                              genuinely-evaluating `Decidable` instances and kernel-`#guard`ed on
                              concrete machines. The artifact the vacuity note demands: a
                              function, not an `em` phrasing.
    decidableEquivOfComplements : decidable template equivalence assembled from intersection +
                              emptiness, with the complement machines (and their correctness) as
                              the one explicit hypothesis — the seam-parametric form.
    detVpa / det_invariant  : the Alur–Madhusudan DETERMINIZATION — subset construction over
                              summary sets, with the reachability invariant proved for every
                              start/end state and end stack simultaneously
    detVpa_complement       : COMPLEMENT by accept-flip on the determinized machine, relative to
                              the non-empty well-matched universe — determinism is load-bearing
    complement_closure      : the once-named `ComplementClosure` residual, DISCHARGED by the
                              construction above
    decidable_template_equivalence : UNCONDITIONAL, COMPUTABLE decidable equivalence — the
                              headline. Kernel-`#guard`ed on concrete machine pairs (equal →
                              true, distinct → false).

Honest scope: this is the FINITE-alphabet fragment (the `Sym = {op, cl, dat}` bracket grid the Dyck
circuit pins). The templater's infinite `Value` data alphabet is out of scope here — classical VPL
theory (and hence this decidability route) transfers cleanly only to the finite fragment.
-/
import Dregg2.Crypto.VpaAsCert
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.VpaDecidable

open Dregg2.Crypto.VpaAsCert

universe u

variable {S₁ S₂ G₁ G₂ : Type u}

/-! ## The language of a VPA — the words its accepting runs read. -/

/-- **`Lang M q₀ accept w`** — the nested-word LANGUAGE of a VPA: `w` is accepted iff some run
accepted per `VpaAccepts` (non-empty, chained, class-disciplined, empty stack at both ends) reads
exactly `w`. This is the object boolean closure and decidable equivalence are about. -/
def Lang {State Gamma : Type u} (M : Vpa State Gamma) (q₀ : State) (accept : State → Prop)
    (w : List Sym) : Prop :=
  ∃ run : List (VStep State Gamma), VpaAccepts M q₀ accept run ∧ run.map (fun s => s.sym) = w

/-- **`wordDelta`** — the net stack-height change of a WORD (sum of per-symbol `heightDelta`s):
`runDelta` freed of the run. -/
def wordDelta : List Sym → ℤ
  | [] => 0
  | s :: rest => heightDelta s + wordDelta rest

/-- `runDelta` genuinely factors through the input word — the definitional face of "the height
change depends on the symbols alone". -/
theorem runDelta_eq_wordDelta {State Gamma : Type u} :
    ∀ run : List (VStep State Gamma), runDelta run = wordDelta (run.map (fun s => s.sym))
  | [] => rfl
  | s :: rest => by
    simp only [runDelta, List.map_cons, wordDelta]
    rw [runDelta_eq_wordDelta rest]

/-- **`WellMatched w`** — the word universe empty-stack acceptance lives in: net height 0 (every
call matched) and every prefix non-negative (no return ever fires on an empty stack). This is the
universe RELATIVE complement must be stated against (`lang_wellMatched` shows every `Lang` is
contained in it, so an absolute complement is unreachable by ANY VPA of this acceptance shape). -/
def WellMatched (w : List Sym) : Prop :=
  wordDelta w = 0 ∧ ∀ p : List Sym, p <+: w → 0 ≤ wordDelta p

/-! ## The product construction — INTERSECTION.

States pair, stack symbols pair. The class-driven discipline means the two machines' stacks move in
lockstep over a shared input, so ONE product stack of pairs simulates both — the construction that
is IMPOSSIBLE for general PDAs (whose stacks desynchronize) and is exactly what
`stack_height_input_determined` licenses. -/

/-- **`prodVpa M₁ M₂`** — the product VPA: run both machines in parallel; a transition fires iff
BOTH components fire on the same symbol. Note `Fintype (S₁ × S₂)` is automatic, so the product
never leaves the finite fragment. -/
def prodVpa (M₁ : Vpa S₁ G₁) (M₂ : Vpa S₂ G₂) : Vpa (S₁ × S₂) (G₁ × G₂) where
  call q s q' γ := M₁.call q.1 s q'.1 γ.1 ∧ M₂.call q.2 s q'.2 γ.2
  ret q s q' γ := M₁.ret q.1 s q'.1 γ.1 ∧ M₂.ret q.2 s q'.2 γ.2
  int q s q' := M₁.int q.1 s q'.1 ∧ M₂.int q.2 s q'.2

/-- First projection of a product step: keep the left state, `map Prod.fst` the stack. -/
def projStep₁ (s : VStep (S₁ × S₂) (G₁ × G₂)) : VStep S₁ G₁ :=
  ⟨⟨s.pre.state.1, s.pre.stack.map Prod.fst⟩, s.sym, ⟨s.post.state.1, s.post.stack.map Prod.fst⟩⟩

/-- Second projection of a product step. -/
def projStep₂ (s : VStep (S₁ × S₂) (G₁ × G₂)) : VStep S₂ G₂ :=
  ⟨⟨s.pre.state.2, s.pre.stack.map Prod.snd⟩, s.sym, ⟨s.post.state.2, s.post.stack.map Prod.snd⟩⟩

/-- **`zipStep`** — the converse: one step of each machine on the same symbol zips into a product
step, stacks zipped pointwise. -/
def zipStep (a : VStep S₁ G₁) (b : VStep S₂ G₂) : VStep (S₁ × S₂) (G₁ × G₂) :=
  ⟨⟨(a.pre.state, b.pre.state), a.pre.stack.zip b.pre.stack⟩, a.sym,
   ⟨(a.post.state, b.post.state), a.post.stack.zip b.post.stack⟩⟩

/-- A valid product step projects to a valid left-component step. -/
theorem projStep₁_valid (M₁ : Vpa S₁ G₁) (M₂ : Vpa S₂ G₂) (s : VStep (S₁ × S₂) (G₁ × G₂))
    (h : stepValid (prodVpa M₁ M₂) s) : stepValid M₁ (projStep₁ s) := by
  cases hs : s.sym with
  | op =>
    simp only [stepValid, classOf, hs, prodVpa] at h
    obtain ⟨γ, ⟨h₁, _⟩, hst⟩ := h
    simp only [stepValid, projStep₁, classOf, hs]
    exact ⟨γ.1, h₁, by rw [hst, List.map_cons]⟩
  | cl =>
    simp only [stepValid, classOf, hs, prodVpa] at h
    obtain ⟨γ, rest, ⟨h₁, _⟩, hpre, hpost⟩ := h
    simp only [stepValid, projStep₁, classOf, hs]
    exact ⟨γ.1, rest.map Prod.fst, h₁, by rw [hpre, List.map_cons], by rw [hpost]⟩
  | dat =>
    simp only [stepValid, classOf, hs, prodVpa] at h
    simp only [stepValid, projStep₁, classOf, hs]
    exact ⟨h.1.1, by rw [h.2]⟩

/-- A valid product step projects to a valid right-component step. -/
theorem projStep₂_valid (M₁ : Vpa S₁ G₁) (M₂ : Vpa S₂ G₂) (s : VStep (S₁ × S₂) (G₁ × G₂))
    (h : stepValid (prodVpa M₁ M₂) s) : stepValid M₂ (projStep₂ s) := by
  cases hs : s.sym with
  | op =>
    simp only [stepValid, classOf, hs, prodVpa] at h
    obtain ⟨γ, ⟨_, h₂⟩, hst⟩ := h
    simp only [stepValid, projStep₂, classOf, hs]
    exact ⟨γ.2, h₂, by rw [hst, List.map_cons]⟩
  | cl =>
    simp only [stepValid, classOf, hs, prodVpa] at h
    obtain ⟨γ, rest, ⟨_, h₂⟩, hpre, hpost⟩ := h
    simp only [stepValid, projStep₂, classOf, hs]
    exact ⟨γ.2, rest.map Prod.snd, h₂, by rw [hpre, List.map_cons], by rw [hpost]⟩
  | dat =>
    simp only [stepValid, classOf, hs, prodVpa] at h
    simp only [stepValid, projStep₂, classOf, hs]
    exact ⟨h.1.2, by rw [h.2]⟩

/-- **`zipStep_valid`** — THE synchronization lemma: two valid component steps on the SAME symbol
zip into a valid product step. No stack-height side condition is needed — on a call both push (the
zipped stack gains one pair), on a return both pop (it loses one), on an internal both stand still.
The class-driven discipline forces the lockstep; this is `stack_height_input_determined` acting
constructively. -/
theorem zipStep_valid (M₁ : Vpa S₁ G₁) (M₂ : Vpa S₂ G₂) (a : VStep S₁ G₁) (b : VStep S₂ G₂)
    (hsym : a.sym = b.sym) (ha : stepValid M₁ a) (hb : stepValid M₂ b) :
    stepValid (prodVpa M₁ M₂) (zipStep a b) := by
  cases hs : a.sym with
  | op =>
    have hs' : b.sym = Sym.op := by rw [← hsym]; exact hs
    simp only [stepValid, classOf, hs] at ha
    simp only [stepValid, classOf, hs'] at hb
    obtain ⟨γ₁, hc₁, hst₁⟩ := ha
    obtain ⟨γ₂, hc₂, hst₂⟩ := hb
    simp only [stepValid, zipStep, classOf, hs, prodVpa]
    exact ⟨(γ₁, γ₂), ⟨hc₁, hc₂⟩, by rw [hst₁, hst₂, List.zip_cons_cons]⟩
  | cl =>
    have hs' : b.sym = Sym.cl := by rw [← hsym]; exact hs
    simp only [stepValid, classOf, hs] at ha
    simp only [stepValid, classOf, hs'] at hb
    obtain ⟨γ₁, r₁, hr₁, hpre₁, hpost₁⟩ := ha
    obtain ⟨γ₂, r₂, hr₂, hpre₂, hpost₂⟩ := hb
    simp only [stepValid, zipStep, classOf, hs, prodVpa]
    exact ⟨(γ₁, γ₂), r₁.zip r₂, ⟨hr₁, hr₂⟩, by rw [hpre₁, hpre₂, List.zip_cons_cons],
      by rw [hpost₁, hpost₂]⟩
  | dat =>
    have hs' : b.sym = Sym.dat := by rw [← hsym]; exact hs
    simp only [stepValid, classOf, hs] at ha
    simp only [stepValid, classOf, hs'] at hb
    simp only [stepValid, zipStep, classOf, hs, prodVpa]
    exact ⟨⟨ha.1, hb.1⟩, by rw [ha.2, hb.2]⟩

/-- Projections preserve the chaining relation. -/
theorem projStep₁_R {a b : VStep (S₁ × S₂) (G₁ × G₂)} (h : R_vpa a b) :
    R_vpa (projStep₁ a) (projStep₁ b) := by
  have h' : b.pre = a.post := h
  show (projStep₁ b).pre = (projStep₁ a).post
  simp only [projStep₁]
  rw [h']

/-- Projections preserve the chaining relation (right). -/
theorem projStep₂_R {a b : VStep (S₁ × S₂) (G₁ × G₂)} (h : R_vpa a b) :
    R_vpa (projStep₂ a) (projStep₂ b) := by
  have h' : b.pre = a.post := h
  show (projStep₂ b).pre = (projStep₂ a).post
  simp only [projStep₂]
  rw [h']

/-- Zipping preserves the chaining relation. -/
theorem zipStep_R {a₁ a₂ : VStep S₁ G₁} {b₁ b₂ : VStep S₂ G₂}
    (ha : R_vpa a₁ a₂) (hb : R_vpa b₁ b₂) : R_vpa (zipStep a₁ b₁) (zipStep a₂ b₂) := by
  have ha' : a₂.pre = a₁.post := ha
  have hb' : b₂.pre = b₁.post := hb
  show (zipStep a₂ b₂).pre = (zipStep a₁ b₁).post
  simp only [zipStep]
  rw [ha', hb']

/-- Mapping a chain-preserving function over a run preserves `vchained`. -/
theorem vchained_map {State Gamma State' Gamma' : Type u}
    (f : VStep State Gamma → VStep State' Gamma')
    (hf : ∀ a b : VStep State Gamma, R_vpa a b → R_vpa (f a) (f b)) :
    ∀ run : List (VStep State Gamma), vchained run → vchained (run.map f) := by
  intro run
  induction run with
  | nil => intro _; trivial
  | cons a t ih =>
    intro h
    cases t with
    | nil => trivial
    | cons b rest =>
      obtain ⟨hab, htl⟩ := h
      exact ⟨hf a b hab, ih htl⟩

/-- Zipping two chained runs yields a chained run. -/
theorem vchained_zipWith :
    ∀ (r₁ : List (VStep S₁ G₁)) (r₂ : List (VStep S₂ G₂)),
      vchained r₁ → vchained r₂ → vchained (List.zipWith zipStep r₁ r₂) := by
  intro r₁
  induction r₁ with
  | nil => intro r₂ _ _; trivial
  | cons a₁ t₁ ih =>
    intro r₂ h₁ h₂
    cases r₂ with
    | nil => trivial
    | cons b₁ u =>
      cases t₁ with
      | nil => trivial
      | cons a₂ t =>
        cases u with
        | nil => trivial
        | cons b₂ v =>
          obtain ⟨hra, hta⟩ := h₁
          obtain ⟨hrb, htb⟩ := h₂
          exact ⟨zipStep_R hra hrb, ih (b₂ :: v) hta htb⟩

/-- Zipping two valid runs on the same word yields a valid run. -/
theorem zipWith_valid (M₁ : Vpa S₁ G₁) (M₂ : Vpa S₂ G₂) :
    ∀ (r₁ : List (VStep S₁ G₁)) (r₂ : List (VStep S₂ G₂)),
      r₁.map (fun s => s.sym) = r₂.map (fun s => s.sym) →
      (∀ s ∈ r₁, stepValid M₁ s) → (∀ s ∈ r₂, stepValid M₂ s) →
      ∀ s ∈ List.zipWith zipStep r₁ r₂, stepValid (prodVpa M₁ M₂) s := by
  intro r₁
  induction r₁ with
  | nil => intro r₂ _ _ _ s hs; simp at hs
  | cons a t ih =>
    intro r₂ hword hv₁ hv₂ s hs
    cases r₂ with
    | nil => simp at hs
    | cons b u =>
      simp only [List.map_cons, List.cons.injEq] at hword
      rw [List.zipWith_cons_cons] at hs
      rcases List.mem_cons.mp hs with h | h
      · subst h
        exact zipStep_valid M₁ M₂ a b hword.1 (hv₁ a (by simp)) (hv₂ b (by simp))
      · exact ih u hword.2 (fun x hx => hv₁ x (List.mem_cons_of_mem a hx))
          (fun x hx => hv₂ x (List.mem_cons_of_mem b hx)) s h

/-- The zipped run reads the left run's word. -/
theorem zipWith_map_sym :
    ∀ (r₁ : List (VStep S₁ G₁)) (r₂ : List (VStep S₂ G₂)),
      r₁.length = r₂.length →
      (List.zipWith zipStep r₁ r₂).map (fun s => s.sym) = r₁.map (fun s => s.sym) := by
  intro r₁
  induction r₁ with
  | nil => intro r₂ _; rfl
  | cons a t ih =>
    intro r₂ hlen
    cases r₂ with
    | nil =>
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    | cons b u =>
      have hlen' : t.length = u.length := by
        simp only [List.length_cons] at hlen; omega
      simp only [List.zipWith_cons_cons, List.map_cons, zipStep, ih u hlen']

/-- `getLast?` commutes with `zipWith` on equal-length lists (both `some`). -/
theorem getLast?_zipWith {A B C : Type u} (f : A → B → C) :
    ∀ (r₁ : List A) (r₂ : List B) (a : A) (b : B),
      r₁.length = r₂.length → r₁.getLast? = some a → r₂.getLast? = some b →
      (List.zipWith f r₁ r₂).getLast? = some (f a b) := by
  intro r₁
  induction r₁ with
  | nil => intro r₂ a b _ ha _; simp at ha
  | cons x t ih =>
    intro r₂ a b hlen ha hb
    cases r₂ with
    | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
    | cons y u =>
      cases t with
      | nil =>
        cases u with
        | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at ha hb
          subst ha; subst hb
          simp
        | cons z v => simp only [List.length_cons, List.length_nil] at hlen; omega
      | cons p q =>
        cases u with
        | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
        | cons z v =>
          have hlen' : (p :: q).length = (z :: v).length := by
            simp only [List.length_cons] at hlen ⊢; omega
          rw [List.getLast?_cons_cons] at ha hb
          rw [List.zipWith_cons_cons, List.zipWith_cons_cons, List.getLast?_cons_cons,
            ← List.zipWith_cons_cons]
          exact ih (z :: v) a b hlen' ha hb

/-- **`prodVpa_lang`** — INTERSECTION, both directions: the product VPA's language is exactly
`L(M₁) ∩ L(M₂)`. Forward: project the product run componentwise. Backward: the two accepting runs
read the same word, so the class-driven discipline moves their stacks in lockstep and the runs ZIP
into one product run — no height side conditions, the visibly-pushdown synchronization at work.
(For general PDAs this direction is FALSE: CFLs are not closed under intersection.) -/
theorem prodVpa_lang (M₁ : Vpa S₁ G₁) (M₂ : Vpa S₂ G₂) (q₁ : S₁) (q₂ : S₂)
    (acc₁ : S₁ → Prop) (acc₂ : S₂ → Prop) (w : List Sym) :
    Lang (prodVpa M₁ M₂) (q₁, q₂) (fun p => acc₁ p.1 ∧ acc₂ p.2) w ↔
      (Lang M₁ q₁ acc₁ w ∧ Lang M₂ q₂ acc₂ w) := by
  constructor
  · rintro ⟨run, ⟨first, last, hh, hl, hq0, hs0, hacc, hsf, hval, hch⟩, hw⟩
    constructor
    · refine ⟨run.map projStep₁,
        ⟨projStep₁ first, projStep₁ last, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [List.head?_map, hh]; rfl
      · rw [List.getLast?_map, hl]; rfl
      · simp only [projStep₁, hq0]
      · simp only [projStep₁, hs0, List.map_nil]
      · exact hacc.1
      · simp only [projStep₁, hsf, List.map_nil]
      · intro s hs
        obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
        exact projStep₁_valid M₁ M₂ s' (hval s' hs')
      · exact vchained_map projStep₁ (fun a b h => projStep₁_R h) run hch
      · rw [List.map_map]
        exact hw
    · refine ⟨run.map projStep₂,
        ⟨projStep₂ first, projStep₂ last, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [List.head?_map, hh]; rfl
      · rw [List.getLast?_map, hl]; rfl
      · simp only [projStep₂, hq0]
      · simp only [projStep₂, hs0, List.map_nil]
      · exact hacc.2
      · simp only [projStep₂, hsf, List.map_nil]
      · intro s hs
        obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
        exact projStep₂_valid M₁ M₂ s' (hval s' hs')
      · exact vchained_map projStep₂ (fun a b h => projStep₂_R h) run hch
      · rw [List.map_map]
        exact hw
  · rintro ⟨⟨r₁, ⟨f₁, l₁, hh₁, hl₁, hq₁, hs₁, ha₁, hsf₁, hv₁, hc₁⟩, hw₁⟩,
            ⟨r₂, ⟨f₂, l₂, hh₂, hl₂, hq₂, hs₂, ha₂, hsf₂, hv₂, hc₂⟩, hw₂⟩⟩
    have hword : r₁.map (fun s => s.sym) = r₂.map (fun s => s.sym) := by rw [hw₁, hw₂]
    have hlen : r₁.length = r₂.length := by
      simpa using congrArg List.length hword
    refine ⟨List.zipWith zipStep r₁ r₂,
      ⟨zipStep f₁ f₂, zipStep l₁ l₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · cases r₁ with
      | nil => simp at hh₁
      | cons x t =>
        cases r₂ with
        | nil => simp at hh₂
        | cons y u =>
          simp only [List.head?_cons, Option.some.injEq] at hh₁ hh₂
          subst hh₁; subst hh₂
          rfl
    · exact getLast?_zipWith zipStep r₁ r₂ l₁ l₂ hlen hl₁ hl₂
    · simp only [zipStep, hq₁, hq₂]
    · simp only [zipStep, hs₁, hs₂, List.zip_nil_right]
    · exact ⟨ha₁, ha₂⟩
    · simp only [zipStep, hsf₁, hsf₂, List.zip_nil_right]
    · exact zipWith_valid M₁ M₂ r₁ r₂ hword hv₁ hv₂
    · exact vchained_zipWith r₁ r₂ hc₁ hc₂
    · rw [zipWith_map_sym r₁ r₂ hlen, hw₁]

#assert_axioms prodVpa_lang

/-! ## The universe of acceptance — every accepted word is non-empty and well-matched.

These pin the RELATIVE universe the named complement must live in. -/

/-- The empty word is never accepted: `VpaAccepts` demands a non-empty run. -/
theorem lang_not_nil {State Gamma : Type u} (M : Vpa State Gamma) (q₀ : State)
    (accept : State → Prop) : ¬ Lang M q₀ accept ([] : List Sym) := by
  rintro ⟨run, ⟨first, last, hh, _, _, _, _, _, _, _⟩, hw⟩
  cases run with
  | nil => simp at hh
  | cons a t => simp at hw

/-- Every accepted word has net height 0 — all calls matched. Direct corollary of `run_height`
with empty stacks at both ends. -/
theorem lang_wordDelta_zero {State Gamma : Type u} (M : Vpa State Gamma) (q₀ : State)
    (accept : State → Prop) (w : List Sym) (h : Lang M q₀ accept w) : wordDelta w = 0 := by
  obtain ⟨run, ⟨first, last, hh, hl, hq0, hs0, haccs, hsf, hval, hch⟩, hw⟩ := h
  have hgt := run_height M run hval hch first last hh hl
  rw [hs0, hsf] at hgt
  simp only [List.length_nil, Nat.cast_zero, zero_add] at hgt
  rw [← hw, ← runDelta_eq_wordDelta run]
  omega

/-- `vchained` survives `take` — a prefix of a chained run is chained. -/
theorem vchained_take {State Gamma : Type u} :
    ∀ (run : List (VStep State Gamma)) (n : ℕ), vchained run → vchained (run.take n) := by
  intro run
  induction run with
  | nil => intro n _; rw [List.take_nil]; trivial
  | cons a t ih =>
    intro n h
    cases n with
    | zero => trivial
    | succ m =>
      cases t with
      | nil => rw [List.take_succ_cons, List.take_nil]; trivial
      | cons b rest =>
        cases m with
        | zero => trivial
        | succ k =>
          obtain ⟨hab, htl⟩ := h
          exact ⟨hab, ih (k + 1) htl⟩

/-- A non-empty prefix of a run keeps the run's head. -/
theorem head?_take {A : Type u} : ∀ (l : List A) (k : ℕ), l.take k ≠ [] → (l.take k).head? = l.head?
  | [], k, h => by rw [List.take_nil] at h; exact absurd rfl h
  | _ :: _, 0, h => absurd rfl h
  | _ :: _, _ + 1, _ => rfl

/-- Every non-empty list has a `getLast?`. -/
theorem exists_getLast? {A : Type u} : ∀ (l : List A), l ≠ [] → ∃ a, l.getLast? = some a
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.getLast?_singleton⟩
  | a :: b :: t, _ =>
    let ⟨x, hx⟩ := exists_getLast? (b :: t) (List.cons_ne_nil b t)
    ⟨x, by rw [List.getLast?_cons_cons]; exact hx⟩

/-- **`lang_wellMatched`** — every accepted word is WELL-MATCHED: net height 0 AND every prefix
non-negative. The prefix bound is `run_height` on the truncated run: the height after any prefix IS
a stack length, hence ≥ 0. So `Lang M ⊆ WellMatched` for EVERY machine of this acceptance shape —
absolute complement is unreachable, and the complement target below is stated relative to
`WellMatched`. -/
theorem lang_wellMatched {State Gamma : Type u} (M : Vpa State Gamma) (q₀ : State)
    (accept : State → Prop) (w : List Sym) (h : Lang M q₀ accept w) : WellMatched w := by
  refine ⟨lang_wordDelta_zero M q₀ accept w h, ?_⟩
  obtain ⟨run, ⟨first, last, hh, hl, hq0, hs0, haccs, hsf, hval, hch⟩, hw⟩ := h
  intro p hp
  obtain ⟨tail, ht⟩ := hp
  have hpk : w.take p.length = p := by rw [← ht, List.take_left]
  rw [← hpk]
  by_cases hnil : run.take p.length = []
  · have hwn : w.take p.length = [] := by
      rw [← hw, ← List.map_take, hnil, List.map_nil]
    rw [hwn]
    simp [wordDelta]
  · obtain ⟨lastk, hlk⟩ := exists_getLast? (run.take p.length) hnil
    have hheadk : (run.take p.length).head? = some first :=
      (head?_take run p.length hnil).trans hh
    have hvalk : ∀ s ∈ run.take p.length, stepValid M s :=
      fun s hs => hval s (List.take_subset p.length run hs)
    have hchk := vchained_take run p.length hch
    have hgt := run_height M (run.take p.length) hvalk hchk first lastk hheadk hlk
    rw [hs0] at hgt
    simp only [List.length_nil, Nat.cast_zero, zero_add] at hgt
    have hde : runDelta (run.take p.length) = wordDelta (w.take p.length) := by
      rw [runDelta_eq_wordDelta (run.take p.length), List.map_take, hw]
    rw [hde] at hgt
    omega

#assert_axioms lang_not_nil
#assert_axioms lang_wordDelta_zero
#assert_axioms lang_wellMatched

/-! ## The decision pipeline — equivalence reduces to two emptiness checks. -/

/-- **`equiv_iff_symmDiff_empty`** — pure-logic glue (no automaton content, stated to fix the
pipeline's SHAPE): two languages agree iff both one-sided differences are empty. With `prodVpa_lang`
(intersection, PROVED above) and `ComplementClosure` (named below), each one-sided difference
`L(M₁) ∩ ∁L(M₂)` is again a VPL on the finite fragment — so decidable equivalence needs exactly the
two named seams: complement and emptiness. -/
theorem equiv_iff_symmDiff_empty (P₁ P₂ : List Sym → Prop) :
    (∀ w, P₁ w ↔ P₂ w) ↔ (¬ ∃ w, P₁ w ∧ ¬ P₂ w) ∧ (¬ ∃ w, P₂ w ∧ ¬ P₁ w) := by
  constructor
  · intro h
    exact ⟨fun ⟨w, h₁, h₂⟩ => h₂ ((h w).mp h₁), fun ⟨w, h₁, h₂⟩ => h₂ ((h w).mpr h₁)⟩
  · rintro ⟨h₁, h₂⟩ w
    constructor
    · intro hw
      by_contra hc
      exact h₁ ⟨w, hw, hc⟩
    · intro hw
      by_contra hc
      exact h₂ ⟨w, hw, hc⟩

#assert_axioms equiv_iff_symmDiff_empty

/-! ## The complement target — stated here, DISCHARGED below (`complement_closure`).

Each guard in the statement is FORCED, not stylistic:
  * `Fintype S`/`Fintype G` on BOTH sides — over unrestricted (infinite-state, `Prop`-transition)
    machines every subset of the accepted-word universe is some machine's language, so unrestricted
    "closure" would be classically trivial. The finite fragment is where the statement has content
    (and is where Alur–Madhusudan prove it, via determinization over summary-pair state spaces —
    which stays finite).
  * relative to `WellMatched` — `lang_wellMatched`: NO machine of this acceptance shape accepts an
    ill-matched word, so an absolute complement (which would have to) is unreachable.
  * `w ≠ []` — `lang_not_nil`: NO machine accepts the empty word (runs are non-empty), and `[]` is
    well-matched, so the empty word must be exempted or the target is falsified at `w = []`. -/

/-- **`ComplementClosure`** — the precisely-stated complement target: for every finite-fragment
VPA there is a finite-fragment VPA recognizing exactly the non-empty well-matched words the
original rejects. DISCHARGED below (`complement_closure`) by the Alur–Madhusudan route: subset
construction over summary sets (`detVpa`, deterministic by construction) + accept-flip
(`compAcc`), with `detVpa_complement` proving exactly this conclusion. The def is kept as the
named statement `decidableEquivOfComplements` was scoped against. -/
def ComplementClosure : Prop :=
  ∀ (S G : Type) (_ : Fintype S) (_ : Fintype G) (M : Vpa S G) (q₀ : S) (acc : S → Prop),
    ∃ (S' G' : Type) (_ : Fintype S') (_ : Fintype G') (M' : Vpa S' G') (q₀' : S')
      (acc' : S' → Prop),
      ∀ w : List Sym, w ≠ [] →
        (Lang M' q₀' acc' w ↔ (WellMatched w ∧ ¬ Lang M q₀ acc w))

/-! ## NAMED SEAM 2 — the emptiness decision (deliberately NOT a `Prop`).

Every Prop-level phrasing of "emptiness is decidable" we examined is a CLASSICAL TAUTOLOGY, so
stating one and later "proving" it would launder vacuity as progress:

  * `∀ M, (∃ w, Lang M … w) ∨ ¬(∃ w, Lang M … w)` — excluded middle.
  * `∀ M, ∃ b : Bool, b = true ↔ (∃ w, Lang M … w)` — `by_cases` on the right side.
  * `∀ M, ∃ B : ℕ, (∃ w, Lang M … w) → ∃ w, Lang M … w ∧ w.length ≤ B` — if the language is
    non-empty, classically pick any accepted word and let `B` be its length.
  * even `∃ f : ℕ → ℕ → ℕ, ∀ M, …bound by f (card S) (card G)…` — for fixed finite cards there
    are (classically) only finitely many transition relations, so a sup exists without content.

The genuine artifact is therefore one of:
  (a) a CONCRETE bound function `f` (from the VPA→CFG translation's derivation-length pumping
      bound) with its proof — real combinatorial content, usable with a bounded search; or
  (b) a COMPUTABLE `Decidable` instance for `∃ w, Lang M q₀ acc w` (for `DecidableEq`/decidable-
      transition machines), via the standard reachable-summary saturation — real algorithmic
      content.
Route (b) is DELIVERED below (`sat` / `wm_iff_mem_sat` / `decidableLangNonempty`): the
reachable-summary relation `WM` is computed by finite `Finset` saturation — a function you can run
(`#guard`-exercised on concrete machines in `ComputeReference`) — and is proved sound AND complete
against `Lang`. No `em`, no `by_cases` on the language: the decision is the saturation's output.
Combined with `prodVpa_lang` (proved) + `equiv_iff_symmDiff_empty` (proved), it yields
`decidableEquivOfComplements` — decidable template equivalence with `ComplementClosure` as the ONE
remaining explicit hypothesis (taken as an ARGUMENT, never asserted). -/

/-! ## THE EMPTINESS DECISION — computable, by well-matched summary saturation.

Everything from here to `decidableLangNonempty` is route (b) of the analysis above. The shape:

    `Path`   — non-empty valid step sequences between configs (the structural face of a run)
    `WM`     — the SUMMARY relation: `WM M q q'` = the machine can go from `(q, [])` to `(q', [])`
               reading some (necessarily non-empty, well-matched) word. Its four rules are the
               Alur–Madhusudan saturation rules: internal step / call-return wrap (empty or
               summarized inner) / composition.
    `Unw`    — the STRENGTHENED induction target for completeness: what a path from `(q, l)` down
               to empty stack looks like, level by level. This is the trick that eliminates the
               "find the matching return" list surgery: generalizing over the stack makes the
               decomposition fall out of the step case analysis.
    `sat`    — the COMPUTATION: iterate one saturation round `card (S × S)` times from `∅` over
               `Finset (S × S)`. Inflationary on a finite lattice ⇒ fixpoint (`iterate_fixpoint`,
               a cardinality pigeonhole — no choice of witness, just arithmetic).
    `wm_iff_mem_sat` / `lang_nonempty_iff_wm` — soundness + completeness, tying the computed set
               to the actual `Lang`.

The `Decidable` instance at the end is `decidable_of_iff` off a `Finset` membership — a value the
kernel can (and, in `ComputeReference`, does) evaluate. -/

section Emptiness

variable {S G : Type u}

/-- **`Path M c c'`** — a NON-EMPTY sequence of `stepValid` steps from config `c` to config `c'`,
as a structural recursion (one step, or a step followed by a path). `path_run` / `run_path` prove
it equivalent to the list-of-`VStep` runs `VpaAccepts` quantifies over; the structural form is what
the emptiness induction wants. -/
inductive Path (M : Vpa S G) : Config S G → Config S G → Prop
  | single {c c' : Config S G} (sym : Sym) (h : stepValid M ⟨c, sym, c'⟩) : Path M c c'
  | cons {c c' c'' : Config S G} (sym : Sym) (h : stepValid M ⟨c, sym, c'⟩)
      (tail : Path M c' c'') : Path M c c''

/-- Paths concatenate. -/
theorem Path.trans {M : Vpa S G} : ∀ {c c' c'' : Config S G},
    Path M c c' → Path M c' c'' → Path M c c''
  | _, _, _, .single sym h, h₂ => .cons sym h h₂
  | _, _, _, .cons sym h tail, h₂ => .cons sym h (tail.trans h₂)

/-- Append `γ` at the BOTTOM of a config's stack. -/
def liftConfig (γ : G) (c : Config S G) : Config S G := ⟨c.state, c.stack ++ [γ]⟩

/-- The class-driven discipline only ever touches the TOP of the stack, so validity survives
appending a symbol at the BOTTOM — the per-step face of running a well-matched segment one level
down inside an open call. -/
theorem stepValid_lift {M : Vpa S G} (γ : G) {c c' : Config S G} {sym : Sym}
    (h : stepValid M ⟨c, sym, c'⟩) :
    stepValid M ⟨liftConfig γ c, sym, liftConfig γ c'⟩ := by
  cases sym with
  | op =>
    simp only [stepValid, classOf] at h ⊢
    obtain ⟨γ', hc, hst⟩ := h
    exact ⟨γ', hc, by simp [liftConfig, hst]⟩
  | cl =>
    simp only [stepValid, classOf] at h ⊢
    obtain ⟨γ', rest, hr, hpre, hpost⟩ := h
    exact ⟨γ', rest ++ [γ], hr, by simp [liftConfig, hpre], by simp [liftConfig, hpost]⟩
  | dat =>
    simp only [stepValid, classOf] at h ⊢
    exact ⟨h.1, by simp [liftConfig, h.2]⟩

/-- Lift a whole path one stack level down. -/
theorem Path.lift {M : Vpa S G} (γ : G) : ∀ {c c' : Config S G},
    Path M c c' → Path M (liftConfig γ c) (liftConfig γ c')
  | _, _, .single sym h => .single sym (stepValid_lift γ h)
  | _, _, .cons sym h tail => .cons sym (stepValid_lift γ h) (Path.lift γ tail)

/-- **`WM M q q'`** — the well-matched SUMMARY relation: state `q'` is reachable from state `q`
across some non-empty well-matched word (empty stack to empty stack). The four constructors are
exactly the Alur–Madhusudan reachable-summary saturation rules; `wm_iff_mem_sat` below shows the
relation is COMPUTED by finite fixpoint iteration, and `lang_nonempty_iff_wm` that it decides
language non-emptiness. -/
inductive WM (M : Vpa S G) : S → S → Prop
  | int {q q' : S} (h : M.int q Sym.dat q') : WM M q q'
  | wrap0 {q p q' : S} {γ : G} (hc : M.call q Sym.op p γ) (hr : M.ret p Sym.cl q' γ) :
      WM M q q'
  | wrap {q p p' q' : S} {γ : G} (hc : M.call q Sym.op p γ) (hi : WM M p p')
      (hr : M.ret p' Sym.cl q' γ) : WM M q q'
  | comp {q m q' : S} (h₁ : WM M q m) (h₂ : WM M m q') : WM M q q'

/-- SOUNDNESS of the summaries: every `WM M q q'` is realized by an actual path from `(q, [])` to
`(q', [])` — internal rule = one step; wrap = call, (lifted) inner path, return; composition =
concatenation. -/
theorem WM.toPath {M : Vpa S G} {q q' : S} (h : WM M q q') :
    Path M ⟨q, []⟩ ⟨q', []⟩ := by
  induction h with
  | int h => exact .single Sym.dat ⟨h, rfl⟩
  | @wrap0 q p q' γ hc hr =>
    exact .cons (c' := ⟨p, [γ]⟩) Sym.op ⟨γ, hc, rfl⟩
      (.single Sym.cl ⟨γ, [], hr, rfl, rfl⟩)
  | @wrap q p p' q' γ hc hi hr ih =>
    exact .cons (c' := ⟨p, [γ]⟩) Sym.op ⟨γ, hc, rfl⟩
      ((ih.lift γ).trans (.single Sym.cl ⟨γ, [], hr, rfl, rfl⟩))
  | comp h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **`Unw M q l q'`** — the strengthened completeness target: from state `q` with stack `l` the
machine reaches `(q', [])` by a NON-EMPTY valid path, described level-by-level — either the stack
is already empty and the whole path is one well-matched summary, or the top symbol is eventually
popped (after optional well-matched activity) and the rest of the stack unwinds recursively
(`pop`), possibly with the path ending exactly at the final pop (`popLast`). -/
inductive Unw (M : Vpa S G) : S → List G → S → Prop
  | wm {q q' : S} (h : WM M q q') : Unw M q [] q'
  | popLast {q p q' : S} {γ : G} (hpre : q = p ∨ WM M q p) (hr : M.ret p Sym.cl q' γ) :
      Unw M q [γ] q'
  | pop {q p q₁ q' : S} {γ : G} {l : List G} (hpre : q = p ∨ WM M q p)
      (hr : M.ret p Sym.cl q₁ γ) (htail : Unw M q₁ l q') : Unw M q (γ :: l) q'

/-- Prefixing a summary onto an unwind. -/
theorem Unw.prepend {M : Vpa S G} {q p : S} {l : List G} {q' : S}
    (hqp : WM M q p) (h : Unw M p l q') : Unw M q l q' := by
  cases h with
  | wm h' => exact .wm (hqp.comp h')
  | popLast hpre hr =>
    exact .popLast (Or.inr (hpre.elim (fun e => e ▸ hqp) fun w => hqp.comp w)) hr
  | pop hpre hr htail =>
    exact .pop (Or.inr (hpre.elim (fun e => e ▸ hqp) fun w => hqp.comp w)) hr htail

/-- COMPLETENESS core: any path that ends at empty stack unwinds its start stack level-by-level.
Induction on the path, case analysis on the first symbol's class: an internal step prepends a
summary; a call step's pushed symbol must be popped by the induction hypothesis' unwind, and the
call + (summarized) inner + return REASSEMBLE into a `WM` wrap — the matching-return decomposition
with no list surgery; a return step is literally a `pop` node. -/
theorem path_unw {M : Vpa S G} {c c' : Config S G} (h : Path M c c') :
    c'.stack = [] → Unw M c.state c.stack c'.state := by
  induction h with
  | @single a a' sym hs =>
    intro hend
    cases sym with
    | op =>
      simp only [stepValid, classOf] at hs
      obtain ⟨γ, _, hst⟩ := hs
      rw [hend] at hst
      simp at hst
    | cl =>
      simp only [stepValid, classOf] at hs
      obtain ⟨γ, rest, hr, hpre, hpost⟩ := hs
      have hrest : rest = [] := hpost.symm.trans hend
      subst hrest
      rw [hpre]
      exact .popLast (Or.inl rfl) hr
    | dat =>
      simp only [stepValid, classOf] at hs
      have hcs : a.stack = ([] : List G) := hs.2.symm.trans hend
      rw [hcs]
      exact .wm (.int hs.1)
  | @cons a amid a'' sym hs tail ih =>
    intro hend
    have iht := ih hend
    cases sym with
    | op =>
      simp only [stepValid, classOf] at hs
      obtain ⟨γ, hc, hst⟩ := hs
      rw [hst] at iht
      revert iht
      generalize a.stack = cs
      intro iht
      cases iht with
      | popLast hpre hr =>
        exact .wm (hpre.elim (fun e => WM.wrap0 (e ▸ hc) hr) fun w => WM.wrap hc w hr)
      | pop hpre hr htail =>
        exact Unw.prepend
          (hpre.elim (fun e => WM.wrap0 (e ▸ hc) hr) fun w => WM.wrap hc w hr) htail
    | cl =>
      simp only [stepValid, classOf] at hs
      obtain ⟨γ, rest, hr, hpre, hpost⟩ := hs
      rw [hpost] at iht
      rw [hpre]
      exact .pop (Or.inl rfl) hr iht
    | dat =>
      simp only [stepValid, classOf] at hs
      rw [hs.2] at iht
      exact Unw.prepend (WM.int hs.1) iht

/-- COMPLETENESS: a path from `(q, [])` to `(q', [])` yields a summary — with the EMPTY start
stack, `Unw` has only its `wm` constructor, and non-emptiness of the path is what makes the
summary strict (no `q = q'` escape hatch: `lang_not_nil` stays true of the decision). -/
theorem path_wm {M : Vpa S G} {q q' : S} (h : Path M ⟨q, []⟩ ⟨q', []⟩) : WM M q q' := by
  have hu := path_unw h rfl
  cases hu with
  | wm h => exact h

/-- A non-empty, valid, chained run (the `VpaAccepts` shape) is a `Path` from its first `pre` to
its last `post`. -/
theorem run_path (M : Vpa S G) :
    ∀ (run : List (VStep S G)) (first last : VStep S G),
      run.head? = some first → run.getLast? = some last →
      (∀ s ∈ run, stepValid M s) → vchained run → Path M first.pre last.post := by
  intro run
  induction run with
  | nil => intro first last hh _ _ _; simp at hh
  | cons a t ih =>
    intro first last hh hl hval hch
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      exact .single a.sym (hval a (by simp))
    | cons b u =>
      obtain ⟨hR, htail⟩ := hch
      have hl' : (b :: u).getLast? = some last := by
        rw [List.getLast?_cons_cons] at hl; exact hl
      have hb : Path M b.pre last.post :=
        ih b last rfl hl' (fun s hs => hval s (List.mem_cons_of_mem a hs)) htail
      have hbp : b.pre = a.post := hR
      rw [hbp] at hb
      exact .cons a.sym (hval a (by simp)) hb

/-- Conversely, a `Path` is realized by a run of the `VpaAccepts` shape. -/
theorem path_run {M : Vpa S G} {c c' : Config S G} (h : Path M c c') :
    ∃ (run : List (VStep S G)) (first last : VStep S G),
      run.head? = some first ∧ run.getLast? = some last ∧ first.pre = c ∧ last.post = c' ∧
      (∀ s ∈ run, stepValid M s) ∧ vchained run := by
  induction h with
  | @single a a' sym hs =>
    refine ⟨[⟨a, sym, a'⟩], ⟨a, sym, a'⟩, ⟨a, sym, a'⟩, rfl, List.getLast?_singleton, rfl, rfl,
      ?_, trivial⟩
    intro s hs'
    rw [List.mem_singleton] at hs'
    subst hs'
    exact hs
  | @cons a amid a'' sym hs tail ih =>
    obtain ⟨run, first, last, hh, hl, hfp, hlp, hval, hch⟩ := ih
    cases run with
    | nil => simp at hh
    | cons r t =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      refine ⟨⟨a, sym, amid⟩ :: r :: t, ⟨a, sym, amid⟩, last, rfl, ?_, rfl, hlp, ?_, ?_⟩
      · rw [List.getLast?_cons_cons]; exact hl
      · intro s hs'
        rcases List.mem_cons.mp hs' with rfl | hmem
        · exact hs
        · exact hval s hmem
      · exact ⟨hfp, hch⟩

/-- **`lang_nonempty_iff_wm`** — the language is non-empty iff a summary reaches an accepting
state. This is the REDUCTION that makes emptiness decidable: the left side quantifies over all
words and runs; the right side is a relation on the FINITE `S × S` grid. -/
theorem lang_nonempty_iff_wm (M : Vpa S G) (q₀ : S) (acc : S → Prop) :
    (∃ w, Lang M q₀ acc w) ↔ ∃ q' : S, acc q' ∧ WM M q₀ q' := by
  constructor
  · rintro ⟨w, run, ⟨first, last, hh, hl, hq0, hs0, hacc, hsf, hval, hch⟩, -⟩
    refine ⟨last.post.state, hacc, ?_⟩
    have hp := run_path M run first last hh hl hval hch
    have e₁ : first.pre = (⟨q₀, []⟩ : Config S G) := by rw [← hq0, ← hs0]
    have e₂ : last.post = (⟨last.post.state, []⟩ : Config S G) := by rw [← hsf]
    rw [e₁, e₂] at hp
    exact path_wm hp
  · rintro ⟨q', hacc, hwm⟩
    obtain ⟨run, first, last, hh, hl, hfp, hlp, hval, hch⟩ := path_run hwm.toPath
    exact ⟨run.map (fun s => s.sym), run,
      ⟨first, last, hh, hl, by rw [hfp], by rw [hfp], by rw [hlp]; exact hacc, by rw [hlp],
        hval, hch⟩, rfl⟩

#assert_axioms path_wm
#assert_axioms lang_nonempty_iff_wm

/-! ### The computation — `Finset` saturation to a provable fixpoint. -/

section Saturation

variable [DecidableEq S] [Fintype S] [Fintype G] (M : Vpa S G)
variable [∀ q s q' γ, Decidable (M.call q s q' γ)]
variable [∀ q s q' γ, Decidable (M.ret q s q' γ)]
variable [∀ q s q', Decidable (M.int q s q')]

/-- One saturation round: keep everything, add every pair derivable by one `WM` rule from the
current set. A plain computable `Finset` function — the quantifiers range over the FINITE state
and stack-symbol grids, decided by enumeration. -/
def satStep (X : Finset (S × S)) : Finset (S × S) :=
  X ∪ Finset.univ.filter fun qq : S × S =>
    M.int qq.1 Sym.dat qq.2
      ∨ (∃ (p p' : S) (γ : G), M.call qq.1 Sym.op p γ ∧ (p = p' ∨ (p, p') ∈ X)
          ∧ M.ret p' Sym.cl qq.2 γ)
      ∨ (∃ m : S, (qq.1, m) ∈ X ∧ (m, qq.2) ∈ X)

/-- The saturation: iterate the round `card (S × S)` times from `∅`. Enough by the pigeonhole
below — each non-fixpoint round strictly grows a subset of the `card (S × S)`-element grid. -/
def sat : Finset (S × S) := (satStep M)^[Fintype.card (S × S)] ∅

theorem subset_satStep (X : Finset (S × S)) : X ⊆ satStep M X := Finset.subset_union_left

/-- Cardinality pigeonhole: iterating an inflationary `Finset` map on a `Fintype` for
`card α` steps lands on a fixpoint. Pure counting — no choice, no excluded middle on the
underlying predicate. -/
theorem iterate_fixpoint {α : Type u} [DecidableEq α] [Fintype α] (f : Finset α → Finset α)
    (hf : ∀ X, X ⊆ f X) : f (f^[Fintype.card α] ∅) = f^[Fintype.card α] ∅ := by
  have hstab : ∀ k, f (f^[k] ∅) = f^[k] ∅ → ∀ m, f^[k + m] ∅ = f^[k] ∅ := by
    intro k hfix m
    induction m with
    | zero => rfl
    | succ m ih =>
      have he : k + (m + 1) = (k + m) + 1 := by omega
      rw [he, Function.iterate_succ_apply', ih, hfix]
  have hex : ∃ k, k ≤ Fintype.card α ∧ f (f^[k] ∅) = f^[k] ∅ := by
    by_contra hnone
    push Not at hnone
    have hgrow : ∀ k, k ≤ Fintype.card α + 1 → k ≤ (f^[k] ∅).card := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
        intro hk
        have h₁ : k ≤ (f^[k] ∅).card := ih (by omega)
        have hss : f^[k] ∅ ⊂ f^[k + 1] ∅ := by
          rw [Function.iterate_succ_apply']
          exact (hf _).ssubset_of_ne (Ne.symm (hnone k (by omega)))
        have := Finset.card_lt_card hss
        omega
    have hbig := hgrow (Fintype.card α + 1) le_rfl
    have hle : (f^[Fintype.card α + 1] ∅).card ≤ Fintype.card α := Finset.card_le_univ _
    omega
  obtain ⟨k, hkN, hfix⟩ := hex
  have hNk : f^[Fintype.card α] ∅ = f^[k] ∅ := by
    have h := hstab k hfix (Fintype.card α - k)
    rwa [Nat.add_sub_cancel' hkN] at h
  rw [hNk, hfix]

theorem satStep_sat_eq : satStep M (sat M) = sat M :=
  iterate_fixpoint (satStep M) (subset_satStep M)

/-- Saturation SOUNDNESS: everything the iteration puts in is a real summary. -/
theorem wm_of_mem_satIter :
    ∀ (n : ℕ) (qq : S × S), qq ∈ (satStep M)^[n] ∅ → WM M qq.1 qq.2 := by
  intro n
  induction n with
  | zero => intro qq h; simp at h
  | succ n ih =>
    intro qq h
    rw [Function.iterate_succ_apply'] at h
    simp only [satStep] at h
    rcases Finset.mem_union.mp h with h | h
    · exact ih qq h
    · rcases (Finset.mem_filter.mp h).2 with hint | ⟨p, p', γ, hc, hmid, hr⟩ | ⟨m, h₁, h₂⟩
      · exact .int hint
      · rcases hmid with rfl | hX
        · exact .wrap0 hc hr
        · exact .wrap hc (ih (p, p') hX) hr
      · exact .comp (ih (qq.1, m) h₁) (ih (m, qq.2) h₂)

/-- Saturation COMPLETENESS: every summary is in the computed fixpoint — each `WM` rule is one
round of `satStep`, and `sat` absorbs a round. -/
theorem mem_sat_of_wm {q q' : S} (h : WM M q q') : (q, q') ∈ sat M := by
  induction h with
  | int h =>
    rw [← satStep_sat_eq M]
    simp only [satStep]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h⟩)
  | @wrap0 q p q' γ hc hr =>
    rw [← satStep_sat_eq M]
    simp only [satStep]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Or.inr (Or.inl ⟨p, p, γ, hc, Or.inl rfl, hr⟩)⟩)
  | @wrap q p p' q' γ hc hi hr ih =>
    rw [← satStep_sat_eq M]
    simp only [satStep]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Or.inr (Or.inl ⟨p, p', γ, hc, Or.inr ih, hr⟩)⟩)
  | @comp q m q' h₁ h₂ ih₁ ih₂ =>
    rw [← satStep_sat_eq M]
    simp only [satStep]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Or.inr (Or.inr ⟨m, ih₁, ih₂⟩)⟩)

/-- **`wm_iff_mem_sat`** — the summary relation IS the computed `Finset`. -/
theorem wm_iff_mem_sat (q q' : S) : WM M q q' ↔ (q, q') ∈ sat M :=
  ⟨mem_sat_of_wm M, fun h => wm_of_mem_satIter M _ (q, q') h⟩

#assert_axioms wm_iff_mem_sat

/-- **THE ARTIFACT** — a COMPUTABLE `Decidable` instance for language non-emptiness on the finite
fragment: run the saturation, scan the accepting states. `decidable_of_iff` off a `Finset`
membership — the kernel evaluates it (see `ComputeReference`). Not an `em` phrasing: the closing
note's vacuity analysis is answered by a function, not a tautology. -/
instance decidableLangNonempty (q₀ : S) (acc : S → Prop) [DecidablePred acc] :
    Decidable (∃ w, Lang M q₀ acc w) :=
  decidable_of_iff (∃ q' : S, acc q' ∧ (q₀, q') ∈ sat M) <| by
    rw [lang_nonempty_iff_wm M q₀ acc]
    exact exists_congr fun q' => and_congr_right fun _ => (wm_iff_mem_sat M q₀ q').symm

/-- The EMPTINESS decision, in the form the boolean-closure pipeline consumes. -/
instance decidableLangEmpty (q₀ : S) (acc : S → Prop) [DecidablePred acc] :
    Decidable (∀ w, ¬ Lang M q₀ acc w) :=
  decidable_of_iff (¬ ∃ w, Lang M q₀ acc w) not_exists

end Saturation

end Emptiness

/-! ## Non-vacuity — the intersection theorem on the concrete Dyck reference machine. -/

namespace Reference

open Dregg2.Crypto.VpaAsCert.Reference

/-- `op op cl cl` (the Dyck circuit's `n = 2` bracket chain) is in the language of the PRODUCT of
the reference bracket VPA with itself — routed through `prodVpa_lang`'s backward (zip) direction on
the concrete `run2`, so the synchronized product construction is exercised on a real machine. -/
theorem word2_in_prod :
    Lang (prodVpa chainVpa chainVpa) (0, 0) (fun p => p.1 = 0 ∧ p.2 = 0)
      [Sym.op, Sym.op, Sym.cl, Sym.cl] :=
  (prodVpa_lang chainVpa chainVpa 0 0 (· = 0) (· = 0) _).mpr
    ⟨⟨run2, run2_accepts, rfl⟩, ⟨run2, run2_accepts, rfl⟩⟩

/-- And forward: the product membership projects back to membership in each component. -/
theorem word2_components :
    Lang chainVpa 0 (· = 0) [Sym.op, Sym.op, Sym.cl, Sym.cl] ∧
    Lang chainVpa 0 (· = 0) [Sym.op, Sym.op, Sym.cl, Sym.cl] :=
  (prodVpa_lang chainVpa chainVpa 0 0 (· = 0) (· = 0) _).mp word2_in_prod

#assert_axioms word2_in_prod
#assert_axioms word2_components

end Reference

/-! ## Decidable equivalence, assembled to the ONE remaining seam.

`prodVpa` preserves decidability of transitions (conjunctions of decidable components), so the
emptiness decision above applies to the product machines the symmetric-difference pipeline
builds. What follows assembles `equiv_iff_symmDiff_empty` + `prodVpa_lang` + `sat` into a
DECIDABLE equivalence — with the complement machines taken as explicit ARGUMENTS carrying their
correctness proofs. That is precisely the `ComplementClosure` seam and nothing else: supply the
Alur–Madhusudan determinize-and-flip construction and `decidableEquivOfComplements` finishes the
job computably. -/

section ProdDecidable

variable {M₁ : Vpa S₁ G₁} {M₂ : Vpa S₂ G₂}

instance [∀ q s q' γ, Decidable (M₁.call q s q' γ)] [∀ q s q' γ, Decidable (M₂.call q s q' γ)]
    (q : S₁ × S₂) (s : Sym) (q' : S₁ × S₂) (γ : G₁ × G₂) :
    Decidable ((prodVpa M₁ M₂).call q s q' γ) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance [∀ q s q' γ, Decidable (M₁.ret q s q' γ)] [∀ q s q' γ, Decidable (M₂.ret q s q' γ)]
    (q : S₁ × S₂) (s : Sym) (q' : S₁ × S₂) (γ : G₁ × G₂) :
    Decidable ((prodVpa M₁ M₂).ret q s q' γ) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance [∀ q s q', Decidable (M₁.int q s q')] [∀ q s q', Decidable (M₂.int q s q')]
    (q : S₁ × S₂) (s : Sym) (q' : S₁ × S₂) :
    Decidable ((prodVpa M₁ M₂).int q s q') :=
  inferInstanceAs (Decidable (_ ∧ _))

end ProdDecidable

/-- **`decidableEquivOfComplements`** — decidable template equivalence, modulo EXACTLY the
`ComplementClosure` seam: given complement machines `C₁`, `C₂` (with their correctness proofs
`hC₁`, `hC₂` — the conclusion `ComplementClosure` promises, taken here as hypotheses), language
equivalence of `M₁` and `M₂` is DECIDED by running the summary saturation on the two product
machines `M₁ ⊗ C₂` and `M₂ ⊗ C₁`. The `w ≠ []` and `WellMatched` guards in the complement
statement are discharged by `lang_not_nil` / `lang_wellMatched`: any symmetric-difference witness
is automatically non-empty and well-matched, so the guarded complement suffices. Computable end to
end — the only non-computational content is the two correctness proofs, which live in `Prop`. -/
def decidableEquivOfComplements {T₁ H₁ T₂ H₂ : Type u}
    [DecidableEq S₁] [Fintype S₁] [Fintype G₁] [DecidableEq S₂] [Fintype S₂] [Fintype G₂]
    [DecidableEq T₁] [Fintype T₁] [Fintype H₁] [DecidableEq T₂] [Fintype T₂] [Fintype H₂]
    (M₁ : Vpa S₁ G₁) (q₁ : S₁) (acc₁ : S₁ → Prop) [DecidablePred acc₁]
    (M₂ : Vpa S₂ G₂) (q₂ : S₂) (acc₂ : S₂ → Prop) [DecidablePred acc₂]
    (C₁ : Vpa T₁ H₁) (c₁ : T₁) (accC₁ : T₁ → Prop) [DecidablePred accC₁]
    (C₂ : Vpa T₂ H₂) (c₂ : T₂) (accC₂ : T₂ → Prop) [DecidablePred accC₂]
    [∀ q s q' γ, Decidable (M₁.call q s q' γ)] [∀ q s q' γ, Decidable (M₁.ret q s q' γ)]
    [∀ q s q', Decidable (M₁.int q s q')]
    [∀ q s q' γ, Decidable (M₂.call q s q' γ)] [∀ q s q' γ, Decidable (M₂.ret q s q' γ)]
    [∀ q s q', Decidable (M₂.int q s q')]
    [∀ q s q' γ, Decidable (C₁.call q s q' γ)] [∀ q s q' γ, Decidable (C₁.ret q s q' γ)]
    [∀ q s q', Decidable (C₁.int q s q')]
    [∀ q s q' γ, Decidable (C₂.call q s q' γ)] [∀ q s q' γ, Decidable (C₂.ret q s q' γ)]
    [∀ q s q', Decidable (C₂.int q s q')]
    (hC₁ : ∀ w, w ≠ [] → (Lang C₁ c₁ accC₁ w ↔ (WellMatched w ∧ ¬ Lang M₁ q₁ acc₁ w)))
    (hC₂ : ∀ w, w ≠ [] → (Lang C₂ c₂ accC₂ w ↔ (WellMatched w ∧ ¬ Lang M₂ q₂ acc₂ w))) :
    Decidable (∀ w, Lang M₁ q₁ acc₁ w ↔ Lang M₂ q₂ acc₂ w) :=
  haveI : DecidablePred fun p : S₁ × T₂ => acc₁ p.1 ∧ accC₂ p.2 := fun _ =>
    inferInstanceAs (Decidable (_ ∧ _))
  haveI : DecidablePred fun p : S₂ × T₁ => acc₂ p.1 ∧ accC₁ p.2 := fun _ =>
    inferInstanceAs (Decidable (_ ∧ _))
  decidable_of_iff
    ((¬ ∃ w, Lang (prodVpa M₁ C₂) (q₁, c₂) (fun p => acc₁ p.1 ∧ accC₂ p.2) w) ∧
      (¬ ∃ w, Lang (prodVpa M₂ C₁) (q₂, c₁) (fun p => acc₂ p.1 ∧ accC₁ p.2) w)) <| by
    have iff₁ : (∃ w, Lang (prodVpa M₁ C₂) (q₁, c₂) (fun p => acc₁ p.1 ∧ accC₂ p.2) w) ↔
        ∃ w, Lang M₁ q₁ acc₁ w ∧ ¬ Lang M₂ q₂ acc₂ w := by
      constructor
      · rintro ⟨w, hw⟩
        obtain ⟨h₁, hc⟩ := (prodVpa_lang M₁ C₂ q₁ c₂ acc₁ accC₂ w).mp hw
        have hne : w ≠ [] := fun e => lang_not_nil M₁ q₁ acc₁ (e ▸ h₁)
        exact ⟨w, h₁, ((hC₂ w hne).mp hc).2⟩
      · rintro ⟨w, h₁, h₂⟩
        have hne : w ≠ [] := fun e => lang_not_nil M₁ q₁ acc₁ (e ▸ h₁)
        exact ⟨w, (prodVpa_lang M₁ C₂ q₁ c₂ acc₁ accC₂ w).mpr
          ⟨h₁, (hC₂ w hne).mpr ⟨lang_wellMatched M₁ q₁ acc₁ w h₁, h₂⟩⟩⟩
    have iff₂ : (∃ w, Lang (prodVpa M₂ C₁) (q₂, c₁) (fun p => acc₂ p.1 ∧ accC₁ p.2) w) ↔
        ∃ w, Lang M₂ q₂ acc₂ w ∧ ¬ Lang M₁ q₁ acc₁ w := by
      constructor
      · rintro ⟨w, hw⟩
        obtain ⟨h₂, hc⟩ := (prodVpa_lang M₂ C₁ q₂ c₁ acc₂ accC₁ w).mp hw
        have hne : w ≠ [] := fun e => lang_not_nil M₂ q₂ acc₂ (e ▸ h₂)
        exact ⟨w, h₂, ((hC₁ w hne).mp hc).2⟩
      · rintro ⟨w, h₂, h₁⟩
        have hne : w ≠ [] := fun e => lang_not_nil M₂ q₂ acc₂ (e ▸ h₂)
        exact ⟨w, (prodVpa_lang M₂ C₁ q₂ c₁ acc₂ accC₁ w).mpr
          ⟨h₂, (hC₁ w hne).mpr ⟨lang_wellMatched M₂ q₂ acc₂ w h₂, h₁⟩⟩⟩
    rw [equiv_iff_symmDiff_empty (Lang M₁ q₁ acc₁) (Lang M₂ q₂ acc₂)]
    exact and_congr (not_congr iff₁) (not_congr iff₂)

/-! ## The decision COMPUTES — kernel-evaluated on concrete machines.

The `#guard`s below are the teeth: they force the kernel to actually RUN the saturation and the
full non-emptiness decision. A vacuous (`em`-laundered) "decision" cannot pass a `#guard` — there
is nothing to evaluate. -/

namespace ComputeReference

/-- The bracket-chain VPA re-hosted on `Fin 1` states (the `Nat`-state `chainVpa` above is the
same machine; `Fin 1` gives the `Fintype` the computation needs). -/
def finChainVpa : Vpa (Fin 1) Unit where
  call := fun _ s _ _ => s = Sym.op
  ret := fun _ s _ _ => s = Sym.cl
  int := fun _ _ _ => False

instance : ∀ (q : Fin 1) (s : Sym) (q' : Fin 1) (γ : Unit), Decidable (finChainVpa.call q s q' γ) :=
  fun _ s _ _ => inferInstanceAs (Decidable (s = Sym.op))
instance : ∀ (q : Fin 1) (s : Sym) (q' : Fin 1) (γ : Unit), Decidable (finChainVpa.ret q s q' γ) :=
  fun _ s _ _ => inferInstanceAs (Decidable (s = Sym.cl))
instance : ∀ (q : Fin 1) (s : Sym) (q' : Fin 1), Decidable (finChainVpa.int q s q') :=
  fun _ _ _ => inferInstanceAs (Decidable False)

/-- A machine with NO transitions — its language is empty, and the decision must SAY so (this is
the case a vacuity-laundered `q = q'` escape hatch would get wrong; cf. `lang_not_nil`). -/
def deadVpa : Vpa (Fin 1) Unit where
  call := fun _ _ _ _ => False
  ret := fun _ _ _ _ => False
  int := fun _ _ _ => False

instance : ∀ (q : Fin 1) (s : Sym) (q' : Fin 1) (γ : Unit), Decidable (deadVpa.call q s q' γ) :=
  fun _ _ _ _ => inferInstanceAs (Decidable False)
instance : ∀ (q : Fin 1) (s : Sym) (q' : Fin 1) (γ : Unit), Decidable (deadVpa.ret q s q' γ) :=
  fun _ _ _ _ => inferInstanceAs (Decidable False)
instance : ∀ (q : Fin 1) (s : Sym) (q' : Fin 1), Decidable (deadVpa.int q s q') :=
  fun _ _ _ => inferInstanceAs (Decidable False)

-- The saturation COMPUTES: the bracket machine's single summary pair is found ...
#guard ((0, 0) : Fin 1 × Fin 1) ∈ sat finChainVpa
-- ... and the transitionless machine saturates to nothing.
#guard sat deadVpa = ∅

-- The full decision runs end-to-end through `decidableLangNonempty`: the bracket language is
-- inhabited (`op cl` is a witness); the dead machine's language is empty — and `decide` is
-- evaluation, not `em`.
#guard decide (∃ w, Lang finChainVpa 0 (· = 0) w)
#guard decide (∀ w, ¬ Lang deadVpa 0 (· = 0) w)

end ComputeReference

/-! ## THE COMPLEMENT — Alur–Madhusudan determinize-then-flip, PROVED.

This discharges `ComplementClosure`. The construction is the real subset construction over
SUMMARY SETS: the determinized machine's control state is a `Finset (S × S)` — the exact set of
summaries `(q, q')` = "the original machine can go from `(q, ⊥)` to `(q', ⊥)` reading the current
top-level well-matched segment" — and its stack symbol is again a `Finset (S × S)` (the summary
set suspended at the innermost pending call). The stack discipline keeps this DETERMINISTIC
because the stack action is class-driven (`stack_height_input_determined` acting constructively,
again): on a call the machine pushes its current summary set and restarts at the diagonal; on the
matching return it pops and composes through the call/return wrap. The pieces:

    `PathW`            — word-indexed (possibly-empty) valid path; `lang_iff_pathW` ties it to `Lang`
    `detVpa`           — the summary-set subset construction (transitions are FUNCTIONS of the
                         pre-state, written as their graphs)
    `DChain`           — the level-by-level decomposition invariant: what "the original machine
                         reaches `(p, σ)` from `(q, ⊥)` on this input" looks like against the
                         determinized config `(R, Γ)`
    `det_invariant`    — THE determinization theorem, by snoc induction on the word: after any
                         determinized run, `M`-reachability ↔ `DChain` against the reached config
    `det_progress` / `pathW_height` — the determinized machine RUNS on every well-matched word and
                         ends at the empty stack (totality of the subset construction)
    `detVpa_complement`— accept-flip correctness: `Lang (detVpa M) = WellMatched ∖ Lang M` on
                         non-empty words. Determinism is load-bearing exactly here: the flip is
                         sound because the reached summary set is the SAME for every run.
    `complement_closure` / `decidable_template_equivalence` — the discharged seam and the
                         UNCONDITIONAL decidable equivalence, kernel-`#guard`ed below. -/

section WordPaths

variable {S G : Type u}

/-- **`PathW M c w c'`** — a possibly-EMPTY sequence of `stepValid` steps from `c` to `c'` reading
exactly the word `w`. The word-indexed face of `Path`: the determinization invariant is a
statement about "all configs reachable on THIS word", so the word must ride the derivation.
Allowing the empty path (unlike `Path`/`WM`) makes the call/return wrap subsume the empty-body
case (`wrap0`) for free. -/
inductive PathW (M : Vpa S G) : Config S G → List Sym → Config S G → Prop
  | nil (c : Config S G) : PathW M c [] c
  | cons {c c' c'' : Config S G} {w : List Sym} (sym : Sym) (h : stepValid M ⟨c, sym, c'⟩)
      (tail : PathW M c' w c'') : PathW M c (sym :: w) c''

theorem pathW_nil_inv {M : Vpa S G} {c c' : Config S G} (h : PathW M c [] c') : c' = c := by
  cases h; rfl

theorem PathW.append {M : Vpa S G} {c c' : Config S G} {u : List Sym}
    (h₁ : PathW M c u c') : ∀ {v : List Sym} {c'' : Config S G},
      PathW M c' v c'' → PathW M c (u ++ v) c'' := by
  induction h₁ with
  | nil => intro v c'' h₂; exact h₂
  | cons sym h t ih => intro v c'' h₂; exact .cons sym h (ih h₂)

/-- Splitting one step off the RIGHT end — the elimination the snoc induction needs. -/
theorem pathW_snoc {M : Vpa S G} : ∀ {u : List Sym} {c c'' : Config S G} {s : Sym},
    PathW M c (u ++ [s]) c'' → ∃ mid, PathW M c u mid ∧ stepValid M ⟨mid, s, c''⟩ := by
  intro u
  induction u with
  | nil =>
    intro c c'' s h
    rw [List.nil_append] at h
    cases h with
    | cons sym hs tail =>
      have he := pathW_nil_inv tail
      subst he
      exact ⟨c, .nil c, hs⟩
  | cons a u' ih =>
    intro c c'' s h
    rw [List.cons_append] at h
    cases h with
    | cons sym hs tail =>
      obtain ⟨mid, hp, hst⟩ := ih tail
      exact ⟨mid, .cons a hs hp, hst⟩

theorem pathW_snoc_iff {M : Vpa S G} {c c'' : Config S G} {u : List Sym} {s : Sym} :
    PathW M c (u ++ [s]) c'' ↔ ∃ mid, PathW M c u mid ∧ stepValid M ⟨mid, s, c''⟩ := by
  constructor
  · exact pathW_snoc
  · rintro ⟨mid, hp, hs⟩
    exact hp.append (.cons s hs (.nil c''))

/-- The stack height along ANY `PathW` is the start height plus the word's `wordDelta` —
`run_height` restated on the word-indexed paths (and, applied to `detVpa` below, the reason the
determinized run of a well-matched word ends at the empty stack). -/
theorem pathW_height {M : Vpa S G} : ∀ {c c' : Config S G} {w : List Sym},
    PathW M c w c' → (c'.stack.length : ℤ) = (c.stack.length : ℤ) + wordDelta w := by
  intro c c' w h
  induction h with
  | nil => simp [wordDelta]
  | cons sym hs t ih =>
    have hstep := step_stack_length M _ hs
    dsimp only at hstep
    simp only [wordDelta]
    omega

/-- A `VpaAccepts`-shaped run is a `PathW` reading its word. -/
theorem run_pathW (M : Vpa S G) : ∀ (run : List (VStep S G)) (first last : VStep S G),
    run.head? = some first → run.getLast? = some last →
    (∀ s ∈ run, stepValid M s) → vchained run →
    PathW M first.pre (run.map (fun s => s.sym)) last.post := by
  intro run
  induction run with
  | nil => intro first last hh _ _ _; simp at hh
  | cons a t ih =>
    intro first last hh hl hval hch
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      exact .cons a.sym (hval a (by simp)) (.nil a.post)
    | cons b u =>
      obtain ⟨hR, htail⟩ := hch
      have hl' : (b :: u).getLast? = some last := by
        rw [List.getLast?_cons_cons] at hl; exact hl
      have hp := ih b last rfl hl' (fun s hs => hval s (List.mem_cons_of_mem a hs)) htail
      have hbp : b.pre = a.post := hR
      rw [hbp] at hp
      exact .cons a.sym (hval a (by simp)) hp

/-- Conversely, a non-empty `PathW` is realized by a `VpaAccepts`-shaped run reading its word. -/
theorem pathW_run (M : Vpa S G) : ∀ {c c' : Config S G} {w : List Sym},
    PathW M c w c' → w ≠ [] →
    ∃ (run : List (VStep S G)) (first last : VStep S G),
      run.head? = some first ∧ run.getLast? = some last ∧ first.pre = c ∧ last.post = c' ∧
      (∀ s ∈ run, stepValid M s) ∧ vchained run ∧ run.map (fun s => s.sym) = w := by
  intro c c' w h
  induction h with
  | nil => intro hne; exact absurd rfl hne
  | @cons a b c₂ w' sym hs tail ih =>
    intro _
    cases w' with
    | nil =>
      have he := pathW_nil_inv tail
      subst he
      refine ⟨[⟨a, sym, c₂⟩], ⟨a, sym, c₂⟩, ⟨a, sym, c₂⟩, rfl, List.getLast?_singleton, rfl, rfl,
        ?_, trivial, rfl⟩
      intro s hs'
      rw [List.mem_singleton] at hs'
      subst hs'
      exact hs
    | cons s₂ w'' =>
      obtain ⟨run', f', l', hh', hl', hfp', hlp', hv', hc', hm'⟩ := ih (by simp)
      cases run' with
      | nil => simp at hm'
      | cons r₀ rt =>
        simp only [List.head?_cons, Option.some.injEq] at hh'
        subst hh'
        refine ⟨⟨a, sym, b⟩ :: r₀ :: rt, ⟨a, sym, b⟩, l', rfl, ?_, rfl, hlp', ?_, ?_, ?_⟩
        · rw [List.getLast?_cons_cons]; exact hl'
        · intro s hs'
          rcases List.mem_cons.mp hs' with rfl | hmem
          · exact hs
          · exact hv' s hmem
        · exact ⟨hfp', hc'⟩
        · simp only [List.map_cons] at hm' ⊢
          rw [hm']

/-- **`lang_iff_pathW`** — `Lang` in path form: a non-empty word is accepted iff a `PathW` reads
it from `(q₀, ⊥)` to an accepting empty-stack config. -/
theorem lang_iff_pathW (M : Vpa S G) (q₀ : S) (acc : S → Prop) (w : List Sym) (hne : w ≠ []) :
    Lang M q₀ acc w ↔ ∃ q' : S, acc q' ∧ PathW M ⟨q₀, []⟩ w ⟨q', []⟩ := by
  constructor
  · rintro ⟨run, ⟨first, last, hh, hl, hq0, hs0, hacc, hsf, hval, hch⟩, hw⟩
    refine ⟨last.post.state, hacc, ?_⟩
    have hp := run_pathW M run first last hh hl hval hch
    have e₁ : first.pre = (⟨q₀, []⟩ : Config S G) := by rw [← hq0, ← hs0]
    have e₂ : last.post = (⟨last.post.state, []⟩ : Config S G) := by rw [← hsf]
    rw [hw, e₁, e₂] at hp
    exact hp
  · rintro ⟨q', hacc, hp⟩
    obtain ⟨run, first, last, hh, hl, hfp, hlp, hval, hch, hmap⟩ := pathW_run M hp hne
    exact ⟨run, ⟨first, last, hh, hl, by rw [hfp], by rw [hfp], by rw [hlp]; exact hacc,
      by rw [hlp], hval, hch⟩, hmap⟩

/-- **`DChain M R Γ σ q p`** — the determinization INVARIANT, as a level-by-level decomposition:
against determinized control state `R` and determinized stack `Γ` (top first), the original
machine can go from `(q, ⊥)` to `(p, σ)` — reaching the segment-summary in `R` at the top level,
with each deeper `Γ`-level contributing its suspended summary set plus the pending call that
pushed the matching `σ`-symbol. `det_invariant` proves this IS `M`-reachability on the word the
determinized machine read. -/
inductive DChain (M : Vpa S G) : Finset (S × S) → List (Finset (S × S)) → List G → S → S → Prop
  | base {R : Finset (S × S)} {q p : S} (h : (q, p) ∈ R) : DChain M R [] [] q p
  | step {R D : Finset (S × S)} {Γ : List (Finset (S × S))} {g : G} {σ : List G} {q x t p : S}
      (hc : DChain M D Γ σ q x) (hcall : M.call x Sym.op t g) (hR : (t, p) ∈ R) :
      DChain M R (D :: Γ) (g :: σ) q p

theorem dchain_nil_inv {M : Vpa S G} {R : Finset (S × S)} {σ : List G} {q p : S}
    (h : DChain M R [] σ q p) : σ = [] ∧ (q, p) ∈ R := by
  cases h with | base h => exact ⟨rfl, h⟩

theorem dchain_cons_inv {M : Vpa S G} {R D : Finset (S × S)} {Γ : List (Finset (S × S))}
    {σ : List G} {q p : S} (h : DChain M R (D :: Γ) σ q p) :
    ∃ (g : G) (σ' : List G) (x t : S),
      σ = g :: σ' ∧ DChain M D Γ σ' q x ∧ M.call x Sym.op t g ∧ (t, p) ∈ R := by
  cases h with | step hc hcall hR => exact ⟨_, _, _, _, rfl, hc, hcall, hR⟩

end WordPaths

section Determinize

variable {S G : Type u} [DecidableEq S] [Fintype S] [Fintype G] (M : Vpa S G)
variable [∀ q s q' γ, Decidable (M.call q s q' γ)]
variable [∀ q s q' γ, Decidable (M.ret q s q' γ)]
variable [∀ q s q', Decidable (M.int q s q')]

/-- The diagonal relation, as a `Finset` — the determinized machine's initial state and its
post-call restart (a fresh top-level segment summarizes to the identity: the empty path). -/
def diagRel : Finset (S × S) := Finset.univ.filter fun qq => qq.1 = qq.2

/-- Relation composition on the `Finset (S × S)` grid. -/
def relComp (X Y : Finset (S × S)) : Finset (S × S) :=
  Finset.univ.filter fun qq => ∃ m, (qq.1, m) ∈ X ∧ (m, qq.2) ∈ Y

/-- The one-internal-step relation of `M`. -/
def relInt : Finset (S × S) := Finset.univ.filter fun qq => M.int qq.1 Sym.dat qq.2

/-- The call/return WRAP of a summary set: one matching `op … cl` pair around an inner segment
summarized by `X`. Because `X` contains the diagonal whenever the inner segment can be empty,
this subsumes the `wrap0` case of `WM` with no extra disjunct. -/
def relWrap (X : Finset (S × S)) : Finset (S × S) :=
  Finset.univ.filter fun qq =>
    ∃ p p' γ, M.call qq.1 Sym.op p γ ∧ (p, p') ∈ X ∧ M.ret p' Sym.cl qq.2 γ

theorem mem_diagRel {a b : S} : (a, b) ∈ (diagRel : Finset (S × S)) ↔ a = b := by
  simp [diagRel]

theorem mem_relComp {X Y : Finset (S × S)} {a b : S} :
    (a, b) ∈ relComp X Y ↔ ∃ m, (a, m) ∈ X ∧ (m, b) ∈ Y := by
  simp [relComp]

omit [DecidableEq S] [Fintype G] [∀ q s q' γ, Decidable (M.call q s q' γ)]
    [∀ q s q' γ, Decidable (M.ret q s q' γ)] in
theorem mem_relInt {a b : S} : (a, b) ∈ relInt M ↔ M.int a Sym.dat b := by
  simp [relInt]

omit [∀ q s q', Decidable (M.int q s q')] in
theorem mem_relWrap {X : Finset (S × S)} {a b : S} :
    (a, b) ∈ relWrap M X ↔
      ∃ p p' γ, M.call a Sym.op p γ ∧ (p, p') ∈ X ∧ M.ret p' Sym.cl b γ := by
  simp [relWrap]

/-- **`detVpa M`** — the Alur–Madhusudan DETERMINIZATION: states and stack symbols are summary
sets. Every transition relation is the GRAPH of a function of the pre-state (and, on returns, the
popped symbol) — determinism is syntactic, not a side condition. A call suspends the current
summary set on the stack and restarts at the diagonal; a return pops the suspended set and
composes it through the call/return wrap of the finished inner segment; an internal composes the
one-step relation on the right. -/
def detVpa : Vpa (Finset (S × S)) (Finset (S × S)) where
  call R _ R' γ := R' = diagRel ∧ γ = R
  ret R _ R' γ := R' = relComp γ (relWrap M R)
  int R _ R' := R' = relComp R (relInt M)

instance detCallDecidable (R : Finset (S × S)) (s : Sym) (R' γ : Finset (S × S)) :
    Decidable ((detVpa M).call R s R' γ) :=
  inferInstanceAs (Decidable (R' = diagRel ∧ γ = R))

instance detRetDecidable (R : Finset (S × S)) (s : Sym) (R' γ : Finset (S × S)) :
    Decidable ((detVpa M).ret R s R' γ) :=
  inferInstanceAs (Decidable (R' = relComp γ (relWrap M R)))

instance detIntDecidable (R : Finset (S × S)) (s : Sym) (R' : Finset (S × S)) :
    Decidable ((detVpa M).int R s R') :=
  inferInstanceAs (Decidable (R' = relComp R (relInt M)))

omit [Fintype G] [∀ q s q' γ, Decidable (M.call q s q' γ)]
    [∀ q s q' γ, Decidable (M.ret q s q' γ)] [∀ q s q', Decidable (M.int q s q')] in
/-- Composing on the right of the TOP summary set commutes with `DChain` — the top level is the
only place the control state acts, so the composition peels off as a final relational step. -/
theorem dchain_comp {X R : Finset (S × S)} {Γ : List (Finset (S × S))} {σ : List G} {q p : S} :
    DChain M (relComp R X) Γ σ q p ↔ ∃ m, DChain M R Γ σ q m ∧ (m, p) ∈ X := by
  constructor
  · intro h
    cases h with
    | base hmem =>
      obtain ⟨m, h₁, h₂⟩ := mem_relComp.mp hmem
      exact ⟨m, .base h₁, h₂⟩
    | step hc hcall hR =>
      obtain ⟨m, h₁, h₂⟩ := mem_relComp.mp hR
      exact ⟨m, .step hc hcall h₁, h₂⟩
  · rintro ⟨m, hd, hmem⟩
    cases hd with
    | base h₁ => exact .base (mem_relComp.mpr ⟨m, h₁, hmem⟩)
    | step hc hcall hR => exact .step hc hcall (mem_relComp.mpr ⟨m, hR, hmem⟩)

/-- **`det_invariant`** — THE determinization theorem. After the determinized machine reads `w`
(from the diagonal, empty stack) and sits at `(R, Γ)`, the original machine's reachability on `w`
is EXACTLY the `DChain` decomposition against `(R, Γ)` — for every start state, end state, and
end stack simultaneously. Snoc induction on the word; each symbol class is one algebraic step
(`dchain_comp`, the `DChain` constructors, and their inversions). This is where
`stack_height_input_determined` pays out as a construction: the determinized stack moves in
lockstep with EVERY run of the original machine at once. -/
theorem det_invariant : ∀ (w : List Sym) {R : Finset (S × S)} {Γ : List (Finset (S × S))},
    PathW (detVpa M) ⟨diagRel, []⟩ w ⟨R, Γ⟩ →
    ∀ (q p : S) (σ : List G), PathW M ⟨q, []⟩ w ⟨p, σ⟩ ↔ DChain M R Γ σ q p := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro R Γ hdet q p σ
    have h0 := pathW_nil_inv hdet
    rw [Config.mk.injEq] at h0
    obtain ⟨rfl, rfl⟩ := h0
    constructor
    · intro hp
      have h1 := pathW_nil_inv hp
      rw [Config.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact .base (mem_diagRel.mpr rfl)
    · intro hd
      obtain ⟨rfl, hmem⟩ := dchain_nil_inv hd
      rw [mem_diagRel] at hmem
      subst hmem
      exact .nil _
  | append_singleton u s ih =>
    intro R Γ hdet q p σ
    obtain ⟨⟨R₀, Γ₀⟩, hu, hstep⟩ := pathW_snoc hdet
    rw [pathW_snoc_iff]
    cases s with
    | dat =>
      simp only [stepValid, classOf, detVpa] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      rw [dchain_comp]
      constructor
      · rintro ⟨⟨m, σm⟩, hpm, hsm⟩
        simp only [stepValid, classOf] at hsm
        obtain ⟨hint, rfl⟩ := hsm
        exact ⟨m, (ih hu q m σ).mp hpm, (mem_relInt M).mpr hint⟩
      · rintro ⟨m, hd, hmem⟩
        exact ⟨⟨m, σ⟩, (ih hu q m σ).mpr hd, ⟨(mem_relInt M).mp hmem, rfl⟩⟩
    | op =>
      simp only [stepValid, classOf, detVpa] at hstep
      obtain ⟨γ, ⟨rfl, rfl⟩, rfl⟩ := hstep
      constructor
      · rintro ⟨⟨m, σm⟩, hpm, hsm⟩
        simp only [stepValid, classOf] at hsm
        obtain ⟨g, hcall, rfl⟩ := hsm
        exact .step ((ih hu q m σm).mp hpm) hcall (mem_diagRel.mpr rfl)
      · intro hd
        obtain ⟨g, σ', x, t, rfl, hc, hcall, htp⟩ := dchain_cons_inv hd
        rw [mem_diagRel] at htp
        subst htp
        exact ⟨⟨x, σ'⟩, (ih hu q x σ').mpr hc, ⟨g, hcall, rfl⟩⟩
    | cl =>
      simp only [stepValid, classOf, detVpa] at hstep
      obtain ⟨γ, rest, rfl, rfl, rfl⟩ := hstep
      rw [dchain_comp]
      constructor
      · rintro ⟨⟨m, σm⟩, hpm, hsm⟩
        simp only [stepValid, classOf] at hsm
        obtain ⟨g, rest', hretM, rfl, rfl⟩ := hsm
        have hd := (ih hu q m (g :: σ)).mp hpm
        obtain ⟨g', σ'', x, t, heq, hc, hcall, htm⟩ := dchain_cons_inv hd
        injection heq with h₁ h₂
        subst h₁
        subst h₂
        exact ⟨x, hc, (mem_relWrap M).mpr ⟨t, m, g, hcall, htm, hretM⟩⟩
      · rintro ⟨x, hch, hxp⟩
        obtain ⟨t, m, g, hcall, htm, hretM⟩ := (mem_relWrap M).mp hxp
        exact ⟨⟨m, g :: σ⟩, (ih hu q m (g :: σ)).mpr (.step hch hcall htm),
          ⟨g, σ, hretM, rfl, rfl⟩⟩

/-- **`det_progress`** — TOTALITY of the subset construction: the determinized machine runs on
ANY word whose prefixes never take the (input-determined) height negative. Every transition is a
total function of the pre-state, so the only obstruction would be a return on the empty stack —
excluded by the prefix condition. This is the existence half that makes the accept-FLIP sound:
the flipped machine must actually ACCEPT the words the original rejects, not merely fail to
accept the ones it accepts. -/
theorem det_progress : ∀ (w : List Sym) (c : Config (Finset (S × S)) (Finset (S × S))),
    (∀ p : List Sym, p <+: w → 0 ≤ (c.stack.length : ℤ) + wordDelta p) →
    ∃ c', PathW (detVpa M) c w c' := by
  intro w
  induction w with
  | nil => intro c _; exact ⟨c, .nil c⟩
  | cons s w' ih =>
    intro c h
    cases s with
    | op =>
      have hnext : ∀ p : List Sym, p <+: w' →
          0 ≤ ((c.state :: c.stack).length : ℤ) + wordDelta p := by
        intro p hp
        obtain ⟨t, ht⟩ := hp
        have := h (Sym.op :: p) ⟨t, by rw [List.cons_append, ht]⟩
        simp only [wordDelta, heightDelta, List.length_cons] at this ⊢
        push_cast at this ⊢
        omega
      obtain ⟨c', hp'⟩ := ih ⟨diagRel, c.state :: c.stack⟩ hnext
      exact ⟨c', .cons (c' := ⟨diagRel, c.state :: c.stack⟩) Sym.op
        ⟨c.state, ⟨rfl, rfl⟩, rfl⟩ hp'⟩
    | cl =>
      have h1 := h [Sym.cl] ⟨w', rfl⟩
      simp only [wordDelta, heightDelta] at h1
      cases hst : c.stack with
      | nil =>
        rw [hst] at h1
        simp only [List.length_nil, Nat.cast_zero] at h1
        omega
      | cons γ rest =>
        have hnext : ∀ p : List Sym, p <+: w' →
            0 ≤ ((rest.length : ℤ)) + wordDelta p := by
          intro p hp
          obtain ⟨t, ht⟩ := hp
          have := h (Sym.cl :: p) ⟨t, by rw [List.cons_append, ht]⟩
          rw [hst] at this
          simp only [wordDelta, heightDelta, List.length_cons] at this
          push_cast at this
          omega
        obtain ⟨c', hp'⟩ := ih ⟨relComp γ (relWrap M c.state), rest⟩ hnext
        exact ⟨c', .cons (c' := ⟨relComp γ (relWrap M c.state), rest⟩) Sym.cl
          ⟨γ, rest, rfl, hst, rfl⟩ hp'⟩
    | dat =>
      have hnext : ∀ p : List Sym, p <+: w' →
          0 ≤ ((c.stack.length : ℤ)) + wordDelta p := by
        intro p hp
        obtain ⟨t, ht⟩ := hp
        have := h (Sym.dat :: p) ⟨t, by rw [List.cons_append, ht]⟩
        simp only [wordDelta, heightDelta] at this
        omega
      obtain ⟨c', hp'⟩ := ih ⟨relComp c.state (relInt M), c.stack⟩ hnext
      exact ⟨c', .cons (c' := ⟨relComp c.state (relInt M), c.stack⟩) Sym.dat
        ⟨rfl, rfl⟩ hp'⟩

/-- The FLIPPED acceptance: reject exactly when the original machine would accept from `q₀` —
sound to state on the determinized control state because that state is the same for every run
(determinism), so "the summary set reached" is a function of the word. -/
def compAcc (q₀ : S) (acc : S → Prop) : Finset (S × S) → Prop :=
  fun R => ¬ ∃ q' : S, acc q' ∧ (q₀, q') ∈ R

instance compAccDecidable (q₀ : S) (acc : S → Prop) [DecidablePred acc] :
    DecidablePred (compAcc q₀ acc) := fun R =>
  inferInstanceAs (Decidable (¬ ∃ q' : S, acc q' ∧ (q₀, q') ∈ R))

/-- **`detVpa_complement`** — COMPLEMENT correctness, the conclusion `ComplementClosure`
promises: on non-empty words the flipped determinized machine accepts EXACTLY the well-matched
words the original machine rejects. Forward: any accepted word is well-matched
(`lang_wellMatched`), and by `det_invariant` an original accepting path would put an accepting
summary in the reached set, contradicting the flip. Backward: `det_progress` + `pathW_height` run
the determinized machine to the empty stack on any well-matched word, and the flip holds at the
reached set because an accepting summary would (again by `det_invariant`) yield an original
accepting run. Determinism is load-bearing in BOTH directions: there is ONE reached summary set,
so flipping it cannot lose or invent runs. -/
theorem detVpa_complement (q₀ : S) (acc : S → Prop) :
    ∀ w : List Sym, w ≠ [] →
      (Lang (detVpa M) diagRel (compAcc q₀ acc) w ↔ (WellMatched w ∧ ¬ Lang M q₀ acc w)) := by
  intro w hne
  constructor
  · intro h
    refine ⟨lang_wellMatched _ _ _ w h, ?_⟩
    obtain ⟨R, hR, hpath⟩ := (lang_iff_pathW (detVpa M) diagRel (compAcc q₀ acc) w hne).mp h
    intro hM
    obtain ⟨q', hacc, hpM⟩ := (lang_iff_pathW M q₀ acc w hne).mp hM
    have hd := (det_invariant M w hpath q₀ q' []).mp hpM
    exact hR ⟨q', hacc, (dchain_nil_inv hd).2⟩
  · rintro ⟨hwm, hnot⟩
    obtain ⟨c', hpath⟩ := det_progress M w ⟨diagRel, []⟩ (by
      intro p hp
      simpa using hwm.2 p hp)
    obtain ⟨R, Γ⟩ := c'
    have hΓ : Γ = [] := by
      have hlen := pathW_height hpath
      simp only [List.length_nil, Nat.cast_zero, zero_add, hwm.1] at hlen
      cases Γ with
      | nil => rfl
      | cons a t =>
        simp only [List.length_cons] at hlen
        push_cast at hlen
        omega
    subst hΓ
    have hcomp : compAcc q₀ acc R := by
      intro hc
      obtain ⟨q', hacc, hmem⟩ := hc
      exact hnot ((lang_iff_pathW M q₀ acc w hne).mpr
        ⟨q', hacc, (det_invariant M w hpath q₀ q' []).mpr (.base hmem)⟩)
    exact (lang_iff_pathW (detVpa M) diagRel (compAcc q₀ acc) w hne).mpr ⟨R, hcomp, hpath⟩

end Determinize

/-- **`complement_closure`** — the named residual, DISCHARGED: the witness is the real
determinize-then-flip (`detVpa` + `compAcc`), with `detVpa_complement` as its correctness proof.
The statement carries no decidability hypotheses, so the (undecidable, `Prop`-valued) transition
relations are lifted into the subset construction classically — `Classical.choice` supplies
`Decidable` for the filter predicates, nothing else; the construction and every step of its
correctness proof are the genuine Alur–Madhusudan argument, and the COMPUTABLE face of the very
same construction is exercised by kernel `#guard`s below (a vacuous `em`-complement could not
be). -/
theorem complement_closure : ComplementClosure := by
  intro S G fS fG M q₀ acc
  haveI := fS
  haveI := fG
  classical
  exact ⟨Finset (S × S), Finset (S × S), inferInstance, inferInstance, detVpa M, diagRel,
    compAcc q₀ acc, detVpa_complement M q₀ acc⟩

#assert_axioms complement_closure

/-- **`decidable_template_equivalence`** — the HEADLINE, now UNCONDITIONAL: decidable language
equivalence of two finite-fragment VPAs with decidable transitions. No complement hypotheses —
`decidableEquivOfComplements` is fed the determinize-then-flip machines and their proved
correctness (`detVpa_complement`). Computable end to end: the decision is two summary
saturations on the product machines `M₁ ⊗ ∁M₂` and `M₂ ⊗ ∁M₁` (kernel-`#guard`ed below on
concrete machines, both answers). The state-space cost is the Alur–Madhusudan exponential
(`Finset (S × S)`), as it must be — VPL equivalence is EXPTIME-complete. -/
def decidable_template_equivalence
    [DecidableEq S₁] [Fintype S₁] [Fintype G₁] [DecidableEq S₂] [Fintype S₂] [Fintype G₂]
    (M₁ : Vpa S₁ G₁) (q₁ : S₁) (acc₁ : S₁ → Prop) [DecidablePred acc₁]
    (M₂ : Vpa S₂ G₂) (q₂ : S₂) (acc₂ : S₂ → Prop) [DecidablePred acc₂]
    [∀ q s q' γ, Decidable (M₁.call q s q' γ)] [∀ q s q' γ, Decidable (M₁.ret q s q' γ)]
    [∀ q s q', Decidable (M₁.int q s q')]
    [∀ q s q' γ, Decidable (M₂.call q s q' γ)] [∀ q s q' γ, Decidable (M₂.ret q s q' γ)]
    [∀ q s q', Decidable (M₂.int q s q')] :
    Decidable (∀ w, Lang M₁ q₁ acc₁ w ↔ Lang M₂ q₂ acc₂ w) :=
  decidableEquivOfComplements M₁ q₁ acc₁ M₂ q₂ acc₂
    (detVpa M₁) diagRel (compAcc q₁ acc₁)
    (detVpa M₂) diagRel (compAcc q₂ acc₂)
    (detVpa_complement M₁ q₁ acc₁)
    (detVpa_complement M₂ q₂ acc₂)

#assert_axioms det_invariant
#assert_axioms detVpa_complement
#assert_axioms decidable_template_equivalence

/-! ### The unconditional decider COMPUTES — kernel-evaluated, both answers. -/

namespace ComputeReference

-- Equal pair: the same machine against itself — the decider must answer TRUE (both product
-- saturations find no symmetric-difference witness).
#guard @decide (∀ w, Lang finChainVpa 0 (· = 0) w ↔ Lang finChainVpa 0 (· = 0) w)
  (decidable_template_equivalence finChainVpa 0 (· = 0) finChainVpa 0 (· = 0))

-- Distinct pair: the bracket machine against the transitionless machine — the decider must
-- answer FALSE (`op cl` witnesses the difference, found by the saturation on `M₁ ⊗ ∁M₂`).
#guard !(@decide (∀ w, Lang finChainVpa 0 (· = 0) w ↔ Lang deadVpa 0 (· = 0) w)
  (decidable_template_equivalence finChainVpa 0 (· = 0) deadVpa 0 (· = 0)))

end ComputeReference

/-! ## Recap — the pipeline is CLOSED.

PROVED: intersection (`prodVpa_lang`, both directions, finiteness-preserving since
`Fintype (S₁ × S₂)` is automatic) · the acceptance universe (`lang_wellMatched`,
`lang_wordDelta_zero`, `lang_not_nil`) · the equivalence→emptiness reduction
(`equiv_iff_symmDiff_empty`) · **the COMPUTABLE emptiness decision** (`sat` saturation, sound +
complete: `wm_iff_mem_sat`, `lang_nonempty_iff_wm`, `decidableLangNonempty` /
`decidableLangEmpty`, kernel-`#guard`ed on concrete machines) · **COMPLEMENT**
(`detVpa` determinization over summary sets + `det_invariant` + accept-flip:
`detVpa_complement`, discharging the once-named `ComplementClosure` as `complement_closure`) ·
**UNCONDITIONAL decidable equivalence** (`decidable_template_equivalence`, kernel-`#guard`ed on
an equal and a distinct pair of concrete machines).

No named seam remains in this file. Union needs no separate construction: `∁(∁L₁ ∩ ∁L₂)`, or
directly by a disjoint sum. Honest scope, unchanged: this is the FINITE `Sym` fragment; the
templater's infinite `Value` data alphabet stays out of scope, exactly as in `VpaAsCert`'s
honest-scope note — and the decider's state space is the Alur–Madhusudan exponential, as
EXPTIME-completeness demands.
-/

end Dregg2.Crypto.VpaDecidable
