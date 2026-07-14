/-
# Market.FhIRAdmissible — the `fhIR` admissibility direction: **compiles ⇒ admissible** (the honest ⟸).

**The type-safety / soundness direction of the `fhIR` admissibility theorem.**
`docs/deos/FHEGG-PRODUCT-ORDER-FRONTIER.md` (the headline) and `docs/deos/DREGGFI-PRIVACY-TIERS.md §3`
state the organizing claim of the typed order/product DSL: *"a product is admissible AT TIER T iff it
compiles at tier T."* The **full IFF is a named research target** (six parts; resource-relative
maximality). This module formalizes and PROVES the honest, tractable **⟸ direction**:

    a product's convex program passes the tier-T resource manifest  ⇒  it is tier-T-admissible (runnable),

and NAMES the ⟹ (admissible ⇒ compiles — completeness / no-false-reject, the resource-relative
maximality gap) as the open target — with a CONCRETE counterexample witnessing why it is open.

This mirrors the verify-not-find pattern one level up: a *syntactic* manifest check (the `fhIR` typecheck)
soundly implies a *semantic* runtime guarantee (a crypto carrier that transports the program + a
trace-independent certificate) — exactly the shape of `Dregg2/Circuit.lean`'s `satisfied → fullStepInv`,
lifted from a single circuit to the product/tier surface.

## The model

  * **`Manifest`** — what the compiler emits about a compiled program: `publicOps` (`A, P` public+sparse —
    the *true* efficiency boundary per codex, the FHE public-matvec line), `approvedCone` (`𝒦` on the
    declared v0 `ProxLib` — a **conservative** list: no PSD/exp-cone in v0), `boundedDims`
    (dims/sparsity/precision/iteration bounds — a bounded circuit), `noIntegrality` (no endogenous
    binary/disjunction — stays convex), `traceIndepCert` (a small trace-independent `Cert-F`/gap check
    exists — verify-not-find).
  * **`passes T` (SYNTACTIC)** — the tier-T `fhIR` typecheck: **Tier 0 DARK** needs everything (FHE:
    matrices public); **Tier 1 SHIELDED** drops `publicOps` (the solver sees plaintext); **Tier 2 OPEN**
    passes anything (the general matcher). Monotone: `passes dark ⇒ passes shielded ⇒ passes open`.
  * **`RunnableAt T` (SEMANTIC)** — the actual runtime guarantee: the tier's crypto `carrierTransports`
    the program (FHE needs public matvec + bounded; STARK any bounded circuit; public re-exec anything)
    AND `verifyNotFind` (a sound trace-independent certificate exists, or the public tier re-executes).

## What is proved (honest scope)

  * **`passes_runnable` (the per-form ⟸ core).** `passes T m ⇒ RunnableAt T m` — the manifest typecheck
    soundly delivers the runtime guarantee, by destructuring the manifest's clauses into the carrier and
    certificate obligations. Not vacuous: `passes` is a Bool over manifest fields; `RunnableAt` is a
    semantic Prop about carrier transport + certificate soundness — the theorem *maps* one to the other.
  * **`compiles_admissible` (THE KEYSTONE, ⟸).** For a `Product` (a set of equivalent compiled forms),
    `compilesAt T P ⇒ AdmissibleAt T P`: if SOME form passes the tier-T manifest, the product runs at
    tier T. The verify-not-find direction of the admissibility theorem.
  * **Monotonicity** (`passes_mono`, `runnable_mono`, `admissible_mono`) — Tier-0-admissible ⇒
    Tier-1-admissible ⇒ Tier-2-admissible: more visibility only ever *adds* runnable mechanisms.
  * **`mostPrivateTier` + soundness** — the compiler computes the most private tier a product runs at, and
    `mostPrivateTier_runnable` proves the offered tier is always genuinely runnable; `mostPrivate_dark_iff`
    proves the type system (not marketing) decides the DARK label.

**The ⟹ direction is the NAMED OPEN target — with a concrete witness.** `runnable_not_compiles` exhibits
a manifest that is `RunnableAt shielded` yet does NOT `passes shielded` — its cone is off the *conservative*
declared v0 `ProxLib` (`approvedCone = false`) even though a bounded STARK circuit would carry it. So
`AdmissibleAt ⇏ compilesAt` in general (`admissible_not_compiles`): the full IFF requires the
**resource-relative maximality** argument (`FHEGG-PRODUCT-ORDER-FRONTIER.md`: "equivalent convex functions
can have radically different prox costs; maximality is relative to a declared `ProxLib`") — the honest
open piece. Also open (not modelled here): semantic preservation, the cost bound, conditional
completeness, no-wrap, and leakage refinement (the other five parts of the six-part theorem).

Pure.
-/
import Mathlib.Tactic.Tauto
import Dregg2.Tactics

namespace Market

/-! ## 1. Tiers, the compiled manifest, and the two judgements. -/

/-- **The three privacy tiers** (`DREGGFI-PRIVACY-TIERS.md`): `dark` (FHE, no-viewer), `shielded`
(STARK-ZK, solver-sees), `open` (public, general). -/
inductive Tier | dark | shielded | «open»
  deriving DecidableEq, Repr

/-- **A compiled product's resource manifest** — the facts the `fhIR` compiler emits about a program. -/
structure Manifest where
  /-- `A, P` public + sparse (the FHE public-matvec line — the *true* efficiency boundary). -/
  publicOps : Bool
  /-- `𝒦` on the declared v0 `ProxLib` (a CONSERVATIVE list: no PSD / exp-cone in v0). -/
  approvedCone : Bool
  /-- Dims / sparsity / precision / iteration bounds met (a bounded circuit). -/
  boundedDims : Bool
  /-- No endogenous binary / disjunction (stays in the convex regime). -/
  noIntegrality : Bool
  /-- A small trace-independent `Cert-F` / gap check exists (verify-not-find). -/
  traceIndepCert : Bool
  deriving DecidableEq, Repr

/-- **`passes T m` — the SYNTACTIC tier-T `fhIR` typecheck.** Tier 0 DARK requires everything (FHE:
matrices public + approved cone + bounded + convex + certificate); Tier 1 SHIELDED drops `publicOps` (the
solver sees plaintext, so private matrices are fine); Tier 2 OPEN passes anything (the general matcher). -/
def passes : Tier → Manifest → Bool
  | .dark,     m => m.publicOps && m.approvedCone && m.boundedDims && m.noIntegrality && m.traceIndepCert
  | .shielded, m => m.approvedCone && m.boundedDims && m.noIntegrality && m.traceIndepCert
  | .«open»,   _ => true

/-- **The tier's crypto carrier can TRANSPORT the program (semantic).** FHE (dark) needs a public matvec
and a bounded envelope; STARK (shielded) carries any bounded convex circuit; public re-execution (open)
carries anything. Note: the carrier does NOT require `approvedCone` — the approved-cone list is a
conservative *declaration*, not a runtime necessity (this is where the ⟹ direction opens up). -/
def carrierTransports : Tier → Manifest → Prop
  | .dark,     m => m.publicOps = true ∧ m.boundedDims = true
  | .shielded, m => m.boundedDims = true
  | .«open»,   _ => True

/-- **A sound verify-not-find certificate exists (semantic).** For the private tiers a convex program
(`noIntegrality`) with a trace-independent gap check is verify-not-find sound; the public tier re-executes
(re-execution IS the check). -/
def verifyNotFind : Tier → Manifest → Prop
  | .«open», _ => True
  | _,       m => m.noIntegrality = true ∧ m.traceIndepCert = true

/-- **`RunnableAt T m` — the SEMANTIC runtime guarantee: the product actually runs soundly at tier T.**
The tier's crypto carrier transports the program AND a sound verify-not-find certificate is available.
This is the "admissible" side — a behavioural predicate, distinct from the syntactic `passes`. -/
def RunnableAt (T : Tier) (m : Manifest) : Prop := carrierTransports T m ∧ verifyNotFind T m

/-! ## 2. THE ⟸ CORE — the manifest typecheck soundly delivers the runtime guarantee. -/

/-- **`passes_runnable` — `passes T m ⇒ RunnableAt T m` (the per-form soundness core).** The syntactic
tier-T manifest check implies the semantic runtime guarantee, by destructuring the manifest's boolean
clauses into the carrier-transport and certificate obligations. This is the type-system soundness — the
`fhIR` typecheck never promises a tier the math cannot deliver. Non-vacuous: `passes` is a Bool over
manifest fields, `RunnableAt` a semantic Prop about carrier + certificate; the proof maps one to the other. -/
theorem passes_runnable {T : Tier} {m : Manifest} (h : passes T m = true) : RunnableAt T m := by
  cases T with
  | dark =>
    simp only [passes, Bool.and_eq_true] at h
    exact ⟨⟨h.1.1.1.1, h.1.1.2⟩, h.1.2, h.2⟩
  | shielded =>
    simp only [passes, Bool.and_eq_true] at h
    exact ⟨h.1.1.2, h.1.2, h.2⟩
  | «open» => exact ⟨trivial, trivial⟩

/-! ## 3. Monotonicity — more visibility only ADDS runnable mechanisms (Tier 0 ⇒ 1 ⇒ 2). -/

/-- **`passes_mono` — the syntactic typecheck is monotone in visibility.** `passes dark ⇒ passes shielded
⇒ passes open`: DARK's requirements strictly contain SHIELDED's (it adds `publicOps`), which contain
OPEN's (`true`). -/
theorem passes_mono (m : Manifest) :
    (passes .dark m = true → passes .shielded m = true) ∧
    (passes .shielded m = true → passes .«open» m = true) := by
  constructor
  · intro h; simp only [passes, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨h.1.1.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩
  · intro _; rfl

/-- **`runnable_mono` — the semantic guarantee is monotone in visibility.** `RunnableAt dark ⇒ RunnableAt
shielded ⇒ RunnableAt open`: dropping `publicOps` from the carrier (dark → shielded) and then to the
public re-executor (shielded → open) only weakens the runtime demand. The `DREGGFI-PRIVACY-TIERS.md §3`
"Tier-0-admissible ⇒ Tier-1-admissible ⇒ Tier-2-admissible." -/
theorem runnable_mono (m : Manifest) :
    (RunnableAt .dark m → RunnableAt .shielded m) ∧
    (RunnableAt .shielded m → RunnableAt .«open» m) := by
  constructor
  · rintro ⟨⟨_, hb⟩, hv⟩; exact ⟨hb, hv⟩
  · rintro _; exact ⟨trivial, trivial⟩

/-! ## 4. Products (representation-relative) and the ⟸ KEYSTONE. -/

/-- **A product is a nonempty set of equivalent compiled FORMS** (reformulations under the declared
`ProxLib`) — the resource-relative view the admissibility theorem's honest maximality demands
(`FHEGG-PRODUCT-ORDER-FRONTIER.md`: equivalent convex functions can have radically different prox costs). -/
structure Product where
  /-- The equivalent compiled forms (reformulations). -/
  forms : List Manifest
  /-- At least one form (a real product compiles to something). -/
  nonempty : forms ≠ []

/-- **`compilesAt T P` — the compiler finds SOME form of `P` that passes the tier-T manifest.** -/
def compilesAt (T : Tier) (P : Product) : Prop := ∃ m ∈ P.forms, passes T m = true

/-- **`AdmissibleAt T P` — SOME form of `P` actually runs at tier T.** -/
def AdmissibleAt (T : Tier) (P : Product) : Prop := ∃ m ∈ P.forms, RunnableAt T m

/-- **`compiles_admissible` — THE KEYSTONE (⟸): a product that COMPILES at tier T is ADMISSIBLE at tier
T.** If some form passes the tier-T typecheck, that same form runs at tier T (`passes_runnable`), so the
product is admissible. The verify-not-find direction of the `fhIR` admissibility theorem, over the
resource-relative product. **This is the honest, tractable half of "admissible iff compiles."** -/
theorem compiles_admissible {T : Tier} {P : Product} (h : compilesAt T P) : AdmissibleAt T P := by
  obtain ⟨m, hmem, hpass⟩ := h
  exact ⟨m, hmem, passes_runnable hpass⟩

/-- **`admissible_mono` — admissibility is monotone in visibility (composed from `runnable_mono`).** -/
theorem admissible_mono (P : Product) :
    (AdmissibleAt .dark P → AdmissibleAt .shielded P) ∧
    (AdmissibleAt .shielded P → AdmissibleAt .«open» P) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨m, hm, hr⟩; exact ⟨m, hm, (runnable_mono m).1 hr⟩
  · rintro ⟨m, hm, hr⟩; exact ⟨m, hm, (runnable_mono m).2 hr⟩

/-! ## 5. The compiler offers the MOST PRIVATE honest tier (and refuses to promise more). -/

/-- **`mostPrivateTier m` — the most private tier the manifest honestly passes** (DARK if FHE-tractable,
else SHIELDED if STARK-tractable, else OPEN). The `DREGGFI-PRIVACY-TIERS.md §3` "the compiler reports the
most private tier a given product can honestly run at." -/
def mostPrivateTier (m : Manifest) : Tier :=
  if passes .dark m then .dark else if passes .shielded m then .shielded else .«open»

/-- **`mostPrivateTier_runnable` — the offered tier is ALWAYS genuinely runnable (sound offering).** The
compiler never promises a tier the math cannot deliver: whatever `mostPrivateTier` returns, the manifest
is `RunnableAt` it. (In the final `open` branch the public re-executor runs anything.) -/
theorem mostPrivateTier_runnable (m : Manifest) : RunnableAt (mostPrivateTier m) m := by
  unfold mostPrivateTier
  split_ifs with hd hs
  · exact passes_runnable hd
  · exact passes_runnable hs
  · exact ⟨trivial, trivial⟩

/-- **`mostPrivate_dark_iff` — the TYPE SYSTEM (not marketing) decides the DARK label.** The compiler
offers Tier 0 DARK for exactly the products that pass the DARK manifest — it cannot dark-wash a product
that fails the FHE typecheck. -/
theorem mostPrivate_dark_iff (m : Manifest) :
    mostPrivateTier m = .dark ↔ passes .dark m = true := by
  unfold mostPrivateTier
  constructor
  · intro h; by_contra hp
    simp only [Bool.not_eq_true] at hp
    rw [hp] at h; simp only [Bool.false_eq_true, if_false] at h
    split_ifs at h <;> simp_all
  · intro h; rw [h]; rfl

/-! ## 6. NON-VACUITY — positive polarity (a cheap product compiles + is admissible everywhere). -/

/-- A fully cheap product: public sparse operators, approved cone, bounded, convex, certificate — the
`fhEgg` base case (uniform-price auction / `Cert-F` circulation). -/
def cheapM : Manifest :=
  { publicOps := true, approvedCone := true, boundedDims := true,
    noIntegrality := true, traceIndepCert := true }

def cheapProduct : Product := ⟨[cheapM], by simp⟩

/-- **THE KEYSTONE, INSTANTIATED — the cheap product compiles at DARK, hence is admissible at every tier.**
It passes the DARK typecheck, so `compiles_admissible` gives `AdmissibleAt dark`, and `admissible_mono`
lifts it to SHIELDED and OPEN. A concrete, non-vacuous run through the ⟸ keystone + monotonicity. -/
theorem cheapProduct_admissible_everywhere :
    AdmissibleAt .dark cheapProduct ∧ AdmissibleAt .shielded cheapProduct ∧
      AdmissibleAt .«open» cheapProduct := by
  have hd : AdmissibleAt .dark cheapProduct := compiles_admissible ⟨cheapM, by simp [cheapProduct], rfl⟩
  have hs := (admissible_mono cheapProduct).1 hd
  exact ⟨hd, hs, (admissible_mono cheapProduct).2 hs⟩

/-- The most private tier of the cheap manifest is DARK (the compiler offers no-viewer). -/
theorem cheapM_mostPrivate : mostPrivateTier cheapM = .dark := by
  rw [mostPrivate_dark_iff]; rfl

/-! ## 7. NON-VACUITY — negative polarity (the reject-list bites; the tier a product runs at is a type). -/

/-- A private-matrix product (Markowitz QP: the covariance `Σ` is PRIVATE, so `publicOps = false`) — off
the FHE public-matvec line, but a bounded convex STARK circuit. -/
def markowitzM : Manifest :=
  { publicOps := false, approvedCone := true, boundedDims := true,
    noIntegrality := true, traceIndepCert := true }

def markowitzProduct : Product := ⟨[markowitzM], by simp⟩

/-- **TOOTH (private matrix ⇒ NOT DARK, offered SHIELDED).** The Markowitz QP fails the DARK typecheck
(`publicOps = false`: a private Hessian breaks the public-matvec FHE line), so it is NOT `compilesAt dark`
— but it DOES compile (and is admissible) at SHIELDED. The compiler refuses to promise Tier 0 and offers
the tier the math delivers. Mirrors `DREGGFI-PRIVACY-TIERS.md`'s "Markowitz → Tier 1." -/
theorem markowitz_not_dark_but_shielded :
    ¬ compilesAt .dark markowitzProduct ∧ AdmissibleAt .shielded markowitzProduct := by
  refine ⟨?_, compiles_admissible ⟨markowitzM, by simp [markowitzProduct], rfl⟩⟩
  rintro ⟨m, hm, hp⟩
  simp only [markowitzProduct, List.mem_singleton] at hm
  subst hm; simp [passes, markowitzM] at hp

/-- An endogenous-integrality product (AON / FOK: the fill itself is a binary decision, so
`noIntegrality = false`) — off the convex regime entirely. -/
def aonM : Manifest :=
  { publicOps := true, approvedCone := true, boundedDims := true,
    noIntegrality := false, traceIndepCert := true }

def aonProduct : Product := ⟨[aonM], by simp⟩

/-- **TOOTH (endogenous integrality ⇒ NOT SHIELDED, offered OPEN).** AON/FOK falls off the convex cliff
(`noIntegrality = false`), so it fails BOTH the DARK and SHIELDED typechecks — but the OPEN general matcher
(Johnson cycles + TTC) still expresses it. It is offered public-general only. Mirrors
`DREGGFI-PRIVACY-TIERS.md`'s "AON-FOK optimization → Tier 2." -/
theorem aon_not_shielded_but_open :
    ¬ compilesAt .shielded aonProduct ∧ AdmissibleAt .«open» aonProduct := by
  refine ⟨?_, compiles_admissible ⟨aonM, by simp [aonProduct], rfl⟩⟩
  rintro ⟨m, hm, hp⟩
  simp only [aonProduct, List.mem_singleton] at hm
  subst hm; simp [passes, aonM] at hp

/-! ## 8. THE OPEN ⟹ DIRECTION, made concrete — admissible does NOT imply compiles.

The full IFF `admissible ⟺ compiles` is the named research target. The ⟹ (admissible ⇒ compiles) FAILS
in general because the manifest's `approvedCone` clause is a CONSERVATIVE declaration (the v0 `ProxLib`),
not a runtime necessity: a bounded convex STARK circuit runs whether or not its cone is on the blessed
list. We exhibit the witness. -/

/-- A product whose cone is NOT on the conservative v0 `ProxLib` (`approvedCone = false`) but is a bounded,
convex, certified STARK circuit — it WOULD run at SHIELDED, but the manifest conservatively rejects it. -/
def frontierConeM : Manifest :=
  { publicOps := true, approvedCone := false, boundedDims := true,
    noIntegrality := true, traceIndepCert := true }

/-- **`runnable_not_compiles` — the per-form ⟹ counterexample.** `frontierConeM` is `RunnableAt shielded`
(a bounded convex certified circuit — the STARK carrier does not need the cone blessed) yet does NOT
`passes shielded` (its cone is off the declared v0 `ProxLib`). So the syntactic typecheck is STRICTLY
weaker than semantic runnability — the source of the resource-relative maximality gap. -/
theorem runnable_not_compiles :
    RunnableAt .shielded frontierConeM ∧ passes .shielded frontierConeM = false :=
  ⟨⟨rfl, rfl, rfl⟩, rfl⟩

def frontierProduct : Product := ⟨[frontierConeM], by simp⟩

/-- **`admissible_not_compiles` — the ⟹ direction is OPEN (product-level witness).** `frontierProduct` is
`AdmissibleAt shielded` (it runs) yet is NOT `compilesAt shielded` (no form passes the conservative
manifest). So `AdmissibleAt ⇏ compilesAt`: the full IFF requires the resource-relative maximality argument
(a declared `ProxLib` + cost budget) — the honest open piece of the six-part theorem. The ⟸ we proved
(`compiles_admissible`) is the sound, tractable half; this is precisely the gap that remains research. -/
theorem admissible_not_compiles :
    AdmissibleAt .shielded frontierProduct ∧ ¬ compilesAt .shielded frontierProduct := by
  refine ⟨⟨frontierConeM, by simp [frontierProduct], runnable_not_compiles.1⟩, ?_⟩
  rintro ⟨m, hm, hp⟩
  simp only [frontierProduct, List.mem_singleton] at hm
  subst hm
  rw [runnable_not_compiles.2] at hp
  exact absurd hp (by decide)

/-! ### `#guard` smoke — the typechecks are COMPUTED, not asserted. -/

-- the cheap product passes at every tier; its most-private tier is DARK:
#guard passes .dark cheapM == true
#guard passes .shielded cheapM == true
-- the private-matrix (Markowitz) product fails DARK, passes SHIELDED:
#guard passes .dark markowitzM == false
#guard passes .shielded markowitzM == true
-- the integrality (AON) product fails SHIELDED, passes OPEN:
#guard passes .shielded aonM == false
#guard passes .«open» aonM == true
-- the frontier-cone product is off the conservative manifest (the ⟹ gap):
#guard passes .shielded frontierConeM == false

/-! ### Axiom hygiene — the `fhIR` admissibility keystones pinned kernel-clean. -/

#assert_all_clean [Market.passes_runnable, Market.passes_mono, Market.runnable_mono,
  Market.compiles_admissible, Market.admissible_mono, Market.mostPrivateTier_runnable,
  Market.mostPrivate_dark_iff, Market.cheapProduct_admissible_everywhere, Market.cheapM_mostPrivate,
  Market.markowitz_not_dark_but_shielded, Market.aon_not_shielded_but_open,
  Market.runnable_not_compiles, Market.admissible_not_compiles]

end Market
