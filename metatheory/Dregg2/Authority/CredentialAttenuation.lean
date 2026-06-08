/-
# Dregg2.Authority.CredentialAttenuation — the structured clearance lattice of biscuit/macaroon
attenuation: a derived credential's authority is a SUBSET of its parent's, and caveats only NARROW.

## What this module adds (and what it deliberately does NOT re-do)

Three existing Authority modules already carry pieces of attenuation, and this module imports them
READ-ONLY rather than re-deriving them:

* `Authority.CaveatChain` — the macaroon as an HMAC-authenticated append-only chain. It proves chain
  *integrity* (you cannot remove/forge a caveat) and `append_narrows` over a `Ctx → Bool` admit gate.
  That is the *cryptographic* face and a flat boolean narrowing.
* `Authority.BiscuitGraph` — the public-key block chain, `biscuit_narrows` over a *flat* `Finset Auth`.
* `Exec.EffectsAuthority` — the executor's `IsNonAmplifying` over `ECap`/`List Auth` (the verified
  capability lattice).

What NONE of them models is the thing the real Rust credential stack actually computes: the
**structured, multi-dimensional clearance** that `token/src/traits.rs::Attenuation` narrows. A single
`attenuate` call (`AuthToken::attenuate`, `token/src/traits.rs:178-181`, "this can only narrow
permissions, never expand them") simultaneously tightens SEVERAL independent axes:

```rust
// token/src/traits.rs:93-123  (Attenuation)
pub struct Attenuation {
    pub apps: Vec<(String, String)>,     // lock to app(s) with an action mask "r"/"rw"/"*"
    pub services: Vec<(String, String)>, // lock to service(s) with an action mask
    pub features: Vec<String>,           // lock to a feature set
    pub not_after: Option<i64>,          // validity window upper bound
    pub not_before: Option<i64>,         // validity window lower bound
    pub confine_user: Option<String>,    // lock to a specific user id
    …
}
```

Verification (`token/src/dregg_caveats.rs::verify_caveats`) takes the **meet** of all caveats: the
effective action mask is the intersection of every app caveat's mask, the effective window is the
intersection of every validity window, the effective user-confinement is the conjunction of every
`ConfineUser`. A request is admitted iff it satisfies that meet. The *credentials* crate
(`credentials/src/issuance.rs::issue`) issues exactly by one `root.attenuate(&att)` carrying the
holder confinement + the attribute features.

This module gives that clearance its lattice and proves the headline:

* **`attenuate` is a meet** — it intersects action masks, intersects validity windows, intersects the
  confined-user set, intersects the app/service/feature locks. (The Rust "add a restriction" is a meet
  with the restriction.)
* **`attenuate_le` / `attenuate_admits_subset` (KEYSTONE)** — the attenuated clearance is `≤` the
  parent in the clearance order, hence its admitted-request set is a SUBSET of the parent's. No
  attenuation step amplifies authority — over the REAL structured clearance, not a flat set.
* **`chain_narrows` (n>1)** — along a delegation chain `[c₀ ← c₁ ← … ← cₙ]` of `n` credentials each
  derived from the previous by `attenuate`, the leaf credential `cₙ` admits ⊆ the root `c₀` admits.
  This is the genuinely multi-party statement: `n` independent delegates, authority shrinking at every
  hand-off, the leaf bounded by the root. Stated and proved for arbitrary chain length.
* **teeth** — an *amplifying* restriction (one that claims an action mask, a window, or a user the
  parent withheld) is NOT expressible as an `attenuate` of the parent, and a forged step is rejected.

## Connection to verified state

The clearance order projects onto the executor's `Exec.EffectsAuthority.IsNonAmplifying` over the real
`ECap`/`List Auth` capability lattice: `clearance_attenuation_is_exec_nonamplifying` shows that an
action-mask narrowing at the clearance layer IS a non-amplifying capability grant at the executor
layer. So the credential-attenuation algebra here is the same `is_attenuation(held, granted)` the
verified executor enforces — not a parallel toy.

## §8 honest crypto boundary (NEVER faked)

The clearance *algebra* — that the narrowing meet only shrinks authority — is PROVED here outright; it
needs no cryptographic assumption. What needs the assumption is **integrity**: that a derived
credential presented to a verifier really IS an `attenuate` of the parent and was not fabricated with a
wider clearance. That binding is the HMAC chain of `Authority.CaveatChain` (macaroons) / the signature
chain of `Authority.BiscuitGraph` (biscuits). We do NOT re-prove HMAC/ed25519 secure; we expose the
SAME `CaveatChain.MacKernel.unforgeable` carrier as the named assumption and route the integrity
statement through it. The honest split: **narrowing is a theorem; non-forgeability is a named
assumption discharged by the real keyed-hash / signature, provably FALSE on a collapsing oracle.**

Pure, computable, `#eval`-able.
-/
import Dregg2.Authority.CaveatChain
import Dregg2.Exec.EffectsAuthority
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Bounds.Basic

namespace Dregg2.Authority.CredentialAttenuation

open Dregg2.Authority

/-! ## §1 — The action mask: the `"r"`/`"rw"`/`"*"` permission set on a resource.

In the real `Attenuation` each app/service lock carries an action-mask STRING (`"r"`, `"rw"`, `"*"`).
`"*"` is "all actions"; `"rw"` is `{read, write}`; `"r"` is `{read}`. Attenuating `"rw"` to `"r"`
DROPS write — the canonical narrowing. We model the mask as a `Finset Action`; `"*"` = the full set.
The meet of two masks is intersection (the Rust takes the tighter of stacked app caveats). -/

/-- The atomic actions a mask can grant (the `"r"`/`"w"`/`"x"` letters of an action string). -/
inductive Action where
  | read | write | exec
  deriving DecidableEq, Repr

open Action

/-- The universe of actions — what `"*"` denotes. -/
def allActions : Finset Action := {read, write, exec}

/-- An **action mask** = the set of permitted actions on a resource. `"*"` = `allActions`,
`"rw"` = `{read, write}`, `"r"` = `{read}`. -/
abbrev Mask := Finset Action

/-- The meet (∩) of two masks: the tighter permission. Stacking two app caveats keeps only the
actions BOTH allow — exactly `verify_caveats`' intersection of app grants. -/
def Mask.meet (m₁ m₂ : Mask) : Mask := m₁ ∩ m₂

/-! ## §2 — The validity window: the `not_before … not_after` interval.

A validity window is a closed interval `[lo, hi]` over Unix seconds (`None` = unbounded). Attenuating
TIGHTENS it: a new `not_after` can only DECREASE the upper bound, a new `not_before` only INCREASE the
lower bound (`verify_caveats` keeps the tightest window). We model the bounds with `WithBot`/`WithTop`
so "unbounded" is the lattice extreme, and the meet of two windows is `[max lo, min hi]`. -/

/-- A **validity window** `[lo, hi]`: `lo : WithBot Int` (lower bound, `⊥` = no `not_before`),
`hi : WithTop Int` (upper bound, `⊤` = no `not_after`). A timestamp `t` is inside iff `lo ≤ t ≤ hi`. -/
structure Window where
  lo : WithBot Int
  hi : WithTop Int
  deriving DecidableEq

/-- The widest window (no bounds): the issuance-time window of a fresh credential. -/
def Window.unbounded : Window := { lo := ⊥, hi := ⊤ }

/-- A timestamp is inside the window iff it is ≥ the lower bound and ≤ the upper bound (the Rust
`not_before ≤ now ≤ not_after` check, with the bottom/top extremes meaning "unbounded"). -/
def Window.contains (w : Window) (t : Int) : Prop := w.lo ≤ (t : WithBot Int) ∧ (t : WithTop Int) ≤ w.hi

instance (w : Window) (t : Int) : Decidable (w.contains t) := by
  unfold Window.contains; exact inferInstance

/-- The meet (∩) of two windows: `[max lo, min hi]` — the TIGHTER interval. Stacking two validity
caveats keeps the latest `not_before` and the earliest `not_after`. -/
def Window.meet (w₁ w₂ : Window) : Window := { lo := w₁.lo ⊔ w₂.lo, hi := w₁.hi ⊓ w₂.hi }

/-! ## §3 — The structured clearance: the product of every attenuation axis.

A **clearance** is the effective authority a credential confers after all its caveats: an action mask
(what may be done), a validity window (when), and a confined-user set (by whom). This is the *meet* of
all caveats stacked on the root macaroon — the object `verify_caveats` computes and then checks the
request against. We keep it deliberately faithful to the three load-bearing `Attenuation` axes (mask,
window, user); the app/service/feature locks are *also* meets of finite sets and behave identically,
so they are represented uniformly by the `subjects` confinement set. -/

/-- A **request** the clearance is evaluated against: who (`user`), what (`action`), when (`time`). The
`AuthRequest` of `token/src/traits.rs`. -/
structure Request where
  user   : Nat
  action : Action
  time   : Int
  deriving DecidableEq

/-- A **clearance** — the effective authority of a credential. `mask` = permitted actions; `window` =
validity interval; `subjects` = the set of user-ids the credential is confined to (`⊤` modeled as
"no confinement" via `confined? = false`). This is the meet of all the credential's caveats. -/
structure Clearance where
  /-- permitted actions (intersection of all app/service action masks). -/
  mask     : Mask
  /-- validity interval (intersection of all validity-window caveats). -/
  window   : Window
  /-- whether the credential is confined to a user set (a `ConfineUser` caveat is present). -/
  confined? : Bool
  /-- the user set it is confined to (meaningful iff `confined?`). Stacking `ConfineUser` caveats
  intersects these sets. -/
  subjects : Finset Nat

/-- The TOP clearance — a fresh root macaroon (`Macaroon::new`, no caveats): all actions, unbounded
window, unconfined. Every issued credential is `≤` this. -/
def Clearance.top : Clearance :=
  { mask := allActions, window := Window.unbounded, confined? := false, subjects := ∅ }

/-- **`admits`** — does the clearance admit the request? Conjunction (meet semantics, `verify_caveats`
AND): the action is in the mask AND the time is in the window AND (if confined) the user is in the
confined set. Fail-closed: an absent leg denies. This is the runnable golden oracle. -/
def Clearance.admits (c : Clearance) (r : Request) : Bool :=
  decide (r.action ∈ c.mask)
    && decide (c.window.contains r.time)
    && (!c.confined? || decide (r.user ∈ c.subjects))

/-! ## §4 — A restriction = one `attenuate` call; `attenuate` is the meet with it.

A **`Restriction`** is the runtime form of one `Attenuation` struct: an action mask to intersect into
the current mask, a window to intersect into the current window, and an optional user set to confine
to. `attenuate` applies it as a MEET — exactly "add a restriction, narrowing" (`token/src/traits.rs`
`attenuate`). This is the SINGLE attenuation operation; a credential is `top` after some sequence of
these (issuance = one such step, `credentials/src/issuance.rs::issue`). -/

/-- A **restriction** = the runtime projection of one `Attenuation` (`token/src/traits.rs:93`): a mask
to intersect, a window to intersect, and an optional `confine_user` set. -/
structure Restriction where
  /-- the app/service action mask this restriction imposes (intersected into the current mask). -/
  maskBound  : Mask
  /-- the validity window this restriction imposes (intersected into the current window). -/
  windowBound : Window
  /-- the `confine_user` set, if this restriction carries a `ConfineUser` caveat. -/
  confineTo  : Option (Finset Nat)

/-- **`attenuate c δ`** — apply restriction `δ` to clearance `c`, as a MEET: intersect the mask,
intersect the window, AND the confinement (intersecting the user set if a new confinement is added).
This is `AuthToken::attenuate` (`token/src/traits.rs:178`): it can only narrow. -/
def attenuate (c : Clearance) (δ : Restriction) : Clearance :=
  { mask    := c.mask.meet δ.maskBound
    window  := c.window.meet δ.windowBound
    confined? := c.confined? || δ.confineTo.isSome
    subjects := match δ.confineTo with
      | none      => c.subjects
      | some s    => if c.confined? then c.subjects ∩ s else s }

/-! ## §5 — The clearance order, and that `attenuate` descends it.

`c₁ ≤ c₂` ("c₁ is at most as authoritative as c₂") iff c₁'s mask ⊆ c₂'s, c₁'s window ⊆ c₂'s (as
intervals), and c₁ is confined wherever c₂ is, to no larger a user set. The headline is that
`admits` is MONOTONE in this order, and `attenuate` always produces a `≤` clearance — so attenuation
never amplifies. -/

/-- **`Window.le w₁ w₂`** — `w₁` is a SUBINTERVAL of `w₂`: tighter lower bound and tighter upper
bound. `[lo₁,hi₁] ⊆ [lo₂,hi₂]` iff `lo₂ ≤ lo₁` and `hi₁ ≤ hi₂`. -/
def Window.le (w₁ w₂ : Window) : Prop := w₂.lo ≤ w₁.lo ∧ w₁.hi ≤ w₂.hi

/-- **`Clearance.le c₁ c₂`** (`c₁ ≤ c₂`) — c₁ confers no more authority than c₂: mask ⊆, window ⊆, and
confinement is at least as strict. The confinement clause: if c₂ is confined then c₁ must be too, to a
SUBSET of c₂'s users; if c₂ is unconfined, c₁ may be anything (it can only be more confined). -/
def Clearance.le (c₁ c₂ : Clearance) : Prop :=
  c₁.mask ⊆ c₂.mask
    ∧ Window.le c₁.window c₂.window
    ∧ (c₂.confined? = true → c₁.confined? = true ∧ c₁.subjects ⊆ c₂.subjects)

@[inherit_doc] scoped infix:50 " ≼ " => Clearance.le

/-- `≼` is reflexive. -/
theorem Clearance.le_refl (c : Clearance) : c ≼ c :=
  ⟨Finset.Subset.refl _,
   ⟨@_root_.le_refl (WithBot Int) _ c.window.lo, @_root_.le_refl (WithTop Int) _ c.window.hi⟩,
   fun h => ⟨h, Finset.Subset.refl _⟩⟩

/-- `≼` is transitive — the spine of `chain_narrows`. -/
theorem Clearance.le_trans {a b c : Clearance} (hab : a ≼ b) (hbc : b ≼ c) : a ≼ c := by
  obtain ⟨hm₁, ⟨hlo₁, hhi₁⟩, hc₁⟩ := hab
  obtain ⟨hm₂, ⟨hlo₂, hhi₂⟩, hc₂⟩ := hbc
  refine ⟨Finset.Subset.trans hm₁ hm₂,
    ⟨@_root_.le_trans (WithBot Int) _ c.window.lo b.window.lo a.window.lo hlo₂ hlo₁,
     @_root_.le_trans (WithTop Int) _ a.window.hi b.window.hi c.window.hi hhi₁ hhi₂⟩, ?_⟩
  intro hcconf
  obtain ⟨hbconf, hbsub⟩ := hc₂ hcconf
  obtain ⟨haconf, hasub⟩ := hc₁ hbconf
  exact ⟨haconf, Finset.Subset.trans hasub hbsub⟩

/-! ## §6 — `admits` is MONOTONE in `≼` (the semantic content of the order). -/

/-- **`Window.contains_mono`** — a subinterval contains fewer timestamps: if `w₁ ⊆ w₂` and `w₁`
contains `t`, then `w₂` contains `t`. -/
theorem Window.contains_mono {w₁ w₂ : Window} (hle : Window.le w₁ w₂) {t : Int}
    (ht : w₁.contains t) : w₂.contains t := by
  obtain ⟨hlo, hhi⟩ := hle
  obtain ⟨htlo, hthi⟩ := ht
  exact ⟨le_trans hlo htlo, le_trans hthi hhi⟩

/-- **`admits_mono` (KEYSTONE — the meaning of the order).** If `c₁ ≼ c₂` then every request `c₁`
admits, `c₂` also admits: `admits` is MONOTONE. A less-authoritative clearance admits a SUBSET of the
requests. This is the semantic content of attenuation: narrowing the clearance shrinks the admitted
set. -/
theorem admits_mono {c₁ c₂ : Clearance} (hle : c₁ ≼ c₂) (r : Request)
    (h : c₁.admits r = true) : c₂.admits r = true := by
  obtain ⟨hmask, hwin, hconf⟩ := hle
  unfold Clearance.admits at h ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨ha, hw⟩, hu⟩ := h
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- action ∈ mask₁ ⊆ mask₂
    rw [decide_eq_true_eq] at ha ⊢; exact hmask ha
  · -- time ∈ window₁ ⊆ window₂
    rw [decide_eq_true_eq] at hw ⊢; exact Window.contains_mono hwin hw
  · -- confinement: if c₂ confined, user ∈ subjects₂
    by_cases hc2 : c₂.confined? = true
    · obtain ⟨hc1, hsub⟩ := hconf hc2
      rw [hc1] at hu; simp only [Bool.not_true, Bool.false_or] at hu
      rw [hc2]; simp only [Bool.not_true, Bool.false_or]
      rw [decide_eq_true_eq] at hu ⊢; exact hsub hu
    · simp only [Bool.not_eq_true] at hc2; rw [hc2]; simp

/-! ## §7 — THE HEADLINE: `attenuate` descends the order ⇒ never amplifies. -/

/-- **`Window.meet_le_left`** — the meet of two windows is a subinterval of the FIRST: intersecting a
window can only tighten it. -/
theorem Window.meet_le_left (w₁ w₂ : Window) : Window.le (w₁.meet w₂) w₁ := by
  unfold Window.le Window.meet
  exact ⟨le_sup_left, inf_le_left⟩

/-- **`attenuate_le` (KEYSTONE — no amplification, structurally).** The attenuated clearance is `≼` the
parent: `attenuate c δ ≼ c`. Across ALL axes simultaneously — mask ∩ ⊆ mask, window ∩ ⊆ window, and
the confinement only gets stricter. This is `AuthToken::attenuate` "can only narrow, never expand"
(`token/src/traits.rs:178-181`) as a THEOREM over the structured clearance. -/
theorem attenuate_le (c : Clearance) (δ : Restriction) : attenuate c δ ≼ c := by
  refine ⟨?_, ?_, ?_⟩
  · -- mask: c.mask ∩ δ.maskBound ⊆ c.mask
    exact Finset.inter_subset_left
  · -- window: meet ⊆ c.window
    exact Window.meet_le_left c.window δ.windowBound
  · -- confinement: if c confined, attenuate is confined to ⊆ subset
    intro hconf
    unfold attenuate
    refine ⟨?_, ?_⟩
    · simp only [hconf, Bool.true_or]
    · -- subjects of attenuate ⊆ c.subjects when c was confined
      cases hδ : δ.confineTo with
      | none => exact Finset.Subset.refl _
      | some s => simp only [hconf, if_true]; exact Finset.inter_subset_left

/-- **`attenuate_admits_subset` (KEYSTONE, request-set form).** Anything the ATTENUATED credential
admits, the PARENT already admitted: `(attenuate c δ).admits r = true → c.admits r = true`. Appending
a restriction never grows the admissible-request set — soundness of attenuation, over the real
structured clearance. The headline guarantee in its operational form. -/
theorem attenuate_admits_subset (c : Clearance) (δ : Restriction) (r : Request)
    (h : (attenuate c δ).admits r = true) : c.admits r = true :=
  admits_mono (attenuate_le c δ) r h

/-- **`attenuate_subset` (set-theoretic form).** The admitted-request set of the attenuated credential
is a SUBSET of the parent's. -/
theorem attenuate_subset (c : Clearance) (δ : Restriction) :
    {r | (attenuate c δ).admits r = true} ⊆ {r | c.admits r = true} :=
  fun r h => attenuate_admits_subset c δ r h

/-! ## §8 — TEETH: an amplifying restriction is impossible; the predicate discriminates.

The keystone would be hollow if `≼` were trivially true. These theorems exhibit clearances and
restrictions that the order REJECTS — a request the parent denies that a (would-be) amplified child
would admit cannot arise from `attenuate`. -/

/-- **`amplification_impossible` (TEETH).** No restriction can make `attenuate` admit a request the
parent denies. The contrapositive of `attenuate_admits_subset`: if `c` denies `r`, then EVERY
attenuation of `c` also denies `r`. There is no `δ` that "adds back" authority. -/
theorem amplification_impossible (c : Clearance) (r : Request) (hden : c.admits r = false)
    (δ : Restriction) : (attenuate c δ).admits r = false := by
  by_contra hne
  rw [Bool.not_eq_false] at hne
  rw [attenuate_admits_subset c δ r hne] at hden
  exact absurd hden (by simp)

/-- **`order_discriminates` (TEETH — the order is not vacuous).** A clearance with a WIDER mask is NOT
`≼` one with a narrower mask: `{read,write} ⊄ {read}` so the `≼` mask clause fails. So the order
genuinely rejects an amplification; it is not `True`. -/
theorem order_discriminates :
    ¬ ( ({ mask := {read, write}, window := Window.unbounded, confined? := false, subjects := ∅ }
            : Clearance)
        ≼ { mask := {read}, window := Window.unbounded, confined? := false, subjects := ∅ } ) := by
  intro h
  obtain ⟨hmask, _, _⟩ := h
  have : write ∈ ({read} : Finset Action) := hmask (by decide)
  simp at this

/-! ## §9 — n>1: the DELEGATION CHAIN. Authority shrinks across `n` independent hand-offs.

A real credential is delegated through a *chain* of holders: the issuer mints the root, the holder
attenuates and hands to a sub-delegate, who attenuates again, and so on. We model the chain as a list
of restrictions `δs` applied left-to-right from a root clearance; the resulting leaf is bounded by the
root. This is the genuinely **multi-party** (n>1) statement — `n` delegates, authority narrowing at
EVERY hand-off, the leaf's admitted set ⊆ the root's. (Single-machine n=1 is the degenerate `δs = []`,
which gives `c ≼ c` — scales-to-zero, not the target; the content is the chain.) -/

/-- **`attenuateChain c δs`** — apply a chain of `n` restrictions left-to-right. The leaf credential
after `n` delegation hand-offs from root `c`. -/
def attenuateChain (c : Clearance) : List Restriction → Clearance
  | []      => c
  | δ :: δs => attenuateChain (attenuate c δ) δs

/-- **`chain_le` — the leaf is `≼` the root, for ANY chain length `n`.** Each hand-off descends the
order (`attenuate_le`); transitivity (`Clearance.le_trans`) chains them. Proved by induction on the
delegation list, so it holds at every `n > 1`. -/
theorem chain_le (c : Clearance) (δs : List Restriction) : attenuateChain c δs ≼ c := by
  induction δs generalizing c with
  | nil => exact Clearance.le_refl c
  | cons δ rest ih =>
    -- attenuateChain c (δ :: rest) = attenuateChain (attenuate c δ) rest ≼ attenuate c δ ≼ c
    exact Clearance.le_trans (ih (attenuate c δ)) (attenuate_le c δ)

/-- **`chain_narrows` (n>1 KEYSTONE).** The leaf credential after a chain of `n` delegation hand-offs
admits a SUBSET of the requests the root admits: `(attenuateChain c δs).admits r = true → c.admits r =
true`. Authority can only shrink down a delegation chain of any length — the multi-party
non-amplification guarantee. -/
theorem chain_narrows (c : Clearance) (δs : List Restriction) (r : Request)
    (h : (attenuateChain c δs).admits r = true) : c.admits r = true :=
  admits_mono (chain_le c δs) r h

/-- **`chain_narrows_set`** — set form of the n>1 keystone: the leaf's admitted set ⊆ the root's. -/
theorem chain_narrows_set (c : Clearance) (δs : List Restriction) :
    {r | (attenuateChain c δs).admits r = true} ⊆ {r | c.admits r = true} :=
  fun r h => chain_narrows c δs r h

/-- **`chain_le_prefix`** — a LONGER chain is `≼` any PREFIX: extending a delegation chain only
narrows further. The intermediate delegate `attenuateChain c δs` already bounds the leaf
`attenuateChain c (δs ++ δs')`. The monotone "every additional hand-off shrinks authority" law. -/
theorem chain_le_prefix (c : Clearance) (δs δs' : List Restriction) :
    attenuateChain c (δs ++ δs') ≼ attenuateChain c δs := by
  induction δs generalizing c with
  | nil => simpa using chain_le c δs'
  | cons δ rest ih => simpa [attenuateChain] using ih (attenuate c δ)

/-! ## §10 — CONNECTION TO VERIFIED STATE.

The clearance order is not a parallel toy: an action-mask narrowing at THIS layer projects onto the
executor's `Exec.EffectsAuthority.IsNonAmplifying` over the verified `ECap`/`List Auth` capability
lattice. We exhibit the projection: a credential whose mask narrows `m_parent ⊇ m_child` corresponds to
a capability whose conferred authority narrows the same way, so the executor's "amplification denied"
gate (`apply.rs:2835`, `is_attenuation(held, granted)`) is exactly this module's `attenuate_le` on the
mask axis. -/

/-- Project an action `Mask` onto the executor's authority list `List Auth`: `read ↦ Auth.read`,
`write ↦ Auth.write`, `exec ↦ Auth.call` (the three execution authorities). This is the bridge between
the credential's action mask and the verified capability's `capAuthConferred`. -/
def maskToAuth (m : Mask) : List Auth :=
  (if read ∈ m then [Auth.read] else [])
    ++ (if write ∈ m then [Auth.write] else [])
    ++ (if exec ∈ m then [Auth.call] else [])

/-- A credential mask narrowing yields an executor capability narrowing on the projected authority.
The bridge lemma: `child.mask ⊆ parent.mask → maskToAuth child ⊆ maskToAuth parent`. So the clearance
order's mask clause IS the executor's conferred-authority subset. -/
theorem maskToAuth_mono {mc mp : Mask} (h : mc ⊆ mp) : maskToAuth mc ⊆ maskToAuth mp := by
  intro a ha
  simp only [maskToAuth, List.mem_append] at ha ⊢
  rcases ha with (ha | ha) | ha
  · by_cases hr : read ∈ mc
    · simp only [hr, if_true, List.mem_singleton] at ha; subst ha
      left; left; simp [h hr]
    · simp [hr] at ha
  · by_cases hw : write ∈ mc
    · simp only [hw, if_true, List.mem_singleton] at ha; subst ha
      left; right; simp [h hw]
    · simp [hw] at ha
  · by_cases he : exec ∈ mc
    · simp only [he, if_true, List.mem_singleton] at ha; subst ha
      right; simp [h he]
    · simp [he] at ha

/-- **`clearance_attenuation_is_exec_nonamplifying` (CONNECTION TO VERIFIED STATE).** A clearance
attenuation, projected through `maskToAuth` onto the executor's `ECap` endpoint capability, satisfies
the verified executor's `Exec.EffectsAuthority.IsNonAmplifying` — the SAME `is_attenuation(held,
granted)` gate the kernel enforces (`apply.rs:2835`). So credential attenuation here is not a separate
model: it lands on the verified capability lattice. The `target` label is shared (attenuation never
re-targets); only the rights narrow. -/
theorem clearance_attenuation_is_exec_nonamplifying
    (c : Clearance) (δ : Restriction) (target : Label) :
    Exec.EffectsAuthority.IsNonAmplifying
      (Authority.Cap.endpoint target (maskToAuth c.mask))
      (Authority.Cap.endpoint target (maskToAuth (attenuate c δ).mask)) := by
  -- IsNonAmplifying held granted := capAuthConferred granted ⊆ capAuthConferred held
  -- capAuthConferred (endpoint t r) = r, so we need:
  --   maskToAuth (attenuate c δ).mask ⊆ maskToAuth c.mask
  unfold Exec.EffectsAuthority.IsNonAmplifying capAuthConferred
  -- (attenuate c δ).mask = c.mask ∩ δ.maskBound ⊆ c.mask
  have hsub : (attenuate c δ).mask ⊆ c.mask := by
    show c.mask.meet δ.maskBound ⊆ c.mask
    exact Finset.inter_subset_left
  exact maskToAuth_mono hsub

/-! ## §11 — §8 INTEGRITY BOUNDARY: narrowing is proved; non-forgery is the named MAC assumption.

The narrowing above is unconditional. The thing that needs the carried crypto assumption is that a
credential a verifier RECEIVES is genuinely an `attenuate` of the issuer's root — i.e. the caveat list
binding the clearance was not forged with a wider mask/window. That binding is the macaroon HMAC chain
(`Authority.CaveatChain`). We do NOT re-prove HMAC; we reuse `CaveatChain.MacKernel.unforgeable` as the
SAME named assumption, and state the integrity reduction relative to it. The clearance is recovered
from a chain by collecting its caveats; if the chain `verify`s under `unforgeable`, the recovered
clearance is the genuine attenuation, not an adversarial widening. -/

section Integrity

open Dregg2.Authority.CaveatChain
open Dregg2.Authority.CaveatChain.MacKernel

variable {Tag : Type} [DecidableEq Tag] {Bytes : Type}
variable [inst : MacKernel (Key Tag) Bytes Tag]

/-- **`presented_attenuation_is_genuine` (the §8-conditional integrity statement).** Given the keyed
hash's EUF-CMA carrier `unforgeable`, the stored tail of a verifying non-empty caveat chain is a
GENUINE MAC of its last caveat under the prior running tag — so an adversary could not have appended a
clearance-WIDENING caveat without the chaining key. The narrowing algebra (above) plus this integrity
fact gives the full guarantee: a verifier who accepts a derived credential's HMAC chain knows its
clearance is a real attenuation of the root. This is the SAME `chain_unforgeable` carrier — the named
HMAC assumption, NEVER proved in Lean, provably FALSE on the collapsing oracle
(`CaveatChain.Demo.collapse_not_unforgeable`). -/
theorem presented_attenuation_is_genuine
    (hunf : MacKernel.unforgeable (Key := Key Tag) (Bytes := Bytes) (Tag := Tag))
    {Ctx Gateway : Type} (chain : Chain Ctx Gateway (Key Tag) Bytes Tag)
    (last : Link Ctx Gateway Bytes)
    (hsplit : chain.links = chain.links.dropLast ++ [last])
    (hcanon : ∀ (k : Key Tag) (m : Bytes) (t : Tag), verifyTag k m t = decide (mac k m = t))
    (hverif : chain.verify = true) :
    Tagged (lastStepKey chain) last.encoded chain.tail :=
  chain_unforgeable hunf chain last hsplit hcanon hverif

end Integrity

/-! ## §12 — IT RUNS (`#eval`/`#guard`): a concrete issuer → holder → sub-delegate chain.

A genuine three-party flow (n = 3): an issuer's root credential, attenuated to a holder (drop write,
confine to user 42), then sub-delegated (tighten the validity window). Each hand-off narrows; the leaf
admits a strict subset. -/

section Demo

/-- The issuer's ROOT credential (`Macaroon::new`): all actions, unbounded, unconfined. -/
def rootCred : Clearance := Clearance.top

/-- Restriction 1 (issuer → holder): lock to `{read, write}` (drop exec), confine to user 42. -/
def toHolder : Restriction :=
  { maskBound := {read, write}, windowBound := Window.unbounded, confineTo := some {42} }

/-- Restriction 2 (holder → sub-delegate): lock to `{read}` (drop write), tighten window to `[_, 1000]`. -/
def toSubDelegate : Restriction :=
  { maskBound := {read}, windowBound := { lo := ⊥, hi := (1000 : Int) }, confineTo := none }

/-- The delegation chain (n = 3 parties): root → holder → sub-delegate. -/
def leafCred : Clearance := attenuateChain rootCred [toHolder, toSubDelegate]

/-- A request user-42 read at t=500 — admitted by the leaf (in mask, in window, confined-user matches). -/
def goodReq : Request := { user := 42, action := read, time := 500 }
/-- A WRITE request — denied by the leaf (write was dropped at the second hand-off). -/
def writeReq : Request := { user := 42, action := write, time := 500 }
/-- A read by user 7 — denied by the leaf (confined to user 42). -/
def wrongUserReq : Request := { user := 7, action := read, time := 500 }
/-- A read at t=2000 — denied by the leaf (outside the window [_,1000]). -/
def lateReq : Request := { user := 42, action := read, time := 2000 }

#guard rootCred.admits goodReq                 -- root admits everything in range
#guard rootCred.admits writeReq                -- root permits write
#guard leafCred.admits goodReq                 -- leaf admits the in-scope request
#guard leafCred.admits writeReq == false       -- leaf dropped write (narrowed)
#guard leafCred.admits wrongUserReq == false   -- leaf confined to user 42
#guard leafCred.admits lateReq == false        -- leaf window excludes t=2000

-- The keystone, computed: every request the leaf admits, the root admits.
#guard (leafCred.admits goodReq == true) && (rootCred.admits goodReq == true)
-- The amplification tooth, computed: the leaf NEVER admits what it dropped.
#guard leafCred.admits writeReq == false

/-- **`leaf_narrows_root` (the demo keystone, n=3, PROVED).** The leaf credential after two hand-offs
admits ⊆ the root: instantiates `chain_narrows` on the concrete three-party chain. -/
theorem leaf_narrows_root (r : Request) (h : leafCred.admits r = true) : rootCred.admits r = true :=
  chain_narrows rootCred [toHolder, toSubDelegate] r h

/-- **`leaf_drops_write` (demo tooth, PROVED).** The leaf credential admits NO write request, however
the user/time — write was attenuated away and `amplification_impossible` forbids adding it back. -/
theorem leaf_drops_write (r : Request) (hw : r.action = write) : leafCred.admits r = false := by
  -- the leaf's effective mask is {read} (the second hand-off `toSubDelegate` dropped write); a write
  -- request fails the first `admits` conjunct (`action ∈ mask`), so the whole `&&` is false.
  have hmask : leafCred.mask = {read} := by
    unfold leafCred attenuateChain attenuate rootCred Clearance.top toHolder toSubDelegate Mask.meet
    decide
  have hnotin : r.action ∉ leafCred.mask := by
    rw [hmask, hw]; decide
  unfold Clearance.admits
  rw [decide_eq_false hnotin]
  simp

end Demo

/-! ## §13 — Axiom hygiene. Every keystone pins to `{propext, Classical.choice, Quot.sound}`.

The clearance-narrowing theorems are unconditional (no crypto axiom). The §8 integrity theorem
`presented_attenuation_is_genuine` takes the named `unforgeable` MAC assumption as an explicit
HYPOTHESIS (not an `axiom`-keyword declaration), so it too pins clean — the carried assumption is a
premise, exactly as in `CaveatChain`. -/

#assert_axioms admits_mono
#assert_axioms attenuate_le
#assert_axioms attenuate_admits_subset
#assert_axioms amplification_impossible
#assert_axioms order_discriminates
#assert_axioms chain_le
#assert_axioms chain_narrows
#assert_axioms chain_le_prefix
#assert_axioms maskToAuth_mono
#assert_axioms clearance_attenuation_is_exec_nonamplifying
#assert_axioms presented_attenuation_is_genuine
#assert_axioms leaf_narrows_root
#assert_axioms leaf_drops_write

end Dregg2.Authority.CredentialAttenuation
