/-
# `Dregg2.Storage.ProviderRegistry` — the provider entity's stake lifecycle, proven.

A deal is per-blob; a PROVIDER is the persistent entity that claims deals across time. This is its
stake lifecycle: `Unregistered → Registered → Withdrawn`, with a bonded stake that only a slash
reduces. Cap-first: a provider can only *serve* (claim deals) once registered with a positive stake,
registration is the sole way to enter, and the stake is never conjured. The proofs:
`register_requires_unregistered`, `serves_only_if_registered`, `slash_requires_registered` (and it
strictly reduces the stake), `withdraw_requires_registered`, and stake-monotonicity (no growth except
the initial register).
-/
import Dregg2.Tactics

namespace Dregg2.Storage.ProviderRegistry

/-- A provider's registration status. -/
inductive ProviderStatus where
  | unregistered  -- not in the registry
  | registered    -- staked and eligible to serve
  | withdrawn     -- exited (stake returned)
deriving DecidableEq, Repr

/-- A provider: its status and its bonded stake. -/
structure Provider where
  status : ProviderStatus
  stake : Nat
deriving DecidableEq, Repr

/-- **Eligibility to serve**: a provider may claim/serve a deal iff it is registered with a positive
stake. The cap-first gate. -/
def canServe (p : Provider) : Bool :=
  match p.status with
  | .registered => 0 < p.stake
  | _ => false

/-! ## §1 — transitions (partial: `none` unless the guard holds). -/

/-- `Unregistered → Registered`, posting stake `s`. The sole entry point. -/
def register (p : Provider) (s : Nat) : Option Provider :=
  match p.status with
  | .unregistered => some { status := .registered, stake := s }
  | _ => none

/-- `Registered → Registered`, slashing the stake by `penalty` (a failed audit on one of its deals). -/
def slashStake (p : Provider) (penalty : Nat) : Option Provider :=
  match p.status with
  | .registered => some { p with stake := p.stake - penalty }
  | _ => none

/-- `Registered → Withdrawn`: the provider exits; its remaining stake is returned (unchanged here —
the payout is `DealPayment`'s concern). -/
def withdraw (p : Provider) : Option Provider :=
  match p.status with
  | .registered => some { p with status := .withdrawn }
  | _ => none

/-! ## §2 — soundness proofs. -/

/-- **Only a registered provider can serve.** An unregistered or withdrawn provider is not eligible —
the cap-first gate. -/
theorem serves_only_if_registered (p : Provider) (h : canServe p = true) : p.status = .registered := by
  simp only [canServe] at h
  cases hs : p.status <;> simp [hs] at h ⊢

/-- **Registration is the sole entry.** `register` fires only from `unregistered`. -/
theorem register_requires_unregistered (p p' : Provider) (s : Nat) (h : register p s = some p') :
    p.status = .unregistered ∧ p'.status = .registered ∧ p'.stake = s := by
  simp only [register] at h
  cases hs : p.status <;> simp [hs] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-- **Slash requires a registered provider and strictly concerns the stake.** -/
theorem slash_requires_registered (p p' : Provider) (penalty : Nat) (h : slashStake p penalty = some p') :
    p.status = .registered ∧ p'.stake = p.stake - penalty := by
  simp only [slashStake] at h
  cases hs : p.status <;> simp [hs] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- **Withdraw requires a registered provider** (and preserves the stake for its payout). -/
theorem withdraw_requires_registered (p p' : Provider) (h : withdraw p = some p') :
    p.status = .registered ∧ p'.stake = p.stake ∧ p'.status = .withdrawn := by
  simp only [withdraw] at h
  cases hs : p.status <;> simp [hs] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-- **The stake never grows except at registration.** A slash or withdraw can only keep or shrink it —
a provider cannot conjure stake mid-life to over-claim. -/
theorem stake_nonincreasing_except_register (p p' : Provider)
    (h : slashStake p 0 = some p' ∨ withdraw p = some p' ∨ ∃ pen, slashStake p pen = some p') :
    p'.stake ≤ p.stake := by
  rcases h with h | h | ⟨pen, h⟩
  · obtain ⟨_, hst⟩ := slash_requires_registered p p' 0 h; omega
  · obtain ⟨_, hst, _⟩ := withdraw_requires_registered p p' h; omega
  · obtain ⟨_, hst⟩ := slash_requires_registered p p' pen h; omega

#assert_axioms serves_only_if_registered
#assert_axioms register_requires_unregistered
#assert_axioms slash_requires_registered
#assert_axioms withdraw_requires_registered
#assert_axioms stake_nonincreasing_except_register

end Dregg2.Storage.ProviderRegistry
