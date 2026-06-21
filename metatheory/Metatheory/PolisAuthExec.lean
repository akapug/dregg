/-
# Metatheory.PolisAuthExec — governance over the REAL executor's cap-transitions.

The other grounded-polis files (`PolisAuthReach`, `PolisAuthGameN`) govern the
*propose-whole-`Caps`* abstraction: a turn proposes an entire next `Caps : Label → List Cap`
and the governor admits/refuses the *proposed table*. That abstraction never RUNS the
kernel — the "step" is `fun _ caps' => caps'`, a pure proposal. This file closes that gap:
governance acts over the **deployed executor** `Dregg2.Exec.Kernel.exec`, the computable
machine that actually CHECKS authority (`authorizedB`) and resource availability fail-closed
and either COMMITS the transfer or returns `none`.

  * World := `KernelState` — the real executable kernel state (live accounts, balances, cap table).
  * Move  := `Turn`       — the real op (`actor` moves `amt` of resource `src ⇒ dst` under authority).
  * step  := `realStep`   — `(exec k t).getD k`: run the real executor; on a refused turn (the gate
                            tripped) the world STAYS (fail-closed shield, exactly the kernel's own
                            `none`).
  * floor := `consFloor T0` — the real conservation law `total k = T0` (the Σ that `exec_conserves`
                            keeps), composed with a liveness floor (accounts never disappear).

The governor is `PolisGovernorTheory.genGovStep` over this real step + floor, so the whole
`genGov_safe`/`combine_*` machinery applies. The load-bearing facts are tied to the EXECUTOR'S
OWN deployed theorems, never re-proved:

  * `realStep_conserves` ⇐ `Kernel.exec_conserves`   (a committed turn preserves Σ);
  * `gov_admits_honest_transfer`                       (exec succeeds + Σ kept ⟹ governor passes it);
  * `gov_refuses_overdraft`   ⇐ the `exec` availability gate (`amt ≤ bal src`);
  * `gov_refuses_unauthorized` ⇐ `Kernel.exec_unauthorized_fails` / `exec_authorized`.

This is the authority/conservation-axis counterpart of `PolisDreggGame` over PHYSICALLY-REALIZABLE
dregg turns: every admitted move is one the deployed kernel actually committed. No `sorry`, no
load-bearing `True`; the concrete admit/refuse facts are `decide`-checked on a real `KernelState`.
-/
import Metatheory.PolisGovernorTheory
import Dregg2.Exec.Kernel

namespace Metatheory.PolisAuthExec

open Dregg2.Authority Dregg2.Exec Metatheory.PolisGovernorTheory

/-! ## §1. The real step: run the deployed executor, fail-closed. -/

/-- **The governed world's step IS the deployed kernel executor.** Run `exec`; if it commits, take
the new state; if the gate tripped (unauthorized, overdraft, dead account, self-transfer) it returns
`none` and the world STAYS — exactly the kernel's own fail-closed semantics, now read as the
governor's shield. -/
def realStep (k : KernelState) (t : Turn) : KernelState := (exec k t).getD k

/-- A committed turn IS the step. -/
theorem realStep_commit {k k' : KernelState} {t : Turn} (h : exec k t = some k') :
    realStep k t = k' := by unfold realStep; rw [h]; rfl

/-- A refused turn leaves the world unchanged (fail-closed shield). -/
theorem realStep_refuse {k : KernelState} {t : Turn} (h : exec k t = none) :
    realStep k t = k := by unfold realStep; rw [h]; rfl

/-- **The deployed `exec` never edits the live `accounts` set** — it only rewrites `bal`. So the
liveness floor is preserved by every committed turn, structurally (no per-witness reproof). -/
theorem exec_preserves_accounts {k k' : KernelState} {t : Turn} (h : exec k t = some k') :
    k'.accounts = k.accounts := by
  unfold exec at h
  split at h
  · rw [Option.some.injEq] at h; rw [← h]
  · exact absurd h (by simp)

/-- **`realStep_conserves` ⇐ the deployed `exec_conserves`.** A committed turn preserves total
supply; a refused turn leaves the state (hence the total) fixed. Either way the real step keeps Σ. -/
theorem realStep_conserves (k : KernelState) (t : Turn) : total (realStep k t) = total k := by
  unfold realStep
  cases h : exec k t with
  | none => simp
  | some k' => simp only [Option.getD_some]; exact exec_conserves k k' t h

/-! ## §2. The real floors: conservation (Σ = baseline) and liveness (accounts fixed). -/

/-- **The conservation floor** — total supply equals a fixed baseline `T0`. This is the very Σ the
executor's `exec_conserves` keeps; the polis floor is the deployed conservation law, not a proxy. -/
def consFloor (T0 : ℤ) : Floor KernelState := fun k => total k = T0

instance (T0 : ℤ) : DecidablePred (consFloor T0) :=
  fun k => inferInstanceAs (Decidable (total k = T0))

/-- **The liveness floor** — the live `accounts` set is exactly `acc0`. A turn that conserves Σ but
quietly drops a cell from the conserved set would still pass `consFloor`; this floor forbids that.
(The deployed `exec` never touches `accounts`, so honest turns keep it; it is a genuine second axis.) -/
def liveFloor (acc0 : Finset CellId) : Floor KernelState := fun k => k.accounts = acc0

instance (acc0 : Finset CellId) : DecidablePred (liveFloor acc0) :=
  fun k => inferInstanceAs (Decidable (k.accounts = acc0))

/-- **The grounded executor floor** — conservation AND liveness, a `combineFloor`, so the whole
`combine_safe`/`combine_monotone` theory applies over the REAL executor step. -/
def execFloor (T0 : ℤ) (acc0 : Finset CellId) : Floor KernelState :=
  combineFloor (consFloor T0) (liveFloor acc0)

instance (T0 : ℤ) (acc0 : Finset CellId) : DecidablePred (execFloor T0 acc0) :=
  inferInstanceAs (DecidablePred (combineFloor _ _))

/-! ## §3. The grounded executor governor + its safety (∀ controller, every tick). -/

/-- **The grounded executor governor** = `genGovStep` over the real step + the real floor: admit the
controller's proposed `Turn` iff RUNNING it on the deployed kernel keeps Σ at the baseline and keeps
the accounts live, else SHIELD (stay). Computable. -/
def execGov (T0 : ℤ) (acc0 : Finset CellId) (k : KernelState) (t : Turn) : KernelState :=
  genGovStep (execFloor T0 acc0) realStep k t

/-- **`execGov_safe`** — from any baseline-conserving, accounts-live start, NO opaque controller
breaks the floor at any tick: Σ stays at `T0` AND the accounts stay live, forever. This is
`genGov_safe` over the REAL executor step, so every admitted move was one the deployed kernel
actually committed (`realStep`), and the conservation half rides on the deployed `exec_conserves`. -/
theorem execGov_safe (T0 : ℤ) (acc0 : Finset CellId)
    (ctrl : KernelState → Turn) (k0 : KernelState) (h0 : execFloor T0 acc0 k0) :
    ∀ n, execFloor T0 acc0 (genGovTraj (execFloor T0 acc0) realStep ctrl k0 n) :=
  genGov_safe (execFloor T0 acc0) realStep ctrl k0 h0

/-- **Both axes, every tick** (the `combine_safe` projection): Σ stays at `T0` at every tick AND the
accounts stay live at every tick, for any controller. -/
theorem execGov_safe_both (T0 : ℤ) (acc0 : Finset CellId)
    (ctrl : KernelState → Turn) (k0 : KernelState) (h0 : execFloor T0 acc0 k0) :
    (∀ n, consFloor T0 (genGovTraj (execFloor T0 acc0) realStep ctrl k0 n))
      ∧ (∀ n, liveFloor acc0 (genGovTraj (execFloor T0 acc0) realStep ctrl k0 n)) :=
  ⟨fun n => (execGov_safe T0 acc0 ctrl k0 h0 n).1,
   fun n => (execGov_safe T0 acc0 ctrl k0 h0 n).2⟩

/-! ## §4. ADMIT an honest turn; REFUSE overdraft / unauthorized — tied to the executor's theorems. -/

/-- **`gov_admits_honest_transfer`.** An honest turn — the deployed `exec` COMMITS it (`exec k t =
some k'`) into a state that still meets the floor (Σ at baseline, accounts live) — is passed through
UNCHANGED: the governor's output is exactly the kernel's committed successor `k'`. The committed-Σ
side is the deployed `exec_conserves` (via `realStep_conserves`); the governor adds no friction to a
physically-realizable, floor-preserving turn. -/
theorem gov_admits_honest_transfer (T0 : ℤ) (acc0 : Finset CellId)
    {k k' : KernelState} {t : Turn} (hc : exec k t = some k')
    (hfloor : execFloor T0 acc0 k') :
    execGov T0 acc0 k t = k' := by
  unfold execGov
  rw [genGov_admits_benign (execFloor T0 acc0) realStep k t (by rw [realStep_commit hc]; exact hfloor)]
  exact realStep_commit hc

/-- **`gov_refuses_overdraft` ⇐ the `exec` availability gate.** A turn spending more than the source
holds (`bal src < amt`) trips the executor's own availability gate, so `exec` returns `none` and the
real step STAYS at `k`: the governor shields. The refusal is the kernel's resource gate, not an
external rule. -/
theorem gov_refuses_overdraft (T0 : ℤ) (acc0 : Finset CellId)
    {k : KernelState} {t : Turn} (hover : k.bal t.src < t.amt) :
    execGov T0 acc0 k t = k := by
  have hnone : exec k t = none := by
    unfold exec; rw [if_neg]
    rintro ⟨_, _, havail, _⟩
    exact absurd havail (not_le.mpr hover)
  -- `exec` refused, so the real step stays at `k`; `genGovStep` then returns `k` on either branch.
  unfold execGov genGovStep
  rw [realStep_refuse hnone]
  split <;> rfl

/-- **`gov_refuses_unauthorized` ⇐ the deployed `exec_unauthorized_fails`.** A turn whose actor lacks
authority over `src` (`authorizedB = false`) fails the executor's integrity gate, so `exec` returns
`none` and the real step STAYS: the governor shields. The refusal is the kernel's OWN authority check
(`exec_authorized`'s contrapositive), internalized — no out-of-band gate. -/
theorem gov_refuses_unauthorized (T0 : ℤ) (acc0 : Finset CellId)
    {k : KernelState} {t : Turn} (hbad : authorizedB k.caps t = false) :
    execGov T0 acc0 k t = k := by
  have hnone : exec k t = none := exec_unauthorized_fails k t hbad
  unfold execGov genGovStep
  rw [realStep_refuse hnone]
  split <;> rfl

/-! ## §5. A concrete real-exec witness — decided on an actual `KernelState`.

`s0`: cell 0 owns 100, cell 1 owns 5, accounts `{0,1}`, empty cap table (authority = ownership).
Baseline `T0 = 105`, live set `{0,1}`. We exhibit, ALL `decide`-checked on the deployed `exec`:
  * an HONEST transfer (actor 0 owns src 0, amt 30 ≤ 100) — exec commits, floor kept, ADMITTED;
  * an OVERDRAFT (actor 0, amt 200 > 100) — exec's availability gate trips, REFUSED;
  * an UNAUTHORIZED move (actor 2 has no cap on src 0) — exec's integrity gate trips, REFUSED. -/

/-- The conserved baseline of `s0` (100 + 5). -/
def T0 : ℤ := 105
/-- The live account set of `s0`. -/
def acc0 : Finset CellId := {0, 1}

/-- An honest transfer: actor 0 owns src 0, moves 30 to cell 1 — within balance, authorized. -/
def tHonest : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }
/-- An overdraft: actor 0 tries to move 200 from src 0 (which holds only 100). -/
def tOverdraft : Turn := { actor := 0, src := 0, dst := 1, amt := 200 }
/-- An unauthorized move: actor 2 holds no cap on src 0. -/
def tUnauth : Turn := { actor := 2, src := 0, dst := 1, amt := 30 }

-- The deployed executor COMMITS the honest turn, REFUSES the overdraft, REFUSES the unauthorized.
#guard (exec s0 tHonest).isSome
#guard (exec s0 tOverdraft).isSome == false
#guard (exec s0 tUnauth).isSome == false

/-- The start meets the grounded executor floor (Σ = 105, accounts = {0,1}). -/
theorem s0_grounded : execFloor T0 acc0 s0 := by
  refine ⟨?_, ?_⟩
  · show total s0 = T0; decide
  · show s0.accounts = acc0; rfl

/-- The deployed executor COMMITS the honest turn: `exec s0 tHonest = some (its successor)`. The
successor is named as `(exec s0 tHonest).getD s0` so no function-valued `KernelState` literal is
written; the equation follows from `isSome` (decidable on the real `exec`). -/
theorem exec_s0_honest_some : exec s0 tHonest = some ((exec s0 tHonest).getD s0) := by
  have hs : (exec s0 tHonest).isSome := by decide
  cases h : exec s0 tHonest with
  | none => rw [h] at hs; exact absurd hs (by simp)
  | some k' => rfl

/-- The honest transfer's committed successor still meets the floor (Σ conserved, accounts live).
The Σ-half is the deployed `exec_conserves` applied through the committed equation; the liveness-half
holds because `exec` never edits `accounts`. -/
theorem honest_succ_grounded : execFloor T0 acc0 ((exec s0 tHonest).getD s0) := by
  refine ⟨?_, ?_⟩
  · -- Σ stays at the baseline `s0_grounded` keeps, by `exec_conserves` on the committed turn.
    show total ((exec s0 tHonest).getD s0) = T0
    have := exec_conserves s0 ((exec s0 tHonest).getD s0) tHonest exec_s0_honest_some
    rw [this]; exact s0_grounded.1
  · -- `exec` returns `{ s0 with bal := … }`, so `accounts` is untouched (the structural lemma).
    show ((exec s0 tHonest).getD s0).accounts = acc0
    rw [exec_preserves_accounts exec_s0_honest_some]; exact s0_grounded.2

/-- **ADMIT (on the real kernel).** The governor passes the honest transfer through to the deployed
executor's committed successor — exactly `(exec s0 tHonest).getD s0`, the real post-state. Tied to
`gov_admits_honest_transfer` (whose Σ-side is `exec_conserves`). -/
theorem s0_admits_honest :
    execGov T0 acc0 s0 tHonest = (exec s0 tHonest).getD s0 :=
  gov_admits_honest_transfer T0 acc0 exec_s0_honest_some honest_succ_grounded

/-- **REFUSE-OVERDRAFT (decided on the real kernel).** The overdraft trips `exec`'s availability
gate, so the governor shields to `s0`. -/
theorem s0_refuses_overdraft : execGov T0 acc0 s0 tOverdraft = s0 :=
  gov_refuses_overdraft T0 acc0 (by decide : s0.bal tOverdraft.src < tOverdraft.amt)

/-- **REFUSE-UNAUTHORIZED (decided on the real kernel).** Actor 2 holds no cap on src 0, so `exec`'s
integrity gate trips and the governor shields to `s0`. Tied to `exec_unauthorized_fails`. -/
theorem s0_refuses_unauthorized : execGov T0 acc0 s0 tUnauth = s0 :=
  gov_refuses_unauthorized T0 acc0 (by decide : authorizedB s0.caps tUnauth = false)

/-! ## §6. The DELEGATE axis — an authorized cross-vat write via a delegated cap, decided.

The kernel's `authorizedB` admits a NON-owner who holds an `endpoint`-cap carrying `write` on the
source (the l4v cross-vat policy edge). So delegation is physically realizable here: cell 0 GRANTS
actor 9 a write-cap on cell 0, and then actor 9's transfer commits — whereas without the cap it is
refused. This is the authority counterpart of the conservation refusals above. -/

/-- Like `s0`, but cell 0 has DELEGATED a write-cap on itself to actor 9 (the cross-vat edge). -/
def sDeleg : KernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0
    caps := fun a => if a = 9 then [.endpoint 0 [Auth.write]] else [] }

/-- Actor 9 (the delegate) moves 30 from cell 0 — authorized ONLY via the delegated write-cap. -/
def tDelegated : Turn := { actor := 9, src := 0, dst := 1, amt := 30 }

-- Without the delegated cap (s0), actor 9's transfer is REFUSED; WITH it (sDeleg), it COMMITS.
#guard (exec s0 tDelegated).isSome == false
#guard (exec sDeleg tDelegated).isSome
-- The delegated transfer still conserves Σ (105) — authority changed, resource law held.
#guard ((exec sDeleg tDelegated).map total) == some 105

/-- `sDeleg` meets the grounded floor (Σ = 105, accounts = {0,1}). -/
theorem sDeleg_grounded : execFloor T0 acc0 sDeleg := by
  refine ⟨?_, ?_⟩
  · show total sDeleg = T0; decide
  · show sDeleg.accounts = acc0; rfl

/-- The deployed executor COMMITS the delegated turn (named like the honest case). -/
theorem exec_sDeleg_some : exec sDeleg tDelegated = some ((exec sDeleg tDelegated).getD sDeleg) := by
  have hs : (exec sDeleg tDelegated).isSome := by decide
  cases h : exec sDeleg tDelegated with
  | none => rw [h] at hs; exact absurd hs (by simp)
  | some k' => rfl

/-- The delegated transfer's committed successor meets the floor (Σ via `exec_conserves`; accounts
untouched). -/
theorem delegated_succ_grounded : execFloor T0 acc0 ((exec sDeleg tDelegated).getD sDeleg) := by
  refine ⟨?_, ?_⟩
  · show total ((exec sDeleg tDelegated).getD sDeleg) = T0
    have := exec_conserves sDeleg ((exec sDeleg tDelegated).getD sDeleg) tDelegated exec_sDeleg_some
    rw [this]; exact sDeleg_grounded.1
  · show ((exec sDeleg tDelegated).getD sDeleg).accounts = acc0
    rw [exec_preserves_accounts exec_sDeleg_some]; exact sDeleg_grounded.2

/-- **ADMIT-DELEGATE (on the real kernel).** A delegate authorized by a real `endpoint`+`write` cap
has its transfer COMMITTED by the deployed executor; the governor passes it through to the real
post-state. The authorized cross-vat turn is physically realizable AND floor-preserving. -/
theorem sDeleg_admits_delegated :
    execGov T0 acc0 sDeleg tDelegated = (exec sDeleg tDelegated).getD sDeleg :=
  gov_admits_honest_transfer T0 acc0 exec_sDeleg_some delegated_succ_grounded

/-- **REFUSE the SAME turn without the delegation (decided).** On `s0` (no cap), actor 9 is
unauthorized, so the identical `Turn` is refused — the executor's integrity gate is what makes the
delegation load-bearing. Tied to `exec_unauthorized_fails`. -/
theorem s0_refuses_undelegated : execGov T0 acc0 s0 tDelegated = s0 :=
  gov_refuses_unauthorized T0 acc0 (by decide : authorizedB s0.caps tDelegated = false)

/-! ## §7. Axiom hygiene. -/

#print axioms realStep_conserves
#print axioms execGov_safe
#print axioms gov_admits_honest_transfer
#print axioms gov_refuses_overdraft
#print axioms gov_refuses_unauthorized
#print axioms s0_admits_honest
#print axioms s0_refuses_overdraft
#print axioms s0_refuses_unauthorized
#print axioms sDeleg_admits_delegated
#print axioms s0_refuses_undelegated

/-!
Governance over the REAL executor, in one breath:

  1. `realStep` — the governed step IS the deployed `Kernel.exec` (fail-closed shield on a refused
     turn). `realStep_conserves` rides on the deployed `exec_conserves`.
  2. `execFloor` — the real conservation law (Σ = baseline) AND liveness (accounts fixed), a
     `combineFloor`, so `combine_safe`/`combine_monotone` apply over the real machine.
  3. `execGov_safe` — from any baseline-conserving, accounts-live start, NO opaque controller breaks
     the floor at any tick; every admitted move was one the deployed kernel actually committed.
  4. ADMIT an honest transfer (exec commits + floor kept); REFUSE overdraft (the availability gate)
     and unauthorized (`exec_unauthorized_fails`); ADMIT an authorized DELEGATE (cross-vat write-cap)
     while REFUSING the same turn undelegated — all `decide`-checked on a real `KernelState`.
-/

end Metatheory.PolisAuthExec
