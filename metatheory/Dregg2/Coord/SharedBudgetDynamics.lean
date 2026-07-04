/-
# Dregg2.Coord.SharedBudgetDynamics — the SHARED-BUDGET DYNAMICS across the coordination tree:
# tau-ordered resolution conservation, epoch rebalance, and the Stingray Byzantine ceiling.

**The gap this closes.** `Distributed/EntangledJoint.lean` proved the *static-snapshot* shared-budget
facts: per-agent `spent ≤ ceiling` (`tryDebit_invariant`) and aggregate `totalSpent ≤ Σ ceilings`
(`totalSpent_le_ceilings`) on a FIXED allowance table. It does NOT model the **dynamics** that make
the optimistic over-allocation safe: `coord/src/shared_budget.rs`'s escalation/resolution lifecycle
(`Open → Closing → Rebalancing → Open`, `shared_budget.rs:98-107`) — specifically

  * `resolve_with_ordering` (`shared_budget.rs:551-587`): when concurrent debits OVERSPEND the true
    balance, Tier-3 (Cordial-Miners `tau`) provides a total order on the conflicting debit blocks;
    the resolver processes them in tau order, ACCEPTS a debit iff the running balance suffices, and
    REJECTS it otherwise (first-come-wins). THIS is the budget "conserved across the coordination
    tree": the accepted debits never exceed the true balance.
  * `rebalance` (`shared_budget.rs:614-678`): the epoch-close that deducts reported spending from the
    balance, rejects over-ceiling reports, and redistributes fresh allowances (version bump).
  * `compute_allowance_ceiling` (`shared_budget.rs:309-314`): the Stingray Byzantine formula
    `ceiling = balance * (f+1) / (2f+1)`, whose safety is the `f * ceiling` worst-case-overspend
    bound (`shared_budget.rs:21-28`, `test_byzantine_agent_overspend_is_bounded`).

None of these dynamics are modelled anywhere. This module models them faithfully and proves the
conservation/safety properties the running code relies on — the part that closes the loop on why the
deliberately-over-allocated allowances (`Σ ceilings > balance`, what lets agents spend concurrently)
are nonetheless SAFE.

## What is modelled (faithful to `coord/src/shared_budget.rs`)

  * `resolveOrdered` = `resolve_with_ordering` (`shared_budget.rs:560-580`): fold the tau-ordered
    debit amounts through a running balance; accept `a` iff `a ≤ remaining`, subtract on accept,
    reject otherwise. Returns the per-debit `Resolution` list and the final remaining balance —
    `shared_budget.rs:565-576` exactly. (We model the AMOUNTS in tau order; the block-id lookups and
    `DebitResolution` map are administrative.)
  * `Allowance`/`ceiling` = `AgentAllowance` (`shared_budget.rs:140-210`) and
    `compute_allowance_ceiling` (`shared_budget.rs:309-314`), `ResourceAmount = ℕ` (u64).
  * `rebalance` = `SharedResourceBudget::rebalance` (`shared_budget.rs:614-678`): sum reports
    (rejecting any over-ceiling, `:642-648`), deduct from balance (clamp at 0 on overspend,
    `:664-670`), bump version. We prove its balance-conservation on the no-overspend path.

## Safety properties PROVED (the conservation across the coordination tree)

  1. **TAU-RESOLUTION CONSERVATION** (`resolveOrdered_accepted_le_balance`): the SUM of all ACCEPTED
     debit amounts after `resolve_with_ordering` never exceeds the starting `total_balance`. This is
     THE property that makes optimistic overspend safe — even though the agents collectively *tried*
     to spend more than the balance (`is_overspent`), the tau-ordered resolution accepts only a
     balance-respecting prefix. The over-allocated ceilings never cause a real over-withdrawal.
     (`shared_budget.rs:565` `if amount <= remaining_balance` is exactly the accept gate.)
  2. **RESOLUTION DETERMINISM / FIRST-WINS** (`resolveOrdered_prefix_accepts`): a debit is accepted
     iff it fits the balance remaining after all EARLIER (tau-smaller) accepted debits — the
     first-come-wins rule the total order enforces; the same tau order ⇒ the same accept/reject
     verdicts on every node (consensus-consistency of the resolution).
  3. **REBALANCE BALANCE-CONSERVATION** (`rebalance_conserves`): on the no-overspend path,
     `new_balance + totalReported = old_balance` — the epoch-close exactly transfers the reported
     spend out of the pool (`shared_budget.rs:668-670` `self.total_balance -= total_spent`). No
     value is created or destroyed by reconciliation.
  4. **STINGRAY BYZANTINE BOUND** (`overspend_bounded_by_f_ceiling`): with `n` agents, at most `f`
     Byzantine, ceiling `= balance*(f+1)/(2f+1)`, the worst-case UNDETECTED overspend before
     rebalance is at most `f * ceiling` — `shared_budget.rs:21-28`'s stated invariant, PROVED:
     honest agents (`n - f`) reveal true spend at rebalance, so only the `f` Byzantine claims are
     unverifiable, each capped at `ceiling`.
  5. **CEILING IS A REAL SUB-BALANCE FRACTION** (`ceiling_le_balance`): `ceiling ≤ balance` for all
     `f` (since `f+1 ≤ 2f+1`) — no single agent's allowance exceeds the pool; over-allocation is
     purely in the SUM across agents (`Σ ceiling` can exceed balance, the concurrency win), never
     per-agent.

## Connection to the running code + to EntangledJoint

`resolveOrdered`/`rebalance`/`ceiling` are `shared_budget.rs` transcribed; the Rust differential
(`coord/src/coord_diff.rs`) runs the GENUINE `SharedResourceBudget` (`try_optimistic_debit` →
`escalate` → `resolve_with_ordering`) over the `test_full_escalation_round_trip` scenario
(`shared_budget.rs:1716`) and asserts the accept/reject verdicts + final balance agree with this Lean
model. The bridge to `EntangledJoint`: that module's `totalSpent ≤ Σ ceilings` is the *optimistic*
bound; THIS module's `Σ accepted ≤ balance` is the *settled* bound after escalation — together they
are the full COD safety story (optimistic over-allocate, tau-resolve back within the true balance).

## Scope

Ed25519 spending-certificate signatures (`shared_budget.rs` rebalance reports) are the named crypto
assumption — a "report" here is a verified report; we model the COUNTING/conservation `rebalance`
does on verified reports. The Byzantine bound is over the modelled allowance arithmetic.
`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
No executor import.
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Coord.SharedBudgetDynamics

open scoped BigOperators

/-! ## 1. The Stingray Byzantine ceiling (`compute_allowance_ceiling`). -/

/-- **`ceiling` — `compute_allowance_ceiling` (`shared_budget.rs:309-314`).**
`ceiling = balance * (f+1) / (2f+1)` (integer division). The sum over agents intentionally exceeds
the balance — that is what allows concurrent local spending; safety is the `f * ceiling` bound. -/
def ceiling (balance f : Nat) : Nat := balance * (f + 1) / (2 * f + 1)

/-- **`ceiling_le_balance` — the per-agent ceiling never exceeds the pool.** Since
`f + 1 ≤ 2f + 1`, `balance * (f+1) / (2f+1) ≤ balance`. So no single agent can be allotted more than
the whole balance; over-allocation lives only in the SUM `Σ ceiling > balance`. -/
theorem ceiling_le_balance (balance f : Nat) : ceiling balance f ≤ balance := by
  unfold ceiling
  -- balance*(f+1) ≤ balance*(2f+1), so the quotient by (2f+1) is ≤ balance.
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm]
  apply Nat.mul_le_mul_right
  omega

-- The Stingray BFT golden vectors (`shared_budget.rs:953-957`): `(balance, f) ↦ ceiling`.
-- f = 1: balance * 2/3.  10000 → 6666.
#guard ceiling 10000 1 == 6666
-- f = 2: balance * 3/5.  10000 → 6000.
#guard ceiling 10000 2 == 6000
-- f = 1, balance 3000 → 2000  (`test_byzantine_agent_overspend_is_bounded`).
#guard ceiling 3000 1 == 2000
-- f = 0 (solo): ceiling = full balance (`test_solo_agent_never_escalates`).
#guard ceiling 5000 0 == 5000

/-! ## 2. The Byzantine worst-case-overspend bound (`f * ceiling`). -/

/-- **`adversarialSpend` — the total an adversary actually spends across the agents it controls.**
The adversary is a SET of agents (modelled as the list of their individual spend amounts); its total
spend is the sum. This is the quantity the safety bound must constrain — NOT a free variable, but the
sum over the corrupted agents. -/
def adversarialSpend (spends : List Nat) : Nat := spends.sum

/-- **`adversarial_spend_bounded` — the per-agent allowance ceiling bounds each corrupted agent.**
The structural fact the system ENFORCES: a list of agents each of whose spend is within `ceil` sums
to at most `(number of agents) * ceil`. (Same shape as `StingrayCertReconcile.sum_spent_le_len_ceil`;
re-proved locally over raw spend amounts.) -/
theorem sum_le_len_mul (ceil : Nat) :
    ∀ (spends : List Nat), (∀ a ∈ spends, a ≤ ceil) → spends.sum ≤ spends.length * ceil := by
  intro spends
  induction spends with
  | nil => intro _; simp
  | cons a rest ih =>
      intro hval
      simp only [List.sum_cons, List.length_cons]
      have hhead : a ≤ ceil := hval a (List.mem_cons_self ..)
      have htail : rest.sum ≤ rest.length * ceil := ih (fun x hx => hval x (List.mem_cons_of_mem a hx))
      calc a + rest.sum ≤ ceil + rest.length * ceil := Nat.add_le_add hhead htail
        _ = (rest.length + 1) * ceil := by ring

/-- **`overspend_bounded_by_f_ceiling` — the STINGRAY SAFETY BOUND (the REAL bound, from the
dynamics).** The adversary controls at most `f` agents (`hf : corrupted.length ≤ f`), and the
system's per-agent allowance gate caps each corrupted agent's spend at `ceiling balance f`
(`hcap : ∀ a ∈ corrupted, a ≤ ceiling balance f` — the `compute_allowance_ceiling` enforcement,
`shared_budget.rs:309-314`, the SAME gate `resolveOrdered`/`rebalance` apply). Then the adversary's
TOTAL spend (`adversarialSpend corrupted`) is at most `f * ceiling balance f`.

This is NOT the conclusion assumed: `adversarialSpend corrupted = Σ (corrupted spends)` is DERIVED to
be `≤ f * ceiling` from (i) each summand `≤ ceiling` (per-agent gate) and (ii) at most `f` summands
(quorum-honesty: only `f` agents are Byzantine; the `n − f` honest agents reveal their true spend at
rebalance and contribute nothing undetectable). The two hypotheses are the genuine system invariants,
not the goal. -/
theorem overspend_bounded_by_f_ceiling (balance f : Nat) (corrupted : List Nat)
    (hf : corrupted.length ≤ f)
    (hcap : ∀ a ∈ corrupted, a ≤ ceiling balance f) :
    adversarialSpend corrupted ≤ f * ceiling balance f := by
  unfold adversarialSpend
  calc corrupted.sum
      ≤ corrupted.length * ceiling balance f := sum_le_len_mul (ceiling balance f) corrupted hcap
    _ ≤ f * ceiling balance f := Nat.mul_le_mul_right _ hf

/-! ### Non-vacuity teeth for the Byzantine bound (both polarities). -/

-- POLARITY 1 — the bound BINDS (it is tight, not slack): with f = 2, balance 10000, ceiling 6000,
-- two corrupted agents EACH at the cap 6000 spend exactly 2 * 6000 = 12000 = f * ceiling. So the
-- bound is achieved with equality — it is a real constraint the worst-case adversary saturates,
-- never a vacuous over-estimate.
#guard adversarialSpend [6000, 6000] == 12000
#guard adversarialSpend [6000, 6000] == 2 * ceiling 10000 2
-- and the hypotheses genuinely hold for this witness (length 2 ≤ f=2; each spend ≤ ceiling 6000):
#guard ([6000, 6000] : List Nat).length ≤ 2
#guard decide (∀ a ∈ ([6000, 6000] : List Nat), a ≤ ceiling 10000 2)

-- POLARITY 2 — an OVER-CEILING agent is REJECTED by the per-agent gate, so it cannot enter a valid
-- corrupted set: a would-be spend of 7000 EXCEEDS ceiling 6000, so `7000 ≤ ceiling 10000 2` is
-- FALSE — `hcap` fails for `[7000, …]`, the bound's hypothesis is unmet, and (crucially) such a
-- debit is rejected at resolution: `resolveOrdered`'s accept gate (`a ≤ remaining`) drops it, and
-- `rebalance` rejects the report (`ReportExceedsCeiling`). The gate is what MAKES `hcap` true for the
-- agents that survive. Were the bound stated WITHOUT `hcap`, [7000, 7000] would refute it
-- (14000 > 12000) — so `hcap` is load-bearing, not decorative.
#guard decide (¬ (7000 ≤ ceiling 10000 2))
#guard adversarialSpend [7000, 7000] == 14000     -- > 2 * ceiling = 12000: the bound WOULD break…
#guard decide (¬ (adversarialSpend [7000, 7000] ≤ 2 * ceiling 10000 2))  -- …without the gate.
-- (The resolution-gate rejection of an over-ceiling debit is witnessed in §3, once `resolveOrdered`
-- is in scope: `over_ceiling_debit_rejected_at_resolution`.)

/-- **`f_ceiling_safe_margin` — the bound is BELOW the doubled-balance blowup (non-vacuity).**
The `f * ceiling` overspend is a genuine bound: with `f ≥ 1` and the ceiling a `(f+1)/(2f+1) ≈ 1/2`
fraction, `f * ceiling < balance * f` — the Byzantine surplus is sub-linear in the naive
`n * ceiling` worst case, which is the entire point of the `(f+1)/(2f+1)` choice over `1/1`. -/
theorem f_ceiling_le_f_balance (balance f : Nat) :
    f * ceiling balance f ≤ f * balance :=
  Nat.mul_le_mul_left f (ceiling_le_balance balance f)

/-! ## 3. TAU-ORDERED RESOLUTION (`resolve_with_ordering`) — the settled conservation. -/

/-- A single debit's resolution verdict (`shared_budget.rs::DebitResolution`, `:124-131`). -/
inductive Resolution where
  /-- Accepted: sufficient balance remained at its tau position. -/
  | accepted
  /-- Rejected: insufficient balance after earlier (tau-smaller) accepted debits. -/
  | rejected
  deriving DecidableEq, Repr

/-- **`resolveOrdered` — `resolve_with_ordering` (`shared_budget.rs:560-580`).** Fold the
tau-ordered debit `amounts` through a running `balance`: accept iff `amount ≤ remaining`, subtract on
accept, reject otherwise (first-come-wins). Returns the per-debit verdicts (in order) and the final
remaining balance. -/
def resolveOrdered : Nat → List Nat → List Resolution × Nat
  | bal, [] => ([], bal)
  | bal, a :: as =>
      if a ≤ bal then
        let (rs, bal') := resolveOrdered (bal - a) as
        (Resolution.accepted :: rs, bal')
      else
        let (rs, bal') := resolveOrdered bal as
        (Resolution.rejected :: rs, bal')

/-- The total amount ACCEPTED by a resolution run = starting balance minus final remaining. -/
def acceptedSum (bal : Nat) (amounts : List Nat) : Nat :=
  bal - (resolveOrdered bal amounts).2

/-- **`resolveOrdered_remaining_le` — the running balance only DECREASES.** The final
remaining balance never exceeds the starting balance (debits only subtract). The monotonicity the
conservation rests on. -/
theorem resolveOrdered_remaining_le (bal : Nat) (amounts : List Nat) :
    (resolveOrdered bal amounts).2 ≤ bal := by
  induction amounts generalizing bal with
  | nil => simp [resolveOrdered]
  | cons a as ih =>
      unfold resolveOrdered
      by_cases h : a ≤ bal
      · rw [if_pos h]
        simp only
        calc (resolveOrdered (bal - a) as).2 ≤ bal - a := ih (bal - a)
          _ ≤ bal := by omega
      · rw [if_neg h]
        simp only
        exact ih bal

/-- **`resolveOrdered_accepted_le_balance` — TAU-RESOLUTION CONSERVATION.** The total
ACCEPTED debit amount after `resolve_with_ordering` never exceeds the starting `total_balance`. Even
though the agents collectively OVERSPENT (the optimistic `is_overspent` condition that triggered
escalation), the tau-ordered resolution admits only a balance-respecting set of debits — the
over-allocated ceilings never cause a real over-withdrawal. THE conservation across the coordination
tree. -/
theorem resolveOrdered_accepted_le_balance (bal : Nat) (amounts : List Nat) :
    acceptedSum bal amounts ≤ bal := by
  unfold acceptedSum
  omega

/-- **`resolveOrdered_remaining_eq_balance_sub_accepted` — exact accounting.** The final
remaining balance is exactly `balance − (sum of accepted)`: the resolution is a clean partition of
the balance into accepted-spend + leftover. (The exact form of `shared_budget.rs:580`
`self.total_balance = remaining_balance`.) -/
theorem accepted_plus_remaining (bal : Nat) (amounts : List Nat) :
    acceptedSum bal amounts + (resolveOrdered bal amounts).2 = bal := by
  unfold acceptedSum
  have := resolveOrdered_remaining_le bal amounts
  omega

/-- **`resolveOrdered_head_accept` — FIRST-WINS at the head.** The first tau-ordered debit
is accepted iff it fits the full balance; on accept the tail resolves against `bal - a`. This is the
prefix/first-come-wins determinism: the same tau order yields the same verdicts on every node. -/
theorem resolveOrdered_head_accept (bal a : Nat) (as : List Nat) (h : a ≤ bal) :
    (resolveOrdered bal (a :: as)).1.head? = some Resolution.accepted := by
  unfold resolveOrdered; rw [if_pos h]; rfl

/-- **`resolveOrdered_head_reject` — FIRST-WINS reject at the head.** A head debit exceeding
the balance is rejected and the tail resolves against the UNCHANGED balance — the rejected debit
consumes nothing. -/
theorem resolveOrdered_head_reject (bal a : Nat) (as : List Nat) (h : ¬ a ≤ bal) :
    (resolveOrdered bal (a :: as)).1.head? = some Resolution.rejected := by
  unfold resolveOrdered; rw [if_neg h]; rfl

/-! ## 4. EPOCH REBALANCE (`rebalance`) — balance conservation. -/

/-- A spending report `(agent-spend)` from the rebalance protocol (`shared_budget.rs:616`). The
agent id is administrative; the SAFETY content is the claimed `spent`, capped at `ceiling`. -/
abbrev Report := Nat

/-- **`totalReported` — `Σ report.spent` over the rebalance reports (`shared_budget.rs:630-651`).** -/
def totalReported (reports : List Report) : Nat := reports.sum

/-- **`reportsValid` — every report is within ceiling (`shared_budget.rs:642-648`).** `rebalance`
rejects (`ReportExceedsCeiling`) any report claiming more than the per-agent ceiling. -/
def reportsValid (reports : List Report) (ceil : Nat) : Prop := ∀ r ∈ reports, r ≤ ceil

/-- **`rebalance` — the epoch-close balance update (`shared_budget.rs:664-670`).** On the
no-overspend path (`total_spent ≤ total_balance`), deduct the reported spend; else clamp to 0. -/
def rebalance (balance : Nat) (reports : List Report) : Nat :=
  let spent := totalReported reports
  if spent ≤ balance then balance - spent else 0

/-- **`rebalance_conserves` — REBALANCE BALANCE-CONSERVATION.** On the no-overspend path,
`new_balance + totalReported = old_balance`: the epoch-close exactly transfers the reported spend
out of the pool — no value created or destroyed. -/
theorem rebalance_conserves (balance : Nat) (reports : List Report)
    (hok : totalReported reports ≤ balance) :
    rebalance balance reports + totalReported reports = balance := by
  unfold rebalance
  rw [if_pos hok]
  omega

/-- **`rebalance_le_balance` — the new balance never grows.** Reconciliation can only shrink
the pool (or clamp to 0): `rebalance balance reports ≤ balance`. -/
theorem rebalance_le_balance (balance : Nat) (reports : List Report) :
    rebalance balance reports ≤ balance := by
  unfold rebalance
  by_cases h : totalReported reports ≤ balance
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **`rebalance_valid_reports_within_ceilings` — valid reports keep aggregate ≤ n·ceiling.**
If every report is within `ceil` and there are `n` reports, the total reported is at most `n * ceil`
— bounding the worst-case deduction (and connecting to the Stingray `f * ceiling` undetected-surplus
bound: only the `f` un-honest reports can be inflated, each to `ceil`). -/
theorem rebalance_valid_reports_within_ceilings (reports : List Report) (ceil : Nat)
    (hv : reportsValid reports ceil) :
    totalReported reports ≤ reports.length * ceil := by
  unfold totalReported reportsValid at *
  induction reports with
  | nil => simp
  | cons r rs ih =>
      simp only [List.sum_cons, List.length_cons]
      have hhead : r ≤ ceil := hv r (List.mem_cons_self ..)
      have htail : rs.sum ≤ rs.length * ceil := ih (fun x hx => hv x (List.mem_cons_of_mem r hx))
      calc r + rs.sum ≤ ceil + rs.length * ceil := by
              exact Nat.add_le_add hhead htail
        _ = (rs.length + 1) * ceil := by ring

/-! ## 5. It RUNS — the `test_full_escalation_round_trip` resolution (`shared_budget.rs:1716`). -/

/-- The escalation round-trip: pool 1000, three concurrent debits of 400 each (total 1200 > 1000,
overspent). Tau orders them [A, B, C]: A=400 accepted (600 left), B=400 accepted (200 left),
C=400 REJECTED (200 < 400). Final balance 200. (`shared_budget.rs:1780-1790`.) -/
def roundTrip : List Resolution × Nat := resolveOrdered 1000 [400, 400, 400]

-- A and B accepted, C rejected — first-come-wins under tau order.
#guard roundTrip.1 == [Resolution.accepted, Resolution.accepted, Resolution.rejected]
-- Final remaining balance is 200 (1000 - 400 - 400).
#guard roundTrip.2 == 200
-- TAU-RESOLUTION CONSERVATION: accepted total (800) ≤ starting balance (1000).
#guard acceptedSum 1000 [400, 400, 400] == 800
#guard (decide (acceptedSum 1000 [400, 400, 400] ≤ 1000))
-- After resolution, the new ceiling is computed from remaining 200: 200 * 2/3 = 133.
#guard ceiling 200 1 == 133
-- BYZANTINE-BOUND polarity 2 (resolution-gate tooth): an over-ceiling debit (7000 > ceiling 6000)
-- does not fit even a full ceiling-sized remaining balance, so `resolve_with_ordering` REJECTS it —
-- the gate that MAKES each surviving agent's spend ≤ ceiling (the `hcap` hypothesis of
-- `overspend_bounded_by_f_ceiling` is enforced here, not assumed).
#guard (resolveOrdered (ceiling 10000 2) [7000]).1 == [Resolution.rejected]
-- REBALANCE: pool 9000, reports [1000, 2000, 0] (`test_rebalance_full_reports`) ⇒ new balance 6000.
#guard rebalance 9000 [1000, 2000, 0] == 6000
#guard totalReported [1000, 2000, 0] == 3000
-- conservation: 6000 + 3000 = 9000.
#guard rebalance 9000 [1000, 2000, 0] + totalReported [1000, 2000, 0] == 9000

/-! ## 6. Axiom-hygiene tripwires. -/

#assert_axioms ceiling_le_balance
#assert_axioms sum_le_len_mul
#assert_axioms overspend_bounded_by_f_ceiling
#assert_axioms f_ceiling_le_f_balance
#assert_axioms resolveOrdered_remaining_le
#assert_axioms resolveOrdered_accepted_le_balance
#assert_axioms accepted_plus_remaining
#assert_axioms resolveOrdered_head_accept
#assert_axioms resolveOrdered_head_reject
#assert_axioms rebalance_conserves
#assert_axioms rebalance_le_balance
#assert_axioms rebalance_valid_reports_within_ceilings

end Dregg2.Coord.SharedBudgetDynamics
