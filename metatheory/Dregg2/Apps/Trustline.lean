/-
# Dregg2.Apps.Trustline — the bilateral line of credit (mutual credit) as a verified cell-program.

**The organ this births** (docs/ORGANS.md §1): trustlines are "built but stillborn at one uncalled
init" — the Stingray bounded-counter machinery exists end to end (`coord/src/shared_budget.rs`,
`coord/src/budget.rs`, the executor `BudgetGate` in `turn/src/budget_gate.rs`, the per-turn seeding
at `node/src/blocklace_sync.rs:2081`), but `node/src/state.rs:1129 init_budget_coordinator` has ZERO
callers, so the gate is always `None` (and the settlement edges `collect_spending_certificates` /
`rebalance_budgets` dangle uncalled too). This module models the thing the init edge births: the
DIRECTIONAL bilateral line of credit, and proves its keystones. The companion design doc
(`docs/TRUSTLINES.md`) names the init/settle weld.

**The model.** "Issuer A extends holder B a line of N" is an ATTENUATED CAPABILITY whose exercise
debits a shared counter:

  * the LINE is a Stingray `Slice` (`Proof/Stingray.Slice` = `BudgetSlice { ceiling, spent }`):
    `ceiling = N` (the attenuation bound, immutable), `spent = drawn` (the exercised amount) —
    `draw_slice_tracks_tryDebit` proves the draw gate IS `Slice.tryDebit`, literally the counter the
    payment-channel demo (`demo-agent/examples/payment_channel_burst.rs`) and the executor's
    `BudgetGate.try_debit` (`turn/src/budget_gate.rs:70`) run;
  * the line is DIRECTIONAL (A→B is not B→A): B draws against A's credit; the drawn amount is a move
    against A's SIGNED WELL in the issuer-asset model (`Substrate/IssuerLedger`, `AssetId := issuer
    CellId`): the holder's credit register carries `+drawn`, the issuer's well `−drawn`, and the
    bilateral sum is EXACTLY ZERO at every reachable state (`trustline_conserved_forever`);
  * draws are digest-identified (`BudgetSlice::debits`, `turn/src/budget_gate.rs:29`): a digest
    commits at most once, ever (`draw_replay_refused`, `no_double_draw_forever`);
  * SETTLEMENT: repayment is monotone-down on `drawn` and restores the line exactly
    (`draw_repay_roundtrip`); closing the line settles the residual against a hard-asset ledger pair
    conservatively (`settlePay_conserves_hard`, `settleAll_clears`) — the `rebalance_budgets`
    `(agent, total_spent)` settlement list (`node/src/state.rs:1213`) applied as a move.

## Keystones PROVED

  1. **BOUNDED BY THE LINE** (`draw_within_line`, `trustline_within_line_forever`): drawing never
     exceeds the extended line, along EVERY adversarial schedule of draws/repays — the
     `StorageGatewayMandate.sgm_volume_legal_forever` pattern on the credit counter.
  2. **BILATERAL CONSERVATION** (`bilateral_conserved`, `trustline_conserved_forever`): holder
     credit + issuer well = 0 forever — the draw is a MOVE against A's well, never a mint; the
     issuer-move model's exact law on the bilateral pair.
  3. **NO DOUBLE DRAW** (`draw_replay_refused`, `draw_records`, `no_double_draw_forever`): a debit
     digest commits at most once; the digest registry is duplicate-free at every reachable state.
  4. **SETTLEMENT RESTORES THE LINE** (`repay_monotone_down`, `draw_repay_roundtrip`,
     `settleAll_clears`, `settlePay_conserves_hard`): repay is monotone-down then the available line
     is back up — draw `a` then repay `a` restores `drawn`/credit/well exactly (the spent digest
     stays burned: one-shot forever); full settlement zeroes the line and moves exactly the drawn
     amount across the hard-asset pair, conserving it.
  5. **THE ATTENUATION PUN** (`holder_credit_le_line_forever`, `ceiling_immutable_forever`): the
     holder's exercised credit never exceeds the attenuation bound, and the bound itself is an
     immutable register — a line of credit IS an attenuated capability with a balance bound
     (`Exec/AuthTurn.recKDelegateAtten`'s granted ⊆ held, with the `⊆` made quantitative).

Non-vacuity both polarities (§7 `#guard`s): a within-line draw ADMITS (and the boundary draw is
tight); an over-line draw, a replayed digest, and an over-repay are each REFUSED. No
`sorry`/`:= True`/`native_decide`; `#assert_axioms`-clean (⊆ {propext, Classical.choice,
Quot.sound}). No executor import — the cell shape (which registers, which slot caveats) is the
design doc's §3; the SGM/CWM mandate modules are the executor-welding precedent.
-/
import Dregg2.Proof.Stingray
import Dregg2.Tactics

namespace Dregg2.Apps.Trustline

open Dregg2.Proof.Stingray (Slice)

/-! ## §1 — The trustline state (the bilateral cell's registers).

The trustline IS a cell; A (issuer) and B (holder) are the parties; these are its registers. The
`ceiling` is the extended line N (immutable for the line's life — re-extension is a new birth or a
governed amendment); `drawn` is the shared counter; `draws` is the debit-digest registry
(`BudgetSlice::debits`); `holderAcct`/`issuerWell` are the bilateral signed-well pair in the
issuer's asset (`AssetId := issuer`, the issuer carries the negative well). -/

/-- The bilateral trustline: issuer A extends holder B a line of `ceiling`. Directional — this
record IS the A→B line; a B→A line is a separate trustline with the roles swapped. -/
structure Line where
  /-- The extended line N — the attenuation bound (`Slice.ceiling`). Immutable register. -/
  ceiling : Nat
  /-- Outstanding drawn amount — the shared counter (`Slice.spent`). -/
  drawn : Nat
  /-- Committed draw digests (`BudgetSlice::debits`, `turn/src/budget_gate.rs:29`) — the
  no-double-draw registry. A digest is one-shot FOREVER (repayment does not resurrect it). -/
  draws : List Nat
  /-- The holder's credit balance in the issuer-asset: `+drawn`. -/
  holderAcct : Int
  /-- The issuer's signed well in its own asset: `−drawn` (the issuer-move model — the draw is
  PRODUCTION at the issuer's negative-capable well, never an out-of-thin-air mint). -/
  issuerWell : Int
  deriving Repr, DecidableEq

/-- The trustline's `Slice` face: the line IS the Stingray bounded counter
(`coord/src/budget.rs::BudgetSlice`), `ceiling = N`, `spent = drawn`. -/
def Line.slice (t : Line) : Slice := ⟨t.ceiling, t.drawn⟩

/-- Remaining undrawn line (`BudgetSlice::remaining`, truncated subtraction = saturating). -/
def Line.remaining (t : Line) : Nat := t.ceiling - t.drawn

/-- The remaining line agrees with the slice face's remaining. -/
theorem Line.remaining_eq_slice (t : Line) : t.remaining = t.slice.remaining := rfl

/-- **Well-formedness — the reachable-state invariant.** Drawn within the line; the bilateral pair
carries exactly `±drawn`; the digest registry is duplicate-free. -/
def Line.WF (t : Line) : Prop :=
  t.drawn ≤ t.ceiling
    ∧ t.holderAcct = (t.drawn : Int)
    ∧ t.issuerWell = -(t.drawn : Int)
    ∧ t.draws.Nodup

instance (t : Line) : Decidable t.WF := by
  unfold Line.WF; infer_instance

/-! ## §2 — Birth, draw, repay (the ops). -/

/-- **`init` — the BIRTH of the line** (the missing `init_budget_coordinator` edge,
`node/src/state.rs:1129`): issuer extends a fresh line of `n`. Nothing drawn, no digests, both
wells level. The REAL birth must be funded by a ledger debit at the issuer (design doc §2); this
is the post-birth cell state it installs. -/
def Line.init (n : Nat) : Line :=
  { ceiling := n, drawn := 0, draws := [], holderAcct := 0, issuerWell := 0 }

/-- **`draw` — the holder exercises the line** (`BudgetSlice::try_debit` + digest registration).
Fail-closed twice over: a replayed digest is refused (no-double-draw); an amount beyond the
remaining line is refused (the attenuation bound). On commit: counter up, digest burned, holder
credit up, issuer well down — a MOVE against the issuer's well. -/
def draw (t : Line) (digest amt : Nat) : Option Line :=
  if digest ∈ t.draws then none
  else if amt ≤ t.ceiling - t.drawn then
    some { t with drawn := t.drawn + amt
                , draws := digest :: t.draws
                , holderAcct := t.holderAcct + (amt : Int)
                , issuerWell := t.issuerWell - (amt : Int) }
  else none

/-- **`repay` — the holder restores the line.** Fail-closed: repaying more than is drawn is
refused (over-repayment would MINT credit at the issuer's well). On commit: counter down, holder
credit down, issuer well up — the inverse move. The digest registry is untouched: spent digests
stay burned. -/
def repay (t : Line) (amt : Nat) : Option Line :=
  if amt ≤ t.drawn then
    some { t with drawn := t.drawn - amt
                , holderAcct := t.holderAcct - (amt : Int)
                , issuerWell := t.issuerWell + (amt : Int) }
  else none

/-- **`draw_spec` — the commit-shape lemma.** A committed draw means: the digest was fresh, the
amount fit the remaining line, and the post-state is exactly the four-register move. -/
theorem draw_spec {t t' : Line} {d amt : Nat} (h : draw t d amt = some t') :
    d ∉ t.draws ∧ amt ≤ t.ceiling - t.drawn
      ∧ t' = { t with drawn := t.drawn + amt
                    , draws := d :: t.draws
                    , holderAcct := t.holderAcct + (amt : Int)
                    , issuerWell := t.issuerWell - (amt : Int) } := by
  unfold draw at h
  by_cases hd : d ∈ t.draws
  · rw [if_pos hd] at h; exact absurd h (by simp)
  · rw [if_neg hd] at h
    by_cases hb : amt ≤ t.ceiling - t.drawn
    · rw [if_pos hb] at h
      simp only [Option.some.injEq] at h
      exact ⟨hd, hb, h.symm⟩
    · rw [if_neg hb] at h; exact absurd h (by simp)

/-- **`repay_spec` — the settle-shape lemma.** A committed repay means: the amount was within the
outstanding draw, and the post-state is exactly the inverse three-register move. -/
theorem repay_spec {t t' : Line} {amt : Nat} (h : repay t amt = some t') :
    amt ≤ t.drawn
      ∧ t' = { t with drawn := t.drawn - amt
                    , holderAcct := t.holderAcct - (amt : Int)
                    , issuerWell := t.issuerWell + (amt : Int) } := by
  unfold repay at h
  by_cases hb : amt ≤ t.drawn
  · rw [if_pos hb] at h
    simp only [Option.some.injEq] at h
    exact ⟨hb, h.symm⟩
  · rw [if_neg hb] at h; exact absurd h (by simp)

/-- Birth is well-formed. -/
theorem init_WF (n : Nat) : (Line.init n).WF := by
  simp [Line.WF, Line.init]

/-- Birth opens the whole line: remaining = n. -/
theorem init_remaining (n : Nat) : (Line.init n).remaining = n := by
  simp [Line.remaining, Line.init]

/-! ## §3 — Keystone 1: BOUNDED BY THE LINE (per-step). -/

/-- **`draw_within_line`** — a committed draw stays within the line (the `boundedBy` ceiling,
the SGM volume-budget shape). -/
theorem draw_within_line {t t' : Line} {d amt : Nat} (hwf : t.WF)
    (h : draw t d amt = some t') : t'.drawn ≤ t'.ceiling := by
  obtain ⟨hle, -, -, -⟩ := hwf
  obtain ⟨-, hb, rfl⟩ := draw_spec h
  show t.drawn + amt ≤ t.ceiling
  omega

/-- **`over_line_draw_refused` — the REFUSAL tooth.** An over-line draw is fail-closed `none`,
at every state, unconditionally. -/
theorem over_line_draw_refused {t : Line} {d amt : Nat}
    (h : ¬ amt ≤ t.ceiling - t.drawn) : draw t d amt = none := by
  unfold draw
  by_cases hd : d ∈ t.draws
  · rw [if_pos hd]
  · rw [if_neg hd, if_neg h]

/-- A committed draw advances the counter by exactly `amt`, leaves the line fixed, and burns
the digest. -/
theorem draw_records {t t' : Line} {d amt : Nat} (h : draw t d amt = some t') :
    t'.drawn = t.drawn + amt ∧ t'.ceiling = t.ceiling ∧ d ∈ t'.draws := by
  obtain ⟨-, -, rfl⟩ := draw_spec h
  exact ⟨rfl, rfl, List.mem_cons_self ..⟩

/-! ## §4 — Keystone 3: NO DOUBLE DRAW (per-step). -/

/-- **`draw_replay_refused`** — a digest already in the registry can never debit again, no matter
the amount. The anti-replay the `BudgetSlice::debits` list carries in Rust, here a theorem. -/
theorem draw_replay_refused {t : Line} {d amt : Nat} (h : d ∈ t.draws) :
    draw t d amt = none :=
  if_pos h

/-- A committed draw's digest was FRESH — `draw` commits a given digest at most once, ever. -/
theorem draw_digest_was_fresh {t t' : Line} {d amt : Nat} (h : draw t d amt = some t') :
    d ∉ t.draws :=
  (draw_spec h).1

/-- Repay leaves the digest registry untouched: repayment never resurrects a spent digest. -/
theorem repay_draws_fixed {t t' : Line} {amt : Nat} (h : repay t amt = some t') :
    t'.draws = t.draws := by
  obtain ⟨-, rfl⟩ := repay_spec h
  rfl

/-! ## §5 — Keystones 2 & 4: CONSERVATION and SETTLEMENT (per-step). -/

/-- **`bilateral_conserved`** — at every well-formed state, holder credit + issuer well = 0.
The draw is a move against A's well: value is never created across the pair. -/
theorem bilateral_conserved {t : Line} (hwf : t.WF) :
    t.holderAcct + t.issuerWell = 0 := by
  obtain ⟨-, hh, hw, -⟩ := hwf
  rw [hh, hw]
  omega

/-- **`repay_monotone_down`** — a committed repay debits the counter by exactly `amt`
(and leaves the line fixed): settlement is monotone-down on `drawn`. -/
theorem repay_monotone_down {t t' : Line} {amt : Nat} (h : repay t amt = some t') :
    t'.drawn = t.drawn - amt ∧ t'.ceiling = t.ceiling := by
  obtain ⟨-, rfl⟩ := repay_spec h
  exact ⟨rfl, rfl⟩

/-- **`over_repay_refused` — the over-repayment tooth.** Repaying more than is drawn is
fail-closed `none` (it would mint credit at the issuer's well). -/
theorem over_repay_refused {t : Line} {amt : Nat} (h : ¬ amt ≤ t.drawn) :
    repay t amt = none :=
  if_neg h

/-- **`draw_repay_roundtrip` — SETTLEMENT RESTORES THE LINE.** Draw `a`, repay `a`: the counter,
the holder credit, the issuer well, and the remaining line are all back exactly where they started
— monotone-down-then-up, value-neutral. (Only the spent digest stays burned: anti-replay survives
settlement.) -/
theorem draw_repay_roundtrip {t t₁ t₂ : Line} {d a : Nat}
    (h₁ : draw t d a = some t₁) (h₂ : repay t₁ a = some t₂) :
    t₂.drawn = t.drawn ∧ t₂.holderAcct = t.holderAcct ∧ t₂.issuerWell = t.issuerWell
      ∧ t₂.remaining = t.remaining := by
  obtain ⟨-, hb, rfl⟩ := draw_spec h₁
  obtain ⟨-, rfl⟩ := repay_spec h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · show t.drawn + a - a = t.drawn
    omega
  · show t.holderAcct + (a : Int) - (a : Int) = t.holderAcct
    omega
  · show t.issuerWell - (a : Int) + (a : Int) = t.issuerWell
    omega
  · show t.ceiling - (t.drawn + a - a) = t.ceiling - t.drawn
    omega

/-! ### §5b — Settlement against the hard-asset ledger.

Closing the line returns to the ledger: the residual `drawn` is paid in a HARD asset (an ordinary
move, holder→issuer) while the credit legs unwind. This is `rebalance_budgets`'s
`(agent, total_spent)` settlement list (`node/src/state.rs:1213-1216`) applied as a move — the
design doc's §4 weld. We model the hard-asset pair explicitly and prove the settle conserves it. -/

/-- A trustline together with the parties' hard-asset balances (the settlement target ledger). -/
structure Channel where
  tl : Line
  /-- Issuer's hard-asset balance (e.g. the devnet payment asset). -/
  issuerHard : Int
  /-- Holder's hard-asset balance. -/
  holderHard : Int
  deriving Repr, DecidableEq

/-- **`settlePay`** — settle `amt` of the outstanding draw: the holder pays `amt` hard asset to
the issuer AND the credit legs unwind by `amt` (a `repay`). Fail-closed via `repay`'s gate. -/
def settlePay (c : Channel) (amt : Nat) : Option Channel :=
  (repay c.tl amt).map fun tl' =>
    { tl := tl', issuerHard := c.issuerHard + (amt : Int), holderHard := c.holderHard - (amt : Int) }

/-- **`settlePay_conserves_hard`** — settlement is a MOVE on the hard-asset pair: the combined
hard balance is exactly conserved (the `rebalance_conserves` shape, on the bilateral ledger). -/
theorem settlePay_conserves_hard {c c' : Channel} {amt : Nat} (h : settlePay c amt = some c') :
    c'.issuerHard + c'.holderHard = c.issuerHard + c.holderHard := by
  unfold settlePay at h
  cases hr : repay c.tl amt with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some tl' =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      show c.issuerHard + (amt : Int) + (c.holderHard - (amt : Int)) = c.issuerHard + c.holderHard
      omega

/-- **`settleAll`** — close the line: settle the whole outstanding draw. Total — the full repay
always fires (`drawn ≤ drawn`). -/
def settleAll (c : Channel) : Channel := (settlePay c c.tl.drawn).getD c

/-- **`settleAll_clears`** — closing the line zeroes the counter and levels BOTH credit wells:
the trustline returns to its just-born shape (full line available), and the hard-asset move paid
exactly the drawn amount. -/
theorem settleAll_clears (c : Channel) (hwf : c.tl.WF) :
    (settleAll c).tl.drawn = 0
      ∧ (settleAll c).tl.holderAcct = 0
      ∧ (settleAll c).tl.issuerWell = 0
      ∧ (settleAll c).issuerHard = c.issuerHard + (c.tl.drawn : Int) := by
  obtain ⟨-, hh, hw, -⟩ := hwf
  unfold settleAll settlePay repay
  rw [if_pos (Nat.le_refl c.tl.drawn)]
  simp only [Option.map_some, Option.getD_some]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show c.tl.drawn - c.tl.drawn = 0
    omega
  · show c.tl.holderAcct - (c.tl.drawn : Int) = 0
    rw [hh]; omega
  · show c.tl.issuerWell + (c.tl.drawn : Int) = 0
    rw [hw]; omega
  · trivial

/-! ## §6 — The FOREVER crowns: every keystone along every adversarial schedule.

The `sgm_volume_legal_forever` pattern: an adversary picks any infinite schedule of draws and
repays (any digests, any amounts); refused ops are no-ops; the invariant rides the trajectory. -/

/-- One adversarial op against the line. -/
inductive TLOp where
  | draw (digest amt : Nat)
  | repay (amt : Nat)
  deriving Repr, DecidableEq

/-- An adversarial schedule. -/
def TLSched : Type := Nat → TLOp

/-- One step: apply the op; a refused op leaves the state fixed (fail-closed no-op). -/
def step (t : Line) : TLOp → Line
  | .draw d a => (draw t d a).getD t
  | .repay a  => (repay t a).getD t

/-- The trajectory under a schedule. -/
def traj (t₀ : Line) (sched : TLSched) : Nat → Line
  | 0     => t₀
  | n + 1 => step (traj t₀ sched n) (sched n)

/-- A committed draw preserves well-formedness. -/
theorem draw_preserves_WF {t t' : Line} {d amt : Nat} (hwf : t.WF)
    (h : draw t d amt = some t') : t'.WF := by
  obtain ⟨hle, hh, hw, hnd⟩ := hwf
  obtain ⟨hd, hb, rfl⟩ := draw_spec h
  unfold Line.WF
  refine ⟨?_, ?_, ?_, ?_⟩
  · show t.drawn + amt ≤ t.ceiling
    omega
  · show t.holderAcct + (amt : Int) = ((t.drawn + amt : Nat) : Int)
    omega
  · show t.issuerWell - (amt : Int) = -((t.drawn + amt : Nat) : Int)
    omega
  · show (d :: t.draws).Nodup
    exact List.nodup_cons.mpr ⟨hd, hnd⟩

/-- A committed repay preserves well-formedness. -/
theorem repay_preserves_WF {t t' : Line} {amt : Nat} (hwf : t.WF)
    (h : repay t amt = some t') : t'.WF := by
  obtain ⟨hle, hh, hw, hnd⟩ := hwf
  obtain ⟨hb, rfl⟩ := repay_spec h
  unfold Line.WF
  refine ⟨?_, ?_, ?_, ?_⟩
  · show t.drawn - amt ≤ t.ceiling
    omega
  · show t.holderAcct - (amt : Int) = ((t.drawn - amt : Nat) : Int)
    omega
  · show t.issuerWell + (amt : Int) = -((t.drawn - amt : Nat) : Int)
    omega
  · show t.draws.Nodup
    exact hnd

/-- One adversarial step preserves well-formedness (refused ops are identity). -/
theorem step_preserves_WF (t : Line) (op : TLOp) (hwf : t.WF) : (step t op).WF := by
  cases op with
  | draw d a =>
      show ((draw t d a).getD t).WF
      cases h : draw t d a with
      | some t' => simp only [Option.getD_some]; exact draw_preserves_WF hwf h
      | none    => simp only [Option.getD_none]; exact hwf
  | repay a =>
      show ((repay t a).getD t).WF
      cases h : repay t a with
      | some t' => simp only [Option.getD_some]; exact repay_preserves_WF hwf h
      | none    => simp only [Option.getD_none]; exact hwf

/-- **`trustline_WF_forever`** — well-formedness rides every adversarial trajectory. -/
theorem trustline_WF_forever (t₀ : Line) (hinit : t₀.WF) (sched : TLSched) :
    ∀ n, (traj t₀ sched n).WF := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih => exact step_preserves_WF (traj t₀ sched k) (sched k) ih

/-- **KEYSTONE 1 forever: `trustline_within_line_forever`** — drawing never exceeds the line,
along every adversarial schedule. -/
theorem trustline_within_line_forever (t₀ : Line) (hinit : t₀.WF) (sched : TLSched) :
    ∀ n, (traj t₀ sched n).drawn ≤ (traj t₀ sched n).ceiling :=
  fun n => (trustline_WF_forever t₀ hinit sched n).1

/-- **KEYSTONE 2 forever: `trustline_conserved_forever`** — the bilateral pair sums to zero at
every reachable state: no schedule of draws/repays creates or destroys value across the line. -/
theorem trustline_conserved_forever (t₀ : Line) (hinit : t₀.WF) (sched : TLSched) :
    ∀ n, (traj t₀ sched n).holderAcct + (traj t₀ sched n).issuerWell = 0 :=
  fun n => bilateral_conserved (trustline_WF_forever t₀ hinit sched n)

/-- **KEYSTONE 3 forever: `no_double_draw_forever`** — the digest registry is duplicate-free at
every reachable state: no digest ever debits twice. -/
theorem no_double_draw_forever (t₀ : Line) (hinit : t₀.WF) (sched : TLSched) :
    ∀ n, (traj t₀ sched n).draws.Nodup :=
  fun n => (trustline_WF_forever t₀ hinit sched n).2.2.2

/-- **THE PUN forever: `holder_credit_le_line_forever`** — the holder's exercised credit never
exceeds the attenuation bound: granted ⊆ held, quantitatively, at every reachable state. -/
theorem holder_credit_le_line_forever (t₀ : Line) (hinit : t₀.WF) (sched : TLSched) :
    ∀ n, (traj t₀ sched n).holderAcct ≤ ((traj t₀ sched n).ceiling : Int) := by
  intro n
  obtain ⟨hle, hh, -, -⟩ := trustline_WF_forever t₀ hinit sched n
  rw [hh]
  omega

/-- The line itself is an immutable register: no op ever moves the ceiling. -/
theorem step_ceiling_fixed (t : Line) (op : TLOp) : (step t op).ceiling = t.ceiling := by
  cases op with
  | draw d a =>
      show ((draw t d a).getD t).ceiling = t.ceiling
      cases h : draw t d a with
      | some t' => simp only [Option.getD_some]; exact (draw_records h).2.1
      | none    => rfl
  | repay a =>
      show ((repay t a).getD t).ceiling = t.ceiling
      cases h : repay t a with
      | some t' => simp only [Option.getD_some]; exact (repay_monotone_down h).2
      | none    => rfl

/-- **`ceiling_immutable_forever`** — the extended line is the same N at every reachable state
(the `.immutable` slot-caveat shape, design doc §3). -/
theorem ceiling_immutable_forever (t₀ : Line) (sched : TLSched) :
    ∀ n, (traj t₀ sched n).ceiling = t₀.ceiling := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [show traj t₀ sched (k+1) = step (traj t₀ sched k) (sched k) from rfl,
          step_ceiling_fixed, ih]

/-! ## §6b — The Stingray bridge: the draw gate IS `Slice.tryDebit`.

The trustline's counter is LITERALLY the bounded counter the executor's `BudgetGate` runs
(`turn/src/budget_gate.rs:70 try_debit`) and the payment-channel demo bursts against — lines of
credit and payment channels are one primitive at two settings (docs/ORGANS.md §1). -/

/-- **`draw_slice_tracks_tryDebit`** — a committed draw's counter move IS `Slice.tryDebit` on the
line's slice face: same gate, same arithmetic, same post-state. -/
theorem draw_slice_tracks_tryDebit {t t' : Line} {d amt : Nat}
    (h : draw t d amt = some t') : t.slice.tryDebit amt = some t'.slice := by
  obtain ⟨-, hb, rfl⟩ := draw_spec h
  unfold Slice.tryDebit
  rw [if_pos (show amt ≤ t.slice.remaining from hb)]
  rfl

/-- **`draw_fires_iff_tryDebit`** — for a fresh digest, the draw fires IFF the Stingray counter's
`tryDebit` fires: the trustline gate adds exactly the anti-replay leg, nothing else. -/
theorem draw_fires_iff_tryDebit (t : Line) (d amt : Nat) (hfresh : d ∉ t.draws) :
    (draw t d amt).isSome = (t.slice.tryDebit amt).isSome := by
  unfold draw Slice.tryDebit
  rw [if_neg hfresh]
  by_cases hb : amt ≤ t.ceiling - t.drawn
  · rw [if_pos hb, if_pos (show amt ≤ t.slice.remaining from hb)]
    rfl
  · rw [if_neg hb, if_neg (show ¬ amt ≤ t.slice.remaining from hb)]
    rfl

/-! ## §7 — It RUNS: non-vacuity, both polarities. -/

/-- Demo: issuer extends holder a line of 100. -/
def demo₀ : Line := Line.init 100

#guard decide demo₀.WF
#guard demo₀.remaining == 100

-- POSITIVE polarity: a within-line draw ADMITS (digest 7, amount 30).
#guard (draw demo₀ 7 30).isSome

/-- After the first draw: 30 drawn, 70 remaining. -/
def demo₁ : Line := (draw demo₀ 7 30).getD demo₀

#guard demo₁.drawn == 30
#guard demo₁.remaining == 70
#guard demo₁.holderAcct == 30
#guard demo₁.issuerWell == -30
-- CONSERVATION: the bilateral pair sums to zero.
#guard demo₁.holderAcct + demo₁.issuerWell == 0
#guard decide demo₁.WF

-- NEGATIVE polarity 1: replaying digest 7 is REFUSED (any amount).
#guard (draw demo₁ 7 1).isNone
-- NEGATIVE polarity 2: an over-line draw is REFUSED (80 > 70 remaining).
#guard (draw demo₁ 8 80).isNone
-- ...but the boundary draw (exactly the remaining 70) ADMITS — the bound is tight.
#guard (draw demo₁ 8 70).isSome
-- NEGATIVE polarity 3: over-repay is REFUSED (31 > 30 drawn).
#guard (repay demo₁ 31).isNone

/-- Settlement: repay the full 30 — the line is restored. -/
def demo₂ : Line := (repay demo₁ 30).getD demo₁

#guard demo₂.drawn == 0
#guard demo₂.remaining == 100
#guard demo₂.holderAcct == 0
#guard demo₂.issuerWell == 0
-- The spent digest stays burned: anti-replay survives settlement.
#guard (draw demo₂ 7 10).isNone
-- A fresh digest draws fine on the restored line.
#guard (draw demo₂ 9 100).isSome

/-- Hard-asset settlement: close the line at 30 drawn; both parties start with 500 hard. -/
def demoCh : Channel := { tl := demo₁, issuerHard := 500, holderHard := 500 }
/-- The closed channel. -/
def demoCh' : Channel := settleAll demoCh

#guard demoCh'.tl.drawn == 0
#guard demoCh'.issuerHard == 530
#guard demoCh'.holderHard == 470
-- The hard pair is conserved: 530 + 470 = 500 + 500.
#guard demoCh'.issuerHard + demoCh'.holderHard == demoCh.issuerHard + demoCh.holderHard

/-! ## §8 — Axiom-hygiene tripwires. -/

#assert_axioms draw_spec
#assert_axioms repay_spec
#assert_axioms init_WF
#assert_axioms init_remaining
#assert_axioms draw_within_line
#assert_axioms over_line_draw_refused
#assert_axioms draw_records
#assert_axioms draw_replay_refused
#assert_axioms draw_digest_was_fresh
#assert_axioms repay_draws_fixed
#assert_axioms bilateral_conserved
#assert_axioms repay_monotone_down
#assert_axioms over_repay_refused
#assert_axioms draw_repay_roundtrip
#assert_axioms settlePay_conserves_hard
#assert_axioms settleAll_clears
#assert_axioms draw_preserves_WF
#assert_axioms repay_preserves_WF
#assert_axioms trustline_WF_forever
#assert_axioms trustline_within_line_forever
#assert_axioms trustline_conserved_forever
#assert_axioms no_double_draw_forever
#assert_axioms holder_credit_le_line_forever
#assert_axioms ceiling_immutable_forever
#assert_axioms draw_slice_tracks_tryDebit
#assert_axioms draw_fires_iff_tryDebit

end Dregg2.Apps.Trustline
