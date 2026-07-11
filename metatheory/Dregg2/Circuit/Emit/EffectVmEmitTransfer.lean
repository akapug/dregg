/-
# Dregg2.Circuit.Emit.EffectVmEmitTransfer — the TRANSFER effect's concrete circuit, EMITTED.

This module re-derives the running `Transfer` row constraints FROM the transfer intent and emits
them through the `EffectVmEmit` IR as `transferVmDescriptor`, then proves the emitted descriptor's
denotation is EQUIVALENT to that intent (`transferVm_faithful`) + the anti-ghost teeth. So the
EffectVM transfer circuit the Rust prover (`EffectVmP3Air`) runs IS the verified intent by
construction.

## The TARGET (the running prover's transfer constraints)

From `circuit/src/effect_vm_p3_full_air.rs` (mirror of `effect_vm/air.rs`), on a TRANSFER row
(`s_transfer = 1`, all other selectors 0, so `s_noop = 0`):

  * `new_bal_lo - old_bal_lo - amount + 2·direction·amount = 0`   (debit/credit on the lo limb)
  * `new_bal_hi - old_bal_hi = 0`                                  (hi limb unchanged)
  * `direction·(direction - 1) = 0`                               (direction ∈ {0,1})
  * `new_cap_root - old_cap_root = 0`, `new_reserved - old_reserved = 0`  (frame passthrough)
  * `fld_a i - fld_b i = 0`  for i ∈ 0..8                          (fields frozen)
  * `new_nonce - old_nonce - (1 - s_noop) = 0`  ⟹  `new_nonce = old_nonce + 1`  (nonce tick)
  * transition continuity `next.state_before[i] = this.state_after[i]` for the whole state block
  * GROUP-4 state-commitment hash chain: 4 ordered `H4` sites with
    `state_after.state_commit = H4(inter1, inter2, inter3, 0)`, the inters binding the after-state
  * boundary pins: row-0 `{nonce, bal_lo, bal_hi, state_commit}` to `{ACTOR_NONCE, INIT_BAL_LO,
    INIT_BAL_HI, OLD_COMMIT}`; last-row `{state_commit, bal_lo, bal_hi}` to `{NEW_COMMIT,
    FINAL_BAL_LO, FINAL_BAL_HI}`.

## The INTENT (independent, the faithfulness target)

`TransferRowIntent` is the field-level transfer move written from protocol intent — the SAME
debit/credit `Spec.CircuitSpecTriangle.intentTransfer` pins abstractly, projected to the EffectVM
row layout (balance limbs + nonce + frame). `transferVm_faithful` proves the emitted descriptor's
per-row gate set is satisfied on a transfer row IFF `TransferRowIntent` holds — so the concrete
circuit enforces EXACTLY the intent, and any wrong-output row (tampered balance / nonce / frame)
makes the descriptor UNSAT (`transferVm_rejects_*`).
-/
import Dregg2.Circuit.Emit.EffectVmEmit

namespace Dregg2.Circuit.Emit.EffectVmEmitTransfer

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — Column readers as `EmittedExpr` (the gate-body builders).

These build the SAME `var`/`add`/`mul` ASTs the running prover's `lc`/`sb`/`sa`/`prm` accessors
read, so the emitted gate bodies are the prover's polynomials. -/

/-- `state_before[off]` as an expression. -/
def eSB (off : Nat) : EmittedExpr := .var (sbCol off)
/-- `state_after[off]` as an expression. -/
def eSA (off : Nat) : EmittedExpr := .var (saCol off)
/-- `param[i]` as an expression. -/
def ePrm (i : Nat) : EmittedExpr := .var (prmCol i)
/-- The transfer selector column as an expression. -/
def eSelTransfer : EmittedExpr := .var sel.TRANSFER
/-- The noop selector column as an expression. -/
def eSelNoop : EmittedExpr := .var sel.NOOP

/-- `a - b` as an `EmittedExpr` (`a + (-1)·b`). -/
def eSub (a b : EmittedExpr) : EmittedExpr := .add a (.mul (.const (-1)) b)

/-! ## §0.5 — Field-denotation glue.

`VmConstraint.holdsVm` on a gate now asserts the body is `≡ 0 [ZMOD p]` (`p = 2013265921`, the
BabyBear prime), NOT `= 0` over ℤ — the DEPLOYED field constraint. These helpers translate between a
gate body vanishing mod `p` and the field-level move it enforces, using `p`'s primality (proved in
`BabyBearFriField`) and the deployed range-check canonicality `0 ≤ cell < p`. -/

/-- The BabyBear modulus `p = 2013265921` is prime (over ℤ). Reuses the campaign's canonical fact. -/
theorem pPrimeInt : Prime (2013265921 : ℤ) := by
  exact_mod_cast Nat.prime_iff_prime_int.mp Dregg2.Circuit.BabyBearFriField.babyBearP_prime

/-- Lift an integer equality to a mod-`p` congruence (the POSITIVE-direction glue: a real trace with
`residual = 0` satisfies the field gate `residual ≡ 0`). -/
theorem eqToModEq {a b : ℤ} (h : a = b) : a ≡ b [ZMOD 2013265921] := by rw [h]

/-- A gate body `x = a − b` vanishes mod `p` IFF the two field values are congruent mod `p`. This is
the field-faithful equivalence: the gate `x ≡ 0 [ZMOD p]` says exactly `a ≡ b [ZMOD p]`. -/
theorem gate_modEq_iff {x a b : ℤ} (hx : x = a - b) :
    (x ≡ 0 [ZMOD 2013265921]) ↔ (a ≡ b [ZMOD 2013265921]) := by
  rw [Int.modEq_zero_iff_dvd, Int.modEq_iff_dvd, hx]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨-k, by omega⟩
  · rintro ⟨k, hk⟩; exact ⟨-k, by omega⟩

/-- NEGATIVE-tooth glue: a gate body `x = a − b` with BOTH field values CANONICAL (`0 ≤ · < p`, the
deployed range-check invariant) does NOT vanish mod `p` when `a ≠ b`. Prime `p` is unnecessary here —
canonicality forces the residual into `(−p, p)`, so `p ∣ residual` collapses it to `0`. -/
theorem not_modEq_zero_of_canon {x a b : ℤ} (hx : x = a - b)
    (ha : 0 ≤ a ∧ a < 2013265921) (hb : 0 ≤ b ∧ b < 2013265921) (hne : a ≠ b) :
    ¬ (x ≡ 0 [ZMOD 2013265921]) := by
  rw [Int.modEq_zero_iff_dvd, hx]
  rintro ⟨k, hk⟩
  omega

/-! ## §1 — The TRANSFER gate bodies (term-for-term the running prover's, ungated by `s_transfer`).

We emit the gates ALREADY specialized to a transfer row: the running prover multiplies each by
`s_transfer`, which is `1` on a transfer row, so the row-restricted gate body is the inner
polynomial. (The selector-validity / sum-to-one gates of GROUP 1 are global well-formedness; the
transfer faithfulness is about the per-effect transition, so we emit the transfer-specialized
bodies and PROVE they coincide with the intent on the transfer row.) -/

/-- Balance-lo debit/credit body: `new_bal_lo - old_bal_lo - amount + 2·direction·amount`. -/
def gBalLo : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO))
    (.add (.mul (.const (-1)) (ePrm param.AMOUNT))
      (.mul (.const 2) (.mul (ePrm param.DIRECTION) (ePrm param.AMOUNT))))

/-- Balance-hi unchanged body: `new_bal_hi - old_bal_hi`. -/
def gBalHi : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)

/-- Direction-boolean body: `direction·(direction - 1)`. -/
def gDirBool : EmittedExpr :=
  .mul (ePrm param.DIRECTION) (.add (ePrm param.DIRECTION) (.const (-1)))

/-- Nonce-increment body (ungated, transfer-specialized): `new_nonce - old_nonce - (1 - s_noop)`.
On a transfer row `s_noop = 0`, so this is `new_nonce - old_nonce - 1`. -/
def gNonce : EmittedExpr :=
  eSub (eSub (eSA state.NONCE) (eSB state.NONCE)) (eSub (.const 1) eSelNoop)

/-- Cap-root passthrough body: `new_cap_root - old_cap_root`. -/
def gCapPass : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)

/-- Reserved passthrough body: `new_reserved - old_reserved`. -/
def gResPass : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)

/-- Field-`i` passthrough body: `field_after[i] - field_before[i]`. -/
def gFieldPass (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

/-- The eight field-passthrough gates. -/
def gFieldPassAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldPass i))

/-! ## §2 — The TRANSITION + BOUNDARY + PI constraints.

Transition continuity over the whole state block; the 7 boundary pins (4 first-row, 3 last-row)
as `piBinding`s. -/

/-- Transition continuity for the whole state block: `next.state_before[i] = this.state_after[i]`. -/
def transitionAll : List VmConstraint :=
  (List.range STATE_SIZE).map (fun i => VmConstraint.transition i i)

/-- The first-row boundary PI pins (`nonce`/`bal_lo`/`bal_hi`/`state_commit`). -/
def boundaryFirstPins : List VmConstraint :=
  [ .piBinding .first (sbCol state.NONCE)        pi.ACTOR_NONCE
  , .piBinding .first (sbCol state.BALANCE_LO)   pi.INIT_BAL_LO
  , .piBinding .first (sbCol state.BALANCE_HI)   pi.INIT_BAL_HI
  , .piBinding .first (sbCol state.STATE_COMMIT) pi.OLD_COMMIT ]

/-- The last-row boundary PI pins (`state_commit`/`bal_lo`/`bal_hi`). -/
def boundaryLastPins : List VmConstraint :=
  [ .piBinding .last (saCol state.STATE_COMMIT) pi.NEW_COMMIT
  , .piBinding .last (saCol state.BALANCE_LO)   pi.FINAL_BAL_LO
  , .piBinding .last (saCol state.BALANCE_HI)   pi.FINAL_BAL_HI ]

/-! ## §3 — The GROUP-4 state-commitment hash sites (ordered).

The four `H4` sites of the running prover (in the FIXED `hash_sites()` order), binding the
after-state cells into `state_after.state_commit`. Abstract `hash : List ℤ → ℤ` carrier. -/

/-- Site 0: `inter1 = H4(after.bal_lo, after.bal_hi, after.nonce, after.field[0])`. -/
def site0 : VmHashSite :=
  { digestCol := auxCol aux_off.STATE_INTER1
  , inputs := [ .col (saCol state.BALANCE_LO), .col (saCol state.BALANCE_HI)
              , .col (saCol state.NONCE),      .col (saCol (state.FIELD_BASE + 0)) ]
  , arity := 4 }

/-- Site 1: `inter2 = H4(after.field[1..5])`. -/
def site1 : VmHashSite :=
  { digestCol := auxCol aux_off.STATE_INTER2
  , inputs := [ .col (saCol (state.FIELD_BASE + 1)), .col (saCol (state.FIELD_BASE + 2))
              , .col (saCol (state.FIELD_BASE + 3)), .col (saCol (state.FIELD_BASE + 4)) ]
  , arity := 4 }

/-- Site 2: `inter3 = H4(after.field[5], after.field[6], after.field[7], after.cap_root)`. -/
def site2 : VmHashSite :=
  { digestCol := auxCol aux_off.STATE_INTER3
  , inputs := [ .col (saCol (state.FIELD_BASE + 5)), .col (saCol (state.FIELD_BASE + 6))
              , .col (saCol (state.FIELD_BASE + 7)), .col (saCol state.CAP_ROOT) ]
  , arity := 4 }

/-- Site 3: `state_commit = H4(inter1, inter2, inter3, record_digest)` (the published post-state
commitment). Result column is `state_after.state_commit` itself (the GROUP-4 `sa(STATE_COMMIT) ==
digest` binding), reading sites 0/1/2's digests. The FOURTH input is the witnessed authority-residue
`record_digest` (`aux_off.STATE_RECORD_DIGEST`, absolute col `auxCol 96 = 186`) — replacing the old
literal `.zero`, audit P0-2 — so `state_commit` (and thus `OLD_COMMIT`/`NEW_COMMIT`) binds the FULL
cell state. Matches the Rust `cell_state.rs::compute_commitment` / `air.rs` GROUP-4
(`local[AUX_BASE + aux_off::STATE_RECORD_DIGEST]`). A residue-free cell witnesses `0` here, so this is
byte-identical to the legacy `…, 0)` form. -/
def site3 : VmHashSite :=
  { digestCol := saCol state.STATE_COMMIT
  , inputs := [ .digest 0, .digest 1, .digest 2, .col (auxCol aux_off.STATE_RECORD_DIGEST) ]
  , arity := 4 }

/-- The ordered GROUP-4 hash sites (site `i` ↔ aux block `i`, the Rust `hash_sites()` contract). -/
def transferHashSites : List VmHashSite := [site0, site1, site2, site3]

/-! ## §4 — The emitted TRANSFER descriptor. -/

/-- The transfer AIR identity (carried for the fingerprint binding). -/
def transferVmAirName : String := "dregg-effectvm-transfer-v1"

/-- The transfer-specialized per-row gates (balance lo/hi, direction bool, nonce, frame). -/
def transferRowGates : List VmConstraint :=
  [ .gate gBalLo, .gate gBalHi, .gate gDirBool, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`transferVmDescriptor`** — the TRANSFER effect's full concrete circuit, emitted through the
EffectVM IR: the per-row debit/credit/nonce/frame gates ++ transition continuity ++ the 7
boundary PI pins, with the 4 ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def transferVmDescriptor : EffectVmDescriptor :=
  { name := transferVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := transferRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates sel.TRANSFER
  , hashSites := transferHashSites
  -- ⚠ DEPLOYED SOUNDNESS GAP #4 (wrap-class, verdict A, HIGH — `docs/reference/WRAP-CLASS-AUDIT.md`) — CLOSED by the
  -- AVAILABILITY WELD in §11.7 (`transferVmDescriptorAvail`), STAGED for the big-bang VK/fixture regen (the vault
  -- pattern: `Dregg2.Deos.VaultSatDescriptor` / `vault_weld.rs`). The bare descriptor below range-checks ONLY the
  -- AFTER limbs; the debit gate `after.bal_lo ≡ before.bal_lo − amount [ZMOD p]` alone admits an UNDERFLOW WRAP
  -- (witness `before=1, amount=1006632961, after=1006632961`: `after − before + amount = p ≡ 0`, `after < 2^30`),
  -- and the availability tooth used to LAUNDER the gap through an `hcanonMove` (= `0 ≤ before − amount`, availability
  -- ITSELF) that no gate enforced. The §11.7 hardened descriptor DECOMPOSES the debit into 15-bit limbs with a
  -- borrow chain (`before = after + amount`, no residual reaches `p`), range-checks `amount` + the operand limbs, and
  -- DERIVES availability in-circuit (`transferAvail_derives_availability`, NO `hcanonMove`; the forgery is UNSAT,
  -- `transferAvail_forgery_unsat`). Covers Transfer debit / Burn / fee-debit. Until the flip the LIVE registry still
  -- routes this bare descriptor; a pure light client does not yet witness availability in production.
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §5 — The TRANSFER ROW INTENT (the independent faithfulness target).

`TransferRowIntent` is the field-level transfer move, written from protocol intent (NOT from the
gate bodies): on a transfer row, the new balance is the old balance moved by `amount` in the
direction sign, the hi limb and the whole frame (cap/reserved/8 fields) are FIXED, the nonce
ticks by one, and `direction` is a bit. This is the EffectVM-row projection of
`CircuitSpecTriangle.intentTransfer`'s debit-src/credit-dst (here the actor cell's own limb moves
by the signed amount; `direction = 1` debits, `direction = 0` credits). -/

/-- **`TransferRowIntent env`** — the intended transfer move on the row `env.loc`. FIELD-FAITHFUL:
each clause is a congruence mod `p = 2013265921` (the BabyBear prime), because the deployed circuit
enforces the move IN THE FIELD — a canonical trace can carry an ℤ residual equal to `p ≠ 0`, so the
old ℤ `=` was provably too strong. The gate set holds IFF this field move holds (no canonicality
needed for the biconditional — both sides live in the field). -/
def TransferRowIntent (env : VmRowEnv) : Prop :=
  -- direction is a bit (mod p)
  (env.loc (prmCol param.DIRECTION) ≡ 0 [ZMOD 2013265921]
    ∨ env.loc (prmCol param.DIRECTION) ≡ 1 [ZMOD 2013265921])
  -- balance lo moves by the signed amount: new ≡ old + amount·(1 - 2·direction)
  ∧ env.loc (saCol state.BALANCE_LO)
      ≡ env.loc (sbCol state.BALANCE_LO)
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION)) [ZMOD 2013265921]
  -- balance hi unchanged
  ∧ env.loc (saCol state.BALANCE_HI) ≡ env.loc (sbCol state.BALANCE_HI) [ZMOD 2013265921]
  -- nonce ticks by one
  ∧ env.loc (saCol state.NONCE) ≡ env.loc (sbCol state.NONCE) + 1 [ZMOD 2013265921]
  -- cap root + reserved fixed
  ∧ env.loc (saCol state.CAP_ROOT) ≡ env.loc (sbCol state.CAP_ROOT) [ZMOD 2013265921]
  ∧ env.loc (saCol state.RESERVED) ≡ env.loc (sbCol state.RESERVED) [ZMOD 2013265921]
  -- the 8 fields fixed
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i))
      ≡ env.loc (sbCol (state.FIELD_BASE + i)) [ZMOD 2013265921])

/-! ## §6 — The transfer-row environment hypothesis (selectors).

On a genuine transfer row the transfer selector is `1` and the noop selector is `0` (GROUP-1
selector validity + sum-to-one forces exactly one selector hot). `IsTransferRow` names this; it
is what the running prover's `s_transfer = 1`, `s_noop = 0` factoring relies on. -/

/-- The row is a transfer row: `s_transfer = 1`, `s_noop = 0`. -/
def IsTransferRow (env : VmRowEnv) : Prop :=
  env.loc sel.TRANSFER = 1 ∧ env.loc sel.NOOP = 0

/-! ## §7 — FAITHFULNESS: the emitted per-row gates ⟺ the intent.

The load-bearing theorem: on a transfer row, the emitted descriptor's per-row gates
(`transferRowGates`) all hold IFF `TransferRowIntent` holds. The gate bodies are the SAME
polynomials the running prover asserts (specialized to the transfer row), and they pin EXACTLY
the intent move — so the concrete EffectVM circuit enforces the verified intent. -/

/-- Helper: every gate in `transferRowGates` holds means each body vanishes on `env.loc`. -/
theorem transferRowGates_holds_iff (env : VmRowEnv) (hrow : IsTransferRow env) :
    (∀ c ∈ transferRowGates, c.holdsVm env false false) ↔ TransferRowIntent env := by
  obtain ⟨_hsT, hsN⟩ := hrow
  unfold transferRowGates gFieldPassAll TransferRowIntent
  constructor
  · intro h
    -- extract each gate from membership
    have hLo := h (.gate gBalLo) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hDir := h (.gate gDirBool) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    -- unfold each holds (now each body is `≡ 0 [ZMOD p]`)
    simp only [VmConstraint.holdsVm, gBalLo, gBalHi, gDirBool, gNonce, gCapPass, gResPass,
      eSA, eSB, ePrm, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hDir hNon hCap hRes
    rw [hsN] at hNon
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- direction bit, from p ∣ direction·(direction-1); p prime ⟹ p ∣ dir ∨ p ∣ (dir-1)
      rw [Int.modEq_zero_iff_dvd] at hDir
      rcases (pPrimeInt.dvd_mul.mp hDir) with hd | hd
      · exact Or.inl (by rw [Int.modEq_zero_iff_dvd]; exact hd)
      · refine Or.inr ?_
        rw [Int.modEq_iff_dvd]; obtain ⟨k, hk⟩ := hd; exact ⟨-k, by omega⟩
    · -- balance lo move: hLo is `(new - old) + (-amount + 2·(dir·amount)) ≡ 0`.
      exact (gate_modEq_iff (by ring)).mp hLo
    · exact (gate_modEq_iff (by ring)).mp hHi
    · -- nonce: hNon is `(new - old) - (1 - 0) ≡ 0`.
      exact (gate_modEq_iff (by ring)).mp hNon
    · exact (gate_modEq_iff (by ring)).mp hCap
    · exact (gate_modEq_iff (by ring)).mp hRes
    · intro i hi
      have hfi := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at hfi
      exact (gate_modEq_iff (by ring)).mp hfi
  · rintro ⟨hDir, hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    -- dispatch by which gate `c` is
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · -- gBalLo
      simp only [VmConstraint.holdsVm, gBalLo, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hLo
    · -- gBalHi
      simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hHi
    · -- gDirBool: from `dir ≡ 0 ∨ dir ≡ 1` the boolean gate `dir·(dir-1) ≡ 0` holds
      simp only [VmConstraint.holdsVm, gDirBool, ePrm, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]
      rcases hDir with hd | hd
      · rw [Int.modEq_zero_iff_dvd] at hd
        exact dvd_mul_of_dvd_left hd _
      · rw [Int.modEq_iff_dvd] at hd
        have hdd : (2013265921 : ℤ) ∣ (env.loc (prmCol param.DIRECTION) + -1) := by
          obtain ⟨k, hk⟩ := hd; exact ⟨-k, by omega⟩
        exact dvd_mul_of_dvd_right hdd _
    · -- gNonce
      simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hsN]
      exact (gate_modEq_iff (by ring)).mpr hNon
    · -- gCapPass
      simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hCap
    · -- gResPass
      simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hRes
    · -- gFieldPass i
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr (hFld i hi)

/-- **`transferVm_faithful` — THE deliverable (the load-bearing direction + converse).** On a
transfer row, the emitted descriptor's per-row gates hold IFF the transfer intent holds. So the
concrete EffectVM transfer circuit the Rust prover runs enforces EXACTLY the verified intent move
(`TransferRowIntent` = the EffectVM-row projection of `CircuitSpecTriangle.intentTransfer`). -/
theorem transferVm_faithful (env : VmRowEnv) (hrow : IsTransferRow env) :
    (∀ c ∈ transferRowGates, c.holdsVm env false false) ↔ TransferRowIntent env :=
  transferRowGates_holds_iff env hrow

/-! ## §8 — ANTI-GHOST: a wrong-output transfer row fails the emitted descriptor.

The contrapositive of `transferVm_faithful`: any transfer row whose post-state is NOT the intent
move (wrong balance, wrong nonce tick, tampered frame) violates some per-row gate, so the emitted
descriptor is UNSAT for it. -/

/-- **Anti-ghost (general).** A transfer row whose post-state is NOT the intent move does NOT
satisfy the per-row gates. -/
theorem transferVm_rejects_wrong_output (env : VmRowEnv) (hrow : IsTransferRow env)
    (hwrong : ¬ TransferRowIntent env) :
    ¬ (∀ c ∈ transferRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((transferVm_faithful env hrow).mp h)

/-- **Anti-ghost (balance tamper).** A transfer row whose post-`bal_lo` is NOT the signed move has
no satisfying gate set — the `gBalLo` gate alone rejects it (UNSAT). FIELD-FAITHFUL: the tooth now
rejects a field-`≢` output, so it needs the DEPLOYED range-check canonicality — the after-balance
(`saCol BALANCE_LO`, a `transferRanges` wire) and the intended debited balance both lie in `[0, p)`.
Under canonicality a WRONG `bal_lo` differs from the intended value by less than `p`, so `p` cannot
divide the residual and the field gate is UNSAT (no wrap-around forgery). -/
theorem transferVm_rejects_wrong_balance (env : VmRowEnv)
    (hcanonNew : 0 ≤ env.loc (saCol state.BALANCE_LO)
      ∧ env.loc (saCol state.BALANCE_LO) < 2013265921)
    (hcanonMove : 0 ≤ env.loc (sbCol state.BALANCE_LO)
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION))
      ∧ env.loc (sbCol state.BALANCE_LO)
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION)) < 2013265921)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO)
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION))) :
    ¬ (VmConstraint.gate gBalLo).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLo, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  exact not_modEq_zero_of_canon (by ring) hcanonNew hcanonMove hwrong

/-- **Anti-ghost (nonce tamper).** A transfer row whose nonce does NOT tick by one (`s_noop = 0`)
fails the `gNonce` gate. FIELD-FAITHFUL: needs the deployed canonicality — the after-nonce lies in
`[0, p)` and the pre-nonce ticked (`old + 1`) lies in `[0, p)` (nonces are far below the modulus), so
a wrong nonce differs from `old + 1` by less than `p` and the field gate cannot pass by wrap-around. -/
theorem transferVm_rejects_wrong_nonce (env : VmRowEnv) (hsN : env.loc sel.NOOP = 0)
    (hcanonNew : 0 ≤ env.loc (saCol state.NONCE) ∧ env.loc (saCol state.NONCE) < 2013265921)
    (hcanonTick : 0 ≤ env.loc (sbCol state.NONCE) + 1
      ∧ env.loc (sbCol state.NONCE) + 1 < 2013265921)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + 1) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  rw [hsN]
  exact not_modEq_zero_of_canon (by ring) hcanonNew hcanonTick hwrong

/-! ## §9 — Boundary + transition faithfulness (the PI/continuity clauses pin the turn boundary).

The boundary/transition constraints are pure equalities, so their denotation is exactly the
intended pin. We expose them as faithfulness lemmas: a satisfying descriptor pins row-0
`state_before` to the OLD commitment / init balances / actor nonce, and the last row's
`state_after.state_commit` to the NEW commitment. -/

/-- The row-0 boundary pins, when satisfied on the first row, force `state_before`'s
nonce/balances/commitment to the public inputs (turn-identity binding). -/
theorem boundaryFirst_pins (env : VmRowEnv)
    (h : ∀ c ∈ boundaryFirstPins, c.holdsVm env true false) :
    env.loc (sbCol state.NONCE) ≡ env.pub pi.ACTOR_NONCE [ZMOD 2013265921]
    ∧ env.loc (sbCol state.BALANCE_LO) ≡ env.pub pi.INIT_BAL_LO [ZMOD 2013265921]
    ∧ env.loc (sbCol state.BALANCE_HI) ≡ env.pub pi.INIT_BAL_HI [ZMOD 2013265921]
    ∧ env.loc (sbCol state.STATE_COMMIT) ≡ env.pub pi.OLD_COMMIT [ZMOD 2013265921] := by
  have key : ∀ col k, VmConstraint.piBinding VmRow.first col k ∈ boundaryFirstPins →
      env.loc col ≡ env.pub k [ZMOD 2013265921] := by
    intro col k hmem
    have hh := h _ hmem
    simp only [VmConstraint.holdsVm] at hh
    exact hh trivial
  refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_⟩ <;>
    · unfold boundaryFirstPins; simp

/-- The last-row boundary pins force `state_after.state_commit` to `NEW_COMMIT` (the published
post-state commitment) and the final balances to their PIs. -/
theorem boundaryLast_pins (env : VmRowEnv)
    (h : ∀ c ∈ boundaryLastPins, c.holdsVm env false true) :
    env.loc (saCol state.STATE_COMMIT) ≡ env.pub pi.NEW_COMMIT [ZMOD 2013265921]
    ∧ env.loc (saCol state.BALANCE_LO) ≡ env.pub pi.FINAL_BAL_LO [ZMOD 2013265921]
    ∧ env.loc (saCol state.BALANCE_HI) ≡ env.pub pi.FINAL_BAL_HI [ZMOD 2013265921] := by
  have key : ∀ col k, VmConstraint.piBinding VmRow.last col k ∈ boundaryLastPins →
      env.loc col ≡ env.pub k [ZMOD 2013265921] := by
    intro col k hmem
    have hh := h _ hmem
    simp only [VmConstraint.holdsVm] at hh
    exact hh trivial
  refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_⟩ <;>
    · unfold boundaryLastPins; simp

/-! ## §10 — The hash-chain binding: the published commitment IS the genuine digest of the
after-state (under the abstract Poseidon carrier).

`transferHashSites` satisfied means `state_after.state_commit = H4(inter1, inter2, inter3, 0)`
with the inters the genuine `H4` of the after-state cells — the GROUP-4 anti-ghost that pins the
WHOLE post-state into the commitment. -/

/-- A satisfying hash-site set forces `state_after.state_commit` to the genuine 4-level digest of
the after-state (abstract `hash`). The site ORDER is load-bearing: site 3 reads sites 0/1/2's
digests, exactly as the running prover's `digests[3] = H4(digests[0], digests[1], digests[2], 0)`. -/
theorem transferHash_binds (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env transferHashSites) :
    env.loc (saCol state.STATE_COMMIT)
      = hash [ hash [ env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI)
                    , env.loc (saCol state.NONCE), env.loc (saCol (state.FIELD_BASE + 0)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2))
                    , env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6))
                    , env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT) ]
             , env.loc (auxCol aux_off.STATE_RECORD_DIGEST) ] := by
  -- unfold the ordered site walk: sites 0,1,2,3 in order.
  unfold siteHoldsAll transferHashSites at h
  simp only [siteHoldsAll.go, site0, site1, site2, site3, VmHashSite.resolvedInputs,
    HashInput.resolve, List.map_cons, List.map_nil, List.getD] at h
  obtain ⟨h0, h1, h2, h3, _⟩ := h
  -- h3 : env.loc (saCol STATE_COMMIT) = hash [d0, d1, d2, 0]; substitute the inter digests.
  rw [h3]
  -- the accumulator at site 3 is [d0, d1, d2]; its getD 0/1/2 are d0/d1/d2.
  rfl

/-! ## §11 — Putting it together: the satisfied descriptor pins the intent + boundary + commitment.

`transferVmDescriptor_pins_intent`: a transfer row satisfying the WHOLE emitted descriptor (gates
+ transitions + boundaries + hash sites) on the LAST row of the trace realizes the transfer intent
AND publishes the genuine post-state commitment. This is the corner-(b) statement at the concrete
EffectVM level: the running circuit's satisfaction ⇒ the verified intent. -/

/-- **`transferVmDescriptor_pins_commit` — the last-row commit pin (FAITHFUL, `when_last_row()`).**
A row satisfying the descriptor at `isLast = true` publishes `state_after.STATE_COMMIT = NEW_COMMIT`.
This is purely the `boundaryLastPins` (`.piBinding .last`) clause, which fires under `when_last_row()`;
it does NOT depend on the gates (which run under `when_transition()`). -/
theorem transferVmDescriptor_pins_commit (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hsat : satisfiedVm hash transferVmDescriptor env true true) :
    env.loc (saCol state.STATE_COMMIT) ≡ env.pub pi.NEW_COMMIT [ZMOD 2013265921] := by
  obtain ⟨hcs, _hsites⟩ := hsat
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ transferVmDescriptor.constraints := by
      unfold transferVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    -- boundaryLastPins are `.piBinding .last …`; holdsVm under (true,true) ⟹ under (false,true).
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  exact (boundaryLast_pins env hlast).1

/-- **`transferVmDescriptor_pins_intent` — corner (b), concrete (FAITHFUL to `when_transition()`).**
The intent move and the commit pin are enforced on DIFFERENT rows of the deployed circuit, so the
faithful statement takes them from the rows where they fire:
  * `hgatesat` — the descriptor satisfied at the ACTIVE row (`isLast = false`): the deployed gates run
    under `builder.when_transition()`, so they bind on every row but the last; the active effect row of
    any real trace is a transition row. This yields `TransferRowIntent`.
  * `hsat` — the descriptor satisfied with `isLast = true`: the `boundaryLastPins` (`.piBinding .last`)
    run under `when_last_row()`, so the published `state_after.STATE_COMMIT = NEW_COMMIT` is pinned on
    the LAST row.
A SINGLE `(true,true)` row — the only row being simultaneously first and last — does NOT bind the gates
(it is the wrap row), which is exactly the degenerate window a faithful denotation must not over-pin;
hence the two evidences are separate. On the one-effect trace the active row's after-state equals the
last row's after-state (frozen frame), so the two views agree on the decoded `env`. -/
theorem transferVmDescriptor_pins_intent (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hrow : IsTransferRow env)
    (hgatesat : satisfiedVm hash transferVmDescriptor env true false)
    (hsat : satisfiedVm hash transferVmDescriptor env true true) :
    TransferRowIntent env
    ∧ env.loc (saCol state.STATE_COMMIT) ≡ env.pub pi.NEW_COMMIT [ZMOD 2013265921] := by
  obtain ⟨hcsT, _⟩ := hgatesat
  -- The per-row gates, drawn at the ACTIVE row (`isLast = false`), where `when_transition()` binds.
  have hgates' : ∀ c ∈ transferRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ transferVmDescriptor.constraints := by
      unfold transferVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcsT c hmem
    -- transferRowGates are all `.gate _`; at `isLast = false` `holdsVm` IS the body equation.
    unfold transferRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  exact ⟨(transferVm_faithful env hrow).mp hgates', transferVmDescriptor_pins_commit hash env hsat⟩

/-! ## §11.5 — NON-VACUITY: a concrete transfer row that satisfies the intent, and one that does not.

The faithfulness biconditional is only meaningful if BOTH sides are inhabited and refutable. We
exhibit a concrete row `goodRow` (outgoing transfer of 30 from a cell with bal_lo 100 → 70, nonce
5 → 6, frame fixed) that REALIZES `TransferRowIntent` — and `badRow` (same but post-`bal_lo`
forged to 999) that VIOLATES it, so `transferVm_rejects_wrong_output` fires concretely. -/

/-- A concrete environment: a transfer row. `loc` reads the named EffectVM columns; everything
unmentioned is `0`. Outgoing (`direction = 1`) transfer of `amount = 30`: `bal_lo 100 → 70`,
`nonce 5 → 6`, frame (cap/reserved/fields) fixed at `0`. -/
def goodRow : VmRowEnv where
  loc := fun v =>
    if v = sel.TRANSFER then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 70
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else if v = prmCol param.AMOUNT then 30
    else if v = prmCol param.DIRECTION then 1
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `goodRow` is a genuine transfer row. -/
theorem goodRow_isTransferRow : IsTransferRow goodRow := by
  unfold IsTransferRow goodRow
  constructor <;> norm_num [sel.TRANSFER, sel.NOOP, sbCol, saCol, prmCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.AMOUNT, param.DIRECTION]

/-- **NON-VACUITY (witness TRUE).** `goodRow` REALIZES the transfer intent: bal_lo moves
`100 → 70 = 100 + 30·(1 - 2·1)`, hi/frame fixed, nonce `5 → 6`. So the faithfulness biconditional's
intent side is inhabited (not `False`). -/
theorem goodRow_realizes_intent : TransferRowIntent goodRow := by
  unfold TransferRowIntent goodRow
  simp only [sbCol, saCol, prmCol, sel.TRANSFER, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.AMOUNT, param.DIRECTION]
  refine ⟨Or.inr (eqToModEq ?_), eqToModEq ?_, eqToModEq ?_, eqToModEq ?_, eqToModEq ?_,
    eqToModEq ?_, ?_⟩
  · rfl
  · norm_num
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    refine eqToModEq ?_
    -- both `state_after.field[i]` (col 79+i) and `state_before.field[i]` (col 57+i) miss every
    -- named column of `goodRow`, so both sides are the final `else 0`.
    have e1 : (76 + (3 + i) = 1) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have e6 : (76 + (3 + i) = 68) = False := by simp; omega
    have e7 : (76 + (3 + i) = 69) = False := by simp; omega
    have f1 : (54 + (3 + i) = 1) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    have f6 : (54 + (3 + i) = 68) = False := by simp; omega
    have f7 : (54 + (3 + i) = 69) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, e6, e7, f1, f2, f3, f4, f5, f6, f7, if_false]

/-- A FORGED transfer row: `goodRow` with the post-`bal_lo` tampered to `999` (a value not equal
to the intended `70`). -/
def badRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodRow.loc v
  nxt := goodRow.nxt
  pub := goodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badRow`'s post-`bal_lo` is NOT the
signed move, so the `gBalLo` gate REJECTS it — a concrete UNSAT, the anti-ghost end-to-end. -/
theorem badRow_rejected : ¬ (VmConstraint.gate gBalLo).holdsVm badRow false false := by
  -- `badRow` post-`bal_lo = 999`; intended move `= 100 + 30·(1 − 2·1) = 70`; both canonical in [0, p).
  apply transferVm_rejects_wrong_balance <;>
    simp only [badRow, goodRow, sbCol, saCol, prmCol, sel.TRANSFER, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, param.AMOUNT, param.DIRECTION] <;> norm_num

/-! ## §11.5 — THE FEE DEBIT (trust-surface hole #5 close).

The deployed sovereign turn debits `turn.fee` from the actor cell in executor PHASE 1, BEFORE
proving; the proof was then built over the PRE-fee balance and the verifier blindly UNDID the
debit (`pre_balance = post_fee_balance + turn.fee`) from the TRUSTED `turn.fee`. So the fee debit
was NOT a constraint in the proven transition — a ledgerless light client could not verify the fee
was correctly taken. For a sovereign turn the fee is debited from the SAME cell the rotated proof
covers, so the fee debit becomes a balance constraint IN that proof.

The MECHANISM (off the ROT_WIDTH flag-day — no new committed column, no pre-limb geometry change):
the fee rides in the after-block `RESERVED` state column (`saCol state.RESERVED`), which is dead
weight in the v1 layout (a pure `before == after` passthrough, NOT absorbed into the state
commitment, NOT welded into any rotated pre-limb). The balance-lo gate is AUGMENTED to subtract the
fee column as well as the transfer move (`new = old − transfer − fee`), so the proven FINAL_BAL —
the value `NEW_COMMIT` binds — is the POST-fee balance the executor's PHASE-1 debit produced. The
rotated leg then pins the fee column to a published fee PI (`rotateV3WithFeePin`,
`EffectVmEmitRotationV3`), so the verifier's published `turn.fee` is FORCED equal to the balance
the proof actually moved. A proof claiming a SMALLER fee than the balance moved, or a fee not
debited (`post ≠ pre − transfer − fee`), is UNSAT — no trusted reconstruction. -/

/-- The fee column: the after-block `RESERVED` state limb carries `turn.fee`. Dead weight in the
unfee'd transfer (passthrough, commitment-free), repurposed here as the published fee carrier. -/
def feeCol : Nat := saCol state.RESERVED

/-- Balance-lo debit/credit body WITH the fee debit: `new_bal_lo − old_bal_lo − amount + 2·dir·amount
+ fee`. On a fee'd transfer row this forces `new = old − amount·(1−2·dir) − fee` — the transfer move
AND the fee debit, both on the actor's lo limb. -/
def gBalLoFee : EmittedExpr :=
  .add gBalLo (.var feeCol)

/-- The fee'd per-row gates: the transfer gates with `gBalLo` swapped for `gBalLoFee` and the
RESERVED passthrough `gResPass` DROPPED (RESERVED now carries the fee, so it is no longer frozen). -/
def transferFeeRowGates : List VmConstraint :=
  [ .gate gBalLoFee, .gate gBalHi, .gate gDirBool, .gate gNonce, .gate gCapPass ] ++ gFieldPassAll

/-- **`transferFeeVmDescriptor`** — the fee'd TRANSFER descriptor: identical to `transferVmDescriptor`
except the balance-lo gate also debits the fee column and RESERVED is no longer frozen (it carries
the fee). The fee column gets a 30-bit range check (a fee near the field modulus would WRAP and forge
a negative debit — the field-soundness tooth). The rotated leg (`rotateV3WithFeePin`) pins the fee
column to the published fee PI. -/
def transferFeeVmDescriptor : EffectVmDescriptor :=
  { name := transferVmAirName ++ "-fee"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := transferFeeRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates sel.TRANSFER
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩, ⟨feeCol, 30⟩ ] }

/-- **`TransferFeeRowIntent env`** — the intended fee'd transfer move: the balance lo moves by the
signed transfer amount AND the fee is debited; everything else (hi limb, nonce tick, cap_root, the 8
fields) matches the unfee'd intent. RESERVED is NO LONGER frozen (it carries the fee). -/
def TransferFeeRowIntent (env : VmRowEnv) : Prop :=
  (env.loc (prmCol param.DIRECTION) ≡ 0 [ZMOD 2013265921]
    ∨ env.loc (prmCol param.DIRECTION) ≡ 1 [ZMOD 2013265921])
  ∧ env.loc (saCol state.BALANCE_LO)
      ≡ env.loc (sbCol state.BALANCE_LO)
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION))
        - env.loc feeCol [ZMOD 2013265921]
  ∧ env.loc (saCol state.BALANCE_HI) ≡ env.loc (sbCol state.BALANCE_HI) [ZMOD 2013265921]
  ∧ env.loc (saCol state.NONCE) ≡ env.loc (sbCol state.NONCE) + 1 [ZMOD 2013265921]
  ∧ env.loc (saCol state.CAP_ROOT) ≡ env.loc (sbCol state.CAP_ROOT) [ZMOD 2013265921]
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i))
      ≡ env.loc (sbCol (state.FIELD_BASE + i)) [ZMOD 2013265921])

/-- **`transferFeeVm_faithful` — the fee'd deliverable.** On a transfer row, the fee'd descriptor's
per-row gates hold IFF the fee'd transfer intent holds. So the concrete circuit enforces EXACTLY
`new = old − transfer − fee` — the fee debit is now a proven balance constraint. -/
theorem transferFeeVm_faithful (env : VmRowEnv) (hrow : IsTransferRow env) :
    (∀ c ∈ transferFeeRowGates, c.holdsVm env false false) ↔ TransferFeeRowIntent env := by
  obtain ⟨_hsT, hsN⟩ := hrow
  unfold transferFeeRowGates gFieldPassAll TransferFeeRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFee) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hDir := h (.gate gDirBool) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFee, gBalLo, gBalHi, gDirBool, gNonce, gCapPass,
      eSA, eSB, ePrm, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hDir hNon hCap
    rw [hsN] at hNon
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Int.modEq_zero_iff_dvd] at hDir
      rcases (pPrimeInt.dvd_mul.mp hDir) with hd | hd
      · exact Or.inl (by rw [Int.modEq_zero_iff_dvd]; exact hd)
      · refine Or.inr ?_
        rw [Int.modEq_iff_dvd]; obtain ⟨k, hk⟩ := hd; exact ⟨-k, by omega⟩
    · exact (gate_modEq_iff (by ring)).mp hLo
    · exact (gate_modEq_iff (by ring)).mp hHi
    · exact (gate_modEq_iff (by ring)).mp hNon
    · exact (gate_modEq_iff (by ring)).mp hCap
    · intro i hi
      have hfi := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at hfi
      exact (gate_modEq_iff (by ring)).mp hfi
  · rintro ⟨hDir, hLo, hHi, hNon, hCap, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFee, gBalLo, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hLo
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hHi
    · simp only [VmConstraint.holdsVm, gDirBool, ePrm, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]
      rcases hDir with hd | hd
      · rw [Int.modEq_zero_iff_dvd] at hd
        exact dvd_mul_of_dvd_left hd _
      · rw [Int.modEq_iff_dvd] at hd
        have hdd : (2013265921 : ℤ) ∣ (env.loc (prmCol param.DIRECTION) + -1) := by
          obtain ⟨k, hk⟩ := hd; exact ⟨-k, by omega⟩
        exact dvd_mul_of_dvd_right hdd _
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hsN]
      exact (gate_modEq_iff (by ring)).mpr hNon
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hCap
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr (hFld i hi)

/-- **Anti-ghost (fee tamper / the light-client tooth).** A fee'd transfer row whose post-`bal_lo`
is NOT `old − transfer − fee` — i.e. the published fee column claims a SMALLER fee than the balance
actually moved, or the fee was not debited — fails the `gBalLoFee` gate (UNSAT). This is the
in-circuit bite: a ledgerless verifier needs NO trusted `+ turn.fee` reconstruction. -/
theorem transferFeeVm_rejects_wrong_fee (env : VmRowEnv)
    (hcanonNew : 0 ≤ env.loc (saCol state.BALANCE_LO)
      ∧ env.loc (saCol state.BALANCE_LO) < 2013265921)
    (hcanonMove : 0 ≤ env.loc (sbCol state.BALANCE_LO)
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION))
        - env.loc feeCol
      ∧ env.loc (sbCol state.BALANCE_LO)
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION))
        - env.loc feeCol < 2013265921)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO)
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION))
        - env.loc feeCol) :
    ¬ (VmConstraint.gate gBalLoFee).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFee, gBalLo, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  exact not_modEq_zero_of_canon (by ring) hcanonNew hcanonMove hwrong

/-! ## §11.7 — THE AVAILABILITY WELD (DEPLOYED SOUNDNESS GAP #4 close, STAGED).

The bare `transferVmDescriptor` range-checks only the AFTER balance limbs; the debit gate `gBalLo`
admits the underflow-wrap forgery (`before=1, amount=1006632961, after=1006632961`: `after − before +
amount = p ≡ 0`, `after < 2^30`) that OVER-DEBITS ~10^9 while passing the after-range. Range-checking a
single 30-bit operand does NOT close it (`p ≈ 2·2^30`, so the wrap window `[p−2^30, p)` OVERLAPS
`[0, 2^30)`). The FIX — mirroring the vault's proven `borrow_compare` (`Dregg2.Deos.VaultSatDescriptor` /
`vault_weld.rs`, 15-bit limbs + borrow bits so no residual reaches `p`) — decomposes the debit into two
15-bit limbs with a borrow chain: on a DEBIT row (`direction = 1`) the gates force `before = after +
amount` over ℤ with a final NO-BORROW, so `before ≥ amount` (AVAILABILITY) is DERIVED, not assumed. The
credit direction (`direction = 0`) cannot over-mint (an overflowing credit destroys value), so the
borrow gates are `direction`-gated to bite only on the debit — the exact surface of the value forgery.

Witness columns live PAST the base width (`≥ EFFECT_VM_WIDTH = 188`), so they are DISTINCT from every
base-layout column; the widened descriptor + its registry row + VK ride the ONE big-bang regen (STAGED,
the vault status). -/

/-- The availability-weld witness-column base (past the base trace width — the vault/sysroots pattern). -/
def AVAIL_BASE : Nat := EFFECT_VM_WIDTH
/-- `before.bal_lo` low/high 15-bit limbs. -/
def cBEF0 : Nat := AVAIL_BASE
def cBEF1 : Nat := AVAIL_BASE + 1
/-- `after.bal_lo` low/high 15-bit limbs. -/
def cAFT0 : Nat := AVAIL_BASE + 2
def cAFT1 : Nat := AVAIL_BASE + 3
/-- `amount` low/high 15-bit limbs. -/
def cAM0 : Nat := AVAIL_BASE + 4
def cAM1 : Nat := AVAIL_BASE + 5
/-- The two borrow bits (`cBRW1` = the final borrow; `= 0` ⟺ `before ≥ amount`). -/
def cBRW0 : Nat := AVAIL_BASE + 6
def cBRW1 : Nat := AVAIL_BASE + 7
/-- The widened trace width. -/
def AVAIL_WIDTH : Nat := AVAIL_BASE + 8

/-- Operand assembly: `before.bal_lo = bef0 + 2^15·bef1` (pins the 30-bit operand to its 15-bit limbs). -/
def gAsmBefore : EmittedExpr :=
  eSub (eSB state.BALANCE_LO) (.add (.var cBEF0) (.mul (.const 32768) (.var cBEF1)))
/-- Operand assembly: `after.bal_lo = aft0 + 2^15·aft1`. -/
def gAsmAfter : EmittedExpr :=
  eSub (eSA state.BALANCE_LO) (.add (.var cAFT0) (.mul (.const 32768) (.var cAFT1)))
/-- Operand assembly: `amount = am0 + 2^15·am1` (the previously-UNRANGED amount, now decomposed). -/
def gAsmAmount : EmittedExpr :=
  eSub (ePrm param.AMOUNT) (.add (.var cAM0) (.mul (.const 32768) (.var cAM1)))
/-- Borrow-bit booleanity: `bb0·(bb0 − 1)`. -/
def gBrw0Bool : EmittedExpr := .mul (.var cBRW0) (.add (.var cBRW0) (.const (-1)))
/-- Borrow-bit booleanity: `bb1·(bb1 − 1)`. -/
def gBrw1Bool : EmittedExpr := .mul (.var cBRW1) (.add (.var cBRW1) (.const (-1)))
/-- Debit borrow, limb 0 (`direction`-gated): `dir·(bef0 − am0 + bb0·2^15 − aft0)`. On a debit row this
forces `bef0 − am0 = aft0 − bb0·2^15` — the low-limb borrow subtraction (mirror of `vault_weld`'s
`borrow_compare_gates`, with `Q=before, P=amount, W=after`). -/
def gBorrow0 : EmittedExpr :=
  .mul (ePrm param.DIRECTION)
    (eSub (.add (eSub (.var cBEF0) (.var cAM0)) (.mul (.const 32768) (.var cBRW0))) (.var cAFT0))
/-- Debit borrow, limb 1 (`direction`-gated): `dir·(bef1 − am1 − bb0 + bb1·2^15 − aft1)`. -/
def gBorrow1 : EmittedExpr :=
  .mul (ePrm param.DIRECTION)
    (eSub (.add (eSub (eSub (.var cBEF1) (.var cAM1)) (.var cBRW0)) (.mul (.const 32768) (.var cBRW1)))
      (.var cAFT1))
/-- The NO-FINAL-BORROW gate (`direction`-gated): `dir·bb1`. On a debit row `bb1 = 0`, i.e. `before ≥
amount` — AVAILABILITY, enforced in-circuit. -/
def gNoBorrow : EmittedExpr := .mul (ePrm param.DIRECTION) (.var cBRW1)

/-- The availability-weld gates (assembly + borrow chain). Appended to the transfer descriptor. -/
def transferAvailGates : List VmConstraint :=
  [ .gate gAsmBefore, .gate gAsmAfter, .gate gAsmAmount
  , .gate gBrw0Bool, .gate gBrw1Bool
  , .gate gBorrow0, .gate gBorrow1, .gate gNoBorrow ]

/-- The availability-weld range checks: the operand + amount 15-bit limbs (bounds every operand to
`[0, 2^30) ⊂ [0, p)` and, crucially, RANGES `amount`, closing the unranged-amount hole). -/
def transferAvailRanges : List VmRange :=
  [ ⟨cBEF0, 15⟩, ⟨cBEF1, 15⟩, ⟨cAFT0, 15⟩, ⟨cAFT1, 15⟩, ⟨cAM0, 15⟩, ⟨cAM1, 15⟩ ]

/-- **`transferVmDescriptorAvail`** — the HARDENED transfer descriptor: the bare `transferVmDescriptor`
PLUS the availability-weld gates and the amount/operand limb range checks, trace widened to carry the
witness columns. Closes DEPLOYED SOUNDNESS GAP #4 (in-circuit availability; no `hcanonMove`). STAGED. -/
def transferVmDescriptorAvail : EffectVmDescriptor :=
  { transferVmDescriptor with
    name        := transferVmAirName ++ "-avail"
    traceWidth  := AVAIL_WIDTH
    constraints := transferVmDescriptor.constraints ++ transferAvailGates
    ranges      := transferVmDescriptor.ranges ++ transferAvailRanges }

/-- A weld gate is a member of the hardened descriptor's constraints. -/
theorem availGate_mem (g : VmConstraint) (hg : g ∈ transferAvailGates) :
    g ∈ transferVmDescriptorAvail.constraints :=
  List.mem_append_right _ hg

/-- A weld range is a member of the hardened descriptor's ranges. -/
theorem availRange_mem (r : VmRange) (hr : r ∈ transferAvailRanges) :
    r ∈ transferVmDescriptorAvail.ranges :=
  List.mem_append_right _ hr

/-- A residual congruent to `0 mod p` and confined to `(−p, p)` by the 15-bit limb/borrow range checks
is EXACTLY `0` over ℤ (the vault's `modEqZeroBounded` — the soundness payoff of 15-bit limbs). -/
private theorem availBounded {R : ℤ} (h : R ≡ 0 [ZMOD 2013265921])
    (hlo : -2013265921 < R) (hhi : R < 2013265921) : R = 0 := by
  rw [Int.modEq_zero_iff_dvd] at h; obtain ⟨k, hk⟩ := h; omega

/-- Two CANONICAL (`[0, p)`) integers congruent mod `p` are EQUAL (the deployed range-check lift). -/
private theorem availCanonEq {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha0 : 0 ≤ a) (hap : a < 2013265921) (hb0 : 0 ≤ b) (hbp : b < 2013265921) : a = b := by
  unfold Int.ModEq at h; rwa [Int.emod_eq_of_lt ha0 hap, Int.emod_eq_of_lt hb0 hbp] at h

/-- **SOUNDNESS — AVAILABILITY DERIVED IN-CIRCUIT (GAP #4 CLOSED).** On a DEBIT row (`direction = 1`) a
trace satisfying the hardened descriptor FORCES `amount ≤ before.bal_lo` AND the exact ℤ move `after =
before − amount` — with NO `hcanonMove` assumption. The only hypothesis is the DEPLOYED canonicality
invariant `0 ≤ loc c < p` (each column a canonical field element — the SAME fact
`transferVm_rejects_wrong_balance` uses, NOT availability laundered in). The borrow chain + 15-bit limb
range checks make the subtraction exact over ℤ, so the underflow wrap is STRUCTURALLY impossible. -/
theorem transferAvail_derives_availability (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hcanon : ∀ c, 0 ≤ env.loc c ∧ env.loc c < 2013265921)
    (hsat : satisfiedVm hash transferVmDescriptorAvail env true false)
    (hdir : env.loc (prmCol param.DIRECTION) = 1) :
    env.loc (prmCol param.AMOUNT) ≤ env.loc (sbCol state.BALANCE_LO)
    ∧ env.loc (saCol state.BALANCE_LO)
        = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.AMOUNT) := by
  obtain ⟨hcs, _hsites, hrs⟩ := hsat
  -- range facts (each limb in [0, 2^15))
  have hb0 := hrs _ (availRange_mem ⟨cBEF0, 15⟩ (by simp [transferAvailRanges]))
  have hb1 := hrs _ (availRange_mem ⟨cBEF1, 15⟩ (by simp [transferAvailRanges]))
  have ha0 := hrs _ (availRange_mem ⟨cAFT0, 15⟩ (by simp [transferAvailRanges]))
  have ha1 := hrs _ (availRange_mem ⟨cAFT1, 15⟩ (by simp [transferAvailRanges]))
  have hm0 := hrs _ (availRange_mem ⟨cAM0, 15⟩ (by simp [transferAvailRanges]))
  have hm1 := hrs _ (availRange_mem ⟨cAM1, 15⟩ (by simp [transferAvailRanges]))
  simp only [VmRange.holds] at hb0 hb1 ha0 ha1 hm0 hm1
  norm_num at hb0 hb1 ha0 ha1 hm0 hm1
  -- gate facts (bodies vanish mod p on the active row)
  have gAsmB := hcs _ (availGate_mem (.gate gAsmBefore) (by simp [transferAvailGates]))
  have gAsmA := hcs _ (availGate_mem (.gate gAsmAfter) (by simp [transferAvailGates]))
  have gAsmM := hcs _ (availGate_mem (.gate gAsmAmount) (by simp [transferAvailGates]))
  have gB0 := hcs _ (availGate_mem (.gate gBrw0Bool) (by simp [transferAvailGates]))
  have gB1 := hcs _ (availGate_mem (.gate gBrw1Bool) (by simp [transferAvailGates]))
  have gBor0 := hcs _ (availGate_mem (.gate gBorrow0) (by simp [transferAvailGates]))
  have gBor1 := hcs _ (availGate_mem (.gate gBorrow1) (by simp [transferAvailGates]))
  have gNoB := hcs _ (availGate_mem (.gate gNoBorrow) (by simp [transferAvailGates]))
  simp only [holdsVm_gate_false, gAsmBefore, gAsmAfter, gAsmAmount, gBrw0Bool, gBrw1Bool,
    gBorrow0, gBorrow1, gNoBorrow, eSA, eSB, ePrm, eSub, EmittedExpr.eval] at gAsmB gAsmA gAsmM gB0 gB1 gBor0 gBor1 gNoB
  rw [hdir, one_mul] at gBor0 gBor1 gNoB
  -- borrow bits are boolean (mod-p booleanity + canonicality + p prime)
  have brw0Bool : 0 ≤ env.loc cBRW0 ∧ env.loc cBRW0 ≤ 1 := by
    rw [Int.modEq_zero_iff_dvd] at gB0
    obtain ⟨z0, zp⟩ := hcanon cBRW0
    rcases pPrimeInt.dvd_mul.mp gB0 with hd | hd
    · obtain ⟨k, hk⟩ := hd; omega
    · obtain ⟨k, hk⟩ := hd; omega
  have brw1Bool : 0 ≤ env.loc cBRW1 ∧ env.loc cBRW1 ≤ 1 := by
    rw [Int.modEq_zero_iff_dvd] at gB1
    obtain ⟨z0, zp⟩ := hcanon cBRW1
    rcases pPrimeInt.dvd_mul.mp gB1 with hd | hd
    · obtain ⟨k, hk⟩ := hd; omega
    · obtain ⟨k, hk⟩ := hd; omega
  -- operand assemblies lift to exact ℤ (canonical operand, limb sum < 2^30 < p)
  have eBef : env.loc (sbCol state.BALANCE_LO) = env.loc cBEF0 + 32768 * env.loc cBEF1 :=
    availCanonEq ((gate_modEq_iff (by ring)).mp gAsmB) (hcanon _).1 (hcanon _).2 (by omega) (by omega)
  have eAft : env.loc (saCol state.BALANCE_LO) = env.loc cAFT0 + 32768 * env.loc cAFT1 :=
    availCanonEq ((gate_modEq_iff (by ring)).mp gAsmA) (hcanon _).1 (hcanon _).2 (by omega) (by omega)
  have eAmt : env.loc (prmCol param.AMOUNT) = env.loc cAM0 + 32768 * env.loc cAM1 :=
    availCanonEq ((gate_modEq_iff (by ring)).mp gAsmM) (hcanon _).1 (hcanon _).2 (by omega) (by omega)
  -- the borrow subtraction is exact over ℤ (each residual confined to (−p, p) by the 15-bit ranges)
  have e0 : env.loc cBEF0 + -1 * env.loc cAM0 + 32768 * env.loc cBRW0 + -1 * env.loc cAFT0 = 0 :=
    availBounded gBor0 (by omega) (by omega)
  have e1 : env.loc cBEF1 + -1 * env.loc cAM1 + -1 * env.loc cBRW0
      + 32768 * env.loc cBRW1 + -1 * env.loc cAFT1 = 0 :=
    availBounded gBor1 (by omega) (by omega)
  have eBB : env.loc cBRW1 = 0 := availBounded gNoB (by omega) (by omega)
  -- availability + exact move: purely linear now (no residual congruences left)
  constructor
  · omega
  · omega

/-- **THE FORGERY IS UNSAT (GAP #4 witness).** The audit's over-debit forgery witness (`before=1,
amount=1006632961, after=1006632961, direction=1`) CANNOT satisfy the hardened descriptor: its debit
availability `amount ≤ before` (`1006632961 ≤ 1`) is false, so the borrow chain has no witness. The
underflow-wrap value forgery is closed in-circuit. -/
theorem transferAvail_forgery_unsat (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hcanon : ∀ c, 0 ≤ env.loc c ∧ env.loc c < 2013265921)
    (hsat : satisfiedVm hash transferVmDescriptorAvail env true false)
    (hbefore : env.loc (sbCol state.BALANCE_LO) = 1)
    (hamount : env.loc (prmCol param.AMOUNT) = 1006632961)
    (hdir : env.loc (prmCol param.DIRECTION) = 1) : False := by
  have h := (transferAvail_derives_availability hash env hcanon hsat hdir).1
  rw [hbefore, hamount] at h; omega

/-! ### LIVENESS: an honest debit (`goodRow` + its limb witnesses) satisfies the weld. -/

/-- `goodRow` (debit of 30 from bal_lo 100 → 70) extended with the availability-weld witness columns:
`before = 100` limbs `(100, 0)`, `after = 70` limbs `(70, 0)`, `amount = 30` limbs `(30, 0)`, no
borrows. -/
def goodAvailRow : VmRowEnv where
  loc := fun v =>
    if v = cBEF0 then 100 else if v = cAFT0 then 70 else if v = cAM0 then 30 else goodRow.loc v
  nxt := goodRow.nxt
  pub := goodRow.pub

/-- **LIVENESS.** Every availability-weld gate holds on the honest `goodAvailRow` — no valid transfer is
rejected by the new gates (the borrow chain closes with zero borrows: `100 − 30 = 70`). -/
theorem goodAvailRow_gates_hold (c : VmConstraint) (hc : c ∈ transferAvailGates) :
    c.holdsVm goodAvailRow false false := by
  have hb : ∃ b, c = .gate b ∧ b.eval goodAvailRow.loc = 0 := by
    fin_cases hc <;> exact ⟨_, rfl, by decide⟩
  obtain ⟨b, rfl, hval⟩ := hb
  rw [holdsVm_gate_false, hval]

/-- **LIVENESS (ranges).** The honest limb witnesses satisfy the 15-bit range checks. -/
theorem goodAvailRow_ranges_hold (r : VmRange) (hr : r ∈ transferAvailRanges) :
    r.holds goodAvailRow := by
  fin_cases hr <;> exact ⟨by decide, by decide⟩

/-! ## §12 — Axiom-hygiene pins (the honesty tripwire). -/

#guard transferVmDescriptor.constraints.length == 14 + 14 + 4 + 3 + 1  -- gates+transitions+4first+3last+selectorGate
#guard transferVmDescriptor.hashSites.length == 4
#guard transferVmDescriptor.ranges.length == 2
#guard transferVmDescriptor.traceWidth == 188

-- The fee'd descriptor: one fewer per-row gate (RESERVED passthrough dropped), one more range check.
#guard transferFeeVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard transferFeeVmDescriptor.ranges.length == 3
#guard transferFeeVmDescriptor.traceWidth == 188
#assert_axioms transferFeeVm_faithful
#assert_axioms transferFeeVm_rejects_wrong_fee

-- The availability weld (GAP #4): the hardened descriptor adds 8 gates + 6 ranges and 8 witness cols.
#guard transferVmDescriptorAvail.constraints.length == (14 + 14 + 4 + 3 + 1) + 8
#guard transferVmDescriptorAvail.ranges.length == 2 + 6
#guard transferVmDescriptorAvail.traceWidth == 196
-- LIVENESS witness (kernel-evaluated): every weld gate body is 0 on the honest debit row.
#guard transferAvailGates.all (fun c => match c with | .gate b => b.eval goodAvailRow.loc == 0 | _ => true)
#assert_axioms transferAvail_derives_availability
#assert_axioms transferAvail_forgery_unsat
#assert_axioms goodAvailRow_gates_hold
#assert_axioms goodAvailRow_ranges_hold

#assert_axioms transferRowGates_holds_iff
#assert_axioms transferVm_faithful
#assert_axioms transferVm_rejects_wrong_output
#assert_axioms transferVm_rejects_wrong_balance
#assert_axioms transferVm_rejects_wrong_nonce
#assert_axioms transferHash_binds
#assert_axioms boundaryFirst_pins
#assert_axioms boundaryLast_pins
#assert_axioms transferVmDescriptor_pins_intent
#assert_axioms goodRow_realizes_intent
#assert_axioms badRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitTransfer
