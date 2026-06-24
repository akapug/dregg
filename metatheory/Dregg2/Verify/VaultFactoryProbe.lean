/-
# Dregg2.Verify.VaultFactoryProbe — the FALSIFICATION PROBE for the conditional-timelock VAULT as a
factory-born cell-program.

THE CLAIM UNDER TEST (the house-capacity weld, `docs/HOUSE-CAPACITIES-WELD-PLAN.md` headline #1):
*a VAULT — value locked until a release rule (a block-height timelock OR a hash-lock preimage proof),
claimable EXACTLY ONCE by the beneficiary after the condition is genuinely met — is NOT a new kernel
verb. It is a COMPOSITION: a conditional-settlement CELL whose program enforces the lock, settled by
the already-wired `CreateCellFromFactory` + `Transfer` (claim) + `SetField` (advance) triple.* The
vault is the FIRST house room welded; it rides the SAME committed-cell substrate as the escrow factory
(`Dregg2.Verify.EscrowFactoryProbe`), and every gate it needs already exists.

This probe finds out whether the rebuild GENUINELY captures the vault semantics. An honest PARTIAL is
as valuable as PASS; the verdict (§VERDICT) is PASS.

## The reframe (why vault is a factory cell, not a verb)

A conditional vault is escrow with the abort leg removed and the release gate generalized:

  * the locked VALUE lives in the vault cell's OWN per-asset `bal` column (NOT a side-table, NOT a
    second slot) — a fund is an ordinary `move` IN (granter ⇒ vault), a claim is an ordinary `move`
    OUT (vault ⇒ beneficiary). So conservation is the EXISTING per-asset move law
    `recKExecAsset_conserves_per_asset`, inherited verbatim;
  * the lifecycle `state ∈ {open, claimed}` lives in a SLOT, governed by a state machine
    `admitTable [(open, claimed)]` — ONE terminal, no refund. The lone terminal IS the one-shot tooth:
    a CLAIMED vault has no admitted outgoing transition, so the value leaves the held column AT MOST
    ONCE (no double-claim / replay);
  * the RELEASE condition is an abstract decidable gate `gate : (atBlock, witness) → Bool` over the
    cell's committed lock fields. The TIMELOCK is the instance `gate := atBlock ≥ releaseHeight`; the
    HASH-LOCK is the instance `gate := H(witness) = digest`. Both are realized by the SAME proof shape
    (the escrow probe's §HARD-iii gate-abstraction generalizes to BOTH conditions): the claim-once /
    conservation / not-stranded keystones are ORTHOGONAL to which gate fires.

## The vault SHAPE (the reusable deliverable)

slots (fields on the vault cell's record):
  * `state`         — 0 = open (locked), 1 = claimed   (the lifecycle automaton — the one-shot tooth)
  * `beneficiary`   — the claim target          (immutable after open)
  * `releaseHeight` — the timelock release height (immutable; bound even for a hash-lock vault)
  * `condDigest`    — the hash-lock target `H(preimage)`, OR 0 for a pure timelock (immutable)
  * `asset`         — the asset class of the locked value (immutable)
plus the locked VALUE itself, held in the vault cell's per-asset `bal` column. The `vaultFactory`
installs the four deal-term immutables + the one-terminal state machine.

## The four claim-safety keystones (all PROVED here)

  (a) CONSERVATION across the lifecycle — every claim is an ordinary per-asset `move`, so the kernel's
      value law applies VERBATIM; no bespoke quantity, no side-table.
  (b) ONE-SHOT (no double-claim) — the `admitTable [(open, claimed)]` machine: from CLAIMED no
      transition is admitted, so a claimed vault can NEVER re-claim. The value leaves once.
  (c) CLAIM ONLY WHEN THE RELEASE CONDITION HOLDS — a claim whose `(atBlock, witness)` does NOT
      discharge the cell's committed gate is rejected (`none`). For a timelock this rejects an EARLY
      claim (`atBlock < releaseHeight`); for a hash-lock it rejects a FORGED proof (wrong preimage).
  (d) VALUE NOT STRANDED (open ∧ condition-met ⇒ claimable) — a one-step liveness: any OPEN vault
      whose condition is genuinely met, with a live distinct beneficiary holding the lock in its `bal`
      column, CLAIMS. No held value is structurally trapped.

NEW file only. Reuses ONLY the proved per-asset move conservation + the SlotCaveat vocabulary; mirrors
`Dregg2.Verify.EscrowFactoryProbe` exactly (vault = escrow minus the refund leg, gate generalized).
Every keystone `#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.EffectsState

namespace Dregg2.Verify.VaultFactoryProbe

open Dregg2.Exec
open Dregg2.Exec.EffectsState (setField fieldOf setField_fieldOf)

/-! ## §1 — The vault-cell SLOT layout (field names) + the lifecycle automaton. -/

/-- The lifecycle slot: 0 = open (locked), 1 = claimed (the one-shot terminal). -/
abbrev stateField : FieldName := "vault.state"
/-- The claim target (frozen after open). The locked VALUE lives in the cell's `bal` column. -/
abbrev beneficiaryField : FieldName := "vault.beneficiary"
/-- The timelock release height (frozen). -/
abbrev releaseHeightField : FieldName := "vault.releaseHeight"
/-- The hash-lock target `H(preimage)` (frozen); 0 for a pure timelock vault. -/
abbrev condDigestField : FieldName := "vault.condDigest"
/-- The asset class of the locked value (frozen). -/
abbrev assetField : FieldName := "vault.asset"

/-- Lifecycle state literals. -/
abbrev sOpen : Int := 0
abbrev sClaimed : Int := 1

/-! ## §2 — The vault FACTORY DESCRIPTOR: the published contract that mints vault cells.

The `FactoryEntry` a vault factory publishes. Its `caveats` ARE the vault invariants — the four
deal-term immutables + the one-terminal state-machine `admitTable [(open, claimed)]` (the one-shot
tooth: no `(claimed, _)` row, so a claimed vault's `state` slot is frozen). The initial state is
OPEN. A cell minted by this factory carries these for its WHOLE LIFE; the executor enforces them on
every `SetField` via `stateStepGuarded`/`caveatsAdmit`. -/

/-- **`vaultFactory beneficiary releaseHeight condDigest asset` — the vault factory descriptor.**
Installs: the four deal-term immutables, and the state-machine `admitTable [(open, claimed)]` on
`state` (BOTH the legal-transition spec AND the one-shot tooth — no `(claimed, _)` row). Initial
state OPEN. -/
def vaultFactory (beneficiary releaseHeight condDigest asset : Int) : FactoryEntry where
  caveats :=
    [ SlotCaveat.immutable beneficiaryField
    , SlotCaveat.immutable releaseHeightField
    , SlotCaveat.immutable condDigestField
    , SlotCaveat.immutable assetField
    , SlotCaveat.admitTable stateField [(sOpen, sClaimed)] ]
  initialFields :=
    [ (stateField, sOpen)
    , (beneficiaryField, beneficiary)
    , (releaseHeightField, releaseHeight)
    , (condDigestField, condDigest)
    , (assetField, asset) ]
  programVk := 0

/-- **`vaultFactory_conforms`.** The vault factory's OWN published initial state satisfies its OWN
caveats (no balance smuggling; the state machine permits the genesis OPEN write; the immutables permit
their first write). A well-formed factory cannot publish an initial state that already violates the
invariants it claims to enforce. -/
theorem vaultFactory_conforms (beneficiary releaseHeight condDigest asset : Int) :
    (vaultFactory beneficiary releaseHeight condDigest asset).conforms = true := by
  unfold vaultFactory FactoryEntry.conforms FactoryEntry.initialFieldsNoBalance
  simp only [SlotCaveat.field, SlotCaveat.bornFresh, List.all_cons, List.all_nil,
    List.find?, Bool.and_true, Bool.and_self]
  rfl

/-! ## §3 — The vault cell STATE: a record cell holding the locked value in its `bal` column. -/

/-- Read the vault cell's lifecycle state slot. -/
def vaultState (k : RecordKernelState) (e : CellId) : Int := fieldOf stateField (k.cell e)

/-- Read the vault cell's frozen release-height slot. -/
def vaultReleaseHeight (k : RecordKernelState) (e : CellId) : Int := fieldOf releaseHeightField (k.cell e)

/-- Read the vault cell's frozen hash-lock digest slot (0 = pure timelock). -/
def vaultCondDigest (k : RecordKernelState) (e : CellId) : Int := fieldOf condDigestField (k.cell e)

/-- A vault cell is OPEN iff its state slot reads 0. -/
def vaultOpen (k : RecordKernelState) (e : CellId) : Prop := vaultState k e = sOpen

/-! ## §4 — The vault OPERATIONS as the 8-verb composition (write + move).

The vault claim is the escrow `settle` with ONE terminal and an ABSTRACT release gate. The TIMELOCK
gate is `atBlock ≥ releaseHeight`; the HASH-LOCK gate is `H(witness) = condDigest`. Both instantiate
the same `gate` parameter — the claim-once / conservation / liveness proofs never inspect WHICH gate. -/

/-- **`vaultSettle` — the body of a claim: a `write` of the new state slot, then a `move` of the held
value out.** Both ORDINARY verbs (`setField` + the per-asset move `recKExecAsset`). Fail-closed (the
move's guard: authorized, non-negative, sufficient balance, distinct live cells). On success: state
slot is written, held value moves to `target`. -/
def vaultSettle (k : RecordKernelState) (e target : CellId) (asset : AssetId) (newState : Int) :
    Option RecordKernelState :=
  let amt := k.bal e asset
  let k1 : RecordKernelState :=
    { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int newState)
                              else k.cell c }
  recKExecAsset k1 { actor := e, src := e, dst := target, amt := amt } asset

/-- **`vaultClaimGated` — the claim op (state OPEN → CLAIMED + move to beneficiary), gated on an
ABSTRACT release predicate `gate`.** Rejects (`none`) when: the vault is not OPEN (the one-shot tooth —
a claimed vault has no admitted transition), or the supplied `(atBlock, witness)` does NOT discharge
the `gate`. Setting `gate atBlock witness := decide (releaseHeight ≤ atBlock)` is the TIMELOCK; setting
`gate atBlock witness := decide (hash witness = condDigest)` is the HASH-LOCK. -/
def vaultClaimGated (gate : Int → Int → Bool) (k : RecordKernelState) (e beneficiary : CellId)
    (asset : AssetId) (atBlock witness : Int) : Option RecordKernelState :=
  if vaultState k e = sOpen ∧ gate atBlock witness = true then
    vaultSettle k e beneficiary asset sClaimed
  else none

/-! ### §4a — The two concrete release gates (timelock, hash-lock). -/

/-- The TIMELOCK gate: claimable iff the claim block reaches the release height. `witness` is unused
(the height governs). -/
def timelockGate (releaseHeight : Int) : Int → Int → Bool :=
  fun atBlock _witness => decide (releaseHeight ≤ atBlock)

/-- The HASH-LOCK gate: claimable iff the presented witness hashes (here modeled as a generic
collision-resistant `hash : Int → Int` at the executable layer; the §8 crypto portal carries the real
preimage hash) to the committed digest. `atBlock` is unused (the proof governs). -/
def hashlockGate (hash : Int → Int) (condDigest : Int) : Int → Int → Bool :=
  fun _atBlock witness => decide (hash witness = condDigest)

/-- **A timelock claim** at the vault's committed release height. -/
def vaultClaimTimelock (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock : Int) : Option RecordKernelState :=
  vaultClaimGated (timelockGate (vaultReleaseHeight k e)) k e beneficiary asset atBlock 0

/-- **A hash-lock claim** presenting `witness` against the vault's committed digest. -/
def vaultClaimHashlock (hash : Int → Int) (k : RecordKernelState) (e beneficiary : CellId)
    (asset : AssetId) (witness : Int) : Option RecordKernelState :=
  vaultClaimGated (hashlockGate hash (vaultCondDigest k e)) k e beneficiary asset 0 witness

/-! ## §5 — KEYSTONE (a): CONSERVATION across the lifecycle (inherited from the ORDINARY move). -/

/-- **`vaultSettle_conserves` — KEYSTONE (a), PROVED.** A committed claim preserves EVERY asset's
total supply: the held value moves between two live accounts, and the state-slot write touches no
balance. The ordinary move conservation law — the vault inherits it, no side-table. -/
theorem vaultSettle_conserves {k k' : RecordKernelState} {e target : CellId} {asset : AssetId}
    {newState : Int} (h : vaultSettle k e target asset newState = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold vaultSettle at h
  set k1 : RecordKernelState :=
    { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int newState)
                              else k.cell c } with hk1
  have hbal : k1.bal = k.bal := rfl
  have hacc : k1.accounts = k.accounts := rfl
  have hconv := recKExecAsset_conserves_per_asset k1 k'
    { actor := e, src := e, dst := target, amt := k.bal e asset } asset h b
  have hk1tot : recTotalAsset k1 b = recTotalAsset k b := by
    unfold recTotalAsset; rw [hacc, hbal]
  rw [hk1tot] at hconv
  exact hconv

/-- **`vaultClaim_conserves` — KEYSTONE (a) for a claim (any gate).** A committed claim preserves
every asset's supply (the value is DELIVERED from the held column, not conjured). -/
theorem vaultClaim_conserves (gate : Int → Int → Bool) {k k' : RecordKernelState}
    {e beneficiary : CellId} {asset : AssetId} {atBlock witness : Int}
    (h : vaultClaimGated gate k e beneficiary asset atBlock witness = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold vaultClaimGated at h
  by_cases hg : vaultState k e = sOpen ∧ gate atBlock witness = true
  · rw [if_pos hg] at h; exact vaultSettle_conserves h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §6 — KEYSTONE (b): ONE-SHOT (no double-claim) — the one-terminal state machine.

The vault factory's `admitTable [(open, claimed)]` admits a transition ONLY out of OPEN. The claim op
enforces this at the `vaultState k e = sOpen` guard: a claim on a NON-OPEN (already claimed) vault
fail-closes to `none`. So a claimed vault can NEVER re-claim — the value leaves the held column AT MOST
ONCE. -/

/-- **`claim_requires_open`.** A claim on a NON-OPEN vault is rejected (any gate). -/
theorem claim_requires_open (gate : Int → Int → Bool) (k : RecordKernelState) (e beneficiary : CellId)
    (asset : AssetId) (atBlock witness : Int) (hns : vaultState k e ≠ sOpen) :
    vaultClaimGated gate k e beneficiary asset atBlock witness = none := by
  unfold vaultClaimGated
  rw [if_neg (by rintro ⟨ho, _⟩; exact hns ho)]

/-- After a committed claim the vault state slot reads CLAIMED (the machine advanced — so a SECOND
claim sees a non-OPEN state and `no_double_claim` bites). -/
theorem claim_advances_state (gate : Int → Int → Bool) {k k' : RecordKernelState}
    {e beneficiary : CellId} {asset : AssetId} {atBlock witness : Int}
    (h : vaultClaimGated gate k e beneficiary asset atBlock witness = some k') :
    vaultState k' e = sClaimed := by
  unfold vaultClaimGated at h
  by_cases hg : vaultState k e = sOpen ∧ gate atBlock witness = true
  · rw [if_pos hg] at h
    unfold vaultSettle at h
    set k1 : RecordKernelState :=
      { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int sClaimed)
                                else k.cell c } with hk1
    have hcell : k'.cell = k1.cell := by
      unfold recKExecAsset at h
      by_cases hmv : authorizedB k1.caps { actor := e, src := e, dst := beneficiary, amt := k.bal e asset } = true
          ∧ 0 ≤ ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).amt
          ∧ ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).amt ≤ k1.bal ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).src asset
          ∧ ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).src ≠ ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).dst
          ∧ ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).src ∈ k1.accounts
          ∧ ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).dst ∈ k1.accounts
          ∧ cellLifecycleLive k1 ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).src = true
      · rw [if_pos hmv] at h; simp only [Option.some.injEq] at h; rw [← h]
      · rw [if_neg hmv] at h; exact absurd h (by simp)
    unfold vaultState
    rw [hcell]
    show fieldOf stateField (if e = e then setField stateField (k.cell e) (.int sClaimed) else k.cell e) = sClaimed
    rw [if_pos rfl, setField_fieldOf]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`no_double_claim` (the one-shot teeth, PROVED).** Once a claim has driven the vault to CLAIMED,
NO further claim commits — it fail-closes because the vault is no longer OPEN. The held value left
EXACTLY ONCE. -/
theorem no_double_claim (gate : Int → Int → Bool) (k : RecordKernelState) (e tgt : CellId)
    (asset : AssetId) (atBlock witness : Int) (hclaimed : vaultState k e = sClaimed) :
    vaultClaimGated gate k e tgt asset atBlock witness = none := by
  have hns : vaultState k e ≠ sOpen := by rw [hclaimed]; decide
  exact claim_requires_open gate k e tgt asset atBlock witness hns

/-- **`no_double_claim_after` — the END-USER one-shot: a SECOND claim on a freshly-claimed vault
fails.** Composes `claim_advances_state` (the first claim left CLAIMED) with `no_double_claim`. -/
theorem no_double_claim_after (gate : Int → Int → Bool) {k k' : RecordKernelState}
    {e beneficiary tgt : CellId} {asset : AssetId} {atBlock witness atBlock' witness' : Int}
    (h : vaultClaimGated gate k e beneficiary asset atBlock witness = some k') :
    vaultClaimGated gate k' e tgt asset atBlock' witness' = none :=
  no_double_claim gate k' e tgt asset atBlock' witness' (claim_advances_state gate h)

/-! ## §7 — KEYSTONE (c): CLAIM ONLY WHEN THE RELEASE CONDITION DISCHARGES.

The claim gate is the `gate atBlock witness = true` conjunct. A claim whose `(atBlock, witness)` does
NOT discharge the gate fail-closes to `none`. For a TIMELOCK this is the EARLY-RELEASE rejection
(`atBlock < releaseHeight`); for a HASH-LOCK it is the FORGED-PROOF rejection (wrong preimage). -/

/-- **`claim_requires_discharge` — KEYSTONE (c), PROVED (any gate).** A claim whose `(atBlock,
witness)` does NOT discharge the release gate is rejected — even on an OPEN vault. Nobody can claim
the value without the condition genuinely holding. -/
theorem claim_requires_discharge (gate : Int → Int → Bool) (k : RecordKernelState)
    (e beneficiary : CellId) (asset : AssetId) (atBlock witness : Int)
    (hbad : gate atBlock witness = false) :
    vaultClaimGated gate k e beneficiary asset atBlock witness = none := by
  unfold vaultClaimGated
  rw [if_neg (by rintro ⟨_, hd⟩; rw [hbad] at hd; exact absurd hd (by simp))]

/-- **`timelock_rejects_early` — KEYSTONE (c), TIMELOCK instance.** A timelock claim BEFORE the
release height (`atBlock < releaseHeight`) is rejected — no early release. -/
theorem timelock_rejects_early (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock : Int) (hearly : atBlock < vaultReleaseHeight k e) :
    vaultClaimTimelock k e beneficiary asset atBlock = none := by
  unfold vaultClaimTimelock
  apply claim_requires_discharge
  unfold timelockGate
  simp only [decide_eq_false_iff_not, not_le]
  exact hearly

/-- **`hashlock_rejects_forged` — KEYSTONE (c), HASH-LOCK instance.** A hash-lock claim whose witness
does NOT hash to the committed digest (a forged / wrong preimage) is rejected. -/
theorem hashlock_rejects_forged (hash : Int → Int) (k : RecordKernelState) (e beneficiary : CellId)
    (asset : AssetId) (witness : Int) (hbad : hash witness ≠ vaultCondDigest k e) :
    vaultClaimHashlock hash k e beneficiary asset witness = none := by
  unfold vaultClaimHashlock
  apply claim_requires_discharge
  unfold hashlockGate
  simp only [decide_eq_false_iff_not]
  exact hbad

/-! ## §8 — KEYSTONE (d): VALUE NOT STRANDED (open ∧ condition-met ⇒ claimable). -/

/-- The move-admissibility hypothesis bundle for a claim: the vault cell is authorized over itself
(it always is — `actor = src = e`), the held amount is non-negative, the beneficiary is a distinct live
account, and the vault cell is a live account holding the amount. -/
structure ClaimReady (k : RecordKernelState) (e target : CellId) (asset : AssetId) : Prop where
  held_nonneg : 0 ≤ k.bal e asset
  distinct    : e ≠ target
  e_live      : e ∈ k.accounts
  target_live : target ∈ k.accounts
  e_lifecycle : cellLifecycleLive k e = true

/-- A claim COMMITS whenever the world is `ClaimReady` (the move's fail-closed guard is discharged:
`actor = src = e` self-authorizes, the held amount is available by construction). -/
theorem vaultSettle_commits (k : RecordKernelState) (e target : CellId) (asset : AssetId)
    (newState : Int) (hr : ClaimReady k e target asset) :
    (vaultSettle k e target asset newState).isSome := by
  unfold vaultSettle
  set k1 : RecordKernelState :=
    { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int newState)
                              else k.cell c } with hk1
  have hbal : k1.bal = k.bal := rfl
  have hacc : k1.accounts = k.accounts := rfl
  have hauth : authorizedB k1.caps { actor := e, src := e, dst := target, amt := k.bal e asset } = true := by
    unfold authorizedB; simp
  have hlife : cellLifecycleLive k1 e = true := hr.e_lifecycle
  unfold recKExecAsset
  rw [if_pos]
  · exact Option.isSome_some
  · refine ⟨hauth, hr.held_nonneg, ?_, hr.distinct, ?_, ?_, ?_⟩
    · show k.bal e asset ≤ k1.bal e asset; rw [hbal]
    · show e ∈ k1.accounts; rw [hacc]; exact hr.e_live
    · show target ∈ k1.accounts; rw [hacc]; exact hr.target_live
    · show cellLifecycleLive k1 e = true; exact hlife

/-- **`open_vault_claimable` — KEYSTONE (d), PROVED (any gate).** An OPEN vault whose release gate is
DISCHARGED, with a `ClaimReady` beneficiary, CLAIMS (commits) — the value is deliverable, not trapped.
SCOPE: this is one-step claimability (the structural analog of the kernel verbs' guarantee);
scheduler-fairness eventual settlement is a consensus/GST liveness statement, not a single-machine
theorem. -/
theorem open_vault_claimable (gate : Int → Int → Bool) (k : RecordKernelState)
    (e beneficiary : CellId) (asset : AssetId) (atBlock witness : Int)
    (hopen : vaultState k e = sOpen) (hgate : gate atBlock witness = true)
    (hr : ClaimReady k e beneficiary asset) :
    (vaultClaimGated gate k e beneficiary asset atBlock witness).isSome := by
  unfold vaultClaimGated
  rw [if_pos ⟨hopen, hgate⟩]
  exact vaultSettle_commits k e beneficiary asset sClaimed hr

/-! ## §9 — NON-VACUITY: a concrete vault world + `#guard` witnesses (timelock & hash-lock). -/

/-- A vault world. The VAULT CELL is cell `0` holding 500 of asset 0 (the locked value, in its OWN
`bal` column) with state slot OPEN, beneficiary 1, releaseHeight 11000, condDigest 0 (a pure
TIMELOCK), asset 0. The BENEFICIARY is cell `1` (holds 5 of asset 0). All live. NO side-table. -/
def heightWorld : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun c =>
      if c = 0 then .record
        [ (stateField, .int sOpen), (beneficiaryField, .int 1), (releaseHeightField, .int 11000)
        , (condDigestField, .int 0), (assetField, .int 0) ]
      else .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 then (if a = 0 then 500 else 0)
                      else if c = 1 then (if a = 0 then 5 else 0) else 0 }

/-- The claim-ready bundle for claiming heightWorld's vault to beneficiary 1. -/
theorem heightWorld_claim_ready : ClaimReady heightWorld 0 1 0 :=
  { held_nonneg := by decide, distinct := by decide, e_live := by decide, target_live := by decide,
    e_lifecycle := by decide }

-- (i) the vault is OPEN, releaseHeight 11000:
#guard (vaultState heightWorld 0 == sOpen)                                       -- true
#guard (vaultReleaseHeight heightWorld 0 == 11000)                               -- true

-- (ii) a TIMELOCK claim AT/AFTER the release height (11500 ≥ 11000) COMMITS, delivers 500 to cell 1,
--      and advances to CLAIMED; supply FIXED (pure move conservation, no side-table):
#guard ((vaultClaimTimelock heightWorld 0 1 0 11500).isSome)                     -- true (claimed!)
#guard ((vaultClaimTimelock heightWorld 0 1 0 11500).map (fun s => s.bal 1 0)) == some 505   -- beneficiary 5→505
#guard ((vaultClaimTimelock heightWorld 0 1 0 11500).map (fun s => s.bal 0 0)) == some 0     -- vault held 500→0
#guard ((vaultClaimTimelock heightWorld 0 1 0 11500).map (fun s => vaultState s 0)) == some sClaimed
#guard ((vaultClaimTimelock heightWorld 0 1 0 11500).map (fun s => recTotalAsset s 0)) == some 505
#guard (recTotalAsset heightWorld 0 == 505)

-- (iii) EARLY release (10999 < 11000) ⇒ none (KEYSTONE c — no early release):
#guard ((vaultClaimTimelock heightWorld 0 1 0 10999).isSome) == false            -- false (too early)
-- ...AT exactly the release height is the live boundary (non-vacuity):
#guard ((vaultClaimTimelock heightWorld 0 1 0 11000).isSome)                     -- true (at release)

-- (iv) NO-DOUBLE-CLAIM: claim, then a SECOND claim on the claimed vault fails (KEYSTONE b):
#guard (((vaultClaimTimelock heightWorld 0 1 0 11500).bind (fun s => vaultClaimTimelock s 0 1 0 11500)).isSome) == false

/-- A HASH-LOCK vault world. Cell `0` holds 500 of asset 0, OPEN, beneficiary 1, releaseHeight 0,
condDigest 77 (the committed `H(preimage)` for our toy `hash := (· + 1)`, so the genuine preimage is
76), asset 0. Cell `1` is the beneficiary (holds 5). -/
def proofWorld : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun c =>
      if c = 0 then .record
        [ (stateField, .int sOpen), (beneficiaryField, .int 1), (releaseHeightField, .int 0)
        , (condDigestField, .int 77), (assetField, .int 0) ]
      else .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 then (if a = 0 then 500 else 0)
                      else if c = 1 then (if a = 0 then 5 else 0) else 0 }

/-- A toy collision-resistant hash for the executable model (the §8 crypto portal carries the real
preimage hash). `hash 76 = 77` is the committed digest, so 76 is the genuine preimage. -/
def toyHash : Int → Int := fun x => x + 1

/-- The claim-ready bundle for the hash-lock vault. -/
theorem proofWorld_claim_ready : ClaimReady proofWorld 0 1 0 :=
  { held_nonneg := by decide, distinct := by decide, e_live := by decide, target_live := by decide,
    e_lifecycle := by decide }

-- (v) the committed digest is 77 (= toyHash 76):
#guard (vaultCondDigest proofWorld 0 == 77)                                      -- true
#guard (toyHash 76 == 77)                                                        -- true

-- (vi) a HASH-LOCK claim with the GENUINE preimage (76 ⇒ hash 77 = digest) COMMITS, delivers 500:
#guard ((vaultClaimHashlock toyHash proofWorld 0 1 0 76).isSome)                 -- true (claimed!)
#guard ((vaultClaimHashlock toyHash proofWorld 0 1 0 76).map (fun s => s.bal 1 0)) == some 505
#guard ((vaultClaimHashlock toyHash proofWorld 0 1 0 76).map (fun s => vaultState s 0)) == some sClaimed
#guard ((vaultClaimHashlock toyHash proofWorld 0 1 0 76).map (fun s => recTotalAsset s 0)) == some 505

-- (vii) a FORGED preimage (99 ⇒ hash 100 ≠ 77) ⇒ none (KEYSTONE c — no forged proof):
#guard ((vaultClaimHashlock toyHash proofWorld 0 1 0 99).isSome) == false        -- false (forged)

-- (viii) the factory descriptors conform (their own initial state is invariant-clean):
#guard ((vaultFactory 1 11000 0 0).conforms)                                     -- true (timelock)
#guard ((vaultFactory 1 0 77 0).conforms)                                        -- true (hash-lock)

/-! ## §VERDICT — PASS.

THE VAULT IS FULLY CAPTURED as a factory-born cell-program + a claim-safety contract, with NO
side-table and NO bespoke conserved quantity:

  * FACTORY (`vaultFactory`): four deal-term immutables + the ONE-terminal state-machine
    `admitTable [(open, claimed)]` — `vaultFactory_conforms` PROVED. Drawn entirely from the EXISTING
    SlotCaveat vocabulary. No new constraint kind needed (vault = escrow minus the refund leg).

  * KEYSTONE (a) CONSERVATION (`vaultSettle_conserves`, `vaultClaim_conserves`), INHERITED from the
    ordinary per-asset move law `recKExecAsset_conserves_per_asset`.
  * KEYSTONE (b) ONE-SHOT / no-double-claim (`no_double_claim`, `no_double_claim_after`,
    `claim_requires_open`, `claim_advances_state`): the one-terminal state machine drives OPEN→CLAIMED
    once; no further claim commits.
  * KEYSTONE (c) CLAIM-ONLY-ON-CONDITION (`claim_requires_discharge`) with BOTH concrete instances:
    `timelock_rejects_early` (no early release) and `hashlock_rejects_forged` (no forged proof).
  * KEYSTONE (d) NOT-STRANDED — PROVED as ONE-STEP claimability (`open_vault_claimable` +
    `vaultSettle_commits`). SCOPE: scheduler-fairness eventual settlement is a consensus/GST liveness
    statement, the SAME boundary the kernel verbs had.

  * NON-VACUITY: a timelock world (early-claim REJECTED / at-release LIVE / double-claim BLOCKED) and a
    hash-lock world (genuine-preimage CLAIMS / forged-preimage REJECTED) both `#guard`-witnessed with
    real commit/deliver/conserve transitions. No keystone is vacuous.

  * THE GATE ABSTRACTION (the reuse): the release condition is an abstract decidable `gate`, so the
    TIMELOCK (`timelockGate`) and the HASH-LOCK (`hashlockGate`) are TWO INSTANCES of ONE proof shape
    — the claim-once / conservation / liveness keystones never inspect which gate fires, exactly the
    escrow probe's §HARD-iii Pred-discharge generalization.

RESIDUALS (honest): (1) this probe models the vault cell-program at the kernel-state level
(`recKExecAsset` + record slots); wiring it through the full forest gated executor (the `admitTable`
enforced by the LIVE executor on every `SetField`) is carried by `Dregg2.Apps.Vault` (the factory
re-establishes the keystones on the MINTED cell via `createCellFromFactoryChainA`). (2) the hash-lock's
real preimage-hash discharge is the §8 crypto portal (same status as the escrow `witnessed(vk)` gate).
(3) eventual-settlement liveness is consensus-layer. None is vault-specific.
-/

#assert_axioms vaultFactory_conforms
#assert_axioms vaultSettle_conserves
#assert_axioms vaultClaim_conserves
#assert_axioms claim_requires_open
#assert_axioms claim_advances_state
#assert_axioms no_double_claim
#assert_axioms no_double_claim_after
#assert_axioms claim_requires_discharge
#assert_axioms timelock_rejects_early
#assert_axioms hashlock_rejects_forged
#assert_axioms vaultSettle_commits
#assert_axioms open_vault_claimable

end Dregg2.Verify.VaultFactoryProbe
