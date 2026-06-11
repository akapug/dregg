/-
# Dregg2.Circuit.Spec.bridgeinboundmint — INDEPENDENT full-state spec + executor⟺spec for the
dregg2 effect family **bridge-inbound-mint** (variant: `bridgeMintA` — W1: the BRIDGE-issuer move).

Phase 2 of dregg1's two-phase cross-chain bridge, the INBOUND mint: when the OTHER chain confirms a
lock, this chain credits the recipient with the bridged asset. **W1 (DREGG3 §2.2)**: the BRIDGE cell
IS the issuer of the bridged asset (`AssetId := CellId` — asset `a` = the bridge cell `a`), so the
inbound mint is an ordinary per-asset transfer FROM the bridge's negative-capable well TO the
recipient: the bridge well carries −(outstanding bridged supply) — exactly what this chain owes the
foreign chain — and `Σ_c bal c a` is EXACTLY unchanged. The §8 CryptoPortal hypothesis (the
other-chain confirmation) governs WHEN the bridge may move; conservation holds regardless. The
in-VM gate is the privileged mint authority over the BRIDGE cell (`recCMintAsset` enforces it).

This is a *leaf* module in the `Transfer.lean` lineage (imported by nothing; gated standalone). It
re-derives, INDEPENDENTLY of the executor, the SAME triangle corner the reference
`TransferSpec`/`recKExec_iff_spec`/`recTransfer_correct` establish for `Transfer`. The executor arm
this module specifies is a SINGLE branch:

    execFullA s (.bridgeMintA actor cell a value) = recCMintAsset s actor cell a value

`recCMintAsset` is the chained per-asset mint: it runs the kernel issuer-move `recKMintAsset` and,
on commit, PREPENDS the truthful well→recipient receipt `{actor, src:=a, dst:=cell, amt:=value}`
onto the log. The kernel mint's admissibility guard is the EXACT conjunction (read off the CODE):

    mintAuthorizedB caps actor a = true   -- (1) ISSUER AUTHORITY over the BRIDGE cell (E2)
  ∧ 0 ≤ value                             -- (2) NON-NEGATIVITY
  ∧ a ∈ accounts                          -- (3) BRIDGE-WELL LIVENESS (genesis order)
  ∧ cell ∈ accounts                       -- (4) DESTINATION LIVENESS
  ∧ a ≠ cell                              -- (5) the self-mint no-move is refused

and on commit it produces `some { k with bal := recTransferBal k.bal a cell a value }` — the
issuer-move write: well debited, recipient credited, EVERY other (cell,asset) entry untouched.

## What is proved (the apex reference truth, BOTH directions)

  1. `InboundMintSpec st actor cell a value st'` — the INDEPENDENT declarative full-state
     post-condition: the admissibility guard (`inboundMintAdmit`), the EXACT post-`bal` ledger
     (the issuer-move write), the chained `log` advanced by exactly the truthful receipt, AND the
     FRAME — every OTHER RecordKernelState component LITERALLY unchanged. No frame clause mentions
     the executor.

  2. `recTransferBal_inbound_correct` — the post-`bal` helper validated DECLARATIVELY (the bridge
     well debited by `value`, the `(cell,a)` entry credited by `value`, every other `(c,b)` entry
     literally preserved).

  3. `recCMintAsset_iff_inboundSpec` — the ⟺ on the chained step `recCMintAsset`.
     `execBridgeMintA_iff_spec` — execFullA ⟺ spec for the `bridgeMintA` variant (BOTH directions).

  4. Post-state corollaries: `bridgeMint_credit` (well-debit + recipient-credit + ledger-frame),
     `bridgeMint_supply_delta` (the W1 CONSERVATION CONTENT: a committed inbound mint leaves EVERY
     asset's supply EXACTLY unchanged — the bridge well absorbs the outstanding bridged value),
     `bridgeMint_authorized`, `bridgeMint_nonneg`.

  5. Non-vacuity: `bridgeMint_rejects_unauthorized`, `bridgeMint_rejects_negative`,
     `bridgeMint_rejects_dead_bridge`, `bridgeMint_rejects_dead_cell`, plus `bridgeMint_admits_iff`
     — each forged input fails a guard leg ⇒ the executor returns `none` ⇒ no spec post-state
     exists. Concrete `#guard` witnesses (genuine `decide`, NOT `native_decide`) exhibit a good
     mint committing (the bridge well visibly going negative) and the forgeries decidably rejected.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.BridgeInboundMint

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — the admissibility guard, lifted from the CODE.

`recKMintAsset` (W1) commits IFF this exact conjunction holds: the gate target is the **BRIDGE**
cell `a` — the issuer of the bridged asset (`mintAuthorizedB caps actor a`, the privileged
`node`/`control` gate; a forged other-chain confirmation cannot coin value because only the bridge
authority can move the bridge well). -/

/-- **`inboundMintAdmit`** — the full admissibility guard `recKMintAsset` (and so `recCMintAsset`,
the chained step `bridgeMintA` dispatches to) checks, as a `Prop`: BRIDGE-issuer authority ∧
non-negativity ∧ bridge-well liveness ∧ destination liveness ∧ distinctness. -/
def inboundMintAdmit (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (value : ℤ) : Prop :=
  mintAuthorizedB k.caps actor a = true ∧ 0 ≤ value
    ∧ a ∈ k.accounts ∧ cell ∈ k.accounts ∧ a ≠ cell

/-- The truthful receipt a committed `bridgeMintA` prepends to the log: the bridge-well → recipient
row of size `value`, exactly `recCMintAsset`'s `log` head. Stated HERE so the spec's `log` clause
does not reference the executor's body. -/
def inboundMintReceipt (actor cell : CellId) (a : AssetId) (value : ℤ) : Turn :=
  { actor := actor, src := a, dst := cell, amt := value }

/-! ## §2 — the post-`bal` helper, validated DECLARATIVELY.

`recTransferBal bal a cell a value` (the issuer-move write) is the ONLY thing a committed inbound
mint does to the ledger. We validate it relationally so the spec's `bal = recTransferBal …` clause
carries real meaning rather than trusting the helper's name. -/

/-- **`recTransferBal_inbound_correct`** — the ledger-update helper validated DECLARATIVELY: an
inbound mint debits the bridge well `(a, a)` by exactly `value`, credits `(cell, a)` by exactly
`value`, and leaves every OTHER (cell,asset) entry literally untouched. Well-debit ∧ credit ∧
ledger-frame. -/
theorem recTransferBal_inbound_correct (bal : CellId → AssetId → ℤ) (cell : CellId) (a : AssetId)
    (value : ℤ) (hne : a ≠ cell) :
    recTransferBal bal a cell a value a a = bal a a - value
    ∧ recTransferBal bal a cell a value cell a = bal cell a + value
    ∧ (∀ c b, ¬ (c = a ∧ b = a) → ¬ (c = cell ∧ b = a)
        → recTransferBal bal a cell a value c b = bal c b) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold recTransferBal
    rw [if_pos rfl, if_pos rfl]
  · unfold recTransferBal
    rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl]
  · intro c b hni hnc
    unfold recTransferBal
    rcases eq_or_ne b a with hb | hb
    · have hci : c ≠ a := fun h => hni ⟨h, hb⟩
      have hcc : c ≠ cell := fun h => hnc ⟨h, hb⟩
      rw [if_pos hb, if_neg hci, if_neg hcc]
    · rw [if_neg hb]

/-! ## §3 — the executor projection: `execFullA` on `bridgeMintA` IS `recCMintAsset`. -/

@[simp] theorem execFullA_bridgeMintA (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) :
    execFullA st (.bridgeMintA actor cell a value) = recCMintAsset st actor cell a value := rfl

/-! ## §4 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec. -/

/-- **The full-state declarative spec of a committed bridge-inbound-mint (`bridgeMintA`, W1)** — the
INDEPENDENT reference semantics. Enumerates the FRAME completely: the touched `bal` + `log`, and
every untouched non-`bal` kernel field. -/
def InboundMintSpec (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (st' : RecChainedState) : Prop :=
  inboundMintAdmit st.kernel actor cell a value
  ∧ st'.kernel.bal = recTransferBal st.kernel.bal a cell a value
  ∧ st'.log = inboundMintReceipt actor cell a value :: st.log
  -- THE FRAME: every non-`bal` kernel field literally unchanged (16).
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt

/-- **`recCMintAsset_iff_inboundSpec` — CHAINED EXECUTOR ⟺ SPEC (FULL state, both directions).** The
chained record kernel commits a `bridgeMintA` (via `recCMintAsset`) into `st'` IFF `st'` is EXACTLY
the spec'd full post-state. The `→` VALIDATES `recCMintAsset` against the independent spec — all 18
components (`bal` + `log` + 16 frame fields) are checked, so a silently-mutated component would make
the proof FAIL; the `←` reconstructs the committed state from the spec. -/
theorem recCMintAsset_iff_inboundSpec (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (st' : RecChainedState) :
    recCMintAsset st actor cell a value = some st' ↔ InboundMintSpec st actor cell a value st' := by
  unfold recCMintAsset recKMintAsset InboundMintSpec inboundMintAdmit inboundMintReceipt
  by_cases hg : mintAuthorizedB st.kernel.caps actor a = true ∧ 0 ≤ value
      ∧ a ∈ st.kernel.accounts ∧ cell ∈ st.kernel.accounts ∧ a ≠ cell
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hbal, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
      -- reconstruct st' from the spec: split both records and substitute every field.
      obtain ⟨k', lg'⟩ := st'
      obtain ⟨acc, cl, cp, nl, rv, cm, bl, sc, fc, lc, dc, dl, dn, dge, dgea⟩ := k'
      simp only at hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
      subst hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- **`execBridgeMintA_iff_spec` — THE DELIVERABLE: `execFullA`-LEVEL EXECUTOR ⟺ SPEC (FULL state,
both directions).** The one gated executor commits a `bridgeMintA` turn into `st'` IFF `st'` is
EXACTLY the independent full-state spec. Forward VALIDATES the executor (every one of the 18
components is pinned); backward reconstructs. This is the bridge-inbound-mint corner of the
spec⟺executor(⟺circuit) triangle, the `bridgeMintA` analog of `recKExec_iff_spec`. -/
theorem execBridgeMintA_iff_spec (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (st' : RecChainedState) :
    execFullA st (.bridgeMintA actor cell a value) = some st'
      ↔ InboundMintSpec st actor cell a value st' := by
  rw [execFullA_bridgeMintA]; exact recCMintAsset_iff_inboundSpec st actor cell a value st'

/-! ## §5 — derived guarantees off the spec. -/

/-- **`bridgeMint_authorized` — no inbound supply without BRIDGE-issuer authority (W1/E2).** A
committed `bridgeMintA` PROVES the actor held the privileged mint cap over the BRIDGE cell `a` (NOT
the recipient). Read straight off the spec's guard. -/
theorem bridgeMint_authorized (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (st' : RecChainedState) (h : execFullA st (.bridgeMintA actor cell a value) = some st') :
    mintAuthorizedB st.kernel.caps actor a = true :=
  ((execBridgeMintA_iff_spec st actor cell a value st').mp h).1.1

/-- **`bridgeMint_nonneg` — no negative-amount inbound supply.** -/
theorem bridgeMint_nonneg (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (st' : RecChainedState) (h : execFullA st (.bridgeMintA actor cell a value) = some st') :
    0 ≤ value :=
  ((execBridgeMintA_iff_spec st actor cell a value st').mp h).1.2.1

/-- **`bridgeMint_credit` — the issuer-move, row by row**: the bridge well `(a, a)` debited by
exactly `value` (the well IS −outstanding), the recipient `(cell, a)` credited by exactly `value`,
every OTHER (cell,asset) entry preserved (`recTransferBal_inbound_correct`). -/
theorem bridgeMint_credit (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (st' : RecChainedState) (h : execFullA st (.bridgeMintA actor cell a value) = some st') :
    st'.kernel.bal a a = st.kernel.bal a a - value
    ∧ st'.kernel.bal cell a = st.kernel.bal cell a + value
    ∧ (∀ c b, ¬ (c = a ∧ b = a) → ¬ (c = cell ∧ b = a)
        → st'.kernel.bal c b = st.kernel.bal c b) := by
  have hspec := (execBridgeMintA_iff_spec st actor cell a value st').mp h
  have hbal : st'.kernel.bal = recTransferBal st.kernel.bal a cell a value := hspec.2.1
  have hne : a ≠ cell := hspec.1.2.2.2.2
  obtain ⟨hdeb, hcred, hframe⟩ := recTransferBal_inbound_correct st.kernel.bal cell a value hne
  refine ⟨?_, ?_, ?_⟩
  · rw [hbal]; exact hdeb
  · rw [hbal]; exact hcred
  · intro c b hni hnc; rw [hbal]; exact hframe c b hni hnc

/-- **`bridgeMint_supply_delta` — W1 CONSERVATION CONTENT: a committed inbound mint leaves EVERY
asset's supply EXACTLY unchanged** (`recKMintAsset_delta` lifted to the `execFullA` level). The
bridge well absorbs the bridged value — what this chain owes the foreign chain is ON the ledger,
and the sum never moves. -/
theorem bridgeMint_supply_delta (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (st' : RecChainedState) (h : execFullA st (.bridgeMintA actor cell a value) = some st')
    (b : AssetId) :
    recTotalAsset st'.kernel b = recTotalAsset st.kernel b := by
  -- recover the chained-executor commitment, then reuse the kernel delta on the kernel post-state.
  rw [execFullA_bridgeMintA] at h
  unfold recCMintAsset at h
  cases hm : recKMintAsset st.kernel actor cell a value with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' =>
      rw [hm] at h; simp only [Option.some.injEq] at h
      have hk : st'.kernel = k' := by rw [← h]
      rw [hk]; exact recKMintAsset_delta st.kernel k' actor cell a value hm b

/-! ## §6 — NON-VACUITY: the spec is a genuine GATE (rejects bad inputs). -/

/-- **`bridgeMint_rejects_unauthorized`.** A `bridgeMintA` over a state where the actor lacks the
privileged mint cap over the BRIDGE cell (`mintAuthorizedB caps actor a = false`) is REJECTED.
Unprivileged inbound supply is impossible (a forged other-chain confirmation cannot coin value). -/
theorem bridgeMint_rejects_unauthorized (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (hbad : mintAuthorizedB st.kernel.caps actor a = false) :
    execFullA st (.bridgeMintA actor cell a value) = none := by
  rw [execFullA_bridgeMintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨h, _⟩; rw [hbad] at h; exact absurd h (by simp))]

/-- **`bridgeMint_rejects_negative`.** A `bridgeMintA` with a negative amount is REJECTED. -/
theorem bridgeMint_rejects_negative (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (hbad : value < 0) :
    execFullA st (.bridgeMintA actor cell a value) = none := by
  rw [execFullA_bridgeMintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨_, h, _⟩; exact absurd h (by omega))]

/-- **`bridgeMint_rejects_dead_bridge` (the genesis-order tooth).** A `bridgeMintA` whose bridge
well is NOT a live account (`a ∉ accounts`) is REJECTED — the bridge cell must exist before its
asset flows. -/
theorem bridgeMint_rejects_dead_bridge (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (hbad : a ∉ st.kernel.accounts) :
    execFullA st (.bridgeMintA actor cell a value) = none := by
  rw [execFullA_bridgeMintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨_, _, h, _⟩; exact absurd h hbad)]

/-- **`bridgeMint_rejects_dead_cell`.** A `bridgeMintA` to a destination that is NOT a live account
(`cell ∉ accounts`) is REJECTED. -/
theorem bridgeMint_rejects_dead_cell (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (hbad : cell ∉ st.kernel.accounts) :
    execFullA st (.bridgeMintA actor cell a value) = none := by
  rw [execFullA_bridgeMintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨_, _, _, h, _⟩; exact absurd h hbad)]

/-- **`bridgeMint_admits_iff` — the executor commits IFF the guard holds.** -/
theorem bridgeMint_admits_iff (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ) :
    (∃ st', execFullA st (.bridgeMintA actor cell a value) = some st')
      ↔ inboundMintAdmit st.kernel actor cell a value := by
  rw [execFullA_bridgeMintA]
  unfold recCMintAsset recKMintAsset inboundMintAdmit
  by_cases hg : mintAuthorizedB st.kernel.caps actor a = true ∧ 0 ≤ value
      ∧ a ∈ st.kernel.accounts ∧ cell ∈ st.kernel.accounts ∧ a ≠ cell
  · rw [if_pos hg]; exact ⟨fun _ => hg, fun _ => ⟨_, rfl⟩⟩
  · rw [if_neg hg]
    constructor
    · rintro ⟨st', h⟩; exact absurd h (by simp)
    · intro hg'; exact absurd hg' hg

/-! ## §7 — concrete #guard non-vacuity witnesses (genuine `decide`, NOT `native_decide`).

Cells 0 (the recipient) and 1 (the BRIDGE — the issuer of bridged asset 1) are live; actor 9 holds
the `node 1` BRIDGE cap; actor 0 holds NO cap. An inbound mint of 40 of asset 1 by the privileged
actor commits — the bridge well visibly goes NEGATIVE (−40 = the outstanding bridged supply) and
the sum stays EXACTLY 0; the forgeries are decidably rejected. -/

/-- A concrete pre-state: cells {0, 1} live (1 = the bridge), ledger empty, actor 9 holds the
`node 1` bridge-issuer cap. -/
def stB0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun a => if a = 9 then [Dregg2.Authority.Cap.node 1] else [] }
    log := [] }

-- The privileged inbound mint of 40 of asset 1 (bridge cell 1) onto the live cell 0 COMMITS:
#guard (execFullA stB0 (.bridgeMintA 9 0 1 40)).isSome  --  true
-- ...the bridge well went −40 (the outstanding bridged supply) and the sum stays 0:
#guard ((execFullA stB0 (.bridgeMintA 9 0 1 40)).map
        (fun s => (s.kernel.bal 1 1, s.kernel.bal 0 1, recTotalAsset s.kernel 1)))
        == some (-40, 40, 0)
-- An UNPRIVILEGED inbound mint (actor 0, no `node 1` bridge cap) is REJECTED:
#guard decide ((execFullA stB0 (.bridgeMintA 0 0 1 40)).isNone)  --  true
-- A NEGATIVE-amount inbound mint is REJECTED:
#guard decide ((execFullA stB0 (.bridgeMintA 9 0 1 (-5))).isNone)  --  true
-- An inbound mint over a DEAD bridge well (asset 7: cell 7 ∉ accounts) is REJECTED:
#guard decide ((execFullA stB0 (.bridgeMintA 9 0 7 40)).isNone)  --  true
-- An inbound mint to a DEAD destination (cell 7 ∉ accounts) is REJECTED:
#guard decide ((execFullA stB0 (.bridgeMintA 9 7 1 40)).isNone)  --  true
-- mintAuthorizedB witnesses: actor 9 authorized over the bridge 1, actor 0 not:
#guard mintAuthorizedB stB0.kernel.caps 9 1 == true
#guard mintAuthorizedB stB0.kernel.caps 0 1 == false

/-! ## §8 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms recTransferBal_inbound_correct
#assert_axioms execFullA_bridgeMintA
#assert_axioms recCMintAsset_iff_inboundSpec
#assert_axioms execBridgeMintA_iff_spec
#assert_axioms bridgeMint_authorized
#assert_axioms bridgeMint_nonneg
#assert_axioms bridgeMint_credit
#assert_axioms bridgeMint_supply_delta
#assert_axioms bridgeMint_rejects_unauthorized
#assert_axioms bridgeMint_rejects_negative
#assert_axioms bridgeMint_rejects_dead_bridge
#assert_axioms bridgeMint_rejects_dead_cell
#assert_axioms bridgeMint_admits_iff

end Dregg2.Circuit.Spec.BridgeInboundMint
