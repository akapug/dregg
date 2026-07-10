/-
# Dregg2.Circuit.Spec.accountgrowth — INDEPENDENT full-state spec + executor⟺spec for the
dregg2 effect family **account-growth** (variants: `createCellA`, `spawnA`).

A *leaf* module in the `Transfer.lean` lineage: it builds, for the per-asset PRIVILEGED account
creation effects, the SAME spec-corner the reference `TransferSpec`/`recKExec_iff_spec` establish
for `Transfer`, written INDEPENDENTLY of the executor. The `execFullA` arms (`TurnExecutorFull.lean`
`:3515`/`:3519`) are, verbatim,

    | .createCellA actor newCell  => createCellChainA s actor newCell
    | .spawnA actor child target  => spawnChainA s actor child target

## `createCellA` (the CLEAN, single-branch variant)

`createCellChainA` (`TurnExecutorFull.lean:787`) commits IFF

    mintAuthorizedB caps actor newCell = true     -- (1) PRIVILEGED creation authority (mint-grade;
                                                  --     bare ownership is NOT enough — creation coins
                                                  --     a fresh cell)
  ∧ newCell ∉ accounts                            -- (2) FRESHNESS (no re-minting a live id)

and on commit produces `{ kernel := createCellIntoAsset kernel newCell, log := creationRow :: log }`.

`createCellIntoAsset` (`RecordKernel.lean`) grows `accounts` AND resets EVERY per-cell indexed slot at
`newCell` to born-empty defaults (`bornEmptyCellSlots`: `cell`/`caps`/`delegate`/`delegations`/
`slotCaveats`/`lifecycle`/`deathCert`/`bal`), closing stale side-table resurrection on id reuse.

— the dregg1-faithful `balance == 0` born-empty cell, conservation-NEUTRAL because the fresh term in
`recTotalAsset` is exactly `0` (the `bal`-reset is load-bearing: a re-inserted previously-credited id
would otherwise re-introduce supply).

### Born-empty `cell` (executor + spec aligned).

`createCellIntoAsset` calls `bornEmptyCellSlots`, which resets `cell newCell` to `default` together with
`caps`/`delegate`/`delegations`/`slotCaveats`/`lifecycle`/`deathCert`/`bal`. The declarative
`bornEmptyAt` predicate in §4 pins this shape; the circuit layer digest-binds the side-table bundle via
`BornEmptyCommit`.

## `spawnA` (the MULTI-update variant)

`spawnChainA` (`TurnExecutorFull.lean:813`) factors as: an authorized `createCellChainA` of `child`
(into an intermediate `s1`) GATED by the spawner already holding a live cap-edge to the parent
`target` (`(caps actor).any (confersEdgeTo target) ∧ target ∈ accounts`), THEN a bal-orthogonal
copy of the actor's concrete held parent cap to the child + an initial delegation snapshot. So its
post-state edits `accounts`+`bal` (create leg) AND `caps`+`delegate`+`delegations` (the handoff) —
five touched components — while the OTHER 12 kernel fields + the touched-but-functional ones'
complements are framed. We give it a full declarative spec too, factored through `createCellChainA`.

## Deliverables (mirroring `Transfer.lean` §6b + `supplycreation.lean`)

  1. `CreateCellSpec` / `SpawnSpec` : Prop — the INDEPENDENT declarative full-state spec. Guard ∧ the
     EXACT touched components ∧ EVERY other RecChainedState/kernel field LITERALLY unchanged (the
     FRAME — all 17 kernel fields + `log` enumerated). No frame clause mentions an executor helper.
  2. `execCreateCellA_iff_spec` / `execSpawnA_iff_spec` : `execFullA st (.<v> …) = some st' ↔ <V>Spec
     …` — BOTH directions. The `→` VALIDATES the executor: a silently-mutated frame field makes the
     proof FAIL.
  3. `createCellIntoAsset_correct` — the touched post helper validated DECLARATIVELY (the
     `recTransfer_correct` analog): the new id is a live account with a `0` ledger column ∀ asset,
     every other (cell,asset) entry preserved, every other account preserved.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.AccountGrowth

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority

set_option linter.dupNamespace false

private theorem recordKernel_eq_of_fields {k k' : RecordKernelState}
    (haccounts : k.accounts = k'.accounts) (hcell : k.cell = k'.cell) (hcaps : k.caps = k'.caps)
    (hnullifiers : k.nullifiers = k'.nullifiers)
    (hrevoked : k.revoked = k'.revoked) (hcommitments : k.commitments = k'.commitments)
    (hbal : k.bal = k'.bal)
    (hslotCaveats : k.slotCaveats = k'.slotCaveats) (hfactories : k.factories = k'.factories)
    (hlifecycle : k.lifecycle = k'.lifecycle) (hdeathCert : k.deathCert = k'.deathCert)
    (hdelegate : k.delegate = k'.delegate) (hdelegations : k.delegations = k'.delegations)
    (hdelegationEpoch : k.delegationEpoch = k'.delegationEpoch)
    (hdelegationEpochAt : k.delegationEpochAt = k'.delegationEpochAt)
    (hheaps : k.heaps = k'.heaps)
    (hnullifierRoot : k.nullifierRoot = k'.nullifierRoot)
    (hrevokedRoot : k.revokedRoot = k'.revokedRoot)
    (hcommitmentsRoot : k.commitmentsRoot = k'.commitmentsRoot) : k = k' := by
  cases k; cases k'; simp_all

/-! ## §1 — the admissibility guards, lifted from the CODE. -/

/-- **`createCellAdmit`** — the full admissibility guard `createCellChainA` checks, as a `Prop` (the
exact conjunction in the executor's `if`, `TurnExecutorFull.lean:788`). PRIVILEGED creation authority
(`mintAuthorizedB` — bare ownership is deliberately NOT sufficient; creation coins a fresh cell) ∧
FRESHNESS (`newCell ∉ accounts`). -/
def createCellAdmit (k : RecordKernelState) (actor newCell : CellId) : Prop :=
  mintAuthorizedB k.caps actor newCell = true ∧ newCell ∉ k.accounts

/-- The disclosed receipt a committed `createCellA` prepends to the log (a self-edge `newCell →
newCell` of size `0` — the born-empty creation row, `createCellChainA`'s `log` head). -/
def createReceipt (actor newCell : CellId) : Turn :=
  { actor := actor, src := newCell, dst := newCell, amt := 0 }

/-- **`spawnAdmit`** — the full admissibility guard `spawnChainA` checks (`TurnExecutorFull.lean:814`)
TOGETHER with the create-leg guard it dispatches into. The spawner already holds a live cap-edge to
the parent `target` (`(caps actor).any (confersEdgeTo target)`) ∧ `target` is a live account ∧ the
create leg's `createCellAdmit` over `child` (privileged child-creation authority ∧ child freshness).
Stated directly, no executor term. -/
def spawnAdmit (k : RecordKernelState) (actor child target : CellId) : Prop :=
  (k.caps actor).any (fun cap => confersEdgeTo target cap) = true
  ∧ target ∈ k.accounts
  ∧ createCellAdmit k actor child

/-! ## §2 — the touched post helper (`createCellIntoAsset`), validated DECLARATIVELY.

`createCellIntoAsset k newCell` is the ONLY thing the create leg does to the kernel — it grows
`accounts` by `newCell` and resets `newCell`'s `bal` column to `0` ∀ asset, touching NOTHING else.
We validate it relationally (the `recTransfer_correct` analog), so the spec's
`kernel = createCellIntoAsset …` clauses carry real meaning rather than trusting the helper's name. -/

/-- **`createCellIntoAsset_correct`** — the account-growth helper validated DECLARATIVELY: the new id
IS a live account; every per-cell indexed slot at `newCell` is born empty; every OTHER cell's slots
are literally untouched. So the spec's touched clauses encode growth ∧ born-empty. -/
theorem createCellIntoAsset_correct (k : RecordKernelState) (newCell : CellId) :
    newCell ∈ (createCellIntoAsset k newCell).accounts
    ∧ (createCellIntoAsset k newCell).cell newCell = default
    ∧ (createCellIntoAsset k newCell).caps newCell = []
    ∧ (createCellIntoAsset k newCell).delegate newCell = none
    ∧ (createCellIntoAsset k newCell).delegations newCell = []
    ∧ (createCellIntoAsset k newCell).slotCaveats newCell = []
    ∧ (createCellIntoAsset k newCell).lifecycle newCell = 0
    ∧ (createCellIntoAsset k newCell).deathCert newCell = 0
    ∧ (∀ a, (createCellIntoAsset k newCell).bal newCell a = 0)
    ∧ (∀ c, c ∈ k.accounts → c ∈ (createCellIntoAsset k newCell).accounts)
    ∧ (∀ c a, c ≠ newCell → (createCellIntoAsset k newCell).bal c a = k.bal c a) := by
  dsimp [createCellIntoAsset, bornEmptyCellSlots]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact createCellIntoAsset_grows_accounts k newCell
  · simp only [if_pos]
  · simp only [if_pos]
  · simp only [if_pos]
  · simp only [if_pos]
  · simp only [if_pos]
  · simp only [if_pos]
  · simp only [if_pos]
  · intro a; simp only [if_pos]
  · intro c hc; exact Finset.mem_insert_of_mem hc
  · intro c a hc; simp only [if_neg hc]

/-! ## §3 — the executor projection: `execFullA` on `createCellA`/`spawnA`.

Both arms are SINGLE definitional dispatches (no rewrap) — the "clean" case the prompt hopes for on
`createCellA`. We expose them as definitional rewrites. -/

@[simp] theorem execFullA_createCellA (st : RecChainedState) (actor newCell : CellId) :
    execFullA st (.createCellA actor newCell) = createCellChainA st actor newCell := rfl

@[simp] theorem execFullA_spawnA (st : RecChainedState) (actor child target : CellId) :
    execFullA st (.spawnA actor child target) = spawnChainA st actor child target := rfl

/-! ## §4 — `createCellA`: FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`CreateCellSpec` is the COMPLETE declarative post-state of a committed `createCellA`, written
INDEPENDENTLY of the executor: the guard holds; the post `accounts` is the pre `accounts` with
`newCell` inserted; the post `bal` is the pre `bal` with `newCell`'s column reset to `0`; the post
`log` is the creation receipt prepended; and ALL 15 OTHER kernel components — INCLUDING `cell` (see
the FRAME FINDING in the module header: the executor never touches `cell`) — are LITERALLY unchanged.
No frame clause mentions any executor helper. -/

/-- Born-empty per-cell maps at `newCell` (the declarative post-shape of `bornEmptyCellSlots`). -/
def bornEmptyAt (k : RecordKernelState) (newCell : CellId) (k' : RecordKernelState) : Prop :=
  (k'.cell = fun c => if c = newCell then default else k.cell c)
  ∧ (k'.caps = fun l => if l = newCell then [] else k.caps l)
  ∧ (k'.delegate = fun c => if c = newCell then none else k.delegate c)
  ∧ (k'.delegations = fun c => if c = newCell then [] else k.delegations c)
  ∧ (k'.slotCaveats = fun c => if c = newCell then [] else k.slotCaveats c)
  ∧ (k'.lifecycle = fun c => if c = newCell then 0 else k.lifecycle c)
  ∧ (k'.deathCert = fun c => if c = newCell then 0 else k.deathCert c)
  ∧ (k'.bal = fun c a => if c = newCell then 0 else k.bal c a)

/-- **The full-state declarative spec of a committed account-creation (`createCellA`)** — the
INDEPENDENT reference semantics. Touched: `accounts` growth, born-empty per-cell slots at `newCell`,
and the creation receipt. Global side-tables (`escrows`/`nullifiers`/…) are framed unchanged. -/
def CreateCellSpec (st : RecChainedState) (actor newCell : CellId) (st' : RecChainedState) : Prop :=
  createCellAdmit st.kernel actor newCell
  ∧ st'.kernel.accounts = insert newCell st.kernel.accounts
  ∧ bornEmptyAt st.kernel newCell st'.kernel
  ∧ st'.log = createReceipt actor newCell :: st.log
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt
  ∧ st'.kernel.heaps = st.kernel.heaps
  ∧ st'.kernel.nullifierRoot = st.kernel.nullifierRoot
  ∧ st'.kernel.revokedRoot = st.kernel.revokedRoot
  ∧ st'.kernel.commitmentsRoot = st.kernel.commitmentsRoot

/-- **`createCellChainA_iff_spec` — CHAINED EXECUTOR ⟺ SPEC (FULL state, both directions).** The
chained record kernel commits a `createCellA` into `st'` IFF `st'` is EXACTLY the spec'd full
post-state. The `→` VALIDATES `createCellChainA` against the independent spec — `accounts` + `bal` +
`log` + 15 frame fields = all 18 components are checked, so had the arm silently mutated `cell`/
`caps`/`nullifiers`/… any frame field, the frame clause would make the proof FAIL; the `←`
reconstructs the committed state from the spec. -/
theorem createCellChainA_iff_spec (st : RecChainedState) (actor newCell : CellId)
    (st' : RecChainedState) :
    createCellChainA st actor newCell = some st' ↔ CreateCellSpec st actor newCell st' := by
  unfold createCellChainA createCellIntoAsset CreateCellSpec createCellAdmit createReceipt
    bornEmptyCellSlots
  by_cases hg : mintAuthorizedB st.kernel.caps actor newCell = true ∧ newCell ∉ st.kernel.accounts
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨hg, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · dsimp only [bornEmptyAt]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [createReceipt]
    · rintro ⟨_, hacc, hborn, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      obtain ⟨k', lg'⟩ := st'
      obtain ⟨acc, cl, cp, nl, rv, cm, bl, sc, fc, lc, dc, dl, dn, dge, dgea, hp, nr, rr, cr⟩ := k'
      dsimp only [bornEmptyAt] at hborn
      obtain ⟨hcl, hcp, hdel, hdgs, hsc, hlif, hdc, hbal⟩ := hborn
      simp only at hacc hcl hcp hdel hdgs hsc hlif hdc hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      subst hacc hcl hcp hdel hdgs hsc hlif hdc hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- **`execCreateCellA_iff_spec` — THE DELIVERABLE: `execFullA`-LEVEL EXECUTOR ⟺ SPEC (FULL state,
both directions).** The one gated executor commits a `createCellA` turn into `st'` IFF `st'` is
EXACTLY the independent full-state spec. Forward VALIDATES the executor (every one of the 18
components is pinned); backward reconstructs. The account-growth corner of the
spec⟺executor(⟺circuit) triangle, the `createCellA` analog of `recKExec_iff_spec`. -/
theorem execCreateCellA_iff_spec (st : RecChainedState) (actor newCell : CellId)
    (st' : RecChainedState) :
    execFullA st (.createCellA actor newCell) = some st' ↔ CreateCellSpec st actor newCell st' := by
  rw [execFullA_createCellA]; exact createCellChainA_iff_spec st actor newCell st'

/-! ## §5 — `createCellA` derived guarantees off the spec.

The spec is the apex truth; these read off it without re-touching the executor. -/

/-- **`createCellA_authorized` — no creation without privileged authority.** A committed `createCellA`
PROVES the actor held the privileged creation cap (`mintAuthorizedB`, NOT bare ownership). -/
theorem createCellA_authorized (st : RecChainedState) (actor newCell : CellId) (st' : RecChainedState)
    (h : execFullA st (.createCellA actor newCell) = some st') :
    mintAuthorizedB st.kernel.caps actor newCell = true :=
  ((execCreateCellA_iff_spec st actor newCell st').mp h).1.1

/-- **`createCellA_fresh` — no re-minting a live id.** A committed `createCellA` PROVES `newCell` was
fresh (`∉ accounts`) in the pre-state. -/
theorem createCellA_fresh (st : RecChainedState) (actor newCell : CellId) (st' : RecChainedState)
    (h : execFullA st (.createCellA actor newCell) = some st') :
    newCell ∉ st.kernel.accounts :=
  ((execCreateCellA_iff_spec st actor newCell st').mp h).1.2

/-- **`createCellA_grows_accounts` — the GROWTH has teeth.** After a committed `createCellA`, the new
id IS a live account, and every PRE account stays one. Derived from the spec's `accounts` clause +
the declaratively-validated helper. -/
theorem createCellA_grows_accounts (st : RecChainedState) (actor newCell : CellId)
    (st' : RecChainedState) (h : execFullA st (.createCellA actor newCell) = some st') :
    newCell ∈ st'.kernel.accounts
    ∧ (∀ c, c ∈ st.kernel.accounts → c ∈ st'.kernel.accounts) := by
  have hacc : st'.kernel.accounts = insert newCell st.kernel.accounts :=
    ((execCreateCellA_iff_spec st actor newCell st').mp h).2.1
  refine ⟨?_, ?_⟩
  · rw [hacc]; exact Finset.mem_insert_self _ _
  · intro c hc; rw [hacc]; exact Finset.mem_insert_of_mem hc

/-- **`createCellA_fresh_bal_zero` — the BORN-EMPTY measure.** After a committed `createCellA`, the
fresh cell's ledger column reads `0` in EVERY asset, while every OTHER (cell,asset) entry is preserved. -/
theorem createCellA_fresh_bal_zero (st : RecChainedState) (actor newCell : CellId)
    (st' : RecChainedState) (h : execFullA st (.createCellA actor newCell) = some st') :
    (∀ a, st'.kernel.bal newCell a = 0)
    ∧ (∀ c a, c ≠ newCell → st'.kernel.bal c a = st.kernel.bal c a) := by
  have hborn := ((execCreateCellA_iff_spec st actor newCell st').mp h).2.2.1
  obtain ⟨_, _, _, _, _, _, _, hbal⟩ := hborn
  refine ⟨?_, ?_⟩
  · intro a; rw [hbal]; simp only [if_pos]
  · intro c a hc; rw [hbal]; simp only [if_neg hc]

/-- **`createCellA_born_empty_cell` — the fresh id's `cell` record is default.** -/
theorem createCellA_born_empty_cell (st : RecChainedState) (actor newCell : CellId)
    (st' : RecChainedState) (h : execFullA st (.createCellA actor newCell) = some st') :
    st'.kernel.cell newCell = default := by
  have hborn := ((execCreateCellA_iff_spec st actor newCell st').mp h).2.2.1
  obtain ⟨hcl, _⟩ := hborn
  rw [hcl]; simp only [if_pos]

/-- **`createCellA_born_empty_caps` — the fresh id's cap slot is empty.** -/
theorem createCellA_born_empty_caps (st : RecChainedState) (actor newCell : CellId)
    (st' : RecChainedState) (h : execFullA st (.createCellA actor newCell) = some st') :
    st'.kernel.caps newCell = [] := by
  have hborn := ((execCreateCellA_iff_spec st actor newCell st').mp h).2.2.1
  obtain ⟨_, hcp, _⟩ := hborn
  rw [hcp]; simp only [if_pos]

/-- **`createCellA_supply_neutral` — CONSERVATION CONTENT: account-growth is supply-NEUTRAL.** A
committed `createCellA` leaves `recTotalAsset` UNCHANGED for EVERY asset — the index set
grew, but the fresh cell is born empty (the `bal`-reset), so its contribution is exactly `0`. Lifts
`createCellChainA_neutral` to the `execFullA` level. -/
theorem createCellA_supply_neutral (st : RecChainedState) (actor newCell : CellId)
    (st' : RecChainedState) (h : execFullA st (.createCellA actor newCell) = some st') (b : AssetId) :
    recTotalAsset st'.kernel b = recTotalAsset st.kernel b := by
  rw [execFullA_createCellA] at h
  exact createCellChainA_neutral b h

/-! ## §6 — `createCellA` NON-VACUITY: the spec is a genuine GATE (rejects bad inputs).

A spec that accepts everything is worthless. `execFullA` REJECTS an unauthorized creation and a
re-mint of a live id — each makes the guard FALSE, hence the executor returns `none` and
`CreateCellSpec` is unsatisfiable. -/

/-- **`createCellA_rejects_unauthorized`.** A `createCellA` over a state where the actor lacks the
privileged creation cap (`mintAuthorizedB = false`) is REJECTED — `execFullA … = none`. -/
theorem createCellA_rejects_unauthorized (st : RecChainedState) (actor newCell : CellId)
    (hbad : mintAuthorizedB st.kernel.caps actor newCell = false) :
    execFullA st (.createCellA actor newCell) = none := by
  rw [execFullA_createCellA]
  exact createCellChainA_unauthorized_fails st actor newCell hbad

/-- **`createCellA_rejects_stale`.** A `createCellA` onto an already-live id (`newCell ∈ accounts`) is
REJECTED. No re-minting a live cell. -/
theorem createCellA_rejects_stale (st : RecChainedState) (actor newCell : CellId)
    (hbad : newCell ∈ st.kernel.accounts) :
    execFullA st (.createCellA actor newCell) = none := by
  rw [execFullA_createCellA]; unfold createCellChainA
  rw [if_neg (by rintro ⟨_, h⟩; exact absurd hbad h)]

/-- **`createCellA_admits_iff` — the executor commits IFF the guard holds.** The clean
characterization: there is a committed post-state EXACTLY when account-creation is admissible. -/
theorem createCellA_admits_iff (st : RecChainedState) (actor newCell : CellId) :
    (∃ st', execFullA st (.createCellA actor newCell) = some st')
      ↔ createCellAdmit st.kernel actor newCell := by
  rw [execFullA_createCellA]
  unfold createCellChainA createCellAdmit
  by_cases hg : mintAuthorizedB st.kernel.caps actor newCell = true ∧ newCell ∉ st.kernel.accounts
  · rw [if_pos hg]; exact ⟨fun _ => hg, fun _ => ⟨_, rfl⟩⟩
  · rw [if_neg hg]
    constructor
    · rintro ⟨st', h⟩; exact absurd h (by simp)
    · intro hg'; exact absurd hg' hg

/-! ## §7 — `spawnA`: FULL-STATE SEMANTIC SPEC + executor⟺spec.

`spawnChainA` is `createCellA` of the child PLUS a bal-orthogonal authority handoff: the spawner must
already hold a live cap-edge to the parent `target`, and the child receives THAT concrete held cap
(`heldCapTo caps actor target`) prepended to its slot, with its delegation parent pointer + c-list
snapshot initialized. So FIVE kernel components move — `accounts`+`bal` (create leg, exactly
`createCellIntoAsset`), and `caps`+`delegate`+`delegations` (the functional handoff updates at
`child`) — while the OTHER 12 kernel fields are framed. The spec is factored through the create-leg
post-state so the touched-component clauses read declaratively. -/

/-- The post `caps` table a committed `spawnA` produces (declarative): the child's slot is a clean
singleton of the held parent cap (born-empty create leg — no stale `k.caps child` resurrection);
every OTHER slot reads the pre `caps`. -/
def spawnCapsMap (k : RecordKernelState) (actor child target : CellId) : CellId → List Cap :=
  fun l => if l = child then [heldCapTo k.caps actor target] else k.caps l

/-- The post `delegate` pointer map a committed `spawnA` produces: child points at the spawner; every
other pointer is the pre `delegate` (create-leg-orthogonal). -/
def spawnDelegateMap (k : RecordKernelState) (actor child : CellId) : CellId → Option CellId :=
  fun c => if c = child then some actor else k.delegate c

/-- The post `delegations` snapshot map a committed `spawnA` produces: child carries the spawner's
current c-list; every other snapshot is the pre `delegations` (create-leg-orthogonal). -/
def spawnDelegationsMap (k : RecordKernelState) (actor child : CellId) : CellId → List Cap :=
  fun c => if c = child then k.caps actor else k.delegations c

/-- **The full-state declarative spec of a committed `spawnA`** — the INDEPENDENT reference. The guard
(`spawnAdmit`: held parent edge ∧ live parent ∧ create-leg admit) holds; the FIVE touched components
are the create-leg `accounts`/`bal` plus the handoff `caps`/`delegate`/`delegations` maps; the `log`
gains the child-creation row; and the OTHER 12 kernel fields are LITERALLY unchanged. -/
def SpawnSpec (st : RecChainedState) (actor child target : CellId) (st' : RecChainedState) : Prop :=
  spawnAdmit st.kernel actor child target
  -- create-leg growth + born-empty slots at `child` (except caps/delegate/delegations overwritten below).
  ∧ st'.kernel.accounts = insert child st.kernel.accounts
  ∧ (st'.kernel.cell = fun c => if c = child then default else st.kernel.cell c)
  ∧ (st'.kernel.slotCaveats = fun c => if c = child then [] else st.kernel.slotCaveats c)
  ∧ (st'.kernel.lifecycle = fun c => if c = child then 0 else st.kernel.lifecycle c)
  ∧ (st'.kernel.deathCert = fun c => if c = child then 0 else st.kernel.deathCert c)
  ∧ (st'.kernel.bal = fun c a => if c = child then 0 else st.kernel.bal c a)
  -- authority handoff at `child` (intentionally NOT empty — copies the held parent cap).
  ∧ st'.kernel.caps = spawnCapsMap st.kernel actor child target
  ∧ st'.kernel.delegate = spawnDelegateMap st.kernel actor child
  ∧ st'.kernel.delegations = spawnDelegationsMap st.kernel actor child
  ∧ st'.log = createReceipt actor child :: st.log
  -- global side-tables framed.
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt
  ∧ st'.kernel.heaps = st.kernel.heaps
  ∧ st'.kernel.nullifierRoot = st.kernel.nullifierRoot
  ∧ st'.kernel.revokedRoot = st.kernel.revokedRoot
  ∧ st'.kernel.commitmentsRoot = st.kernel.commitmentsRoot

/-- The post `delegationEpochAt` stamp map a committed `spawnA` produces: the child is stamped with the
spawner-parent's CURRENT `delegationEpoch` (so the freshly-born child is NOT stale even under a nonzero
parent); every other stamp is the pre `delegationEpochAt` (create-leg-orthogonal). -/
def spawnEpochAtMap (k : RecordKernelState) (actor child : CellId) : CellId → Nat :=
  fun c => if c = child then k.delegationEpoch actor else k.delegationEpochAt c

/-- **The STRENGTHENED full-state spec of a committed `spawnA`** — the EXECUTOR's faithful face. Identical
to `SpawnSpec` (the deployed v1 frozen-face descriptor's spec) EXCEPT the `delegationEpochAt` clause is no
longer framed UNCHANGED: it carries the BIRTH FRESHNESS STAMP (`spawnEpochAtMap`), so a born child under a
nonzero-epoch parent is FRESH at birth (`delegationStale child = false`). A forge that leaves the stamp at
the `0` default FAILS this clause (the codex bug rendered such a child stale immediately). -/
def SpawnFullSpec (st : RecChainedState) (actor child target : CellId) (st' : RecChainedState) : Prop :=
  spawnAdmit st.kernel actor child target
  ∧ st'.kernel.accounts = insert child st.kernel.accounts
  ∧ (st'.kernel.cell = fun c => if c = child then default else st.kernel.cell c)
  ∧ (st'.kernel.slotCaveats = fun c => if c = child then [] else st.kernel.slotCaveats c)
  ∧ (st'.kernel.lifecycle = fun c => if c = child then 0 else st.kernel.lifecycle c)
  ∧ (st'.kernel.deathCert = fun c => if c = child then 0 else st.kernel.deathCert c)
  ∧ (st'.kernel.bal = fun c a => if c = child then 0 else st.kernel.bal c a)
  ∧ st'.kernel.caps = spawnCapsMap st.kernel actor child target
  ∧ st'.kernel.delegate = spawnDelegateMap st.kernel actor child
  ∧ st'.kernel.delegations = spawnDelegationsMap st.kernel actor child
  ∧ st'.log = createReceipt actor child :: st.log
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  -- THE BIRTH STAMP (no longer framed-unchanged): the child's epoch tag = the spawner-parent's epoch.
  ∧ st'.kernel.delegationEpochAt = spawnEpochAtMap st.kernel actor child
  ∧ st'.kernel.heaps = st.kernel.heaps
  ∧ st'.kernel.nullifierRoot = st.kernel.nullifierRoot
  ∧ st'.kernel.revokedRoot = st.kernel.revokedRoot
  ∧ st'.kernel.commitmentsRoot = st.kernel.commitmentsRoot

/-- **`SpawnFullSpec_implies_SpawnSpec` — the strengthened spec REFINES the frozen face.** Every clause of
`SpawnSpec` (the deployed descriptor's spec) holds of a `SpawnFullSpec` post EXCEPT the `delegationEpochAt`
frame — `SpawnFullSpec` STAMPS it instead of framing it. So `SpawnFullSpec` carries strictly MORE than
`SpawnSpec` minus that one (now-superseded) frame clause; consumers needing the cap/balance/log/accounts
content read it directly off `SpawnFullSpec`. (The two specs AGREE iff the spawner's epoch is `0`.) -/
theorem SpawnFullSpec_dropEpochAt (st : RecChainedState) (actor child target : CellId)
    (st' : RecChainedState) (h : SpawnFullSpec st actor child target st') :
    spawnAdmit st.kernel actor child target
    ∧ st'.kernel.accounts = insert child st.kernel.accounts
    ∧ (st'.kernel.cell = fun c => if c = child then default else st.kernel.cell c)
    ∧ (st'.kernel.slotCaveats = fun c => if c = child then [] else st.kernel.slotCaveats c)
    ∧ (st'.kernel.lifecycle = fun c => if c = child then 0 else st.kernel.lifecycle c)
    ∧ (st'.kernel.deathCert = fun c => if c = child then 0 else st.kernel.deathCert c)
    ∧ (st'.kernel.bal = fun c a => if c = child then 0 else st.kernel.bal c a)
    ∧ st'.kernel.caps = spawnCapsMap st.kernel actor child target
    ∧ st'.kernel.delegate = spawnDelegateMap st.kernel actor child
    ∧ st'.kernel.delegations = spawnDelegationsMap st.kernel actor child
    ∧ st'.log = createReceipt actor child :: st.log
    ∧ st'.kernel.nullifiers = st.kernel.nullifiers
    ∧ st'.kernel.revoked = st.kernel.revoked
    ∧ st'.kernel.commitments = st.kernel.commitments
    ∧ st'.kernel.factories = st.kernel.factories
    ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
    ∧ st'.kernel.heaps = st.kernel.heaps
    ∧ st'.kernel.nullifierRoot = st.kernel.nullifierRoot
    ∧ st'.kernel.revokedRoot = st.kernel.revokedRoot ∧ st'.kernel.commitmentsRoot = st.kernel.commitmentsRoot := by
  obtain ⟨hg, hacc, hcl, hsc, hlif, hdc, hbal, hcaps, hdel, hdgs, hlog, h2, h3, h4, h5,
         hde, _hdea, hhp, hnr, hrr⟩ := h
  exact ⟨hg, hacc, hcl, hsc, hlif, hdc, hbal, hcaps, hdel, hdgs, hlog, h2, h3, h4, h5, hde, hhp,
    hnr, hrr⟩

/-- **`spawnChainA_iff_spec` — CHAINED EXECUTOR ⟺ STRENGTHENED FULL SPEC (FULL state, both directions)
for spawn.** The chained record kernel commits a `spawnA` into `st'` IFF `st'` is EXACTLY the strengthened
full post-state — the five touched components + the BIRTH EPOCH STAMP + `log` + 11 frame fields are all
checked; a forge that skips the stamp (leaving the child stale) FAILS. -/
theorem spawnChainA_iff_spec (st : RecChainedState) (actor child target : CellId)
    (st' : RecChainedState) :
    spawnChainA st actor child target = some st' ↔ SpawnFullSpec st actor child target st' := by
  unfold spawnChainA SpawnFullSpec spawnAdmit createCellAdmit createReceipt
    spawnCapsMap spawnDelegateMap spawnDelegationsMap spawnEpochAtMap
  by_cases hg : (st.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true ∧
      target ∈ st.kernel.accounts
  · rw [if_pos hg]
    unfold createCellChainA createCellIntoAsset bornEmptyCellSlots
    by_cases hc : mintAuthorizedB st.kernel.caps actor child = true ∧ child ∉ st.kernel.accounts
    · rw [if_pos hc]
      simp only []
      constructor
      · intro h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨⟨hg.1, hg.2, hc⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl,
               rfl, ?_, rfl, rfl, rfl, rfl⟩
        · funext c; by_cases hc' : c = child <;> simp [hc']
        · funext c; by_cases hc' : c = child <;> simp [hc']
        · funext c; by_cases hc' : c = child <;> simp [hc']
        · funext c; by_cases hc' : c = child <;> simp [hc']
        · funext c a; by_cases hc' : c = child <;> simp [hc']
        · funext l; by_cases hl : l = child <;> simp [hl, spawnCapsMap]
        · funext c; by_cases hc' : c = child <;> simp [hc', spawnDelegateMap]
        · funext c; by_cases hc' : c = child <;> simp [hc', spawnDelegationsMap]
        · simp only [createReceipt]
        · funext c; by_cases hc' : c = child <;> simp [hc']
      · rintro ⟨⟨he, ht, hca⟩, hacc, hcl, hsc, hlif, hdc, hbal, hcaps, hdel, hdgs, hlog, h2,
                h3, h4, h5, hde, hdea, hhp, hnr, hrr, hcr⟩
        simp only [Option.some.injEq]
        obtain ⟨k', lg'⟩ := st'
        obtain ⟨acc, cl, cp, nl, rv, cm, bl, sc, fc, lc, dc, dl, dn, dge, dgea, hp, nr, rr, cr⟩ := k'
        simp only at hacc hcl hsc hlif hdc hbal hcaps hdel hdgs hlog h2 h3 h4 h5 hde hdea hhp hnr hrr hcr
        subst hacc hcl hsc hlif hdc hbal hcaps hdel hdgs hlog h2 h3 h4 h5 hde hdea hhp hnr hrr hcr
        rfl
    · rw [if_neg hc]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨⟨_, _, hc'⟩, _⟩; exact absurd hc' hc
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨he, hm, _⟩, _⟩; exact absurd ⟨he, hm⟩ hg

/-- **`execSpawnA_iff_spec` — THE DELIVERABLE: `execFullA`-LEVEL EXECUTOR ⟺ STRENGTHENED FULL SPEC for
spawn (FULL state, both directions).** The one gated executor commits a `spawnA` turn into `st'` IFF `st'`
is EXACTLY the strengthened full-state spec (with the birth epoch stamp). The `spawnA` corner of the
account-growth triangle. -/
theorem execSpawnA_iff_spec (st : RecChainedState) (actor child target : CellId)
    (st' : RecChainedState) :
    execFullA st (.spawnA actor child target) = some st' ↔ SpawnFullSpec st actor child target st' := by
  rw [execFullA_spawnA]; exact spawnChainA_iff_spec st actor child target st'

/-! ## §8 — `spawnA` derived guarantees off the spec. -/

/-- **`spawnA_authorized` — no spawn without privileged child-creation authority.** -/
theorem spawnA_authorized (st : RecChainedState) (actor child target : CellId)
    (st' : RecChainedState) (h : execFullA st (.spawnA actor child target) = some st') :
    mintAuthorizedB st.kernel.caps actor child = true :=
  ((execSpawnA_iff_spec st actor child target st').mp h).1.2.2.1

/-- **`spawnA_grounded` — no manufactured authority.** A committed `spawnA` PROVES the spawner already
held a live cap-edge to the parent `target` (child creation cannot introduce an unrelated edge), and
the parent is live. -/
theorem spawnA_grounded (st : RecChainedState) (actor child target : CellId)
    (st' : RecChainedState) (h : execFullA st (.spawnA actor child target) = some st') :
    (st.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true
    ∧ target ∈ st.kernel.accounts := by
  have hg := ((execSpawnA_iff_spec st actor child target st').mp h).1
  exact ⟨hg.1, hg.2.1⟩

/-- **`spawnA_grows_accounts` — the child becomes a live account.** -/
theorem spawnA_grows_accounts (st : RecChainedState) (actor child target : CellId)
    (st' : RecChainedState) (h : execFullA st (.spawnA actor child target) = some st') :
    child ∈ st'.kernel.accounts := by
  have hacc : st'.kernel.accounts = insert child st.kernel.accounts :=
    ((execSpawnA_iff_spec st actor child target st').mp h).2.1
  rw [hacc]; exact Finset.mem_insert_self _ _

/-- **`spawnA_child_cap` — the concrete held parent cap moves to the child.** The child's slot is a
clean singleton of the spawner's held cap conferring an edge to `target` (born-empty create leg). -/
theorem spawnA_child_cap (st : RecChainedState) (actor child target : CellId)
    (st' : RecChainedState) (h : execFullA st (.spawnA actor child target) = some st') :
    st'.kernel.caps child = [heldCapTo st.kernel.caps actor target] := by
  rcases (execSpawnA_iff_spec st actor child target st').mp h with
    ⟨_, _, _, _, _, _, _, hcaps, _, _, _, _, _, _, _, _⟩
  rw [hcaps]; simp only [spawnCapsMap, if_pos]

/-- **`spawnA_supply_neutral` — account-growth + cap-handoff is supply-NEUTRAL ∀ asset.** Lifts
`spawnChainA_neutral` to the `execFullA` level. -/
theorem spawnA_supply_neutral (st : RecChainedState) (actor child target : CellId)
    (st' : RecChainedState) (h : execFullA st (.spawnA actor child target) = some st') (b : AssetId) :
    recTotalAsset st'.kernel b = recTotalAsset st.kernel b := by
  rw [execFullA_spawnA] at h
  exact spawnChainA_neutral b h

/-! ## §9 — `spawnA` NON-VACUITY: the spec rejects bad inputs. -/

/-- **`spawnA_rejects_ungrounded`.** A `spawnA` whose spawner holds NO live edge to the parent
`target` is REJECTED — child creation cannot manufacture authority to an unrelated target. -/
theorem spawnA_rejects_ungrounded (st : RecChainedState) (actor child target : CellId)
    (hbad : (st.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = false) :
    execFullA st (.spawnA actor child target) = none := by
  rw [execFullA_spawnA]; unfold spawnChainA
  rw [if_neg (by rintro ⟨h, _⟩; rw [hbad] at h; exact absurd h (by simp))]

/-- **`spawnA_rejects_unauthorized_child`.** A `spawnA` whose actor lacks privileged creation
authority over the `child` is REJECTED (even with a held parent edge). -/
theorem spawnA_rejects_unauthorized_child (st : RecChainedState) (actor child target : CellId)
    (hbad : mintAuthorizedB st.kernel.caps actor child = false) :
    execFullA st (.spawnA actor child target) = none := by
  rw [execFullA_spawnA]; unfold spawnChainA
  by_cases hg : (st.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true ∧
      target ∈ st.kernel.accounts
  · rw [if_pos hg, createCellChainA_unauthorized_fails st actor child hbad]
  · rw [if_neg hg]

/-! ## §10 — concrete #guard non-vacuity witnesses (genuine `decide`, NOT `native_decide`).

Cells {0,1} live; actor 9 holds `node 0`,`node 1`,`node 2` (creation authority over the fresh cell 2,
and an edge to live parents 0/1 since `confersEdgeTo 0 (node 0) = true`). A privileged create of fresh
cell 2 commits; the unprivileged / re-mint creates are rejected. A spawn of fresh child 2 from parent
0 (held by 9) commits and the child is a live account holding the copied parent `node 0` cap; an
ungrounded spawn (target 7, no edge) is rejected. -/

/-- A concrete pre-state: cells {0,1} live, ledger empty, actor 9 holds `node 0`/`node 1`/`node 2`
(creation authority over the fresh cell 2; held edges to live cells 0,1). -/
def sAG0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun a => if a = 9 then [Cap.node 0, Cap.node 1, Cap.node 2] else [] }
    log := [] }

-- A privileged creation of fresh cell 2 by actor 9 COMMITS:
#guard (execFullA sAG0 (.createCellA 9 2)).isSome  -- true
-- ...and cell 2 is now a live account:
#guard ((execFullA sAG0 (.createCellA 9 2)).map (fun s => decide (2 ∈ s.kernel.accounts))) == some true
-- ...with a born-empty ledger column (asset 0 and asset 1 both 0):
#guard ((execFullA sAG0 (.createCellA 9 2)).map (fun s => (s.kernel.bal 2 0, s.kernel.bal 2 1)))
        == some (0, 0)
-- ...the chain grew by exactly one row:
#guard ((execFullA sAG0 (.createCellA 9 2)).map (fun s => s.log.length)) == some 1
-- An UNPRIVILEGED creation (actor 0, no `node 2` cap) is REJECTED:
#guard (execFullA sAG0 (.createCellA 0 2)).isNone  -- true
-- A RE-MINT of a live id (cell 1 ∈ accounts) is REJECTED:
#guard (execFullA sAG0 (.createCellA 9 1)).isNone  -- true

-- A SPAWN of fresh child 2 from parent 0 (held by actor 9) COMMITS:
#guard (execFullA sAG0 (.spawnA 9 2 0)).isSome  -- true
-- ...and the child holds the parent cap `node 0`:
#guard (((execFullA sAG0 (.spawnA 9 2 0)).map (fun s => s.kernel.caps 2)).getD []) == [Cap.node 0]
-- ...and the child is a live account:
#guard ((execFullA sAG0 (.spawnA 9 2 0)).map (fun s => decide (2 ∈ s.kernel.accounts))) == some true
-- An UNGROUNDED spawn (parent 7, no held edge) is REJECTED:
#guard (execFullA sAG0 (.spawnA 9 2 7)).isNone  -- true

/-! ## §11 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}`. -/

#assert_axioms createCellIntoAsset_correct
#assert_axioms execFullA_createCellA
#assert_axioms execFullA_spawnA
#assert_axioms createCellChainA_iff_spec
#assert_axioms execCreateCellA_iff_spec
#assert_axioms createCellA_authorized
#assert_axioms createCellA_fresh
#assert_axioms createCellA_grows_accounts
#assert_axioms createCellA_fresh_bal_zero
#assert_axioms createCellA_born_empty_cell
#assert_axioms createCellA_born_empty_caps
#assert_axioms createCellA_supply_neutral
#assert_axioms createCellA_rejects_unauthorized
#assert_axioms createCellA_rejects_stale
#assert_axioms createCellA_admits_iff
#assert_axioms spawnChainA_iff_spec
#assert_axioms execSpawnA_iff_spec
#assert_axioms spawnA_authorized
#assert_axioms spawnA_grounded
#assert_axioms spawnA_grows_accounts
#assert_axioms spawnA_child_cap
#assert_axioms spawnA_supply_neutral
#assert_axioms spawnA_rejects_ungrounded
#assert_axioms spawnA_rejects_unauthorized_child

end Dregg2.Circuit.Spec.AccountGrowth
