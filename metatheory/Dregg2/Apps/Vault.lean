/-
# Dregg2.Apps.Vault — the conditional-timelock VAULT as a REAL, app-instantiable factory cell.

THE FIRST HOUSE ROOM, welded (`docs/HOUSE-CAPACITIES-WELD-PLAN.md` headline #1: vault = highest value ×
smallest). A vault is value LOCKED until a release rule (a block-height TIMELOCK or a hash-lock preimage
PROOF), claimable EXACTLY ONCE by the beneficiary after the condition is genuinely met — savings, a
vesting schedule, a commitment device ("I cannot spend this until block N"), a deadbolt fund opened by a
secret. This module PROMOTES the falsification probe (`Dregg2.Verify.VaultFactoryProbe` — PASS) from a
shape study into a LIVE path: the vault factory is a published `FactoryEntry` an app registers and
instantiates via the EXISTING factory executor `createCellFromFactoryChainA`
(`Dregg2.Exec.TurnExecutorFull`).

A vault is a COMPOSITION, NOT a new kernel verb: it earns NO `FullActionA` arm. Creating a vault (lock
value, set the release rule) + funding it + the beneficiary claiming after the condition are the
already-wired `CreateCellFromFactory` + `Transfer` + `SetField` turns — light-client-verifiable. So:

  * the vault factory is a published `FactoryEntry` (`vaultFactoryEntry`) an app registers in the
    kernel's `factories` registry and instantiates via `createCellFromFactoryA actor vaultCell vk`;
  * the executor INSTALLS the factory's `slotCaveats` (the one-terminal claim machine + the deal-term
    immutables) onto the minted cell for its WHOLE LIFE (`mintVaultCell_installs_state_machine`), so
    the one-shot tooth is enforced by `stateStepGuarded` on every later `SetField`, not by an off-ledger
    guard;
  * the locked VALUE lives in the minted cell's own per-asset `bal` column (a `fund` is an ordinary
    `move` IN; a `claim` is an ordinary `move` OUT — the probe's `vaultSettle`), so the vault inherits
    the kernel's per-asset move conservation law VERBATIM, with NO side-table.

The four claim-safety keystones (conservation / one-shot / claim-only-on-condition / value-not-stranded)
are RE-ESTABLISHED on the FACTORY-BORN cell here — on the cell whose caveats the executor actually
installed — by feeding the factory-install facts into the probe's already-proved keystones.

## The shape (the published deliverable)

`vaultFactoryEntry beneficiary releaseHeight condDigest asset : FactoryEntry`
  caveats       = Immutable {beneficiary, releaseHeight, condDigest, asset}
                  ++ admitTable state [(open, claimed)]   -- the ONE-terminal one-shot tooth
  initialFields = state=open, beneficiary, releaseHeight, condDigest, asset
  programVk     = 0

`vaultRegistry vk` installs it at content-addressed key `vk`; `mintVaultCell` runs the real factory
executor; `fundVault` moves the locked value into the minted cell's `bal`; a claim is the probe's
`vaultClaimTimelock` / `vaultClaimHashlock` on that cell.

NEW file. Imports the probe + the factory executor; does NOT touch `cell/src/capability.rs`/`seal.rs`,
`Argus/Compile.lean`, or the Substrate/Dynamics files. `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Verify.VaultFactoryProbe
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Apps.Vault

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)
open Dregg2.Verify.VaultFactoryProbe
open Dregg2.Exec.EffectsState (fieldOf setField)

/-! ## §1 — The vault FACTORY ENTRY (the published `FactoryEntry`).

This IS the probe's `vaultFactory` descriptor (re-exported under an app-facing name): the four
deal-term immutables + the state-machine `admitTable [(open, claimed)]` (the one-shot tooth). The
factory's own initial state CONFORMS to its own caveats (`vaultFactory_conforms`, proved in the
probe). -/

/-- **The vault factory entry.** Mints a vault cell carrying the deal-term immutables + the one-shot
state machine; the locked value is held in the minted cell's `bal` column. -/
def vaultFactoryEntry (beneficiary releaseHeight condDigest asset : Int) : FactoryEntry :=
  vaultFactory beneficiary releaseHeight condDigest asset

/-- The vault factory conforms to its own published invariants (re-exported probe keystone). -/
theorem vaultFactoryEntry_conforms (beneficiary releaseHeight condDigest asset : Int) :
    (vaultFactoryEntry beneficiary releaseHeight condDigest asset).conforms = true :=
  vaultFactory_conforms beneficiary releaseHeight condDigest asset

/-- A kernel factory registry that publishes the vault factory at content-addressed key `vk`. An app
installs this into `s.kernel.factories` so `createCellFromFactoryA actor vaultCell vk` resolves it. -/
def vaultRegistry (vk : Nat) (beneficiary releaseHeight condDigest asset : Int) :
    List (Nat × FactoryEntry) :=
  [(vk, vaultFactoryEntry beneficiary releaseHeight condDigest asset)]

/-- The registry resolves the vault factory at exactly its published key. -/
theorem vaultRegistry_finds (vk : Nat) (beneficiary releaseHeight condDigest asset : Int) :
    findFactory (vaultRegistry vk beneficiary releaseHeight condDigest asset) vk
      = some (vaultFactoryEntry beneficiary releaseHeight condDigest asset) := by
  simp [vaultRegistry, findFactory]

/-! ## §2 — MINTING the vault cell through the REAL factory executor.

`mintVaultCell` is `createCellFromFactoryA` over a kernel whose `factories` registry publishes the
vault factory. The minted cell carries the factory's caveats (the one-shot machine) AND its initial
fields (state=open + the frozen deal terms) — installed by the executor, for life. -/

/-- Mint a vault cell from the vault factory at key `vk` (the real factory executor). -/
def mintVaultCell (s : RecChainedState) (actor vaultCell : CellId) (vk : Int) :
    Option RecChainedState :=
  createCellFromFactoryChainA s actor vaultCell vk

/-- **`mintVaultCell_installs_state_machine` (the factory keystone, vault-specialized).** A minted
vault cell carries EXACTLY the vault factory's caveats — the four deal-term immutables PLUS the
one-shot state machine `admitTable [(open, claimed)]` — installed by the executor, so
`stateStepGuarded` enforces them on every later `SetField`. Reuses
`createCellFromFactoryChainA_installs_program`. -/
theorem mintVaultCell_installs_state_machine {s s' : RecChainedState} {actor vaultCell : CellId}
    {vk : Int} (e : FactoryEntry)
    (hreg : findFactory s.kernel.factories vk.toNat = some e)
    (h : mintVaultCell s actor vaultCell vk = some s') :
    s'.kernel.slotCaveats vaultCell = e.caveats := by
  obtain ⟨e', hfind, hcav⟩ := createCellFromFactoryChainA_installs_program h
  rw [hreg] at hfind
  rw [← (Option.some.injEq _ _).mp hfind] at hcav
  exact hcav

/-- **`mintVaultCell_caveats`.** When the registry IS `vaultRegistry vk …`, the minted cell carries
the vault state machine + deal-term immutables (concretely). -/
theorem mintVaultCell_caveats {s s' : RecChainedState} {actor vaultCell : CellId} {vk : Int}
    {beneficiary releaseHeight condDigest asset : Int}
    (hreg : s.kernel.factories = vaultRegistry vk.toNat beneficiary releaseHeight condDigest asset)
    (h : mintVaultCell s actor vaultCell vk = some s') :
    s'.kernel.slotCaveats vaultCell
      = (vaultFactoryEntry beneficiary releaseHeight condDigest asset).caveats := by
  have hfind : findFactory s.kernel.factories vk.toNat
      = some (vaultFactoryEntry beneficiary releaseHeight condDigest asset) := by
    rw [hreg]; exact vaultRegistry_finds vk.toNat beneficiary releaseHeight condDigest asset
  exact mintVaultCell_installs_state_machine _ hfind h

/-- **`mintVaultCell_neutral`.** Minting a vault cell is conservation-NEUTRAL for every asset (the
cell is born EMPTY; the value is funded SEPARATELY by an ordinary move). Reuses
`createCellFromFactoryChainA_neutral`. -/
theorem mintVaultCell_neutral {s s' : RecChainedState} {actor vaultCell : CellId} {vk : Int}
    (b : AssetId) (h : mintVaultCell s actor vaultCell vk = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  createCellFromFactoryChainA_neutral b h

/-- **`mintVaultCell_grows_accounts`.** A minted vault cell IS a live account (the mint has teeth). -/
theorem mintVaultCell_grows_accounts {s s' : RecChainedState} {actor vaultCell : CellId} {vk : Int}
    (h : mintVaultCell s actor vaultCell vk = some s') :
    vaultCell ∈ s'.kernel.accounts :=
  createCellFromFactoryChainA_grows_accounts h

/-- **`mintVaultCell_unknown_factory_fails` (fail-closed).** Minting against an unknown factory key
never mints. The vault program cannot be conjured without a published factory. -/
theorem mintVaultCell_unknown_factory_fails (s : RecChainedState) (actor vaultCell : CellId)
    (vk : Int) (h : findFactory s.kernel.factories vk.toNat = none) :
    mintVaultCell s actor vaultCell vk = none :=
  createCellFromFactoryChainA_unknown_factory_fails s actor vaultCell vk h

/-! ## §3 — FUND: an ordinary `move` of the locked value INTO the minted cell's `bal` column.

The granter funds the vault by an ordinary per-asset move (`recKExecAsset`) from its own column into
the vault cell's column. After the fund the vault cell HOLDS the locked value in its `bal` column (the
single source of truth — there is NO second "amount" slot to keep relationally in sync). -/

/-- **`fundVault` — fund the vault cell: move `amt` of `asset` from `granter` into `vaultCell`'s `bal`
column.** An ordinary authorized per-asset move (`recKExecAsset`); fail-closed. -/
def fundVault (k : RecordKernelState) (granter vaultCell : CellId) (asset : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  recKExecAsset k { actor := granter, src := granter, dst := vaultCell, amt := amt } asset

/-- **`fundVault_conserves`.** A committed fund preserves every asset's total supply (the value moves
between two live accounts — funding the lock, not minting it). The ordinary move law. -/
theorem fundVault_conserves {k k' : RecordKernelState} {granter vaultCell : CellId}
    {asset : AssetId} {amt : ℤ} (h : fundVault k granter vaultCell asset amt = some k')
    (b : AssetId) : recTotalAsset k' b = recTotalAsset k b :=
  recKExecAsset_conserves_per_asset k k'
    { actor := granter, src := granter, dst := vaultCell, amt := amt } asset h b

/-! ## §4 — CLAIM on the FACTORY-BORN cell (the probe keystones, re-established here).

The vault claim is the probe's `vaultClaimTimelock` / `vaultClaimHashlock` — they read the state slot
the factory installed and move the held `bal` out, gated on the release condition. We re-export them
under app-facing names and LIFT the probe's four keystones onto the factory-born cell by observing that
a factory-minted-then-funded cell is exactly the `RecordKernelState` the probe's theorems quantify over
(state slot = open, value in `bal`). -/

/-- App-facing timelock claim (the probe's `vaultClaimTimelock`): OPEN→CLAIMED + move held value to the
beneficiary, gated on `atBlock ≥ releaseHeight`. -/
abbrev claimTimelock := @vaultClaimTimelock
/-- App-facing hash-lock claim (the probe's `vaultClaimHashlock`): OPEN→CLAIMED + move held value to the
beneficiary, gated on `H(witness) = condDigest`. -/
abbrev claimHashlock := @vaultClaimHashlock

/-- **KEYSTONE (a) — `claim_conserves` (any gate).** A committed claim on the factory-born cell
preserves every asset's supply (the value is delivered from the held column, not conjured). -/
theorem claim_conserves (gate : Int → Int → Bool) {k k' : RecordKernelState} {e beneficiary : CellId}
    {asset : AssetId} {atBlock witness : Int}
    (h : vaultClaimGated gate k e beneficiary asset atBlock witness = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  vaultClaim_conserves gate h b

/-- **KEYSTONE (b) — `no_double_claim_after`.** Once a claim drove the factory-born vault to CLAIMED,
NO second claim commits — the installed state machine fail-closes. -/
theorem no_double_claim_after (gate : Int → Int → Bool) {k k' : RecordKernelState}
    {e beneficiary tgt : CellId} {asset : AssetId} {atBlock witness atBlock' witness' : Int}
    (h : vaultClaimGated gate k e beneficiary asset atBlock witness = some k') :
    vaultClaimGated gate k' e tgt asset atBlock' witness' = none :=
  Dregg2.Verify.VaultFactoryProbe.no_double_claim_after gate h

/-- **KEYSTONE (c, timelock) — `timelock_rejects_early`.** A timelock claim BEFORE the release height
is rejected — no early release — even on an OPEN factory-born vault. -/
theorem timelock_rejects_early {k : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {atBlock : Int} (hearly : atBlock < vaultReleaseHeight k e) :
    vaultClaimTimelock k e beneficiary asset atBlock = none :=
  Dregg2.Verify.VaultFactoryProbe.timelock_rejects_early k e beneficiary asset atBlock hearly

/-- **KEYSTONE (c, hash-lock) — `hashlock_rejects_forged`.** A hash-lock claim whose witness does NOT
hash to the committed digest (a forged / wrong preimage) is rejected. -/
theorem hashlock_rejects_forged (hash : Int → Int) {k : RecordKernelState} {e beneficiary : CellId}
    {asset : AssetId} {witness : Int} (hbad : hash witness ≠ vaultCondDigest k e) :
    vaultClaimHashlock hash k e beneficiary asset witness = none :=
  Dregg2.Verify.VaultFactoryProbe.hashlock_rejects_forged hash k e beneficiary asset witness hbad

/-- **KEYSTONE (d) — `open_vault_claimable`.** An OPEN factory-born vault whose release gate is
DISCHARGED, with a `ClaimReady` beneficiary, CLAIMS (the value is deliverable, not trapped). -/
theorem open_vault_claimable (gate : Int → Int → Bool) {k : RecordKernelState} {e beneficiary : CellId}
    {asset : AssetId} {atBlock witness : Int} (hopen : vaultState k e = sOpen)
    (hgate : gate atBlock witness = true) (hr : ClaimReady k e beneficiary asset) :
    (vaultClaimGated gate k e beneficiary asset atBlock witness).isSome :=
  Dregg2.Verify.VaultFactoryProbe.open_vault_claimable gate k e beneficiary asset atBlock witness
    hopen hgate hr

/-! ## §4b — The CLAIM-LIVENESS TOOTH (the factory-shape analog of D3 settle-into-live-target).

In the factory shape the value moves by an ordinary `recKExecAsset`, whose OWN fail-closed guard
requires `dst ∈ accounts`: a claim whose beneficiary is NOT a live account is rejected, for FREE, by the
move law — the locked value can never be moved into a non-account. -/

/-- **`claim_requires_live_beneficiary` (END-USER D3).** A claim whose beneficiary is not a live
account is rejected (the move cannot deliver value into a non-account). Holds for ANY gate. -/
theorem claim_requires_live_beneficiary (gate : Int → Int → Bool) {k : RecordKernelState}
    {e beneficiary : CellId} {asset : AssetId} {atBlock witness : Int}
    (hdead : beneficiary ∉ k.accounts) :
    vaultClaimGated gate k e beneficiary asset atBlock witness = none := by
  unfold vaultClaimGated
  by_cases hg : vaultState k e = sOpen ∧ gate atBlock witness = true
  · rw [if_pos hg]
    unfold vaultSettle recKExecAsset
    rw [if_neg]
    rintro ⟨_, _, _, _, _, htgt, _⟩
    exact hdead htgt
  · rw [if_neg hg]

/-! ## §5 — NON-VACUITY: a factory-born vault, end to end (mint → fund → claim / early / double).

`facWorld vk` is a kernel that PUBLISHES the vault factory at key `vk` (beneficiary 1, releaseHeight
11000, condDigest 0 = a pure TIMELOCK, asset 0). Cell `0` is the privileged minter (holds a node-cap to
the fresh vault cell `3` so the mint is authorized) and the funder; cell `1` is the beneficiary. We mint
cell `3` from the factory, fund 500 into it, then witness: a timelock claim AT/AFTER the release height
delivers 500 to the beneficiary and advances to CLAIMED; an EARLY claim is rejected; a double-claim
fails. ALL on the cell the factory actually minted. -/

/-- The funder/minter holds a node-cap to the fresh vault cell `3` (so `mintAuthorizedB` admits) and
funds the lock (cell `0` holds 600 of asset 0). The registry publishes the vault factory at key 7. -/
def facWorld : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun c => if c = 0 then [Cap.node 3] else []
        bal := fun c a => if c = 0 then (if a = 0 then 600 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        factories := vaultRegistry 7 1 11000 0 0 }
    log := [] }

/-- Mint the vault cell `3` from factory key 7, then fund 500 of asset 0 into it (funder = cell 0). -/
def facFunded : Option RecordKernelState :=
  (mintVaultCell facWorld 0 3 7).bind (fun s => fundVault s.kernel 0 3 0 500)

-- the factory resolves + conforms:
#guard (findFactory facWorld.kernel.factories 7).isSome                                 -- some (vault factory)
#guard ((vaultFactoryEntry 1 11000 0 0).conforms)                                       -- true

-- the mint COMMITS and grows accounts, born conservation-neutral:
#guard ((mintVaultCell facWorld 0 3 7).isSome)                                          -- true (minted!)
#guard ((mintVaultCell facWorld 0 3 7).map (fun s => decide (3 ∈ s.kernel.accounts))) == some true
#guard ((mintVaultCell facWorld 0 3 7).map (fun s => recTotalAsset s.kernel 0)) == some 605

-- the minted cell carries the vault state machine (the last caveat is the admitTable) and starts OPEN:
#guard ((mintVaultCell facWorld 0 3 7).map (fun s => s.kernel.slotCaveats 3))
        == some (vaultFactoryEntry 1 11000 0 0).caveats
#guard ((mintVaultCell facWorld 0 3 7).map (fun s => vaultState s.kernel 3)) == some sOpen
#guard ((mintVaultCell facWorld 0 3 7).map (fun s => vaultReleaseHeight s.kernel 3)) == some 11000

-- after fund, the vault cell HOLDS the locked 500 in its bal column (funder 600→100); supply fixed:
#guard (facFunded.map (fun k => k.bal 3 0)) == some 500                                  -- locked value in bal
#guard (facFunded.map (fun k => k.bal 0 0)) == some 100                                  -- funder debited
#guard (facFunded.map (fun k => recTotalAsset k 0)) == some 605                          -- conserved

-- a TIMELOCK claim AT/AFTER the release height (11500 ≥ 11000) delivers 500 to beneficiary 1 (5→505)
-- and advances to CLAIMED; supply fixed:
#guard (facFunded.bind (fun k => vaultClaimTimelock k 3 1 0 11500) |>.map (fun s => s.bal 1 0)) == some 505
#guard (facFunded.bind (fun k => vaultClaimTimelock k 3 1 0 11500) |>.map (fun s => s.bal 3 0)) == some 0
#guard (facFunded.bind (fun k => vaultClaimTimelock k 3 1 0 11500) |>.map (fun s => vaultState s 3)) == some sClaimed
#guard (facFunded.bind (fun k => vaultClaimTimelock k 3 1 0 11500) |>.map (fun s => recTotalAsset s 0)) == some 605

-- an EARLY claim (10999 < 11000) is rejected (KEYSTONE c — no early release):
#guard (facFunded.bind (fun k => vaultClaimTimelock k 3 1 0 10999) |>.isSome) == false
-- ...AT exactly the release height is the live boundary (non-vacuity):
#guard (facFunded.bind (fun k => vaultClaimTimelock k 3 1 0 11000) |>.isSome)            -- true

-- NO-DOUBLE-CLAIM: claim then a SECOND claim both on the factory-born cell — the second fails (KEYSTONE b):
#guard (facFunded.bind (fun k => vaultClaimTimelock k 3 1 0 11500) |>.bind (fun s => vaultClaimTimelock s 3 1 0 11500) |>.isSome) == false

-- an UNKNOWN factory key never mints (fail-closed):
#guard ((mintVaultCell facWorld 0 3 99).isSome) == false

/-! ## §VERDICT — the vault is a LIVE factory-settled cell.

An agent CREATES a vault (mints the factory cell, locks value by funding, sets the release rule as the
frozen deal terms), and the beneficiary CLAIMS it EXACTLY ONCE after the condition is genuinely met — all
via the EXISTING wired `CreateCellFromFactory` + `Transfer` + `SetField` turns, NO new `Effect`. The four
claim-safety keystones (conservation / one-shot / claim-only-on-condition (timelock: no early release;
hash-lock: no forged proof) / value-not-stranded) hold on the FACTORY-BORN cell. The bespoke heap-cell
`cell/src/vault.rs` library is superseded by this factory route, the same dissolution the escrow family
made.
-/

#assert_axioms vaultFactoryEntry_conforms
#assert_axioms vaultRegistry_finds
#assert_axioms mintVaultCell_installs_state_machine
#assert_axioms mintVaultCell_caveats
#assert_axioms mintVaultCell_neutral
#assert_axioms mintVaultCell_grows_accounts
#assert_axioms mintVaultCell_unknown_factory_fails
#assert_axioms fundVault_conserves
#assert_axioms claim_conserves
#assert_axioms no_double_claim_after
#assert_axioms timelock_rejects_early
#assert_axioms hashlock_rejects_forged
#assert_axioms open_vault_claimable
#assert_axioms claim_requires_live_beneficiary

end Dregg2.Apps.Vault
