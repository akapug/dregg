/-
# Dregg2.Apps.Identity — the IDENTITY app as a verified cell-program: REVOKED STAYS REVOKED, FOREVER.

dregg1's identity / verifiable-credential app (`credentials/src/{issuance,revocation,verification}.rs`)
is a three-verb protocol: **issue** mints a credential carrying a stable 32-byte id
(`blake3(encoded)`, `issuance.rs:127`); **revoke** inserts that id into an issuer-side grow-only
`RevocationRegistry` — a `HashSet<[u8;32]>` that is **insert-only** (`revoke()`, `revocation.rs:224`
only `.insert`s, never removes) — and republishes a root commitment; **present/verify** admits a
credential ONLY when a real non-membership check passes (`verify_non_revocation`, `revocation.rs:199`:
recompute-root → match-expected → check the id is *absent* from the committed set; on presence it
returns `NonRevocationError::Revoked` and `verify` rejects, `verification.rs:257`). The verifier never
trusts a self-asserted `revoked` boolean — it checks genuine absence against the committed set.

The **headline safety** the whole protocol exists to guarantee — the one the grow-only registry buys —
is **permanent revocation**: *once an identity's credential is revoked, it can NEVER be re-validated.*
Because the registry only grows, a revoked id stays in the committed set for all time, so every future
non-membership check fails-closed (`Revoked`). dregg2 already models the registry as the kernel-state
`s.kernel.revoked : List Nat` (`RecordKernel.lean`, hole #3 / `#139`, `self.revocation_channel` — the
MDB/derivation-table root `cap_revoke` tears down; single-machine ⇒ immediate revocation) and the
verifier's negative-discharge leg as `FullForestAuth.revocationGate` (`gateOK = … && revocationGate`,
`revocationGate na s = !(s.kernel.revoked.contains na.credNul)`), with the per-step teeth
`FullForestAuth.gateOK_revoked_fails` (a revoked credential's gate fail-closes). This module lifts that
ONE-STEP teeth to the **coinductive living cell** over the SHIPPED executor and carries it FOREVER.

The construction mirrors `Exec/CellNullifier.lean` (the no-double-spend crown over the grow-only
`nullifiers` set) and `Exec/CellConfine.lean` (confinement carried forever), distilled by
`Exec/CellCarry.lean`'s parametric crown `livingCellA_carries` (ANY state predicate `Good` preserved
by ONE living-cell step holds along the ENTIRE unbounded adversarial trajectory `trajA`, under EVERY
schedule). For the revocation registry the per-step bookkeeping is the SHARPEST of the three crowns:
the current 46-effect executor `execFullA` has **NO arm that grows `revoked`** (only the FFI
marshaller writes it back; cf. `gatedNode_check_eq_use` — the gate READS the committed registry, the
ledger effects never edit it), so EVERY committed effect leaves the registry literally UNCHANGED. We
therefore prove the strongest frame — per-step EQUALITY `s'.kernel.revoked = s.kernel.revoked` — and
read the grow-only `⊆` and the permanent-revocation carry off it. (Equality is the faithful invariant:
a ledger turn must NOT silently un-revoke; only an explicit consensus-seam `cap_revoke` may grow the
set, and that — were it added as an effect — would still preserve the carried `⊆`.)

Five theorems, ascending:

* **`execFullA_revoked_eq`** — the per-effect REGISTRY FRAME: a committed `FullActionA` leaves the
  revocation registry UNCHANGED (`s'.kernel.revoked = s.kernel.revoked`). The 46-arm dispatch walk
  (mirroring `execFullA_nullifiers_grow`); every kernel transform writes a NON-`revoked` field, so the
  `.revoked` projection reduces by `rfl`. The `revoke`/`dropRef`/`revokeDelegation` *authority* effects
  route through `recCRevoke`/`recKRevokeTarget` which edit ONLY `caps` — they do NOT grow this
  credential-revocation registry (a distinct side-table). The sharpest dual of the conservation frame.
* **`execFullTurnA_revoked_eq` / `execFullForestA_revoked_eq`** — the turn- and forest-level lift, by
  induction on the action list (chain by `Eq.trans`) through `execFullForestA_eq_execFullTurnA`.
* **`livingCellA_revoked_grow`** — THE CROWN: `rev0 ⊆ s.kernel.revoked` carried by `livingCellA_carries`
  (one-step obligation = the forest frame on a commit + the stay-put self-loop on a reject). A genuinely
  NON-conservation safety (it reads the registry, never the per-asset measure) — *"once revoked, forever
  revoked"* on the SHIPPED machine, against EVERY adversarial schedule.
* **`livingCellA_identity_revoked_forever`** — the HEADLINE, the teeth made temporal: if an identity's
  credential nullifier `credNul` is in the registry initially, it is STILL there at EVERY index of EVERY
  trajectory (`credNul ∈ (trajA …).kernel.revoked`) — so its `revocationGate` / `gateOK` fail-close at
  every reachable state (`FullForestAuth.gateOK_revoked_fails`). The dregg1 `verify_non_revocation` →
  `Revoked` rejection, lifted to *"a revoked identity can never be re-validated, for all time."*
-/
import Dregg2.Exec.CellNullifier
import Dregg2.Exec.FullForestAuth

namespace Dregg2.Apps.Identity

open Dregg2.Boundary
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Exec.EffectsState (stateStep stateStep_factors)

/-! ## Step 0 — registry-frame lemmas for the DEEPLY-NESTED kernel ops (queue-deposit + swiss).

The same five kernel ops that `CellNullifier` hoists (their bodies nest a `match … | some k₁ => if …`
too deep to `unfold`+`split` cleanly inline). Each touches ONLY `queues`/`swiss`/`bal`/`escrows` —
never `revoked` — so a committed step leaves `revoked` literally unchanged. We hoist them to `private`
frame lemmas on `.revoked`, the exact dual of `CellNullifier`'s `_nullifiers` helpers. -/

/-- `queueEnqueueK` commits to `{ k with queues := … }` — `revoked` untouched. -/
private theorem queueEnqueueK_revoked (k : RecordKernelState) (id m : Nat) (k₁ : RecordKernelState)
    (hq : queueEnqueueK k id m = some k₁) : k₁.revoked = k.revoked := by
  unfold queueEnqueueK at hq; split at hq
  · exact absurd hq (by simp)
  · split at hq
    · injection hq with hq; subst hq; rfl
    · exact absurd hq (by simp)

private theorem queueEnqueueDepositK_revoked (k : RecordKernelState) (id m : Nat)
    (sender owner : CellId) (depId : Nat) (dAsset : AssetId) (deposit : ℤ) (k' : RecordKernelState)
    (h : queueEnqueueDepositK k id m sender owner depId dAsset deposit = some k') :
    k'.revoked = k.revoked := by
  unfold queueEnqueueDepositK at h
  split at h
  · exact absurd h (by simp)                                 -- queueEnqueueK = none
  · rename_i k₁ hq                                            -- queueEnqueueK = some k₁
    split at h
    · option_inj at h; subst h                               -- deposit gate true ⇒ k' = createEscrowRawAsset k₁ …
      show k₁.revoked = k.revoked
      exact queueEnqueueK_revoked k id m k₁ hq
    · exact absurd h (by simp)                               -- deposit gate false

/-- `queueDequeueK` commits to `{ k with queues := … }` — `revoked` untouched. -/
private theorem queueDequeueK_revoked (k : RecordKernelState) (id : Nat) (actor : CellId)
    (k₁ : RecordKernelState) (mh : Nat) (hq : queueDequeueK k id actor = some (k₁, mh)) :
    k₁.revoked = k.revoked := by
  unfold queueDequeueK at hq; split at hq
  · exact absurd hq (by simp)
  · split at hq
    · split at hq
      · exact absurd hq (by simp)
      · option_inj at hq; obtain ⟨hq, _⟩ := hq; subst hq; rfl
    · exact absurd hq (by simp)

private theorem queueDequeueRefundK_revoked (k : RecordKernelState) (id : Nat) (actor : CellId)
    (depId : Nat) (k' : RecordKernelState) (mh : Nat)
    (h : queueDequeueRefundK k id actor depId = some (k', mh)) :
    k'.revoked = k.revoked := by
  unfold queueDequeueRefundK at h
  cases hq : queueDequeueK k id actor with
  | none => rw [hq] at h; exact absurd h (by simp)
  | some kp =>
      obtain ⟨k₁, mh₁⟩ := kp
      rw [hq] at h; simp only [] at h
      split at h
      · split at h
        · option_inj at h; obtain ⟨h, _⟩ := h; subst h       -- record found ∧ live ⇒ settle
          show k₁.revoked = k.revoked
          exact queueDequeueK_revoked k id actor k₁ mh₁ hq
        · exact absurd h (by simp)                           -- target not a live account
      · exact absurd h (by simp)                             -- deposit record absent

/-- `swissEnlivenK` commits to `{ k with swiss := … }` — `revoked` untouched. -/
private theorem swissEnlivenK_revoked (k : RecordKernelState) (sw : Nat) (claimed : List Auth)
    (k' : RecordKernelState) (h : swissEnlivenK k sw claimed = some k') :
    k'.revoked = k.revoked := by
  unfold swissEnlivenK at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · injection h with h; subst h; rfl
    · exact absurd h (by simp)

/-- `swissHandoffK` commits to `{ k with swiss := … }` — `revoked` untouched. -/
private theorem swissHandoffK_revoked (k : RecordKernelState) (sw certHash : Nat)
    (k' : RecordKernelState) (h : swissHandoffK k sw certHash = some k') :
    k'.revoked = k.revoked := by
  unfold swissHandoffK at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; subst h; rfl

/-- `swissDropK` commits to `{ k with swiss := … }` (remove or decrement) — `revoked` untouched. -/
private theorem swissDropK_revoked (k : RecordKernelState) (sw : Nat)
    (k' : RecordKernelState) (h : swissDropK k sw = some k') :
    k'.revoked = k.revoked := by
  unfold swissDropK at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · injection h with h; subst h; rfl
      · injection h with h; subst h; rfl

/-! ## Step 1 — `execFullA_revoked_eq`: the per-effect REGISTRY FRAME (the 46-arm dispatch).

Mirrors `CellNullifier.execFullA_nullifiers_grow`'s `cases fa with` walk, but for the credential
revocation registry the result is even SHARPER: EVERY arm leaves `revoked` UNCHANGED (there is no
grower in the current executor — `noteSpend` grows `nullifiers`, not `revoked`; the authority
`revoke`/`dropRef`/`revokeDelegation` effects edit `caps` via `recKRevokeTarget`, not this
credential-revocation side-table). So every arm reduces to `k'.revoked = s.kernel.revoked` (the kernel
op writes a NON-`revoked` field, projection by `rfl`) or a direct factored-state `rfl`. -/

/-- **`execFullA_revoked_eq` (PROVED) — the per-effect revocation-registry FRAME.** A committed
`FullActionA` leaves the credential revocation registry UNCHANGED: `s'.kernel.revoked =
s.kernel.revoked`. No effect of the current executor grows it (the `cap_revoke` consensus seam is the
gate's READ side, not a ledger effect); every kernel transform writes some OTHER field, so the
`.revoked` projection is `rfl`. The sharpest dual of the conservation frame `execFullA_ledger_per_asset`
(there the moved value cancels; here the registry is literally fixed). -/
theorem execFullA_revoked_eq (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s'.kernel.revoked = s.kernel.revoked := by
  cases fa with
  -- §catalog / supply / authority — chained `match kernelOp | some k' => some {kernel:=k',…}` wrappers.
  | balanceA t a =>
      simp only [execFullA, recCexecAsset] at h
      cases hk : recKExecAsset s.kernel t a with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKExecAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel del rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKDelegate at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | revoke holder t =>
      -- `recCRevoke`/`recKRevokeTarget` edit ONLY `caps` — the credential-revocation registry is a
      -- DISTINCT side-table, untouched (the projection through the `{caps := …}` update is `rfl`).
      simp only [execFullA, recCRevoke] at h
      option_inj at h; subst h; rfl
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKMintAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset] at h
      cases hk : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKBurnAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  -- §pure-state — `stateStep` (field write); factors through `stateStep_factors` (kernel = writeField,
  -- a `cell`-only update, `revoked` untouched ⇒ `rfl`). All four share the proof.
  | setFieldA actor cell f v =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | emitEventA actor cell topic data =>
      simp only [execFullA, emitStep] at h
      option_inj at h; subst h; rfl
  | incrementNonceA actor cell n =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | setPermissionsA actor cell p =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | setVKA actor cell vk =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  -- §authority — introduce/validateHandoff route to recKDelegate; delegateAtten to recKDelegateAtten;
  -- attenuate is always-commit (caps-only); dropRef/revokeDelegation to recCRevoke (caps-only);
  -- exercise factors (kernel UNCHANGED). NONE touches the credential-revocation registry.
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKDelegate at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | delegateAttenA del rec t keep =>
      simp only [execFullA, recCDelegateAtten] at h
      cases hk : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKDelegateAtten at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | attenuateA actor idx keep =>
      simp only [execFullA, attenuateStepA] at h
      option_inj at h; subst h; rfl
  | dropRefA holder t =>
      simp only [execFullA, recCRevoke] at h
      option_inj at h; subst h; rfl
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke] at h
      option_inj at h; subst h; rfl
  | validateHandoffA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKDelegate at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | exerciseA actor t =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := exerciseStepA_factors h; subst hs'; rfl
  -- §supply-growth — createCell/spawn factor through their gates (createCellIntoAsset / + a caps grant
  -- — neither touches `revoked`); bridgeMint reuses recCMintAsset.
  | createCellA actor newCell =>
      obtain ⟨_, _, hs'⟩ := createCellChainA_factors (by simpa only [execFullA] using h)
      subst hs'; rfl
  | spawnA actor child target =>
      obtain ⟨s1, hc, hs'⟩ := spawnChainA_factors (by simpa only [execFullA] using h)
      subst hs'
      obtain ⟨_, _, hc'⟩ := createCellChainA_factors hc; subst hc'; rfl
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a value with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKMintAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  -- §escrow / obligation / committed — chained holding-store steps (kernel updates bal/escrows, never
  -- `revoked`). create/obligation/committed-create share createEscrowKAsset; release/refund share
  -- releaseEscrowKAsset/refundEscrowKAsset.
  | createEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | releaseEscrowA id actor =>
      simp only [execFullA, releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold releaseEscrowKAsset settleEscrowRawAsset at hk
          split at hk
          · split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          · exact absurd hk (by simp)
  | refundEscrowA id actor =>
      simp only [execFullA, refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold refundEscrowKAsset settleEscrowRawAsset at hk
          split at hk
          · split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          · exact absurd hk (by simp)
  | createObligationA id actor obligor beneficiary asset stake =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor obligor beneficiary asset stake with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  -- §NOTE-SPEND — grows `nullifiers` (a DIFFERENT registry), `revoked` UNTOUCHED. This is the arm that
  -- moves the nullifier set in `CellNullifier`; here it frames the credential-revocation registry.
  | noteSpendA nf actor =>
      simp only [execFullA, noteSpendChainA] at h
      cases hk : noteSpendNullifier s.kernel nf with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold noteSpendNullifier at hk; split at hk
          · exact absurd hk (by simp)
          · injection hk with hk; subst hk; rfl
  -- §NOTE-CREATE — grows `commitments` (a DIFFERENT set), `revoked` untouched (always-commit).
  | noteCreateA cm actor =>
      simp only [execFullA, noteCreateChainA, noteCreateCommitment] at h
      option_inj at h; subst h; rfl
  | createCommittedEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | releaseCommittedEscrowA id actor =>
      simp only [execFullA, releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold releaseEscrowKAsset settleEscrowRawAsset at hk
          split at hk
          · split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          · exact absurd hk (by simp)
  | refundCommittedEscrowA id actor =>
      simp only [execFullA, refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold refundEscrowKAsset settleEscrowRawAsset at hk
          split at hk
          · split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          · exact absurd hk (by simp)
  -- §bridge — lock/finalize/cancel over the SHARED escrow holding-store (kernel updates bal/escrows).
  | bridgeLockA id actor originator destination asset amount =>
      simp only [execFullA, bridgeLockChainA] at h
      cases hk : bridgeLockKAsset s.kernel id actor originator destination asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold bridgeLockKAsset createBridgeRawAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | bridgeFinalizeA id actor asset amount =>
      simp only [execFullA, bridgeFinalizeChainA] at h
      split at h
      · cases hk : bridgeFinalizeKAsset s.kernel id asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            unfold bridgeFinalizeKAsset bridgeFinalizeRawAsset at hk
            split at hk
            · split at hk
              · injection hk with hk; subst hk; rfl
              · exact absurd hk (by simp)
            · exact absurd hk (by simp)
      · exact absurd h (by simp)
  | bridgeCancelA id actor =>
      simp only [execFullA, bridgeCancelChainA] at h
      split at h
      · cases hk : bridgeCancelKAsset s.kernel id with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            unfold bridgeCancelKAsset settleEscrowRawAsset at hk
            split at hk
            · split at hk
              · injection hk with hk; subst hk; rfl
              · exact absurd hk (by simp)
            · exact absurd hk (by simp)
      · exact absurd h (by simp)
  -- §seal — six bal-neutral field writes via stateStep / makeSovereignStep (cell-only update).
  | sealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | unsealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | createSealPairA actor sealerHolder unsealerHolder =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | makeSovereignA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'; rfl
  | refusalA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | receiptArchiveA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  -- §queue — four ring-buffer effects, each `if stateAuthB … then match queueK … | some k' => …`
  -- (kernel updates `queues`, never `revoked`). Gate-peel the outer `if`, then cases the kernel op.
  | queueAllocateA id actor cell cap =>
      simp only [execFullA, queueAllocateChainA] at h
      split at h
      · cases hk : queueAllocateK s.kernel id actor cap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            unfold queueAllocateK at hk; split at hk
            · exact absurd hk (by simp)
            · injection hk with hk; subst hk; rfl
      · exact absurd h (by simp)
  | queueEnqueueA id m actor cell depId dAsset deposit =>
      simp only [execFullA, queueEnqueueChainA] at h
      split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            exact queueEnqueueDepositK_revoked s.kernel id m actor cell depId dAsset deposit k' hk
      · exact absurd h (by simp)
  | queueDequeueA id actor cell depId deposit =>
      simp only [execFullA, queueDequeueChainA] at h
      split at h
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some kp =>
            rw [hk] at h
            obtain ⟨k', mhd⟩ := kp
            option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            exact queueDequeueRefundK_revoked s.kernel id actor depId k' mhd hk
      · exact absurd h (by simp)
  | queueResizeA id newCap actor cell =>
      simp only [execFullA, queueResizeChainA] at h
      split at h
      · cases hk : queueResizeK s.kernel id newCap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            unfold queueResizeK at hk
            split at hk
            · exact absurd hk (by simp)
            · split at hk
              · injection hk with hk; subst hk; rfl
              · exact absurd hk (by simp)
      · exact absurd h (by simp)
  -- §swiss — four CapTP swiss-table effects, each `if stateAuthB … then match swissK … | some k' => …`
  -- (kernel updates `swiss`, never `revoked`). Gate-peel + cases, as the queue arms.
  | exportSturdyRefA sw actor exporter target rights =>
      simp only [execFullA, swissExportChainA] at h
      split at h
      · cases hk : swissExportK s.kernel sw exporter target rights with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            unfold swissExportK at hk; split at hk
            · exact absurd hk (by simp)
            · split at hk
              · injection hk with hk; subst hk; rfl
              · exact absurd hk (by simp)
      · exact absurd h (by simp)
  | enlivenRefA sw actor exporter claimed =>
      simp only [execFullA, swissEnlivenChainA] at h
      split at h
      · cases hk : swissEnlivenK s.kernel sw claimed with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            exact swissEnlivenK_revoked s.kernel sw claimed k' hk
      · exact absurd h (by simp)
  | swissHandoffA sw certHash introducer exporter =>
      simp only [execFullA, swissHandoffChainA] at h
      split at h
      · cases hk : swissHandoffK s.kernel sw certHash with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            exact swissHandoffK_revoked s.kernel sw certHash k' hk
      · exact absurd h (by simp)
  | swissDropA sw actor exporter =>
      simp only [execFullA, swissDropChainA] at h
      split at h
      · cases hk : swissDropK s.kernel sw with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            exact swissDropK_revoked s.kernel sw k' hk
      · exact absurd h (by simp)

/-! ## Step 2 — the turn- and forest-level lift (induction on the list + the pre-order bridge). -/

/-- **`execFullTurnA_revoked_eq` (PROVED).** A committed per-asset full TURN leaves the credential
revocation registry UNCHANGED. By induction on the action list — each committed `execFullA` step frames
the registry (`execFullA_revoked_eq`), chained by `Eq.trans`; the empty turn is `rfl`. Mirrors
`CellNullifier.execFullTurnA_nullifiers_grow`'s structure (with `=` for `⊆`). -/
theorem execFullTurnA_revoked_eq :
    ∀ (s s' : RecChainedState) (tt : List FullActionA),
      execFullTurnA s tt = some s' → s'.kernel.revoked = s.kernel.revoked
  | s, s', [], h => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; rfl
  | s, s', a :: rest, h => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact (execFullTurnA_revoked_eq s1 s' rest h).trans (execFullA_revoked_eq s s1 a ha)

/-- **`execFullForestA_revoked_eq` (PROVED).** A committed full FOREST leaves the credential revocation
registry UNCHANGED. Read straight through the pre-order bridge `execFullForestA_eq_execFullTurnA` into
the turn-level lemma — the route `CellNullifier.execFullForestA_nullifiers_grow` takes. -/
theorem execFullForestA_revoked_eq (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') : s'.kernel.revoked = s.kernel.revoked := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_revoked_eq s s' (lowerForestA f) h

/-- **`execFullForestA_revoked_grow` (PROVED) — the grow-only COROLLARY.** Read off the equality:
`s.kernel.revoked ⊆ s'.kernel.revoked` (the permanent-revocation frame as the dregg1
`RevocationRegistry`'s insert-only `HashSet` sees it). Stated as `⊆` so the carry below is forward-
compatible with a future explicit `cap_revoke` effect that GROWS the registry. -/
theorem execFullForestA_revoked_grow (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') : s.kernel.revoked ⊆ s'.kernel.revoked := by
  rw [execFullForestA_revoked_eq s s' f h]; exact List.Subset.refl _

/-! ## Step 3 — THE CROWN: `rev0 ⊆ s.kernel.revoked` carried FOREVER by `livingCellA_carries`. -/

/-- **`livingCellA_revoked_grow` (PROVED) — THE permanent-revocation crown: the revocation registry is
grow-only FOREVER.** Fix ANY baseline of revoked credential ids `rev0 ⊆ s.kernel.revoked`. Along the
ENTIRE unbounded adversarial trajectory `trajA s sched`, under EVERY schedule, every id in `rev0` stays
revoked: `rev0 ⊆ (trajA s sched n).kernel.revoked` at EVERY index `n`. This is the dregg1 grow-only
`RevocationRegistry` safety — *"once revoked, forever revoked"* — and it is a genuinely NON-conservation
property: it is carried by `livingCellA_carries` with `Good := (rev0 ⊆ ·.kernel.revoked)`, whose
one-step obligation is discharged from the per-step **registry frame** (`execFullForestA_revoked_grow`
on a commit — the registry never shrinks) and the **stay-put self-loop** on a reject (`cellNextA` leaves
the state, hence the registry, UNCHANGED). It reads the revocation registry, NEVER the per-asset measure
`recTotalAssetWithEscrow` — exactly as `CellNullifier.livingCellA_no_double_spend` reads the nullifier
set. Conservation (`livingCellA_obs_invariant`) is the badge instance; THIS is the
*permanent-revocation* instance the per-asset measure cannot express. -/
theorem livingCellA_revoked_grow (rev0 : List Nat) (s : RecChainedState)
    (hinit : rev0 ⊆ s.kernel.revoked) (sched : SchedA) :
    ∀ n, rev0 ⊆ (trajA s sched n).kernel.revoked :=
  livingCellA_carries (fun s' => rev0 ⊆ s'.kernel.revoked)
    (fun a cf h => by
      -- One-step preservation. `cellNextA a cf = (execFullForestA a cf.1).getD a`: on a COMMIT the
      -- forest registry frame keeps (≥) the revocation registry (chain by `List.Subset.trans`); on a
      -- REJECT the state is the UNCHANGED `a`, so the baseline `⊆` is preserved trivially.
      show rev0 ⊆ (cellNextA a cf).kernel.revoked
      unfold cellNextA
      cases hc : execFullForestA a cf.1 with
      | some a' => simp only [Option.getD_some]
                   exact List.Subset.trans h (execFullForestA_revoked_grow a a' cf.1 hc)
      | none    => simp only [Option.getD_none]; exact h)
    s hinit sched

/-! ## Step 4 — THE HEADLINE: `identity_revoked_forever` — a revoked identity can NEVER be re-validated. -/

/-- **`livingCellA_identity_revoked_forever` (PROVED) — THE HEADLINE.** If an identity's credential
nullifier `credNul` is in the committed revocation registry in the initial state, then at EVERY index of
EVERY adversarial trajectory it is STILL revoked: `credNul ∈ (trajA s sched n).kernel.revoked`. The
single-element instance of the crown (`rev0 := [credNul]`) — the registry-membership fact the
verifier's negative discharge consumes. -/
theorem livingCellA_identity_revoked_forever (credNul : Nat) (s : RecChainedState)
    (hinit : credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, credNul ∈ (trajA s sched n).kernel.revoked := by
  intro n
  have h := livingCellA_revoked_grow [credNul] s (by
    intro x hx; rw [List.mem_singleton] at hx; subst hx; exact hinit) sched n
  exact h (List.mem_singleton.mpr rfl)

/-- **`identity_gate_revoked_forever` (PROVED) — THE TEETH, made temporal.** The headline payoff: a
revoked identity's credential gate fail-closes at EVERY reachable state of EVERY trajectory. If
`na.credNul` is revoked initially, then at EVERY index `n` the FULL auth gate rejects the node —
`FullForestAuth.gateOK na (trajA s sched n) = false` — so its gated step returns `none` and the
whole forest rolls back. This composes the temporal "still-revoked" fact
(`livingCellA_identity_revoked_forever`) with the per-step revocation teeth
(`FullForestAuth.gateOK_revoked_fails`): the dregg1 `verify_non_revocation` → `Revoked` rejection
(`revocation.rs:212`, `verification.rs:257`) is lifted to *"a revoked identity can never be
re-validated, for all time, against any adversarial schedule."* This is the identity app's whole
purpose, certified coinductively on the SHIPPED executor.

NOTE on the `na`-type parameters: `NodeAuthC` carries the gated-layer section variables
`{Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag}` — they are inferred from `na`'s
type and play no role in the proof (the revocation leg reads ONLY `na.credNul` and the kernel registry). -/
theorem identity_gate_revoked_forever
    {Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag : Type}
    [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
    [Dregg2.Laws.Verifiable Stmt Wit]
    [DecidableEq Tag] [CaveatChain.MacKernel (CaveatChain.Key Tag) Bytes Tag]
    [FullForestAuth.AuthPortal (FullForestAuth.Authorization Digest Proof) Ctx]
    (na : FullForestAuth.NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request)
      (Stmt := Stmt) (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx)
      (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (s : RecChainedState) (hinit : na.credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, FullForestAuth.gateOK na (trajA s sched n) = false := by
  intro n
  refine FullForestAuth.gateOK_revoked_fails na (trajA s sched n) ?_
  -- `credNul ∈ revoked` (carried forever) ⇒ `revoked.contains credNul = true`.
  rw [List.contains_iff_mem]
  exact livingCellA_identity_revoked_forever na.credNul s hinit sched n

/-! ## It runs (`#eval`) — the registry is non-empty and STABLE across a real committed turn.

The permanent-revocation invariant would be vacuous if the registry were always empty, OR if a ledger
turn could silently un-revoke. We exhibit a kernel with `credNul = 42` ALREADY revoked, run a real
conserving transfer (`CellReal.transferCF`, actor 0 moves 30 of asset 0), and observe `42` is STILL
revoked afterward (the frame `execFullForestA_revoked_eq` holds on the nose) — so
`livingCellA_identity_revoked_forever` bounds a genuinely non-empty, genuinely stable registry, and the
gate (`revocationGate`) keeps fail-closing on `42`. -/

/-- A real kernel state with credential id `42` ALREADY revoked: `fma0` with `revoked := [42]`. -/
def fmaRevoked : RecChainedState :=
  { fma0 with kernel := { fma0.kernel with revoked := [42] } }

#eval fmaRevoked.kernel.revoked                                                       -- [42] (42 is revoked)
#eval fmaRevoked.kernel.revoked.contains 42                                           -- true
-- run the real conserving transfer; the revocation registry is UNCHANGED (still [42]):
#eval (execFullForestA fmaRevoked transferCF.1).map (fun s' => s'.kernel.revoked)            -- some [42]
#eval (execFullForestA fmaRevoked transferCF.1).map (fun s' => s'.kernel.revoked.contains 42)  -- some true (STILL revoked)
#eval (execFullForestA fmaRevoked transferCF.1).map
        (fun s' => decide (([42] : List Nat) ⊆ s'.kernel.revoked))                    -- some true (the carried ⊆)
-- a credential id NOT revoked (`99`) is genuinely absent — the registry has teeth, not all-true:
#eval fmaRevoked.kernel.revoked.contains 99                                           -- false

/-! ## Axiom hygiene — the permanent-revocation crown pinned to the standard kernel triple (NO `sorryAx`). -/

#assert_axioms execFullA_revoked_eq
#assert_axioms execFullTurnA_revoked_eq
#assert_axioms execFullForestA_revoked_eq
#assert_axioms execFullForestA_revoked_grow
#assert_axioms livingCellA_revoked_grow
#assert_axioms livingCellA_identity_revoked_forever
#assert_axioms identity_gate_revoked_forever

end Dregg2.Apps.Identity
