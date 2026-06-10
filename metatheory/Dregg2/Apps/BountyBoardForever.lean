/-
# Dregg2.Apps.BountyBoardForever — re-lifting the bounty board's LIFETIME ("forever") conservation
guarantees onto the PLAIN `recTotalAsset` measure, for the FACTORY-BORN bounty board.

`Apps/BountyBoardGated.lean` re-points the bounty board off the off-ledger escrow VERB family
(`createEscrowA`/`releaseEscrowA`/`refundEscrowA` over the `escrows` side-table) onto the FACTORY-BORN
escrow cell: the locked reward now lives in the minted cell's OWN per-asset `bal` column, NOT in the
side-table. Its per-op release-safety contract (`bb_post_*_conserves` / `bb_claim_conserves` /
`bb_cancel_conserves`) is consequently re-proved on the ORDINARY plain `recTotalAsset` move law — NO
`recTotalAssetWithEscrow`. That migration set ASIDE the §9 Hatchery "forever" crowns the verb-era file
carried (`bb_asset_conserved_forever`, `bb_board0_*_conserved_forever`, `bb_safety_forever`), because
those were stated on the OLD combined `recTotalAssetWithEscrow` measure (`cellObsA`, the production
`assetConserved` badge = `recTotalAsset + escrowHeldAsset`).

THIS file RECOVERS the lifetime guarantee on the plain measure. It re-proves, via the `Verify/Contract`
toolkit's `CellContract.forever` machinery, that conservation holds along the WHOLE production trajectory
under ANY adversarial gated schedule (`trajG` / `SchedG`) — the `CellContract.forever` crown — now read
off the plain `recTotalAsset` ledger.

## The honest re-lift (and why it is the RIGHT statement)

The Hatchery's parametric forever carry (`assetConserved`/`cellObsA`, the production conservation
contract) is invariant for the COMBINED per-asset quantity `recTotalAssetWithEscrow k a =
recTotalAsset k a + escrowHeldAsset k a` (`RecordKernel.lean:1429`). This is the quantity that is
preserved by EVERY committed conserving gated forest step — including a step that parks value into the
legacy side-table (where `recTotalAsset` drops and `escrowHeldAsset` rises by the same amount). The bare
plain `recTotalAsset` is therefore NOT a step invariant under an ARBITRARY schedule, and stating it as a
blanket forever crown would be FALSE. The faithful crown exposes the decomposition explicitly:

  * `bbf_plain_plus_held_conserved_forever` — the COMBINED quantity `recTotalAsset + escrowHeldAsset`
    never drifts along the whole trajectory under any gated schedule (the `assetConserved` carry, read
    in plain-ledger-plus-side-table form). This is the universally-true lifetime law.
  * `bbf_plain_conserved_forever_of_side_table_quiet` — from that crown, WHENEVER the side-table
    held-value is quiet at an index (`escrowHeldAsset = 0` there and at the baseline — the factory-born
    board's REALITY, since it never touches the side-table), the PLAIN `recTotalAsset` itself is fixed at
    that index. This is the plain-measure guarantee the migration set aside, recovered.

For the FACTORY-BORN board (`board0` from `BountyBoardGated`, whose `escrows` side-table is EMPTY and is
never populated by post/claim/cancel — they move the cell's own `bal`), the side-table summand is `0`
throughout: `cellObsA board0 = recTotalAsset board0.kernel` exactly. The §3 non-vacuity witnesses pin
this — so on the factory board's own trajectory the combined crown IS the plain-measure crown, with no
residual. Post W2's verb deletion, `escrowHeldAsset` is removed and `recTotalAssetWithEscrow` COLLAPSES
to plain `recTotalAsset` (`EscrowFactory.lean §DELETION (4)`), at which point the two crowns coincide
unconditionally.

NEW file — does NOT edit `BountyBoardGated.lean`. Reuses ONLY the shipped `Verify/Contract` forever
machinery (`assetConserved` / `asset_conserved_forever_production`) and the factory board's keystones.
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Apps.BountyBoardGated
import Dregg2.Verify.Contract

namespace Dregg2.Apps.BountyBoardForever

open Dregg2.Exec
open Dregg2.Exec (cellObsA trajG SchedG)
open Dregg2.Verify (assetConserved asset_conserved_forever_production)
open Dregg2.Apps.BountyBoardGated (board0 escrowCellId rewardAmt bountyVk)

/-! ## §1 — Domain carriers. -/

/-- The reward asset class (asset `0` on the canonical `board0`). -/
abbrev rewardAsset : AssetId := 0

/-- The bounty board's conservation contract on the production executor, at the reward asset. This is
the SHIPPED Hatchery `assetConserved` contract (`Verify/Contract.lean:269`): its `Inv` carries the
combined per-asset quantity `cellObsA · rewardAsset = recTotalAssetWithEscrow · rewardAsset` constant,
and its `step_ob` is the proved `cellObsA_next`. Naming it here makes the bounty board's lifetime crown
a `.forever` method call on a named object — the Tier-3 promise. -/
noncomputable def bbRewardConserved (s0 : RecChainedState) : Dregg2.Verify.Production.Contract :=
  assetConserved s0 rewardAsset

/-! ## §2 — The lifetime ("forever") crowns on the PLAIN `recTotalAsset` measure.

`recTotalAssetWithEscrow k b` is DEFINITIONALLY `recTotalAsset k b + escrowHeldAsset k b`
(`RecordKernel.lean:1429`), and `cellObsA s b = recTotalAssetWithEscrow s.kernel b`
(`CellReal.lean:30`). So the production `assetConserved` forever carry, read at the reward asset, IS the
statement that `recTotalAsset + escrowHeldAsset` never drifts along the whole `trajG` trajectory. -/

/-- **`bbf_plain_plus_held_conserved_forever` — THE LIFETIME CROWN (universal).** From any baseline
`s0`, along EVERY adversarial production schedule, the bounty board's reward supply on the PLAIN ledger
PLUS the legacy side-table held-value never drifts — at every index of the unbounded trajectory. This is
the `CellContract.forever` crown for the factory-born board, recovered on the plain-ledger decomposition.
(The combined quantity is the one preserved by every committed gated step; the plain summand is isolated
in §`bbf_plain_conserved_forever_of_side_table_quiet`.) -/
theorem bbf_plain_plus_held_conserved_forever (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, recTotalAsset (trajG s0 sched n).kernel rewardAsset
           + escrowHeldAsset (trajG s0 sched n).kernel rewardAsset
         = recTotalAsset s0.kernel rewardAsset + escrowHeldAsset s0.kernel rewardAsset :=
  asset_conserved_forever_production s0 rewardAsset sched

/-- **`bbf_plain_conserved_forever_of_side_table_quiet` — THE PLAIN-MEASURE LIFETIME CROWN.** From a
baseline whose reward side-table is quiet, then at every trajectory index where the side-table stays
quiet (`escrowHeldAsset = 0`), the PLAIN `recTotalAsset` reward supply is FIXED at its baseline value.
This is the guarantee the escrow-factory migration set aside (the verb-era `bb_asset_conserved_forever`
on `recTotalAssetWithEscrow`), now recovered on the plain measure — discharged from the universal
combined crown by cancelling the (zero) side-table summand. The factory-born board's `post`/`claim`/
`cancel` never populate the side-table, so the quiet hypotheses are its lived reality (§3 witnesses). -/
theorem bbf_plain_conserved_forever_of_side_table_quiet (s0 : RecChainedState) (sched : SchedG)
    (hbase : escrowHeldAsset s0.kernel rewardAsset = 0) :
    ∀ n, escrowHeldAsset (trajG s0 sched n).kernel rewardAsset = 0 →
         recTotalAsset (trajG s0 sched n).kernel rewardAsset = recTotalAsset s0.kernel rewardAsset := by
  intro n hquiet
  have h := bbf_plain_plus_held_conserved_forever s0 sched n
  rw [hquiet, hbase, add_zero, add_zero] at h
  exact h

/-- **`bbf_board0_plain_plus_held_conserved_forever` — the canonical funded-board lifetime witness.** The
shipped factory-born `board0` carries the combined-measure forever crown along every gated schedule. -/
theorem bbf_board0_plain_plus_held_conserved_forever (sched : SchedG) :
    ∀ n, recTotalAsset (trajG board0 sched n).kernel rewardAsset
           + escrowHeldAsset (trajG board0 sched n).kernel rewardAsset
         = recTotalAsset board0.kernel rewardAsset + escrowHeldAsset board0.kernel rewardAsset :=
  bbf_plain_plus_held_conserved_forever board0 sched

/-- **`bbf_board0_plain_conserved_forever` — the canonical funded-board PLAIN lifetime witness.** `board0`'s
reward side-table starts empty (`escrows = []` ⇒ `escrowHeldAsset = 0`, `rfl`-discharged), so wherever it
stays quiet, `board0`'s plain reward supply (`105` of asset `0`) is fixed at every trajectory index. -/
theorem bbf_board0_plain_conserved_forever (sched : SchedG) :
    ∀ n, escrowHeldAsset (trajG board0 sched n).kernel rewardAsset = 0 →
         recTotalAsset (trajG board0 sched n).kernel rewardAsset = recTotalAsset board0.kernel rewardAsset :=
  bbf_plain_conserved_forever_of_side_table_quiet board0 sched rfl

/-! ## §3 — NON-VACUITY: the factory board's side-table is quiet, so the plain crown bites.

`board0`'s `escrows` field is empty (`BountyBoardGated.board0` sets no `escrows`), so its reward
side-table held-value is `0` and the combined measure coincides with the plain ledger from index 0.
The plain reward supply is a genuine, non-trivial `105` (poster's `100` + claimant's `5` of asset `0`),
not a vacuous `x = x` — and the `post`/`claim`/`cancel` ops move it within the `bal` ledger, leaving the
side-table summand at `0`, so the §2 quiet hypotheses fire on real states. -/

-- the factory board's reward side-table is empty ⇒ held-value 0 (the quiet baseline, `rfl`):
#guard (escrowHeldAsset board0.kernel rewardAsset == 0)                                   --  0
-- ...so the combined badge IS the plain ledger at the baseline — a genuine, non-trivial 105:
#guard (cellObsA board0 rewardAsset == recTotalAsset board0.kernel rewardAsset)           --  true (coincide)
#guard (recTotalAsset board0.kernel rewardAsset == 105)                                   --  105 (poster 100 + claimant 5)
#guard (cellObsA board0 rewardAsset == 105)                                               --  105

/-- The forever crown's n=0 face is non-vacuous on the factory board: at index `0` of EVERY gated
schedule, the trajectory is `board0` itself (`trajG _ _ 0 = s`), the side-table held-value is `0`, so
the plain crown's quiet hypothesis fires and the plain reward supply is the genuine, non-trivial `105`. -/
example (sched : SchedG) :
    escrowHeldAsset (trajG board0 sched 0).kernel rewardAsset = 0 ∧
    recTotalAsset (trajG board0 sched 0).kernel rewardAsset = 105 :=
  ⟨rfl, rfl⟩

/-- ...and the plain crown's conclusion at index `0` is exactly the baseline `recTotalAsset` (`105`),
discharged through the actual `bbf_board0_plain_conserved_forever` keystone — not re-asserted. -/
example (sched : SchedG) :
    recTotalAsset (trajG board0 sched 0).kernel rewardAsset = recTotalAsset board0.kernel rewardAsset :=
  bbf_board0_plain_conserved_forever sched 0 rfl

/-! ## §4 — Axiom hygiene — every lifetime crown depends ONLY on `{propext, Classical.choice, Quot.sound}`. -/

#assert_axioms bbRewardConserved
#assert_axioms bbf_plain_plus_held_conserved_forever
#assert_axioms bbf_plain_conserved_forever_of_side_table_quiet
#assert_axioms bbf_board0_plain_plus_held_conserved_forever
#assert_axioms bbf_board0_plain_conserved_forever

end Dregg2.Apps.BountyBoardForever
