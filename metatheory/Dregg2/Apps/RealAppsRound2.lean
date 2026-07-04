/-
# Dregg2.Apps.RealAppsRound2 — round 2 of apps-beyond-toys (the aggregator).

Round 1 (`Apps/IntegratorWedge.lean`) refuted the "lamesauce" critique with two NEW apps. This lane
REBUILDS three of the weakest "toy" `*Gated.lean` apps as GENUINELY REAL ones, each exercising the
round-2 expressiveness this session landed — the new grammar atoms (`senderMemberOf`, `affineDeltaLe`,
`balanceDeltaLe`/`balanceDeltaGe`, `inRangeTwoSided`, the rate gates), cross-cell verified imports
(`Authority/CrossCellImport.lean`), and the async `notify` cap algebra (`Firmament/NotifyAuthority.lean`)
— with biting adversarial teeth (the honest path COMMITS; each adversary trace is `admitsCtx = false`).
Each app: a non-vacuous theorem suite + `#assert_all_clean`.

  * **`SubscriptionMetered`** (rebuilds `SubscriptionGated`'s single `monotonicSeq` slot) — a METERED
    subscription plan as ONE cell program: a spend-RATE floor (`balanceDeltaGe`, no single-turn drain of
    the prepaid balance), a combined two-meter BUDGET whose ceiling is the plan's `budget` SLOT
    (`affineDeltaLeField [(1,api_calls),(1,storage)] budgetF` — what no single-field counter can express,
    and a GOVERNED FIELD a tier upgrade lifts), a tier ALLOWLIST (`memberOf`), the strict period counter
    (`strictMono`), and subscriber PROVENANCE (`senderInField`). Teeth: `impostor_consume_rejected` ·
    `replayed_period_rejected` · `over_drain_rejected` · `meter_blowout_rejected` ·
    `forged_tier_rejected` · `pro_tier_lifts_meter_budget` (the upgraded tier admits a meter-move the free
    tier rejects, NO program change) — while `honest_consume_admits`.

  * **`GovernedParameters`** (rebuilds `GovernedNamespaceGated`'s single-credential gate) — a
    constitution-CITING parameter cell, the userspace home of cross-cell verified imports: a governed
    parameter is BOUND to a constitution cell's receipt by the first-class `ImportBinding.ImportedEq`
    (the `Import`'s `importValid` provenance + the `affineEq` enforcement FUSED in ONE construct, the pair
    no longer hand-threaded — `param_binding_matches_constitution` is now a corollary of the atom's
    keystone `importedEq_binds_provenanced_value`), updated by a multi-admin BOARD (`senderMemberOf`) with
    ACTOR-BOUND approval slots, the constitution pin IMMUTABLE. Teeth: `non_board_member_rejected` ·
    `version_replay_rejected` · `constitution_pin_immutable` · `unprovenanced_parameter_rejected` ·
    `approval_slot_actor_bound` · `lying_import_rejected` (a lie about what the constitution said cannot
    be cited) — while `honest_update_admits` and `param_binding_matches_constitution`.

  * **`ComputeMarketDesk`** (rebuilds `ComputeExchangeGated`'s thin 2-state settle) — a rate-limited
    compute marketplace desk with ASYNC settlement notify WELDED into the program: a payout-RATE ceiling
    that reads the desk's `payout_rate` SLOT (`balanceDeltaLeField`, a GOVERNED FIELD a tier upgrade lifts,
    no one-turn desk drain), a price BAND (`inRangeTwoSided`, no nonsense rate), a provider POOL
    (`senderMemberOf`), a DRAIN invariant on settle (`balanceLe`), AND a PROGRAM-ENFORCED settlement WAKE
    (`wakeOnResolve` — a settle driving the desk to RESOLVED is UNSAT unless the async wake fired; the
    `NotifyCap` algebra below witnesses the wake is authority-contained). Teeth: `non_provider_rejected` ·
    `off_band_price_rejected` · `over_payout_rejected` · `stranded_escrow_rejected` ·
    `unwoken_settle_rejected` (a resolve that forgets the wake is refused) · `premium_tier_lifts_payout_ceiling`
    · `out_of_mask_wake_refused` · `settle_wake_attenuation_no_amplify` — while `honest_settle_admits` and
    `settle_wake_commits`.

All three are `RecordProgram`-level cell programs the executor enforces on every turn (the `admitsCtx`
gate), the same shape as the round-1 `EscrowDeskCouncil`/`AgentOrchestrationBudget` quality bar — the
POLICY layer the `*Gated` toys lacked. Each `#assert_all_clean`.

`lake build Dregg2.Apps.RealAppsRound2` pulls all three apps + their proofs.
-/
import Dregg2.Apps.SubscriptionMetered
import Dregg2.Apps.GovernedParameters
import Dregg2.Apps.ComputeMarketDesk

namespace Dregg2.Apps.RealAppsRound2

/-! This module is a pure aggregator: it re-exports the three apps' namespaces so a downstream consumer
can `import Dregg2.Apps.RealAppsRound2` and reach all three. The verification lives in the imported
modules (each `#assert_all_clean` at its close). -/

end Dregg2.Apps.RealAppsRound2
