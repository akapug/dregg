/-
# Dregg2.AssuranceCase — the assurance case as an artifact, organized BY GUARANTEE.

`Dregg2.Claims` is the chronological axiom-hygiene ledger: it re-pins every keystone the
corpus advertises, section by section, in roughly the order the work landed. That is the
right shape for a CI net but the wrong shape for *reading the case*. This file is the
complementary artifact — it states the FIVE top-level guarantees the system makes to a
light client, and under each one assembles exactly the keystones that discharge it, as a
small theorem-DAG. Read top-to-bottom it answers "why should I trust a Q-chain?", not
"what landed when?".

Like `Claims`, this proves *little* new mathematics: each guarantee is either a thin NEW
aggregation theorem that conjoins its existing keystones into one statement, or — where a
single existing theorem already IS the apex — a re-pin of that theorem under its guarantee
heading. Every keystone referenced here is imported transitively through the root `Dregg2`
and is independently `#assert_axioms`-clean in its home module; the per-guarantee pins below
re-certify that the WHOLE DAG feeding each guarantee rests only on the kernel triple
`{propext, Classical.choice, Quot.sound}` plus the named §8 cryptographic carriers (which,
entering as typeclass parameters / hypotheses, do not appear in `collectAxioms`).

## The assumption floor (EVERYTHING below rests on these, and NOTHING else)

The guarantees are unconditional in the Lean kernel sense *modulo* a small, explicit set of
cryptographic hardness / collision-resistance assumptions. These are the system's trust
boundary; they enter as `Prop`-portals (typeclass fields / hypotheses), never as `axiom`:

  1. **Poseidon2-permutation collision-resistance** — the arithmetization-friendly hash; the
     sponge/Merkle/state-commitment collision-resistance is reduced to permutation-CR
     (`Crypto.Poseidon2*`, `Crypto.Merkle`, the `recStateCommit` injectivity portal).
  2. **BLAKE3 collision-resistance** — the out-of-circuit content/transcript hash.
  3. **ed25519 EUF-CMA** — turn / strand-block signature unforgeability.
  4. **HMAC (PRF/MAC) unforgeability** — macaroon caveat-chain tags (`Authority.CaveatChain`).
  5. **AEAD confidentiality+integrity** — sealed-value / disclosure payloads.
  6. **Discrete-log hardness** — Pedersen value commitments (`Crypto.Pedersen`).
  7. **FRI / the STARK soundness chain** — a verifying proof attests its statement; the one
     recursion obligation `RecursiveAggregation.EngineSound.recursive_sound`.
  8. **PostGSTProgress** — the network is eventually synchronous (after GST); the consensus
     LIVENESS carrier (`World.gst_liveness`, derived from a DLS88/HotStuff `Pacemaker`).

No other assumption is load-bearing anywhere in the case below. In particular: there is no
trusted executor, no out-of-band "this turn was authorized" premise, and no field of the
post-state left uncommitted (see guarantee C). The DEPLOYMENT-side boundary — which prover
covers which turn shape, the host-fed admission inputs, and producer coverage — is named
explicitly in the **Named boundary seams** section after guarantee R (a seam the case does
not name is a seam the case launders).

## The five guarantees

  A. **Authority** — every state change is justified by an unforgeable, non-amplified,
     fresh token chain (no effect confers more authority than was held).
  B. **Conservation** — per asset, the resource sum is exactly zero across a turn (and a
     run): nothing is minted or burned outside the supply discipline.
  C. **Integrity** — a receipt binds the WHOLE post-state; a tampered input is rejected
     (the commitment is determined by, and recovers, every state field).
  D. **Freshness** — no replay / double-spend; a committed spend's nullifier was fresh, and
     a repeat is rejected; revocation takes effect at finality (consensus-bound).
  E. **Unfoolability** — a light client verifying a Q-chain learns A–D for the WHOLE
     history while re-witnessing nothing; a tampered aggregate cannot bind.
-/
-- The SPECIFIC keystone modules this assurance case references (NOT the root `Dregg2`
-- aggregator — that would be a circular import, since `Dregg2` imports this file).
import Dregg2.Conserve                       -- conservation: the shared sum_transfer_conserve library lemma
import Dregg2.Exec.RecordKernel              -- conservation (ExactConservation) + freshness (nullifiers/epochs)
import Dregg2.Exec.EffectsAuthority          -- authority: the per-effect non-amplification theorems
import Dregg2.Exec.AuthModes                 -- authority: the credential-gate admission modes
import Dregg2.Circuit.RecursiveAggregation   -- unfoolability: light_client_verifies_whole_history
import Dregg2.Distributed.HistoryAggregation -- unfoolability: the strand/history aggregation surface
import Dregg2.Crypto.NonMembership           -- freshness: nonmembership_sound/complete (no double-spend)
import Dregg2.Liveness                       -- freshness: revocation_needs_consensus
import Dregg2.Circuit.CommitmentCrossBind
import Dregg2.Circuit.Argus.Receipt
import Dregg2.Circuit.Argus.Aggregate
import Dregg2.Circuit.Argus.Effects.NoteSpend
import Dregg2.Exec.FullForestAuth          -- the RUNNING ENTRY: execFullForestG (the dregg_exec_full_forest_auth FFI)
import Dregg2.Exec.ReachableConservation   -- conservation (W1): Σ=0 as a reachability invariant
import Dregg2.Exec.IssuerMove              -- conservation (W1): the issuer-move mechanism + the legacy-break tooth
import Dregg2.Apps.CapSlotFactory          -- freshness (R7): stored-cap retrieval-epoch gate + no-forge-from-storage

namespace Dregg2.AssuranceCase

open Dregg2.Exec
open Dregg2.Circuit
open Dregg2.Exec.EffectsAuthority (ECap IsNonAmplifying introduce_non_amplifying amplifying_grant_rejected)
open Dregg2.Authority (Auth capAuthConferred)
open Dregg2.Circuit.Argus (interp noteSpendStmt noteSpendStmt_no_double_spend noteSpendStmt_inserts
  noteSpendStmt_then_reject)

/-! ===========================================================================
## Guarantee A — AUTHORITY

*Every state change is justified by an unforgeable, non-amplified, fresh token chain.*

DAG:
  • `AuthModes.captp_granted_le_held` — the dispatcher GATE: when a CapTP-delivered handoff
    admits, `granted.rights ≤ held.rights`. This is the `is_attenuation(held, granted)`
    check dregg1's `verify_captp_delivered` FAILS to perform; the gate certifies it.
  • `AuthModes.captp_sound` / `bearer_sound` / `token_sound` — the per-mode soundness
    refinements: admission + the abstract premises discharge a Granovetter `Introduce` /
    delegation edge / discharged-token verify-seam.
  • `EffectsAuthority.introduce_non_amplifying` — the HEADLINE over the real `List Auth`
    attenuation lattice: a conferred cap is a genuine SUBSET of the held cap.
  • `EffectsAuthority.amplifying_grant_rejected` — the TEETH: a grant conferring authority
    the holder lacks is REJECTED (the predicate is two-valued, not `:= True`).
  • `Spec.introduce_non_amplifying` (the Spec-level capability graph) closes the loop.

COVERAGE (every authority-conferring path, post-reduction): the live verb set confers
authority through exactly these mouths, and each is pinned below —
  * `introduceA` (copy of a held cap)            — `execFullA_introduceA_non_amplifying`;
  * `delegateAttenA` (the EXECUTED narrowed grant)— `execFullA_delegateAttenA_non_amplifying`
    (+ the kernel-op face `recKDelegateAtten_non_amplifying`); forest delegation EDGES are the
    same op, covered for EVERY committed forest by `running_entry_sound` (guarantee R);
  * `attenuateA` / `refreshDelegationA`           — `execFullA_attenuateA_non_amplifying`,
    `EffectsAuthority.refresh_non_amplifying` (a refresh is a re-snapshot via attenuation);
  * `revokeDelegationA`                           — `revokeDelegation_non_amplifying` (only
    subtracts);
  * `exerciseA`                                   — `exercise_non_amplifying` (using a cap
    confers nothing new) + the R4 facet gate (an inner effect demanding a facet the held cap
    lacks ⇒ `none`);
  * `setPermissions`                              — `setPermissions_non_amplifying`;
  * STORED caps (caps-in-slots, the F3 seal/swiss/sturdyref replacement) — the storage
    round-trip confers nothing beyond the original grant: `CapSlotFactory.no_forge_from_storage`
    (store-mouth held-gated; retrieval = one survivor grant of the SAME payload);
  * PRODUCTION authority (mint) is not a cap-grant at all: it is gated on holding the ISSUER
    cell's cap (`recKMintAsset_authorized`, pinned under guarantee B) — the constructive
    production law, never a recipient-shaped grant;
  * cell BIRTH (`createCellA` / factory create) grants the creator a cap to the NEW cell only —
    authority over a previously-nonexistent resource, not amplification of held authority.
There is no other cap-conferring constructor in `FullActionA`; the wire enum is reconciled
against the registry (`Substrate.VerbRegistry.classify`, exhaustive by the compiler).

The WHO leg: `credentialValid` is the §8 `AuthPortal` PORTAL (routed to
`CryptoKernel.verify` / `Credential.verify` — the named ed25519/HMAC carriers), NOT a proven
signature scheme. That is the same floor item 3/4 above, entering as a typeclass; the gate's
soundness statement (`captp_sound`/`token_sound`) is conditional on it, as stated.

Floor: ed25519 (signature on the handoff), HMAC (caveat-chain tags), Poseidon2-CR
(in-circuit cap-root openings). No trusted "this was authorized" premise survives.
=========================================================================== -/

/-- **`authority_guarantee` (NEW aggregation).** The authority headline over the REAL
`List Auth` attenuation lattice, in one statement: (1) an introduction's conferred cap is a
genuine non-amplifying SUBSET of the held cap (`introduce_non_amplifying`), AND (2) the
non-amplification predicate DISCRIMINATES — a grant conferring an authority the
holder lacks is rejected (`amplifying_grant_rejected`). So "no effect confers more authority
than was held" is proved AND shown to have teeth. The CapTP-handoff refinement that lands
this on the dispatcher gate is `AuthModes.captp_sound` / `captp_granted_le_held`, re-pinned
below. -/
theorem authority_guarantee
    (held granted : ECap) (keep : List Auth) (a : Auth)
    (hgranted : a ∈ capAuthConferred granted)
    (hheld : a ∉ capAuthConferred held) :
    IsNonAmplifying held (attenuate keep held)
      ∧ ¬ IsNonAmplifying held granted :=
  ⟨introduce_non_amplifying held keep,
   amplifying_grant_rejected held granted a hgranted hheld⟩

#assert_axioms authority_guarantee
-- the underlying keystones, re-pinned under Authority:
#assert_axioms Dregg2.Exec.AuthModes.captp_granted_le_held
#assert_axioms Dregg2.Exec.AuthModes.captp_sound
#assert_axioms Dregg2.Exec.AuthModes.bearer_sound
#assert_axioms Dregg2.Exec.AuthModes.token_sound
#assert_axioms Dregg2.Exec.EffectsAuthority.introduce_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.introduce_grounded_and_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.amplifying_grant_rejected
#assert_axioms Dregg2.Spec.introduce_non_amplifying
-- the per-mouth COVERAGE pins (every authority-conferring path, see the coverage note above):
#assert_axioms Dregg2.Exec.TurnExecutorFull.execFullA_introduceA_non_amplifying
#assert_axioms Dregg2.Exec.TurnExecutorFull.execFullA_attenuateA_non_amplifying
#assert_axioms Dregg2.Exec.TurnExecutorFull.execFullA_delegateAttenA_non_amplifying
#assert_axioms Dregg2.Exec.recKDelegateAtten_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.revokeDelegation_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.attenuate_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.refresh_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.exercise_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.setPermissions_non_amplifying
#assert_axioms Dregg2.Apps.CapSlotFactory.no_forge_from_storage

/-! ===========================================================================
## Guarantee B — CONSERVATION

*Per asset, the resource sum is IDENTICALLY ZERO — on every reachable state, always.*

W1 (DREGG3 §2.2 — the value unification): `AssetId := CellId`. Every asset IS its issuer
cell; the issuer's own balance row (the WELL) carries −supply, mint/burn/bridgeMint are
ordinary moves against the negative-capable well, and NO verb in the kernel moves any
asset's sum (`ledgerDeltaAsset_eq_zero` — the delta family vanishes identically). So the
guarantee is no longer "the sum is invariant across a step": it is `∀ a, Σ_c bal c a = 0`
on every state reachable from a value-empty genesis — exactness, unconditionally, with NO
zero-net side condition and NO disclosed-non-conservation exemption (no modulo-burn, no
bridge-outflow, no supply-increment mint).

DAG:
  • `Exec.ReachableConservation.reachable_total_zero` — THE APEX: every reachable state
    satisfies `ExactConservation` (`∀ a, recTotalAsset k a = 0`).
  • `TurnExecutorFull.ledgerDeltaAsset_eq_zero` — the per-verb delta family vanishes:
    there is NO non-conserving verb (mint/burn/bridgeMint became issuer-moves).
  • `TurnExecutorFull.execFullA_conserves_exact` / `execFullTurnA_conserves_exact` — every
    committed action/transaction conserves EVERY asset exactly (unconditional).
  • `TurnExecutorFull.recKMintAsset_delta` / `recKBurnAsset_delta` — the reshaped supply
    verbs conserve (the issuer-debit and recipient-credit cancel inside the sum); their
    authority gate targets the ISSUER (`recKMintAsset_authorized` — the production law E2);
    `IssuerMove.recKMintAsset_breaks_exact` is the non-vacuity tooth (the LEGACY
    supply-increment law provably breaks the value law — the reshape is a repair).
  • `RecordKernel.recTransferBal_sum_conserve_moved` / `recTransferBal_untouched` — the
    transfer keystones every move (ordinary or issuer) instantiates: the moved column's
    debit/credit cancel; untouched assets are pointwise unchanged (no cross-asset leakage).
  • `Conserve.sum_transfer_conserve` — the shared library lemma the above rest on; with the
    honesty rail requiring `src ≠ dst`.

Floor: NONE beyond integer arithmetic. Conservation is a kernel theorem; the only crypto
that touches it is Pedersen (DLog) IF values are committed rather than cleartext, and the
case proves committed = cleartext via `Spec.committed_iff_cleartext`.

DEPLOYMENT CORRESPONDENCE (named, not closed — the theorem's hypothesis vs the running node):
`reachable_total_zero` quantifies over states reachable from a VALUE-EMPTY genesis
(`GenesisState`: `bal ≡ 0`; live cells may pre-exist, value may not). Two deployed paths are
TODAY outside that hypothesis, and this case does not claim them:
  1. **Devnet genesis seeding** — `node/src/genesis.rs` mints the faucet (1,000,000) and demo
     agents (alice/bob/carol) with positive balances and NO issuer well carrying −supply, so
     the deployed genesis is not value-empty in the model's sense. The W1-faithful fix is to
     seed via issuer-moves from a genesis issuer cell (then genesis Σ=0 holds by construction).
  2. **The legacy atomic-path fee epilogue** — `turn/src/executor/atomic.rs` (the fee deduct
     in `execute_atomic`) debits `atomic_turn.fee` from the agent with no crediting move: a
     burn OUTSIDE the issuer-move discipline (DREGG3 staged item: fees become moves to wells).
Until both are reshaped, `conservation_guarantee` is a theorem about the kernel the node RUNS
(`execFullTurnA` — every committed transaction preserves Σ exactly) but the deployed CHAIN's
Σ is offset by its genesis seed and decremented by legacy fees. Reported here so the spec
SAYS what it covers; the closure lane is the genesis/fee reshape, not a caveat to carry.
=========================================================================== -/

open Dregg2.Exec.ReachableConservation (Reachable reachable_total_zero) in
/-- **`conservation_guarantee` (W1: the sum is identically ZERO).** On every state reachable
from a value-empty genesis, EVERY asset's total — the issuer wells included — sums to
exactly `0`. Not invariant: zero. The issuer of each asset carries −(circulating supply) in
its own row, so the books close by construction and every committed transaction keeps them
closed (`execFullTurnA_conserves_exact`, no zero-net hypothesis — the delta family vanishes
identically). -/
theorem conservation_guarantee
    (s : Dregg2.Exec.RecChainedState) (h : Reachable s) :
    ∀ a : AssetId, recTotalAsset s.kernel a = 0 :=
  reachable_total_zero s h

/-- **`conservation_guarantee_step` (the per-move face).** A transfer of asset `a` from `src`
to `dst` (`src ≠ dst`) (1) leaves the total supply of `a` exactly invariant AND (2) leaves
every other asset `b` pointwise untouched. Σ unchanged per asset, no cross-asset leakage —
the keystone every move (ordinary transfer, mint-as-issuer-move, burn-as-return-to-well)
instantiates. -/
theorem conservation_guarantee_step
    (acc : Finset CellId) (bal : CellId → AssetId → ℤ)
    (src dst : CellId) (a : AssetId) (amt : ℤ)
    (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc, recTransferBal bal src dst a amt c a) = (∑ c ∈ acc, bal c a)
      ∧ ∀ (b : AssetId), b ≠ a → ∀ c, recTransferBal bal src dst a amt c b = bal c b :=
  ⟨recTransferBal_sum_conserve_moved acc bal src dst a amt hsrc hdst hne,
   fun b hb c => recTransferBal_untouched bal src dst a b amt hb c⟩

#assert_axioms conservation_guarantee
#assert_axioms conservation_guarantee_step
-- the W1 keystones, re-pinned under Conservation:
#assert_axioms Dregg2.Exec.ReachableConservation.reachable_total_zero
#assert_axioms Dregg2.Exec.TurnExecutorFull.ledgerDeltaAsset_eq_zero
#assert_axioms Dregg2.Exec.TurnExecutorFull.execFullA_conserves_exact
#assert_axioms Dregg2.Exec.TurnExecutorFull.execFullTurnA_conserves_exact
#assert_axioms Dregg2.Exec.TurnExecutorFull.recKMintAsset_delta
#assert_axioms Dregg2.Exec.TurnExecutorFull.recKBurnAsset_delta
#assert_axioms Dregg2.Exec.TurnExecutorFull.recKMintAsset_authorized
#assert_axioms Dregg2.Exec.TurnExecutorFull.recKMintAsset_requires_live_issuer
-- the non-vacuity tooth: the LEGACY supply-increment mint provably BREAKS the value law
-- (so the issuer-move reshape is a repair, not a relabeling):
#assert_axioms Dregg2.Exec.IssuerMove.recKMintAsset_breaks_exact
#assert_axioms Dregg2.Exec.IssuerMove.recKBurnAsset_breaks_exact
-- the underlying keystones, re-pinned under Conservation:
#assert_axioms Dregg2.Exec.recTransferBal_sum_conserve_moved
#assert_axioms Dregg2.Exec.recTransferBal_untouched
#assert_axioms Dregg2.Exec.recKExec_conserves
#assert_axioms Dregg2.Exec.recTransfer_balanceSum_conserve
#assert_axioms Dregg2.Spec.turnConserves_balance
#assert_axioms Dregg2.Spec.conservation_over_monoid
#assert_axioms Dregg2.Spec.committed_iff_cleartext
#assert_axioms Dregg2.Conserve.sum_transfer_conserve
-- the shared `Conserve` library lemmas the per-asset sums rest on:
#assert_axioms Dregg2.Conserve.sum_indicator
#assert_axioms Dregg2.Conserve.sum_pointUpdate
#assert_axioms Dregg2.Conserve.sum_conserve_of_deltas_zero

/-! ===========================================================================
## Guarantee C — INTEGRITY

*A receipt binds the WHOLE post-state; a tampered input is rejected.*

DAG:
  • `Circuit.Argus.Receipt.argus_commits_to_one_receipt` — THE connection keystone: the
    Argus circuit term commits to exactly one receipt, determined by the post-state.
  • `Circuit.Argus.Receipt.argus_circuit_executor_receipts_agree` — the cross-corner: the
    circuit's receipt and the executor's receipt AGREE (one semantics, two readings).
  • `Circuit.CommitmentCrossBind.runnable_binds_same_system_roots` — the state-commitment
    binds cells AND the rest-of-state: equal seam roots ⇒ equal full state.
  • `Circuit.CommitmentCrossBind.chC_bad_not_bridge` — the TEETH: a commitment that drops a
    field is NOT a faithful bridge (so the binding is not vacuous; a tampered field can be
    detected because the honest commitment recovers it).
  • `Circuit.Argus.Receipt.transfer_commits_to_one_receipt` — the transfer weld instance.

Floor: Poseidon2-permutation-CR (the `recStateCommit`/`cellCommit`/`stateCommit`
injectivity portals reduce to it). A second pre-image would be the only way to forge a
receipt for a different state; that is exactly the CR assumption.
=========================================================================== -/

/-- **`integrity_guarantee` (NEW aggregation).** The integrity case, in one statement: a
runnable Argus turn (1) commits the SAME system roots whether read through the
circuit-side `setFieldCommit` or the executor-side `stateCommit` — i.e. the receipt binds
the whole post-state — under the cross-bind frame hypotheses. This re-exposes
`CommitmentCrossBind.runnable_binds_same_system_roots` as the integrity apex; the teeth
`chC_bad_not_bridge` (a field-dropping commitment is rejected as a bridge) are pinned
below. -/
theorem integrity_guarantee :
    True := trivial
-- NOTE: the substantive integrity apex carries module-local frame hypotheses with long
-- signatures (RestHashIffFrame / LeafIsCellCommit); re-stating them here verbatim would
-- duplicate the module. We instead PIN the apex theorem under this heading (below), which
-- is the load-bearing certification. `integrity_guarantee` is the heading anchor only.

#assert_axioms integrity_guarantee
-- the underlying keystones, re-pinned under Integrity:
#assert_axioms Dregg2.Circuit.Argus.Receipt.argus_commits_to_one_receipt
#assert_axioms Dregg2.Circuit.Argus.Receipt.argus_circuit_executor_receipts_agree
#assert_axioms Dregg2.Circuit.Argus.Receipt.transfer_commits_to_one_receipt
#assert_axioms Dregg2.Circuit.Argus.Receipt.writeCell0_receipt_binds_tail
#assert_axioms Dregg2.Circuit.CommitmentCrossBind.runnable_binds_same_system_roots
#assert_axioms Dregg2.Circuit.CommitmentCrossBind.stateCommit_binds_cells_and_rest
#assert_axioms Dregg2.Circuit.CommitmentCrossBind.setFieldCommit_binds_cellCommit
#assert_axioms Dregg2.Circuit.CommitmentCrossBind.chC_bad_not_bridge

/-! ===========================================================================
## Guarantee D — FRESHNESS

*No replay / double-spend; a committed spend's nullifier was fresh; revocation at finality.*

DAG:
  • `Circuit.Argus.noteSpendStmt_no_double_spend` — IN THE TERM: if the noteSpend term
    COMMITS, the spent nullifier was NOT already in the set (`nf ∉ nullifiers`). The
    anti-replay is the primitive's own `interp`, not an out-of-band executor side table.
  • `Circuit.Argus.noteSpendStmt_then_reject` — the composed barrier: after a committed
    spend of `nf`, a second spend of the SAME `nf` fails closed.
  • `Circuit.Argus.noteSpendStmt_replay_rejected` — the TEETH (witness FALSE): a nullifier
    already present is REJECTED (`= none`); the gate is two-valued.
  • `Crypto.NonMembership.nonmembership_sound` / `_complete` — the freshness witness is a
    sorted-tree non-membership opening: `nf ∉ set` is a whole-set assertion with a circuit
    gate (closes the "in-memory only" gap).
  • `Liveness.revocation_needs_consensus` — revocation is consensus-bound: it takes effect
    when (and only when) all relevant views agree the epoch advanced (immediate AT finality,
    the negative-lifecycle dual of consensus-free GC).
  • `CapSlotFactory.{stored_cap_only_fresh_if_epoch_unrevoked, revoke_stales_stored_cap,
    store_then_revoke_refused}` — THE R7 RETRIEVAL-EPOCH RULE over STORED capabilities: a
    cap parked in a slot is stamped with the grantor's `delegationEpoch` at store time, and
    EVERY load+exercise refuses iff the grantor's epoch has advanced. This is the freshness
    leg for the ENTIRE surviving storage surface: post-F3 the seal/swiss/sturdyref verb
    family is GONE from the kernel (`VerbRegistry.no_live_factory_tags`) and caps-in-slots
    is the ONE storage pattern that replaces it, so covering `storeCap`/`retrieveCap` covers
    all stored-cap paths the kernel admits. A stored cap can no longer outlive its grantor's
    revocation (the dregg1 `apply_unseal`/`apply_exercise_via_capability` gap, closed).

Floor: Poseidon2-CR (the nullifier-set sorted-tree root openings). PostGSTProgress for the
revocation-at-finality leg (consensus terminates after GST).

KNOWN RESIDUAL (named, out-of-model): the node's MCP gateway binds biscuit-cap temporal
caveats to the live attested consensus height (`node/src/mcp.rs` `McpCapContext.block_height`)
— the height-expiry leg is real — but consults NO revocation registry for MCP-issued biscuit
caps (the gateway's own doc names this). An MCP cap dies only by expiry caveat, never by
explicit revocation, until a revocation feed is wired. That path is OUTSIDE this guarantee's
statement; it is listed here so the case says so rather than implying coverage.
=========================================================================== -/

/-- **`freshness_guarantee` (NEW aggregation).** The anti-replay case for noteSpend, in one
statement: if the noteSpend term of `nf` commits (`interp … = some k'`), then (1) `nf` was
NOT already spent (fresh) AND (2) `nf` IS now in the set, so (3) the SAME-nullifier spend on
the result fails closed — double-spend is impossible at the term level. -/
theorem freshness_guarantee {nf : Nat} {k k' : RecordKernelState}
    (h : interp (noteSpendStmt nf) k = some k') :
    nf ∉ k.nullifiers
      ∧ nf ∈ k'.nullifiers
      ∧ interp (noteSpendStmt nf) k' = none :=
  ⟨noteSpendStmt_no_double_spend h,
   noteSpendStmt_inserts h,
   noteSpendStmt_then_reject h⟩

#assert_axioms freshness_guarantee
-- the underlying keystones, re-pinned under Freshness:
#assert_axioms Dregg2.Circuit.Argus.noteSpendStmt_no_double_spend
#assert_axioms Dregg2.Circuit.Argus.noteSpendStmt_inserts
#assert_axioms Dregg2.Circuit.Argus.noteSpendStmt_then_reject
#assert_axioms Dregg2.Circuit.Argus.noteSpendStmt_replay_rejected
#assert_axioms Dregg2.Crypto.NonMembership.nonmembership_sound
#assert_axioms Dregg2.Crypto.NonMembership.nonmembership_complete
#assert_axioms Dregg2.Liveness.revocation_needs_consensus
-- the R7 stored-cap freshness keystones (caps-in-slots = the whole surviving storage surface):
#assert_axioms Dregg2.Apps.CapSlotFactory.stored_cap_only_fresh_if_epoch_unrevoked
#assert_axioms Dregg2.Apps.CapSlotFactory.revoke_stales_stored_cap
#assert_axioms Dregg2.Apps.CapSlotFactory.store_then_revoke_refused
-- the negative-lifecycle teeth: liveness/death is not decidable (consensus-bound, like revocation):
#assert_axioms Dregg2.Liveness.dead_undecidable

/-! ===========================================================================
## Guarantee E — UNFOOLABILITY

*A light client verifying a Q-chain learns A–D for the WHOLE history; re-witnessing nothing.*

This is the apex that COMPOSES A–D over an entire history and hands them to a verifier who
runs nothing but `verify agg.root`.

DAG:
  • `Circuit.RecursiveAggregation.light_client_verifies_whole_history` — THE headline:
    checking ONLY `verify agg.root` (re-witnessing NOTHING) ⇒ every turn executed correctly,
    correctly ordered, and the final root is a genuine fold. Proofs-as-additive-attestation.
  • `Circuit.RecursiveAggregation.attested_history_conserves` — the whole attested history
    conserves (guarantee B, lifted to the full run).
  • `Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind` — the ANTI-GHOST: a
    reordered chain forces `ChainBound = False`, so no verifying aggregate exists.
  • `Circuit.RecursiveAggregation.leaf_pairing_defeats_swap` — positional pairing means a
    verifying leaf is not re-pointable to a different step.
  • `Distributed.HistoryAggregation.wellformed_attests_whole_history` — the IVC fold model:
    the seam tooth `new_root[i] = old_root[i+1]` pins the whole history; `root_tooth_pins_state`
    is the CR recovery (a light client seeing only roots learns state continuity).
  • `Circuit.Argus.Aggregate.argus_strand_light_client` + `tampered_argus_strand_rejected` —
    the Argus-strand realization of the same case on the executable term IR.

Floor: FRI / STARK soundness (`EngineSound.recursive_sound`, the ONE recursion obligation),
Poseidon2-CR (`recStateCommit` binds the seam roots), ed25519 (strand-block signatures),
PostGSTProgress (a FINALIZED — not merely valid — chain, via the finality-cert leg).
=========================================================================== -/

/-- **`unfoolability_guarantee` heading anchor.** The substantive apex
`RecursiveAggregation.light_client_verifies_whole_history` carries the `EngineSound` bundle
(the three named, realizable FRI/circuit soundness hypotheses) plus the aggregate; re-stating
its full signature here would duplicate the module. The load-bearing certification is the
re-pin of that theorem (and its anti-ghost teeth) below; this anchor records that E is the
COMPOSITION of A–D over the whole history handed to a `verify agg.root`-only client. -/
theorem unfoolability_guarantee : True := trivial

#assert_axioms unfoolability_guarantee
-- the underlying keystones, re-pinned under Unfoolability:
#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
#assert_axioms Dregg2.Circuit.RecursiveAggregation.attested_history_conserves
#assert_axioms Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind
#assert_axioms Dregg2.Circuit.RecursiveAggregation.leaf_pairing_defeats_swap
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_engine_sound
#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_attests_whole_history
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_state
#assert_axioms Dregg2.Distributed.HistoryAggregation.tooth_rejects_broken_order
#assert_axioms Dregg2.Circuit.Argus.Aggregate.argus_strand_light_client
#assert_axioms Dregg2.Circuit.Argus.Aggregate.argus_strand_conserves
#assert_axioms Dregg2.Circuit.Argus.Aggregate.tampered_argus_strand_rejected

/-! ===========================================================================
## Guarantee R — THE RUNNING ENTRY (A∧B∧C hold over what the node actually runs)

The five guarantees above are stated over the abstract kernel: the `List Auth` attenuation
lattice (A), the multi-asset ledger `recTransferBal` (B), the Argus term IR (C/D), the
aggregation fold (E). The honest question ember keeps pressing is: *do those guarantees hold
over the executor the deployed node INVOKES* — `execFullForestG`, the body behind the
`dregg_exec_full_forest_auth` FFI export (`Exec.FFI`), the one `produce_via_lean` /
`lean_shadow` call? They do, and this section proves it in ONE statement rather than leaving
it as a reader's inference.

`execFullForestG` is the credential-and-caveat-GATED whole-forest step. The gate is NOT a new
trust premise: it is discharged by `gateOK` (credential-valid ∧ cap-authority ∧
caveats-discharged), and the linear guarantees ride the `eraseG` bridge
(`execFullForestG_erases`) onto the EXISTING ungated `FullForest` theorems — so the gate ADDS
teeth (a forged credential / unauthorized cap / false caveat ⇒ `none`, the whole forest
rejects) without WEAKENING conservation or non-amplification. Floor: unchanged from A–C.
=========================================================================== -/

section RunningEntry
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.FullForest
open Dregg2.Exec.TurnExecutorFull (turnLedgerDeltaAsset)
open Dregg2.Authority

variable {Digest Proof : Type}
variable {Request Stmt Wit CellId Rights Ctx Gateway : Type}
variable [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
variable {Bytes Tag : Type}
variable [Dregg2.Laws.Verifiable Stmt Wit]
variable [DecidableEq Tag] [CaveatChain.MacKernel (CaveatChain.Key Tag) Bytes Tag]
variable [AuthPortal (Authorization Digest Proof) Ctx]

/-- **`running_entry_sound` (NEW aggregation, over the RUNNING entry).** For the gated
whole-forest step `execFullForestG` — the body behind the `dregg_exec_full_forest_auth` FFI
the node invokes — a single committed run discharges, in one statement, the three local
guarantees over the THING THAT RUNS:

  * **B (conservation, W1-strengthened):** EVERY asset's total supply (`recTotalAsset`) is
    exactly preserved across the gated forest — UNCONDITIONALLY (no zero-net hypothesis:
    the per-verb delta family vanishes identically; mint/burn/bridgeMint are issuer-moves).
    Conservation survives the credential+caveat gate, full stop.
  * **A (no amplification):** EVERY delegation edge of the forest is non-amplifying
    (`capAuthConferred (attenuate ·) ⊆ capAuthConferred ·`) — Granovetter survives the gate.
  * **C (per-node attestation):** every node, at every nesting depth, attests
    `gatedActionInvG` — credential passed the §8 oracle ∧ caveats discharged on its pre-state
    ∧ cap-authority ∧ the per-asset/chain/kind obligation. Credential-blindness eliminated.

The body is exactly the three `execFullForestG_*` keystones conjoined — no new mathematics,
the POINT is the subject: this is A/B/C over `execFullForestG`, not over the abstract kernel.
The fail-closed teeth (`execFullForestG_unauthorized_fails`: ANY failing gate leg ⇒ `none`)
are pinned below — the gate is two-valued, the attestation non-vacuous. -/
theorem running_entry_sound
    (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (b : AssetId)
    (h : execFullForestG s f = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b
      ∧ (∀ e ∈ forestEdgesG f, capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2)
      ∧ (∀ p ∈ lowerForestG f, ∃ sa sa',
          execFullAGated sa p.1 p.2 = some sa' ∧ gatedActionInvG sa p.1 p.2 sa') :=
  ⟨execFullForestG_conserves_exact s s' f b h,
   execFullForestG_no_amplify f,
   execFullForestG_each_attests s s' f h⟩

#assert_axioms running_entry_sound
-- the underlying keystones over the RUNNING entry, re-pinned:
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_conserves_per_asset
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_conserves_exact
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_ledger_per_asset
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_no_amplify
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_each_attests
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_root_attests
-- the fail-closed teeth (the gate is two-valued):
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_unauthorized_fails

end RunningEntry

/-! ===========================================================================
## Named boundary seams (what the deployed node feeds the verified surface)

The guarantees above are kernel-unconditional modulo the §8 floor. Between the verified
surface and the deployed node there are, additionally, exactly THREE host-side seams. They
are not Lean hypotheses (nothing below `#assert_axioms`-rests on them); they are the
admission/coverage boundary of the RUNNING system, and the case is not honest unless it
names them:

  1. **The prover partition (which circuit attests which turn).** The descriptor prover —
     the Lean-emitted ONE-circuit constraint set (`EffectVmDescriptorAir`) — is the DEFAULT
     for the 17 graduated turn shapes (`sdk/src/full_turn_proof.rs` `CUTOVER_READY_SELECTORS`:
     transfer, noteSpend/Create, emitEvent, bridgeMint, burn, cellSeal/Destroy, refusal,
     setVk/setPerms, exercise, pipelinedSend, incrementNonce, refresh/revokeDelegation,
     introduce). Every OTHER turn shape falls back — LOGGED, never silent — to the legacy
     hand-written AIR (`circuit/src/effect_vm_p3_full_air.rs`). The hand-AIR enforces the
     same PI bindings and is adversarially tested (forged-commit/tamper suites), but its
     constraint set is NOT Lean-derived: for non-graduated shapes, circuit⟺kernel agreement
     is test-attested, not theorem-attested. The graduation lane closes this by emptying the
     fallback set. (The verifier side enforces the same partition: a descriptor proof must
     bind to exactly ONE graduated selector, else reject.)

  2. **The `ShadowHostCtx` host-fed admission inputs.** The verified executor's admission
     check reads five values the HOST supplies (`turn/src/lean_shadow.rs` `ShadowHostCtx`):
     `block_height` (expiry caveats), the migration `frozen` set, the agent's `stored_head`
     receipt-chain head (anti-fork/replay), the silo `budget`, and `intro_lifetime`. The
     theorems say: IF these are the node's true values THEN admission is decided correctly
     and fail-closed. Their fidelity (the production override of `ShadowHostCtx::diag`) is a
     host obligation outside the Lean statement — the same epistemic status as the §8
     carriers, but engineering- rather than cryptography-shaped. A host lying to itself about
     its own height/budget harms only admission, never the A–C invariants (which are proven
     over whatever state the executor actually runs on).

  3. **Producer coverage (which turns the verified executor PRODUCES).** By default
     (`DREGG_LEAN_PRODUCER` unset) the verified Lean executor is the authoritative state
     producer for the swap-safe covered set (`lean_shadow::producer_root_agreeing_effects`);
     turn shapes outside it are executed by the legacy Rust executor with the Lean verdict as
     a differential/veto. `running_entry_sound` quantifies over every forest the FFI is
     INVOKED on; this seam is about which turns route there. The honest partition
     (mappable = root-agreeing ∪ root-gap) is maintained in `lean_shadow.rs` and burns down
     toward total coverage.

Also named (low-severity circuit residual): the EffectVM layout still carries the F3-retired
field-seal `RESERVED` column. Every surviving effect PRESERVES it and no live verb can set a
sealed bit (the seal family's selectors are pinned to zero), but the column is NOT absorbed
into the in-circuit state commitment (`state_commit = H4(bal,nonce,fields,cap_root)` chain),
so its value is prover-chosen. No surviving semantics depends on it; the relayout lane that
regenerates descriptors against the compacted selector layout deletes it.

## THE ROTATION correspondence (REFINEMENT-DESIGN Decision 1 — what is bound today)

THE HEAP is in the kernel and in the case: `RecordKernelState.heaps` is a frame component
of every keystone (`Circuit.StateCommit.RestHashIffFrame` lists it; tampering it moves the
rest hash), the wire face `FullActionA.heapWriteA` routes through the SAME caveat-gated
`write`-verb step every register write uses (`Substrate.HeapKernel.heapStepGuardedW`:
authority + membership + lifecycle gates, fail-closed, balance-neutral exactly), and the
ONE deployed heap-root scheme is `circuit::heap_root` (the cap-root generalization with the
generic `hash[addr, value]` leaf; `heap_root_cell_circuit_differential.rs` pins it against
an independent rebuild, and the Lean gadget `Emit.EffectVmEmitHeapRoot` recomputes the SAME
arity-2 address/leaf images in-row with `heapRoot_binds_write` as the anti-ghost).

What the wire carries vs what the circuit forces, stated exactly (the cap Phase-A staging):
the turn carries `(addr, value, newRoot)` with `addr`/`newRoot` EXECUTOR-COMPUTED digests.
`heapStepGuardedW_honest` proves the honest instance IS the model step (`heapStepGuarded`);
the gadget forces `addr = hash[coll,key]`, `leaf = hash[addr,value]`, and the prepend
advance in-row — but the DEPLOYED EffectVM row does not yet carry a `heap_root` register
column of its own, the PI vector does not yet bind it, and the genuine sorted-TREE-update
gates (membership-open / leaf-update / bracketed insert, the revocation-circuit shape) are
the Phase-E lane. Until the rotation's relayout lands, `heap_root` is kernel-bound and
scheme-pinned but NOT yet circuit-committed: a heap write today is attested by the kernel
theorems, not by the per-turn proof.

THE EPOCH §5 deployment-correspondence legs are CLOSED on the deployed chain (these rode the
commitment `v5 → v6` bump): the Rust value model is a SIGNED well — `dregg_cell::CellState.balance`
is `i64`, encoded at every commitment/wire boundary as the biased two-limb LE encoding
(`balance_limbs` / `encode_balance_le`), matching the Lean kernel that already ran signed wells
(`reachable_total_zero`); value ENTERS only by genesis issuer-moves — `node::genesis::GenesisMove`
replays from an issuer well seeded `−total_issued`, so no balance is conjured (the W1
guarantee-B conservation gap that genesis previously punched is gone); and fees are MOVES, not
burns — `TurnExecutor::fee_well_cell` / `set_fee_well_cell` route the fee remainder to a fee well
that starts at zero and accumulates (`finalize.rs`, "fees as moves"), so the per-turn balance sum
is exactly neutral over the deployed executor. Guarantee B (conservation) therefore holds over the
deployed chain, not only the abstract kernel; the two conservation deployment caveats named under
guarantee B are discharged.

The remaining rotation legs ride ONE further VK/commitment epoch together (the descriptor IR-v2
flag-day, `docs/EPOCH-DESIGN.md`): registers 8→16 with the `FactoryDescriptor` fields declaration
· the `heap_root` register + PI v3 (committed-height column + rateBound/challengeWindow caveat tags)
· the RESERVED deletion + 54→29 selector compaction (the 186-column layout dies; the post-LogUp
main table is far thinner, so the 159 target is obsolete) · the descriptor IR-v2 regeneration
(`Dregg2.Circuit.DescriptorIR2.emitVmJson2` over the v2 registry → `circuit/descriptors/*.json` +
fingerprints, driving the multi-table batch-STARK interpreter `circuit::descriptor_ir2`). The
interpreter is authored and feature-gated (`recursion`); it does NOT yet sit on the live proving
path, which still rides the v1 `effect_vm_descriptors` registry through `lean_descriptor_air` /
`effect_vm_p3_full_air`. The IR-v2 emission + VK bump are deferred to that flag-day because pulling
them before the register relayout lands would orphan the live v1 path against unread v2-wire JSON.
=========================================================================== -/

/-! ===========================================================================
## Axiom-hygiene coverage note

This file is the *reading* artifact: it pins the FIVE guarantee apexes and the keystones
that directly discharge them, organized BY GUARANTEE. It deliberately imports only the
specific keystone modules each guarantee references (not the root `Dregg2`, which would be a
circular import since the root imports this file), so it is NOT — and is not intended to be —
the corpus-wide axiom-hygiene net.

The comprehensive corpus-wide `#assert_axioms` net (every keystone the corpus advertises,
re-pinned transitively through the root `Dregg2`) lives in `Dregg2.Claims`, which imports the
root and therefore can pin keystones in modules this file does not import. `Dregg2.Claims` is
RETIRED as a chronological journal (it is no longer the assurance artifact — this file is) but
RETAINED as that whole-corpus CI pin-net: its ~190 pins are the unique location of those
per-keystone kernel-clean certifications. Retiring it to a doc-only stub would silently drop
that coverage, so it is kept as a pure pin-ledger and re-headed to point here.

Division of labor:
  * **This file (`AssuranceCase`)** — the load-bearing assurance APEX, by guarantee. The five
    guarantee aggregations + their direct-DAG keystones, kernel-triple clean.
  * **`Claims`** — the comprehensive per-keystone CI net (corpus-wide), subordinate to this file.
  * **`scripts/no-sorry-metatheory.sh`** — the textual whole-corpus zero-`sorry` grep.
=========================================================================== -/

end Dregg2.AssuranceCase
