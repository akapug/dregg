# Computron Policy — operator-local acceptance, no protocol peg

*What a computron is worth is not a protocol question. Every operator answers it
locally, in a datastructure it owns; the protocol only guarantees that whatever
an operator credits, it credits by CONSERVING transfer out of its own cell.*

Status: rung 1 (operator-local purchase path) is BUILT and tested
(`node/src/relay_service.rs`, tests `computron_refill_*`). Rung 2 (DrEX rate
discovery) is DESIGN in §5, not built.

---

## 1. The frame

A computron is an **operator-local number in a datastructure** — the `balance`
of a cell in a node's ledger (`cell/src/ledger.rs`, signed 64-bit domain). It
meters execution and storage on THAT operator's node. There is deliberately
**no global peg**:

- No protocol constant says what a computron costs in USDC, ETH, or anything
  else.
- Every operator publishes its own acceptance policy — which external assets it
  takes and at what rate — and two operators' policies never need to agree.
- Nothing arbitrages the difference at the protocol layer. An operator quoting
  10× another's rate simply sells fewer refills.

What the protocol DOES fix is the conservation discipline: computrons entering
a user's cell come out of somewhere. The faucet (`node/src/api.rs::post_faucet`)
transfers from the genesis-funded faucet cell — a Transfer turn through the
executor, never a mint. The purchase path below mirrors that exactly: an
operator selling computrons transfers them out of its own pre-funded cell.

## 2. The policy datastructure

`FeePolicy` (`node/src/relay_service.rs`) carries a per-asset acceptance table:

```rust
pub struct FeePolicy {
    pub min_deposit_computrons: u64,
    pub subscription_fee: u64,
    /// keyed by hex-encoded 32-byte Payable asset id
    pub external_assets: BTreeMap<String, AssetRatePolicy>,
}

pub struct AssetRatePolicy {
    /// external asset units per computron, fixed-point 1e6
    /// (COMPUTRON_RATE_SCALE); 0 is invalid and always refuses
    pub rate_micros: u64,
    /// a disabled row refuses without deleting the quoted rate
    pub enabled: bool,
}
```

- The key is the `Payable` asset id — an asset IS its issuer cell's `token_id`
  (`dregg_payable::AssetId`), so bridged tokens (USDC/ETH deposit vouchers with
  a bridge-minted issuer) enter the same table with no special casing.
- **Fail closed**: the default table is empty; an asset absent from the table
  is refused. This generalizes the earlier single-asset knob
  (`accept_external_assets: false` + one `external_rate_micros`) without
  changing the default posture.
- `rate_micros` is the operator's local quote, nothing more. Setting it is
  rung 1's manual step; rung 2 (§5) replaces the hand-set number, not the
  table.

## 3. The refill flow (rung 1)

An accepted external-asset payment credits computrons in two steps, both in
`node/src/relay_service.rs`:

1. **`computron_credit(policy, asset, external_amount)`** — pure conversion
   with every gate fail-closed: unknown asset (`AssetNotAccepted`), disabled
   row (`AssetDisabled`), zero rate (`ZeroRate`), credit outside the signed
   64-bit balance domain (`CreditOverflow` — computed in u128, never wraps or
   saturates), and dust converting to zero computrons (`ZeroCredit` — accepting
   payment while crediting nothing would silently take the payer's asset).

2. **`apply_computron_refill(ledger, policy, operator_cell, voucher)`** — the
   credit lands as a `computron_transfers` entry in a `LedgerDelta`: the
   operator's pre-funded cell is debited and the recipient credited
   **atomically**, under the ledger's ordinary-move discipline (source may not
   go below zero). A refill exceeding the operator cell refuses
   (`OperatorCellInsufficient`) with no state change. **A refill is a transfer,
   never a mint** — total ledger supply is invariant across an accepted refill
   (test `computron_refill_accepted_conserves_exactly`).

Both polarities are pinned by adversarial tests (`computron_refill_*`): every
refusal arm bites, and the accepted path conserves exactly.

**Named residual — voucher binding.** Rung 1 does not verify the external
payment: `RefillVoucher` is the operator's own accounting input. The risk
profile makes this safe to stage: the operator credits out of its OWN cell, so
a false voucher only costs the operator its own computrons. Binding the voucher
to a bridge deposit attestation (the `Payable` receipt / light-client-verified
deposit) is the closure lane, and slots in as a precondition on
`apply_computron_refill` without touching the conversion or transfer logic.

## 4. Fee-distribution docking points

The refill is the INFLOW half of a loop whose OUTFLOW half already exists.
Computrons flow **to** the operator at:

- **Subscription** — `handle_subscribe` charges `fee_policy.subscription_fee`
  per created inbox.
- **Per-message deposits** — `fee_policy.min_deposit_computrons`, the floor a
  sender escrows per relayed message (also the proven-fee figure the dispute
  path uses, `node/src/relay_dispute.rs`).
- **GC fee sweep** — `RelayOperator::gc_expired` splits expired-message
  deposits into `operator_fees` (accumulating in `RelayOperator::earned_fees`,
  `storage/src/operator.rs`) and sender refunds.

The purchase path docks at the same cell: the operator's pre-funded cell is
where earned fees accumulate and where refills draw from. An operator's
computron position is therefore a plain cell balance — auditable, transferable,
and refillable by the operator itself through any path that funds a cell (a
faucet grant on devnet, a Transfer from another cell, or earned fees).

## 5. Rung 2 — rate discovery via DrEX (DESIGN, not built)

Rung 1's `rate_micros` is a hand-set static quote. Rung 2 replaces the
number's ORIGIN, not the table: the operator's quote becomes the outcome of a
cleared market, discovered by the proven ring-clearing engine
(`docs/deos/DREX-DESIGN.md`).

Sketch:

- **Refill offers as orders.** An operator posts *sell computron-refill for
  asset X* orders; users (or their agents) post *buy refill with X* orders.
  Both enter the aggregated book under the rung-2 aggregation theorems
  (`Market/Aggregation.lean` — faithful, no drop/insert/substitution/reorder),
  so an operator cannot be front-run out of the book it quoted into.
- **Clearing discovers the rate.** The priced clearing (`Market/Priced.lean`,
  `priced_clearing_keystone`; conservation ledger-realized through
  `Market/LedgerRealization*.lean`) clears crossing offers; the fill price IS
  the discovered computron rate for that instance. Conservation and both-sides
  fairness (`clearing_respects_limits`) are the already-proven rung-1 theorems:
  an operator is debited only computrons it offered, a buyer receives at least
  its declared minimum.
- **Policy stays sovereign.** The cleared price feeds
  `AssetRatePolicy::rate_micros`; the table's `enabled` bit and the fail-closed
  default remain
  the operator's local veto. DrEX discovers the number; the operator still
  chooses to accept it. Settlement of the refill leg itself stays the §3
  conserving transfer.
- **Still no peg.** A clearing instance's price binds only its participants for
  that clearing. Different operators clear at different prices in different
  instances; no global constant emerges, by construction.

What rung 2 requires beyond today: a refill order type mapping (asset X,
computrons) onto the exact-book matcher's `(offer_asset, want_asset)` pairs,
and the voucher-binding residual from §3 closed (a cleared fill must observe a
REAL deposit, not an operator-trusted voucher).
