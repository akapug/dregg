# TRUSTLINES — the bilateral line of credit: model, init edge, settlement

*(design charter for the ORGANS §1 weld; the verified model is
`metatheory/Dregg2/Apps/Trustline.lean`. Money as woven consent: a currency is
a web of bilateral credit lines, Ripple-classic mutual credit. Everything here
falls out of primitives already in the tree.)*

## 0. What a trustline is

Issuer A extends holder B a line of N: B may draw value against A's credit, up
to N, repeatedly, with repayment restoring the line. The line is DIRECTIONAL —
A→B is a different object from B→A; "mutual" credit is the pair.

**The pun, stated once and load-bearing:** a line of credit IS an attenuated
capability with a balance bound. `recKDelegateAtten`
(`metatheory/Dregg2/Exec/AuthTurn.lean:97`) makes granted ⊆ held qualitative;
the trustline makes the ⊆ quantitative — the holder's exercised credit never
exceeds the bound (`holder_credit_le_line_forever`), and the bound is an
immutable register (`ceiling_immutable_forever`). Adoption is attenuation: B
accepting A's currency = B holding a capability on A's well, attenuated to N.
Same primitive as everything else in the authority algebra.

## 1. What exists (the census, file-pinned)

The machinery is built end to end and disconnected at exactly one joint:

* **The counter.** `coord/src/budget.rs` (`StingrayCounter`, per-silo
  `BudgetSlice`, Ed25519 `SpendingCertificate`s) and
  `coord/src/shared_budget.rs` (escalation → `resolve_with_ordering` →
  `rebalance`). Verified models: `Dregg2/Proof/Stingray.lean` (`Slice`,
  `tryDebit`, `stingray_no_concurrent_overspend`),
  `Dregg2/Coord/SharedBudgetDynamics.lean` (tau-resolution conservation, the
  Byzantine `(f+1)/(2f+1)` ceiling, `rebalance_conserves`),
  `Dregg2/Coord/StingrayCertReconcile.lean` (cert reconciliation under the one
  named `CertUnforgeable` portal).
* **The gate in the hot path.** `turn/src/budget_gate.rs` (`BudgetGate`,
  `try_debit` at :142, digest registry at :29); the executor carries it
  (`turn/src/executor/mod.rs:431`, `with_budget_gate` :631) and the node's
  authoritative path seeds it PER TURN from the live coordinator
  (`node/src/blocklace_sync.rs:2070-2082`).
* **The surfaces.** MCP check/debit tools (`node/src/mcp.rs:4839`
  `tool_check_resource_budget`; :4908 the debit tool → `try_budget_debit`);
  the payment-channel demo (`demo-agent/examples/payment_channel_burst.rs`,
  100 sub-millisecond debits + epoch settle) on the same counter.
* **The stillborn joint.** `node/src/state.rs:1129 init_budget_coordinator`
  has ZERO callers — `budget_coordinators` is always empty, so the per-turn
  seeding at blocklace_sync.rs:2081 never fires and the gate is always
  `None`. The settlement edges dangle the same way:
  `collect_spending_certificates` (state.rs:1191) and `rebalance_budgets`
  (state.rs:1213, which already returns the `(agent, total_spent)` settlement
  list "for ledger settlement") have zero callers.
* **The value model.** `Dregg2/Substrate/IssuerLedger.lean`: `AssetId :=
  issuer CellId`, the issuer carries the NEGATIVE well, conservation is exact
  (`ConservedLedger`). A draw against a line is an issuer-move — production at
  the issuer's negative-capable well — never an out-of-thin-air mint.
* **The app pattern.** `Dregg2/Apps/StorageGatewayMandate.lean`: a
  `volume_spent` register under `.monotonic` + `.boundedBy` slot caveats,
  executor-enforced for the cell's whole life (`execFullForestA_progLive_preserved`),
  with `sgm_volume_legal_forever` on adversarial trajectories. The trustline's
  draw counter is this exact shape (minus monotonic — repayment moves it down).

## 2. The init edge (the missing caller)

**Design rule: the cell is the truth; the coordinator is a derived shadow.**
The trustline is born as a CELL (§3); `init_budget_coordinator` is called as a
downstream consequence of observing that birth, never as an independent
register. This keeps the Stingray metering layer a cache of proven state, so
the gate can never disagree with the ledger.

Three callers, one source of truth:

1. **The effect path (authoritative).** Extending a line is a turn: the
   issuer runs the trustline FACTORY (`createCellFromFactory`, the
   `EscrowFactory`/`ObligationFactory` precedent) which mints the trustline
   cell with its registers and caveats installed at birth. The node, on
   committing a trustline-cell birth, calls
   `init_budget_coordinator(agent := trustline cell, total_balance := line N,
   silos, f)` — the same place it already seeds the gate per turn
   (`blocklace_sync.rs`'s apply path). Re-extension/amendment of N is a
   governed write, which re-inits with a version bump (the coordinator's
   epoch `version` already rejects stale slices, `budget_gate.rs:144`).
2. **The funded birth (the "real ledger debit").** The extension is backed at
   birth, with the backing mode a typed parameter (the ORGANS
   parameterization discipline — reify, don't collapse):
   * `collateral := fullReserve` — the factory turn escrows N of a hard asset
     in the trustline cell's own balance column (the ObligationFactory bond
     pattern: bond in own `bal`, slash/settle = ordinary move). The line is
     then a payment channel (§5).
   * `collateral := pureCredit` — no hard backing; the draw is an issuer-move
     against A's negative-capable well, and the line N is exactly A's
     consented risk. This is the mutual-credit point on the axis; the
     conservation theorem (`trustline_conserved_forever`,
     `IssuerLedger.ConservedLedger`) is what makes "unbacked" still exact —
     credit is never created across the pair, only moved.
3. **The MCP/genesis conveniences.** A `dregg_extend_trustline` MCP tool that
   submits the factory turn (the existing check/debit tools at mcp.rs:4839
   become live the moment coordinators exist); genesis seeding for devnet
   (the docstring at state.rs:1126 already names "from a genesis block or
   epoch transition" — make it true).

One named residue carried with its lane: remote-silo pubkey registration from
federation membership (state.rs:1139-1143 marks it out of scope today) is
required before multi-silo rebalance certificates verify; single-silo (n=1)
collapses it, per the single-machine principle.

## 3. The bilateral cell shape

The trustline IS a cell. A and B are the parties; the line and drawn-amount
are registers; the caveats are the law, installed at factory-birth and
enforced by the executor for the cell's whole life (the SGM
`progLive_preserved` frame):

| register        | slot caveat                          | meaning                                  |
|-----------------|--------------------------------------|------------------------------------------|
| `issuer`        | `.immutable`                         | A — whose well the draws move against     |
| `holder`        | `.immutable`                         | B — who may exercise the line             |
| `line_ceiling`  | `.immutable` (amend = governed write) | N, the attenuation bound                  |
| `drawn`         | `.boundedBy 0 line_ceiling`          | the shared counter (up on draw, down on repay) |
| draw digests    | nullifier set / WriteOnce slots      | no-double-draw (the `BudgetSlice::debits` registry; precedent: PrivacyVoting vote-nullifiers, ShieldedPayment `noteSpend`) |

The credit balances themselves live on the REAL ledger, not in the cell: the
holder's credit is `bal B (asset A)` and the issuer's well is `bal A (asset
A)` (negative-capable), so `IssuerLedger`'s exact conservation covers the pair
with no new accounting. The Lean model
(`Dregg2/Apps/Trustline.lean`) carries both as registers and proves the
coupling invariant (`Line.WF`: the pair is exactly `±drawn`) survives every
adversarial schedule — the executor weld replaces the carried registers with
the real `bal` columns and the caveat table above.

Keystones proved on the model (all `#assert_axioms`-clean, non-vacuous both
polarities):

* `trustline_within_line_forever` — drawn ≤ N along every schedule (the SGM
  `boundedBy` pattern);
* `trustline_conserved_forever` — holder credit + issuer well = 0 forever
  (the draw is a move against A's well);
* `no_double_draw_forever` + `draw_replay_refused` — a digest debits once,
  ever (repayment does not resurrect it);
* `draw_repay_roundtrip` — settlement restores the line exactly
  (monotone-down then up);
* `settlePay_conserves_hard` + `settleAll_clears` — closing the line moves
  exactly the drawn amount across the hard-asset pair, conserving it;
* `draw_slice_tracks_tryDebit` / `draw_fires_iff_tryDebit` — the draw gate IS
  `Slice.tryDebit` (the executor's `BudgetGate.try_debit`), plus exactly the
  anti-replay leg.

## 4. Settlement returning to the ledger

The epoch close is already designed and modeled; it needs its callers:

1. epoch boundary → `collect_spending_certificates` (state.rs:1191) gathers
   this silo's signed spend;
2. federation gossip of certificates (the StingrayCertReconcile gates:
   version-match, ceiling, signature — proved at
   `Dregg2/Coord/StingrayCertReconcile.lean`);
3. `rebalance_budgets` (state.rs:1213) reconciles and returns
   `Vec<(agent, total_spent)>` — TODAY DROPPED ON THE FLOOR; the weld applies
   each entry as an ordinary ledger MOVE (holder → issuer in the hard asset
   for collateralized lines; the inverse issuer-move unwinding the credit legs
   for pure-credit lines). `settlePay_conserves_hard` is the law this
   application must satisfy; `rebalance_conserves`
   (SharedBudgetDynamics) is the law the reconciliation already satisfies.
4. coordinator version bump re-seeds the per-turn gate (already wired,
   blocklace_sync.rs:2081).

Partial repayment intra-epoch is just `repay` (a turn on the trustline cell);
the epoch settle handles the residual net position. `draw_repay_roundtrip`
guarantees the line is exactly restored either way.

## 5. Trustlines and payment channels: one primitive, two settings

`payment_channel_burst.rs` and the trustline run the SAME counter
(`StingrayCounter::try_debit`, consensus-free within the slice; epoch
rebalance with certificates). The settings differ in two parameters:

| parameter      | payment channel            | trustline                       |
|----------------|----------------------------|---------------------------------|
| collateral     | fullReserve (escrowed at open) | pureCredit (the issuer's consented risk) |
| lifetime       | burst → close              | standing; repayment restores it  |

So "open a channel" and "extend a line" are one factory with a typed
parameter, per the parameterization discipline. The channel demo is the
trustline organ's existing integration test.

## 6. Weld vs build

**WELD (exists; needs its caller/wire):**

* `init_budget_coordinator` caller — from trustline-cell birth in the node's
  apply path (+ genesis, + MCP tool). state.rs:1129.
* settlement application — `rebalance_budgets`'s returned settlements applied
  as ledger moves at the epoch hook; `collect_spending_certificates` called at
  the boundary. state.rs:1191/1213.
* the per-turn `BudgetGate` seeding — already wired (blocklace_sync.rs:2081);
  goes live the moment coordinators exist.
* MCP check/debit — already built (mcp.rs:4839/4908); live the same moment.
* remote-silo pubkey registry from federation membership (the named residue,
  state.rs:1139; n=1 collapses it).

**BUILD (new, design-named here; the Rust wiring belongs to the turn/-owning
lane, not this one):**

* the trustline factory cell-program (§3 registers + caveats) — the Lean model
  is `Dregg2/Apps/Trustline.lean`; the executor-welded twin
  (`TrustlineGated` on the one gated entry, the SGM/CWM Gated pattern) is the
  next Lean artifact;
* the draw leg as a gated issuer-move (kernel verbs exist; the composition
  draw = caveat-gated counter write + issuer-move is the new forest);
* the digest anti-replay at executor level (adapt the nullifier set /
  WriteOnce slot machinery);
* multilateral rippling (§7).

## 7. The honest obstruction: the multilateral case — NAMED-LATER

Rippling (A trusts B trusts C; A pays C through B by adjusting both lines) is
NOT in this wave's scope. The verdict, with its shape stated so the later lane
starts warm:

* a ripple is a COMPOSITION of proved bilateral primitives: one draw on the
  (B,C)-line and one repay/draw on the (A,B)-line, executed atomically — the
  atomic cross-cell machinery exists (`Dregg2/Coord/TwoPhaseCommit.lean`, the
  EntangledJoint N-cell-atomic path, the CrossCellCovenant bilateral joint
  path). Per-line conservation composes additively, so the multilateral
  conservation theorem is a sum of the bilateral ones;
* the genuinely hard parts are NOT the atomicity: (a) path discovery over the
  credit graph (routing — off-protocol in Ripple too, an indexer concern);
  (b) liquidity races — concurrent ripples contending for the same line
  capacity, which is EXACTLY the Stingray optimistic-overspend problem and
  inherits its answer (tau-ordered resolution, first-come-wins,
  `resolveOrdered_accepted_le_balance`); (c) exchange-rate/fee legs on
  heterogeneous lines (a pricing concern, not a conservation one);
* so multilateral = its own wave, on top of this one, with no new primitive —
  the bilateral cell + the existing joint-turn machinery carry it.

## 8. Order of work (this organ's lane)

1. Lean model + keystones — LANDED (`Dregg2/Apps/Trustline.lean`, this wave).
2. `TrustlineGated` on the one gated entry (Lean; SGM-Gated pattern).
3. The Rust weld (the turn/-owning lane): factory + birth-observer calling
   `init_budget_coordinator` + epoch settle applying `rebalance_budgets`.
4. The channel/line factory unification (one factory, the collateral
   parameter) + the MCP `dregg_extend_trustline` surface.
5. Multilateral rippling (named-later, §7).
