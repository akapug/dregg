# Private dregg behind a public launchpad — the rotation-absorbing architecture

*ember's question, stated exactly: can we run a REAL launchpad on public chains while
dregg stays fully private and rotates devnets/VKs freely — without exposing users to that
instability? The answer this doc argues, from the real contracts: **yes, because users
never touch dregg.** They touch (a) stable public-chain contracts that hold their assets
and (b) a stable public RPC that takes signed data; dregg clears privately and its result
enters the chain through ONE pluggable seam — `IClearingAttestor` — that carries a boolean,
never a VK. A devnet/VK rotation delays or re-runs a pending clearing at worst; it can never
strand an asset, because dregg never custodies one.*

**Grade of this doc.** DESIGN + INTERFACE VERIFICATION, read-only. Every contract claim is
cited to `chain/contracts/` at the file/line at HEAD. The engine/custody separation and the
`IClearingAttestor` seam are VERIFIED from the contract source. The concrete attestors
(`CommitteeAttestor`, `DreggProofAttestor`, `ConjunctiveAttestor`) and the timeout-refund
backstop (`reclaimEscrow`) are BUILT and cited below. The shielded-clearing finalize path
is DESIGNED-NOT-BUILT and graded as such. No contract or code is edited.

---

## 0. The shape in one diagram

```
                        PUBLIC (stable, permanent)                 PRIVATE (rotatable)
   ┌─────────┐   signed   ┌───────────────┐                     ┌──────────────────────┐
   │  user   │──order────▶│  public RPC   │───intent──────────▶ │  dregg (current       │
   │ wallet  │            │ (drex-web,    │                     │  devnet + current VK) │
   └────┬────┘            │  stable URL)  │◀──result+attest──── │  clears PRIVATELY     │
        │                 └───────────────┘                     └──────────┬───────────┘
        │ deposit (ETH) + sealed bid                                        │ attestation
        ▼                                                                   │ (sig  OR
   ┌──────────────────────────────────────────┐                            │  wrapped proof)
   │  DreggLaunchpad.sol   (holds escrow)      │◀───────────────────────────┘
   │  DreggLaunchToken.sol (hard-capped)       │      via IClearingAttestor.attestClearing()
   │  DreggSolventPool.sol (never-drainable)   │      → returns bool → gates finalizeClearing
   └──────────────────────────────────────────┘
        ▲                                    the ONLY dregg→chain channel is a boolean.
        │ assets live HERE, always.          the contract holds NO dregg VK. rotation invisible.
```

The user's assets sit in EVM contracts whose bytecode dregg cannot alter. dregg is a
matching engine reachable only through a stable RPC, and its verdict enters the chain only
as a boolean from a pluggable attestor. Those three facts are the whole safety argument;
the rest of this doc grounds each one in the source.

---

## 1. The separation: dregg is the engine, the contracts are the custody

The load-bearing invariant is **dregg never holds a user asset.** Every asset lives in one
of three stable contracts, and each is drainable-proof or hidden-supply-proof *by its own
code*, independent of any dregg state.

### 1.1 Escrow lives in the launchpad, not in dregg

A bidder's ETH is escrowed by `DreggLaunchpad.commitBid` into the launchpad's own balance
(`chain/contracts/launchpad/DreggLaunchpad.sol:312-330`): `b.deposit = msg.value` is booked
against the bidder's on-chain `Bid` record (`:326`). dregg is not in this path at all — a
commit is a plain EVM transaction to the stable contract. Settlement moves that
already-escrowed ETH by on-chain rules: `settleBid` (`:477-499`) pays `clearingPrice *
filled`, refunds the exact remainder `deposit - payment`, and the comment records the
invariant the code enforces — `deposit >= price*qty >= clearing*filled` (`:489`). A bidder
can never be charged more than they escrowed, and the refund is arithmetic, not discretion.

### 1.2 The token has no second mint door

`DreggLaunchToken` is hard-capped at construction and minted exactly once
(`chain/contracts/launchpad/DreggLaunchToken.sol:65-73`): `mint` reverts on `msg.sender !=
minter`, reverts on `minted` (the one-shot latch), and reverts on `amount > cap`. There is
no other path to circulating supply. No dregg state — no devnet, no VK, no clearing result —
can inflate the token, because the inflation function does not exist on the EVM.

### 1.3 The graduated pool cannot be drained

`DreggSolventPool` enforces a disclosed per-reserve floor on every swap: `buy` reverts with
`PoolFloorBreached` if the token reserve would fall below `floorToken`
(`chain/contracts/launchpad/DreggSolventPool.sol:135`), `sell` symmetrically for the
quote floor (`:161`), and reserves are tracked internally, not via `balanceOf`, so a
donation cannot move the accounting (`:46-49`). This is the on-chain realization of
`Market/Liquidity.lean`'s `pool_solvent_forever` (the contract header cites the tie at
`GraduationPool.lean`). Again: no dregg state can drain it, because the drain-below-floor
transition reverts in EVM code.

### 1.4 What this buys

Custody is **on the stable chain, enforced by contract code dregg cannot change.** The
strongest thing a compromised, dead, or rotated dregg can do to these assets is *nothing* —
it has no write handle to them except the one gated, value-conserving transition of §3. This
is the first leg of the safety proof (§4a).

---

## 2. The public interface: stable affordances + a stable signed-data RPC

The user's entire surface is two stable things. Neither is a dregg devnet or a VK.

### 2.1 The public affordances = the launchpad contracts (stable)

`DreggLaunchpad` / `DreggLaunchToken` / `DreggSolventPool` are the public affordances: a
launch is `registerLaunch → commitBid → revealBid → finalizeClearing → settleBid →
withdrawProceeds → graduate` (`DreggLaunchpad.sol:242-621`). These are ordinary EVM
contracts at fixed addresses. A user interacts with them through any wallet; their address
and ABI do not change when dregg re-genesises a devnet or flips a VK. The launch's public
inputs — the disclosed schedule — are committed on-chain and publicly checkable via
`checkSchedule` (`:301-303`), a pure re-derivation over `keccak256(abi.encode(s))`.

### 2.2 The public RPC = signed sealed data in, result out

Users submit **signed** data to a stable RPC, never to a devnet directly. The live shape is
`drex-web/serve.mjs` (traced in `docs/deos/DEVNET-DEPLOYMENT-REALITY.md` §2): the browser
places a sealed order, the `cipherclerk` wasm wallet signs it and attaches solvency/eligibility
proofs, `POST /clear` runs the real matching engine privately, and `POST /settle` lands the
result. For the launchpad the same pattern specializes to:

```
   signed sealed bid  ──POST /bid──▶  RPC forwards the on-chain commit tx (sealed hash + escrow)
                                       to DreggLaunchpad.commitBid   [asset custody = on-chain]
   signed reveal/intent ─POST /reveal▶ dregg receives the bid CONTENT privately (current devnet)
   (window closes)                     dregg clears the private book on the CURRENT VK
   result + attestation ◀──────────    RPC returns the clearing (price, fills) + an attestation
                                       anyone submits finalizeClearing(order/⊥, attestation)
                                       → settleBid pays each winner on-chain
```

The signature is the anti-forge tooth on the RPC: an order is a `cipherclerk`-signed
message, so the RPC (and dregg) cannot fabricate a bid the user did not sign, and the user
cannot repudiate one they did. The escrow always rides an on-chain `commitBid` — **the RPC
carries intent, never custody.** The user has touched exactly two stable things: the
launchpad contract (for the escrowed commit) and the RPC URL (for the signed content).
Which dregg devnet cleared it, and under which VK, is invisible to them.

### 2.3 The privacy dial — public reveal vs shielded

There are two grades of this flow, and they differ in whether the bid CONTENT ever appears
on-chain:

- **Public / REPLAYABLE (rung 1, DEPLOYABLE NOW).** `revealBid` opens each sealed bid
  on-chain (`DreggLaunchpad.sol:337-360`) and `finalizeClearing` computes the uniform
  clearing price on-chain from the revealed book via a permutation-checked descending sort +
  marginal-fill walk (`_runClearing`, `:424-451`). In this grade **dregg is not even in the
  settlement loop** — the contract clears itself from public data; `finalizeClearing` is
  permissionless (anyone may call it after `revealEnd`, within the clearing window
  `revealEnd + REFUND_GRACE`; past it the refund path of §5 takes over). This is the
  strongest safety story (dregg is non-load-bearing) but the weakest privacy story (bids are
  public at reveal).
- **Shielded (rung 3, DESIGNED-NOT-BUILT).** The bid CONTENT is never revealed on-chain;
  dregg clears the sealed book privately and only the *result* (`saleSupply`, `clearingPrice`,
  `bookCommit`) settles, gated by the attestor. This is the architecture ember is asking
  for — private dregg behind the RPC — and it is the one that *needs* the trust anchor of §3,
  because there is no public book for the contract to recompute. The design doc grades it
  SPEC/MODEL + UNBUILT (`docs/deos/DREGG-LAUNCHPAD-DESIGN.md` §2.4(b), §5); the shielded
  clearing mechanism itself is proved (`Market/ShieldedClearing.shielded_ring_clears`), but
  the launchpad-effect binding is a named weld.

The honest read: **the deployable-today path (rung 1) makes users immune to dregg by keeping
dregg out of the loop; the private-dregg path (rung 3) makes users immune to dregg by the
trust anchor of §3.** Both are safe for custody (§1); they differ in the liveness backstop
(§4) and the privacy grade. A launch can run rung 1 now and upgrade to rung 3 without
changing the custody contracts.

---

## 3. The rotation-absorbing trust anchor (the crux)

The question that decides everything: **does the contract hard-bind a specific dregg VK?**
If it does, a VK flip bricks a pending launch. It does not. Verified below.

### 3.1 `IClearingAttestor` is the pluggable seam — VERIFIED

The launchpad stores the attestor as an **address**, per launch, and consumes it as a
**boolean**:

- `Launch.attestor` is typed `IClearingAttestor` — an interface handle, i.e. an address
  (`DreggLaunchpad.sol:104`). `0` means REPLAYABLE-only (rung 1).
- It is set at registration from the caller's argument (`:249`, `:293`) and never mutated.
- `finalizeClearing` calls only `L.attestor.attestClearing(launchId, saleSupply,
  clearingPrice, bookCommit, clearingProof)` and branches on the returned `bool`
  (`:404-409`): a `false` reverts `ClearingNotAttested`, a `true` sets `clearingAttested`.

The interface signature is `attestClearing(uint256, uint256, uint256, bytes32, bytes)
external view returns (bool)` (`IClearingAttestor.sol:86-92`). **Read the type: there is no
Groth16 point, no verifying key, no verifier address anywhere in the launchpad's dependency
on dregg.** The `proof` is `bytes calldata` — arm-defined and opaque to the launchpad
(`:71`). The launchpad depends on a boolean from a pluggable contract at a pinned address,
and on *nothing else* from dregg.

**Verdict on the seam: YES, `IClearingAttestor` genuinely decouples the launchpad from
dregg's VK.** A VK rotation cannot break the launchpad because the launchpad never referenced
a VK — it references an attestor *address* and reads a *boolean*. Whatever the attestor
verifies internally (a signature, a proof under epoch N, a proof under epoch N+1) is behind
that address; the launchpad is on the far side of an opaque `bytes` blob and a `bool`.

### 3.2 The one honest nuance: the attestor is pinned per-launch

The attestor address is fixed at `registerLaunch` and immutable for that launch. So the
rotation-absorption cannot happen at the launchpad — it must happen *behind the attestor
address*, i.e. the attestor CONTRACT must itself be rotation-stable. That is the whole design
problem, and it has exactly the two fills below. (For an already-registered launch you cannot
swap the attestor; you rely on the attestor you pinned being one of the two stable kinds.)

### 3.3 What `IClearingAttestor` supports TODAY

Three concrete arms exist in `chain/contracts/launchpad/`, and the launchpad pins the SEAM,
never an arm:

- **`CommitteeAttestor.sol`** — the v1 signature arm (§3.4): threshold-of-n committee
  signatures over the clearing tuple, with on-chain fraud proof + slashing
  (`challengeAttestation`; a slashed committee attests nothing thereafter).
- **`DreggProofAttestor.sol`** — the v2 proof arm (§3.5): `attestClearing` is true iff a
  REAL dregg Groth16(BN254) wrap proof verifies on-chain through the OCIP socket
  (`contracts/socket/DreggVerifier.sol`), which targets the VK-epoch registry — no VK is
  pinned in the attestor. Tested against the real `settlement_groth16.json` fixture, both
  polarities.
- **`ConjunctiveAttestor.sol`** — "AND" over arms (both must attest; a withholding arm is a
  liveness fault into the refund backstop, never a theft).

The NAMED WELD that remains is the **statement, not the wiring**: the dregg wrap statement
is 25 pinned lanes (`genesis_root · final_root · num_turns · chain_digest`) with no lane for
a launch id, clearing price, or book commitment. So the proof attests *a conserved,
rule-abiding dregg transition on the pinned instance*, and the link "that transition IS this
launch's clearing" is asserted by an on-chain one-shot binder (`bindLaunch`, tied to the
launch's `scheduleCommit`) and is TRUSTED, not proved (`DreggProofAttestor.sol` §Trust).
Closing it needs the clearing tuple committed INSIDE the proof's public statement — circuit
work, not contract work. Until then the attestor gates, and never sources, the clearing
values: `_runClearing` computes them on-chain from the public revealed book.

### 3.4 Fill v1 — the operator/committee ATTESTATION (BUILT, trust-MINIMIZED)

`CommitteeAttestor.sol` is the concrete `IClearingAttestor` whose `attestClearing` checks a
**threshold-of-n committee signature** over `(launchId, saleSupply, clearingPrice,
bookCommit)` under a domain tag (`chain/contracts/launchpad/CommitteeAttestor.sol`). The
`proof` bytes carry the signatures; the attestor holds the committee member set and returns
`true` iff a quorum signed the tuple the contract computed.

- **Stable across all internal churn.** The committee signing key does not change when dregg
  re-genesises a devnet or flips a VK. A rotation is invisible to this attestor by
  construction — it never looks at a proof or a VK, only a signature over the result.
- **Provably fair internally, fraud-provable externally.** dregg proves the clearing is the
  fair uniform clearing of the committed book *internally* (the mechanism is proved:
  `uniform_price_no_arbitrage`, `uniform_price_envy_free`, `Market/Optimality.lean`). The
  `bookCommit` binds the exact book the clearing ran over (`DreggLaunchpad.sol:439`, a keccak
  fold over `(bidder, price, qty)`). A committee that signs a clearing that is **not** the
  fair clearing of that book has signed a statement a re-executor can disprove from the
  committed book + the proved mechanism — i.e. **a lie is fraud-provable**, the signature is
  the non-repudiable evidence, and the contract carries the tooth on-chain:
  `challengeAttestation` proves the inconsistency and **slashes** the committee (every
  subsequent `attestClearing` returns false, degrading its launches to the stall-then-refund
  backstop of §5).
- **The bounds the contract enforces regardless of the attestor.** Even a fully dishonest
  committee cannot: mint supply (no second mint door, §1.2), drain the pool (floor guard,
  §1.3), or charge a bidder more than their on-chain escrow (`settleBid` refund arithmetic,
  §1.1; and in the public grade, the per-bid `UnderCollateralized` check at reveal,
  `:352`). The attestor gates *whether* and *at what price* a clearing finalizes, inside a
  box the contract's own code makes value-conserving. The residual power of a corrupt v1
  committee is *misallocation within those bounds* (award the wrong winners / a suboptimal
  price) — a fairness fault, fraud-provable, **not a theft.**

This is exactly the trust posture of an L2 on day one: an operator you must trust for
*liveness and honest sequencing*, inside a contract that bounds what dishonesty can steal,
with fraud made evidential. **Trust-minimized, not trustless — and this doc says so.**

### 3.5 Fill v2 — a STABLE WRAP VK the contract never has to change

The trustless target: the attestor verifies a **proof** under **one outer verifier that never
changes**, and internal VK rotations are absorbed *below* that outer verifier.
`DreggProofAttestor.sol` is the concrete arm (§3.3): it verifies the wrap through the OCIP
socket, which targets the epoch registry — the attestor itself pins no VK. Two mechanisms in
the tree make the outer verifier genuinely stable:

**(a) The universal-fold wrap makes the STATEMENT stable.** The "universal fold"
(`project-universal-fold-buff-lightclient`) folds every off-AIR carrier into one recursion
tree so a single outer proof witnesses the whole turn. The settlement statement that reaches
the chain is a fixed 25-lane public-input vector — `genesis_root ++ final_root ++ num_turns ++
chain_digest` (`chain/contracts/DreggSettlement.sol:182-199`, `IDreggSettlement`). The
*shape* of what the outer verifier checks is stable even as the inner BabyBear VKs that prove
sub-AIRs rotate: a VK-epoch flip re-keys the inner proofs, but they are re-folded under the
same outer recursive statement. For the launchpad, the analogous stable statement is
`(saleSupply, clearingPrice, bookCommit)` — the exact tuple `attestClearing` already takes.

**(b) The upgradeable-VK registry makes the on-chain VERIFIER stable across a flip.** This is
the concrete, already-written contract that absorbs a VK-epoch flip on-chain:
`DreggGroth16VerifierUpgradeable` + `IGroth16VerifierRegistry`
(`chain/contracts/DreggGroth16VerifierUpgradeable.sol`). It moves the VK from *code constants*
into *storage keyed by epoch* (`:19-27`): a flip is one `advanceEpoch(newVk)` transaction, **no
redeploy** (`:150-163`); a proof targets an epoch and is checked against *that* epoch's VK, so
proofs minted under an old VK stay verifiable after the flip (`verifyProofAtEpoch`,
`:207-218`); and already-settled roots are unaffected. The gate is `onlyOwner` (`:117-120`),
and the contract's own header states the deploy law: **for a public instance the owner MUST be
governance behind a TIMELOCK** (`:46-54`), so a flip is observable and vetoable, not an
accept-anything backdoor.

**How the wrap absorbs a VK-epoch flip, concretely:**

1. dregg re-keys internally (nullifier flip, GAP-flip, re-genesis) → new inner VK epoch.
2. The clearing is re-proved under the new epoch and folded to the same outer 25-lane (or
   clearing-tuple) statement.
3. The stable-wrap attestor (`DreggProofAttestor`) delegates to the registry through the
   socket. The **attestor address and the launchpad are untouched.** The registry's *current
   epoch* moved; the *pinned public statement shape* did not.
4. A pending proof minted under the old epoch still verifies at its epoch (§registry), so an
   in-flight clearing is not even delayed by the flip — it settles under the epoch it was
   proved against.

**What makes the outer VK genuinely stable:** the outer verifier binds a *statement shape*
(the fixed public-input lanes), not the *inner circuit's key*. The inner keys are storage,
epoch-indexed, and a flip is an additive `advanceEpoch`, never an in-place mutation
(`setVerifyingKey` refuses to overwrite a set epoch, `:169-178`) — so nothing proved under a
past VK is invalidated or forgeable by a flip. The universal fold is what lets a rotating
inner circuit keep producing proofs of the *same* outer statement.

### 3.6 The honest migration

```
   v1 CommitteeAttestor (BUILT)   v2 DreggProofAttestor (BUILT)
   ────────────────────────────   ─────────────────────────────
   checks a quorum signature ──▶  checks a real proof via socket + epoch registry
   stable: signing key            stable: outer statement shape + epoch-indexed VK storage
   trust: operator/committee      trust: math (BN254 pairing) + governance-timelock on flips
   slashing on proven fraud       launch-binding TRUSTED (§3.3 statement weld) + dev-ceremony VK
   fraud-provable, bounded        trustless up to those two named residuals
```

All arms fit the *same* `IClearingAttestor` interface (plus `ConjunctiveAttestor` for
"both"), so the migration is a change of the pinned attestor CONTRACT for future launches —
**the launchpad, the token, the pool, and every user-facing surface are untouched.** That is
the payoff of the seam being a boolean: the trust model can harden from v1 to v2 without a
single change to custody or the public interface.

**Which does `IClearingAttestor` support today?** Both, concretely: `CommitteeAttestor` and
`DreggProofAttestor` are written and tested (both polarities; the proof arm against the real
Groth16 fixture). What is NOT done is the clearing tuple riding inside the proof's public
statement (§3.3 weld — until then the proof arm's launch-binding is a TRUSTED assertion),
and the registry's epoch-0 VK is a single-party dev ceremony. What runs with zero attestors
is **rung 1 REPLAYABLE** (attestor = 0, on-chain clearing) — for which dregg is not even in
the loop.

---

## 4. The safety proof: users are immune to dregg instability

**Claim.** For any reachable state of the private dregg system (devnet alive/dead/rotated, VK
current/flipped, dregg state present/lost), no user asset held by the launchpad, token, or
pool can be lost or stolen; the worst outcome is a *delayed or re-run clearing*.

**Proof structure — three legs, each grounded in §1–§3:**

**(a) Custody on the stable chain.** Every user asset lives only in `DreggLaunchpad` escrow
(§1.1), `DreggLaunchToken` balances (§1.2), or `DreggSolventPool` reserves (§1.3). dregg has
no write handle to any of them except the single `finalizeClearing` transition, and that
transition only *moves already-escrowed value* by contract-enforced, value-conserving rules
(`settleBid` refund arithmetic; pool floor; no second mint). ⇒ *Assets are safe regardless of
dregg's internal state,* because dregg cannot change the contract code that holds them.

**(b) The trust anchor absorbs VK rotation.** The launchpad's only dependence on dregg is the
attestor *boolean* (§3.1) — it holds no VK. A VK flip is absorbed either by a signature
attestor that never looked at a VK (v1, §3.4) or by the epoch registry that keeps every epoch
verifiable and makes a flip an additive one-tx `advanceEpoch` (v2, §3.5). ⇒ *The contract's
verifier never breaks on a rotation,* because the contract never pinned the thing that
rotated.

**(c) Worst case is delay/re-run, not loss.** The attestor gates *whether/at what price* a
clearing finalizes, inside the value-conserving box of (a). If the attestation is missing (a
dead devnet) the launch simply does not advance to `Cleared`; escrow sits in the launchpad,
recoverable (§4-modes). If the attestation is wrong it is bounded (§3.4) and fraud-provable.
⇒ *No dregg fault maps to a user loss;* it maps to a stalled or re-run clearing over safe
escrow.

### 4.1 Failure modes, itemized

| Failure | What happens on-chain | Safe for users? | Why |
|---|---|---|---|
| **dregg devnet dies mid-clearing** | No `finalizeClearing` lands; launch stays in `Reveal`/`Commit`. Escrow sits in `DreggLaunchpad`. | **YES** | Custody (a). **Public grade:** `finalizeClearing` is permissionless and needs no dregg — anyone recomputes the clearing on-chain after `revealEnd` (`:382-419`); dregg's death is irrelevant. **Any grade:** once the clearing window (`revealEnd + REFUND_GRACE`) elapses un-cleared, `reclaimEscrow` (`:515-537`) permissionlessly refunds every committed bidder's full deposit — stall-then-refund, never loss. |
| **VK flips mid-clearing** | Attestor unaffected (v1 sig) or old epoch still verifies (v2 registry, `verifyProofAtEpoch`). Launch finalizes normally, possibly re-proved under the new epoch. | **YES** | Trust anchor (b). The launchpad holds no VK; the flip is behind the attestor. Worst case: re-prove under the new epoch — a delay, not a loss. |
| **dregg state / devnet re-genesis (state lost)** | On-chain schedule commit + escrowed deposits + minted token survive on the stable chain untouched. Clearing is recomputable (public grade) or re-provable on the new devnet (shielded grade). | **YES** | Custody (a) + re-run (c). dregg re-genesis touches no EVM state. |
| **Attestor returns a WRONG clearing (corrupt v1 committee)** | Finalizes at a wrong price/allocation, inside the contract's bounds: no over-mint, no pool drain, no charge above escrow. | **BOUNDED + fraud-provable** | §3.4. A fairness fault, not a theft; the `bookCommit` + proved mechanism + the committee signature make it evidential. This is the honest v1 trust surface. |
| **RPC down / censoring** | Users cannot submit new signed intents through the private path. | **YES (assets) / liveness hit** | Custody (a). Assets are on-chain and untouched. Backstop: the public-grade on-chain commit/reveal path does not require the private RPC (a user can `commitBid`/`revealBid` directly). |
| **Malicious operator tries to steal escrow** | No transaction exists that pays an operator from escrow: `settleBid` pays the bidder and `withdrawProceeds` pays only `L.creator` the winners' payments (`:547-558`). | **YES** | The theft function is not in the contract. dregg/operator has no drain door. |

### 4.2 The formal statement

Let `S` be any dregg internal state and `A` the pinned attestor. The launchpad's post-state
is a function only of (i) on-chain escrow/schedule/token/pool state and (ii) the boolean
`A.attestClearing(tuple)`. dregg influences the launchpad **solely** through that boolean and
the `tuple` it attests. Since (1) the value-flow of every launchpad transition is bounded and
conserved by contract code independent of the boolean (§1), and (2) the boolean's provenance
(sig or epoch-registry proof) is stable across all rotations of `S` (§3), the map from
"dregg instability" to "user asset outcome" has range ⊆ {finalize-in-bounds,
stall/re-run} — and *loss* ∉ that range. ∎ (modulo the residuals of §5.)

---

## 5. Honest residuals — what this does NOT cover

- **v1 is trust-minimized, not trustless.** The committee attestor is an operator trust
  surface: a corrupt quorum can misallocate *within* the contract's bounds (wrong winners /
  suboptimal price) — bounded, fraud-provable, and slashable (§3.4), but real. Do not narrate
  v1 as trustless.
- **v2's launch-binding is TRUSTED, and the epoch-0 VK is a dev ceremony.**
  `DreggProofAttestor` verifies a real proof, but the wrap statement carries no launch id /
  clearing lanes, so "this transition IS this launch's clearing" is a binder assertion, not a
  theorem (§3.3 statement weld — circuit work). And the registry's epoch-0 VK is a
  single-party dev ceremony (toxic-waste-known); production trust waits on the MPC ceremony.
- **Liveness on a stall resolves to refund, in every grade.** A dead/rotating devnet stalls a
  clearing; escrow is safe (custody), and once `revealEnd + REFUND_GRACE` elapses un-cleared,
  `reclaimEscrow` (`DreggLaunchpad.sol:515-537`) permissionlessly refunds each committed
  bidder's full deposit. The clearing and refund windows are DISJOINT (`ClearingWindowClosed`
  / `RefundNotYetAvailable`), and a per-bid `refunded` latch forbids double-refund
  (`AlreadyRefunded`) — a stale clearing can never override refunds, nor refunds drain a
  cleared launch.
- **The shielded finalize path is designed-not-built.** The current `finalizeClearing` always
  computes the clearing on-chain and treats the attestor as an *additional* check
  (`:399-410`), so it requires bids revealed on-chain. The fully-private "dregg clears, only
  the result settles" needs a shielded `finalizeClearing` variant where the attestor is the
  *sole* source of `(clearingPrice, soldQty, bookCommit)`, with per-bidder escrow kept
  on-chain (only bid *content* hidden) so the contract still bounds each payment by each
  deposit. Graded SPEC/MODEL + UNBUILT (`DREGG-LAUNCHPAD-DESIGN.md` §2.4(b)).
- **The proof covers the mechanical surface only.** As `LAUNCHPAD-OPPORTUNITY.md` §5 states:
  a fairly-launched token can still go to zero; the mechanism fixes the rigged wheel, not the
  casino. "Immune to dregg instability" is a claim about *custody + settlement integrity*, not
  about token value or team conduct.
- **Deploy gates (per MEMORY).** VK-epoch flip + re-genesis, public broadcast, funded-key
  testnet `--broadcast`, and the production MPC VK ceremony are ember-gated; today's on-chain
  proofs ride a dev ceremony (`DEVNET-DEPLOYMENT-REALITY.md` §3, §gated).

---

## 6. Verdict

**Does `IClearingAttestor` actually decouple the contract from dregg's VK? — YES, verified.**
The launchpad stores the attestor as an address (`DreggLaunchpad.sol:104`) and consumes it as
a boolean over `(launchId, saleSupply, clearingPrice, bookCommit, proof)` with `proof` opaque
`bytes` (`:404-409`, `IClearingAttestor.sol:86-92`). The launchpad's dependency on dregg
contains **no VK, no verifier, no Groth16 point** — so a VK rotation cannot break it, because
it never referenced the thing that rotates. The rotation is absorbed *behind* the attestor
address, by either a stable committee signature (`CommitteeAttestor`, v1) or the
epoch-indexed VK registry behind the socket (`DreggProofAttestor` →
`DreggGroth16VerifierUpgradeable`, v2).

**Can we safely run a real launchpad with private dregg behind a public RPC? — YES for
custody; YES for liveness in every grade** (permissionless on-chain finalize in the public
grade; the permissionless `reclaimEscrow` timeout-refund past `revealEnd + REFUND_GRACE` in
all grades). Users' assets live only in stable EVM contracts that are hidden-supply-proof,
un-drainable, and escrow-bounded by their own code (§1), and dregg's only channel to them is
a value-conserving, attestor-gated transition (§4). Every dregg failure mode maps to *stall,
refund, or re-run over safe escrow*, never loss (§4.1).

**The honest v1 trust surface:** the committee attestor is an operator you trust for
*honest sequencing and liveness*, inside a contract that bounds what dishonesty can do to
*misallocation, not theft*, with the wrong result *fraud-provable* from the committed book and
the Lean-proved mechanism, and *slashable* on-chain. That is trust-**minimized** (an L2
day-one posture), not trustless; trustlessness is v2 (`DreggProofAttestor`), whose residuals
are the trusted launch-binding (§3.3 statement weld) and the dev-ceremony epoch-0 VK. Stated
plainly, not dressed up.

The architecture is real: **keep dregg private and rotatable, expose only the stable
contracts and a stable signed-data RPC, and let a boolean-returning pluggable attestor be the
one seam — a seam that carries a result, never a key, so rotation is invisible to everyone who
matters, which is the users.**

---

## Sources (read-only)

- `chain/contracts/launchpad/IClearingAttestor.sol` — the seam (interface + honest scope).
- `chain/contracts/launchpad/DreggLaunchpad.sol` — attestor consumption (`:104`, `:293`,
  `:404-409`), escrow/settle (`:312-330`, `:477-499`), permissionless finalize +
  timeout-refund (`:382-419`, `:515-537`), graduation.
- `chain/contracts/launchpad/CommitteeAttestor.sol` — the v1 signature arm (threshold-of-n,
  fraud challenge + slashing).
- `chain/contracts/launchpad/DreggProofAttestor.sol` — the v2 proof arm (socket + epoch
  registry; §Trust names the launch-binding residual).
- `chain/contracts/launchpad/ConjunctiveAttestor.sol` — "AND" composition over arms.
- `chain/contracts/launchpad/DreggLaunchToken.sol` — one-shot hard-capped mint (`:65-73`).
- `chain/contracts/launchpad/DreggSolventPool.sol` — floor guard (`:135`, `:161`).
- `chain/contracts/launchpad/ILaunchEligibility.sol` — the pluggable-oracle sibling pattern.
- `chain/contracts/DreggSettlement.sol` — the pinned-verifier + stable 25-lane statement.
- `chain/contracts/DreggGroth16VerifierUpgradeable.sol`, `IGroth16VerifierRegistry.sol` — the
  epoch-indexed VK registry that absorbs a VK-epoch flip on-chain (the v2 mechanism).
- `docs/deos/DREGG-LAUNCHPAD-DESIGN.md` (§2.2, §2.4, §5), `docs/deos/LAUNCHPAD-OPPORTUNITY.md`
  (§3, §5), `docs/deos/DEVNET-DEPLOYMENT-REALITY.md` (§2, §3) — the mechanism, the RPC flow,
  the honest infra grade.
- `project-universal-fold-buff-lightclient` — the stable outer statement the wrap folds to.
