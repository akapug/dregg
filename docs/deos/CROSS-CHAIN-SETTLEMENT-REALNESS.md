# CROSS-CHAIN SETTLEMENT — the realness pass (2026-07-14)

A follow-on to `DEVNET-DEPLOYMENT-REALITY.md`, which found the on-chain
settlement was a **pre-generated fixture** proof, the Solana/Cosmos verifiers
**built-but-undeployed**, and the light clients **verified rules with no running
binaries**. This pass closes as much of that gap as is non-gated, and states
precisely what remains a fixture and why. Everything below was RUN this session;
no public broadcast, no funded key, no production ceremony.

---

## 1. The wrap, minted FRESH this session (not a replayed byte-fixture)

The whole STARK→EVM wrap ran end-to-end on this machine, from a **cold** cache,
not by replaying the committed proof bytes:

| stage | what ran | cost (this session) |
|---|---|---|
| apex fold | `prove_turn_chain_recursive` over a 2-turn chain → `ir2_leaf_wrap` apex | **264 s** |
| BN254 shrink | `shrink_apex_to_outer` → `BatchStarkProof<DreggOuterConfig>` | **105 s** |
| export + self-check | real `p3 pcs.verify` + host-side FRI re-verify, then emit `chain/gnark/fixtures/apex_shrink_fri_real.json` | 0.24 s |
| Groth16 R1CS | `SettlementCircuit` compile | 12.9 s (**4,980,767 constraints**) |
| Groth16 setup | dev single-party params (cache HIT, fingerprint `daddc8c7…`) | 1.2 s |
| Groth16 prove | fresh proof over the fresh witness | **16.7 s** |
| Groth16 verify | in-Go verify PASS + forged-statement REJECT | 2 ms |

Regenerate:
```bash
# apex + shrink (cold ≈ 6 min; caches to ~/.cache/dregg-shrink)
cargo test -p dregg-circuit-prove --release --test apex_shrink_gnark_fixture \
  export_real_shrink_fri_fixture_for_gnark -- --ignored --nocapture
# Groth16 wrap → emits the verifier + the calldata fixture
cd chain/gnark && DREGG_SNARK=1 go test -run TestSettlementGroth16EndToEnd -v -timeout 240m
```

**Result of the refresh (vs the previously-committed artifacts):**
- The generated verifier `DreggGroth16Verifier25.sol` and the `.vk` are
  **byte-identical** to the committed ones — the dev-ceremony VK is stable, and
  the fresh proof is consistent with the on-chain-deployed verifier's VK.
- The `settlement_groth16.json` proof **points differ** (an independent fresh
  Groth16 prove) while the **statement is identical** (`genesis_root`,
  `final_root`, `num_turns=2`, the 25-lane public input vector all unchanged).
  So this is a genuinely re-minted proof of the same real state transition, not
  the old bytes.

### Verified LOCALLY against the REAL verifiers (the actual accept path)

- **Base-Sepolia Solidity** — `forge test --match-contract DreggSettlementRealProofTest`
  → **7/7 pass**: the real EIP-197 pairing accepts the fresh proof
  (`test_GeneratedVerifierAcceptsRealProofRaw`, `test_RealProofSettles`), and the
  real pairing **rejects** a tampered proof point, a tampered Pedersen
  commitment, a wrong final root, and a wrong genesis root.
- **Solana** — `cd solana-settlement && cargo test --release` → **2/2 pass** in a
  real `solana-program-test` BPF bank: `real_proof_settles_and_advances_root`
  (BN254 verify via `alt_bn128` syscalls) + `forged_proof_rejected_root_unchanged`.
- **Cosmos (CosmWasm)** — `cd cosmos-settlement && cargo test --release` →
  **5/5 pass**: `real_proof_settles_on_cosmos` (arkworks BN254) + 4 reject
  canaries (tampered point, tampered commitment, wrong final root, broken
  continuity).

The SAME real proof verifies on all three chains' verifiers and every forgery is
refused by the real cryptographic check.

### HONEST: what is still a fixture in the wrap, and why

The apex the wrap folds is a **synthetic 2-turn `IncrementNonce` chain** built
in-process (`circuit-prove/tests/apex_shrink_gnark_fixture.rs::make_turn`), NOT a
turn served by the live node. Two independent reasons, both named, neither a
surprise:

1. **No `FullTurnProof` → `FinalizedTurn` adapter exists.** The live node emits a
   `FullTurnProof` (a composed Effect-VM STARK; `node/src/turn_proving.rs`) at
   `GET /api/turn/{h}/proof`. The wrap folds `FinalizedTurn` /
   `DescriptorParticipant` objects (`prove_turn_chain_recursive`,
   `circuit-prove/src/ivc_turn_chain.rs`). Nothing in the tree converts one to
   the other. Building that adapter is **the** next real step for a literal
   node-turn → wrap; it was out of scope for this pass (it lives adjacent to the
   effect-VM / turn-proving surface a concurrent lane owns).
2. **Value-bearing `Transfer` into the wrap is blocked** by a mid-flight sibling
   wide-registry cutover (GAP #4): a `Transfer` leg fails host admission ("not a
   known R=24 cohort member"), so only `IncrementNonce` currently traverses the
   fold. `make_turn`'s own doc-comment records this.

Also honest and unchanged: the Groth16 trusted setup is a **single-party dev
ceremony** (toxic-waste-known). A production MPC ceremony is ember-gated.

---

## 2. A REAL live-turn proof on the node (cited)

To ground "an actual dregg turn," a real value-bearing turn was driven on the
live solo node (hbox `127.0.0.1:8420`, `--prove-turns --enable-faucet`,
committee-of-one) — the same `/turn/submit` path `drex-web` uses:

- **turn_hash** `48419c58d0ed2d847c143ffe1d209c6f5351f735cb6cce9df82fd1999eeec489`
- effects: `Transfer(operator a2c4bbc0… → 271d67c9…, amount 1)` + `EmitEvent` —
  real value moved (operator `17850→16349`, nonce `8→9`; dest `500→501`).
- receipt: `chain_index 21`, `pre_state 830d6178… → post_state df690328…`,
  `computrons_used 875`, **`has_proof: true`, `witness_count: 1`,
  `executor_signed: true`**, `finality: tentative` (solo).

So the node genuinely **executes real value turns and attaches a self-verified
full-turn STARK proof** to them. This proof is NOT the object the EVM wrap
consumes (see §1.1) — it corroborates the node side is real; it does not itself
settle on-chain. Bridging `48419c58`'s `FullTurnProof` into the wrap is exactly
the missing adapter.

---

## 3. Running light-client binary (was: rules-only libraries)

`eth-lightclient/src/bin/verify_holding.rs` is a **running** Ethereum light
client built from the crate's verified rules. It follows the beacon-header trust
chain over REAL captured mainnet data and settles an ERC-20 holding:

```
cargo run -p eth-lightclient --bin verify_holding
```
```
1. verify_sync_aggregate  (slot 14751307, 397/512 participation) ... OK (real BLS12-381 aggregate accepted)
2. verify_committee_update (committee proven under prev period)   ... OK (SSZ next_sync_committee branch accepted)
3. verify_finalized_update (finality depth 7 + execution depth 4) ... OK  (finalized block 25514839)
4. verify_erc20_holding_finalized (WETH holder 0x8eb8a3b9…)       ... OK
   SETTLED HOLDING (trust = ConsensusProven): 23505.483594361465965613 WETH at Ethereum block 25514839
5. reject canary: forged balance (+1 wei) must be REFUSED         ... REFUSED (fail-closed at the storage-trie gate)
```

Every artifact is external mainnet data (committee pubkeys, aggregate G2
signature, both Merkle branches, EIP-1186 MPT proofs — provenance
`tests/fixtures/e2e_mainnet.rs`); the bin is fully offline (a real captured
checkpoint compiled in). A live LC swaps the checkpoint for `beacon_getState` +
`eth_getProof` behind the **same** verified rules — the rules are the part that
was missing a runnable entry, and now has one.

**Scaffolded from the same rules (running bins are follow-ups):** the Cosmos
Tendermint verifier (`cosmos-lightclient`, real cosmoshub-4 header + ATOM
membership fixtures) and the Base OP-stack / fault-proof verifier
(`eth-lightclient::base` / `base_fault_proof`, live Base output 12086 + dispute
game 17049) each have offline accept tests that a thin bin mirrors identically.

---

## 4. The deploy path — dry-run-validated, keyless (broadcast is ember's)

All three verifier deploys were validated without a funded key and without
`--broadcast`.

### Base-Sepolia Solidity (chainId 84532) — fork dry-run against LIVE testnet state
```bash
cd chain
# keyless local simulation:
forge script script/DeploySettlement.s.sol:DeploySettlement
# read-only FORK of the real testnet (no key, no broadcast):
forge script script/DeploySettlement.s.sol:DeploySettlement --rpc-url https://sepolia.base.org
```
Both simulate the full 3-contract deploy (verifier → adapter → settlement) AND
settle the fresh real proof: `provenHeight=2`,
`provenRoot=0x6ca8f74fdb101030ff19604100917452b750906cffdb216cc889eea8e364b868`
(the same root recorded for the live Base-Sepolia settle). Fork estimate:
~5.21M gas / ~0.0000568 ETH. `SIMULATION COMPLETE` — nothing broadcast.

### Solana native program — BPF program-test bank (keyless)
```bash
cd solana-settlement && cargo test --release   # BPF bank verifies the real proof + rejects forgeries
```

### Cosmos CosmWasm — the built .wasm + arkworks verify (keyless)
```bash
cd cosmos-settlement && cargo test --release    # arkworks BN254 verify of the real proof + rejects
# artifact: cosmos-settlement/artifacts/cosmos_settlement.wasm (checksum in checksums.txt)
```

---

## 5. EMBER-GATED (the outward steps — NOT done here)

- **Public broadcast** of any verifier deploy with a **funded (throwaway) key** —
  `forge script … DeploySettlement --rpc-url base_sepolia --broadcast --verify`
  (EMBER inputs: `DEPLOYER_PRIVATE_KEY`, optionally `DREGG_GENESIS_ANCHOR` for a
  real devnet anchor); the Solana `solana program deploy`; the Cosmos
  `wasmd tx wasm store`.
- **Production MPC VK ceremony** — today's proof rides the single-party dev
  ceremony (toxic-waste-known).
- **VK-epoch flip / re-genesis** of the devnet; **live/real tokens**; **mainnet**;
  the security-review sign-off + go-live decision.

---

## The honest one-line map

Fixtures → real, this session: the wrap is **freshly minted and verified against
the real Base/Solana/Cosmos verifiers locally**; a **running light-client bin**
settles a real mainnet WETH holding; the **deploys dry-run against real testnet
state keyless**; and a **real live-turn STARK proof** exists on the node
(`48419c58…`, `has_proof:true`). The one remaining fixture in the settle path is
the wrap's **apex turn body** — a synthetic `IncrementNonce` chain, not the
node's served `FullTurnProof` — because the `FullTurnProof → FinalizedTurn`
adapter does not yet exist (and `Transfer`-into-the-wrap waits on the sibling
wide-registry regen). That adapter is the single next step to a literal
live-node-turn → on-chain settlement.
