# dregg-chain

EVM settlement layer for dregg: the Solidity contracts + host-side bridge flows
that let dregg proofs and value land on Base/Ethereum (or any EVM chain with the
EIP-196/197 pairing precompiles).

## What is here

```
contracts/DreggVault.sol           shielded vault: deposits → note commitments the
                                   federation mirrors into dregg's private note tree;
                                   withdrawals by wrapped proof; nullifier double-spend guard
contracts/DreggCredentialGate.sol  on-chain anonymous credentials: ring membership +
                                   predicate proofs gate mints/votes, per-action nullifiers
contracts/IDreggSettlement.sol     whole-history settlement: settle(a,b,c, genesisRoot,
                                   finalRoot, numTurns, chainDigest) → Settled event
test/*.t.sol, script/Deploy.s.sol  foundry tests + Base Sepolia deploy (see DEPLOY.md)
gnark/                             the native FRI-verifier wrap circuit (seed; see below)
src/                               host-side Rust: Base event listener, bridge runner,
                                   withdrawal/credential proof-flow drivers
```

## The wrap prover (the open piece)

On-chain verification needs the dregg recursive batch-STARK (`WholeChainProof`,
BabyBear/Poseidon2/FRI) wrapped into a ~256-byte Groth16/BN254 proof (~250–300k
gas to verify). The wrap prover is the **native gnark FRI-verifier circuit** —
design, milestones, and the honest size estimate in
`docs/deos/ETH-NATIVE-WRAP.md`; Lean spec + refinement obligation
(`GnarkRefines`) in `metatheory/Dregg2/Circuit/FriVerifier.lean`. The circuit
seed is `gnark/fri_verifier.go`.

Until the gnark path is wired, proof generation is **fail-closed**: without an
explicit feature choice the proof functions return
`ChainError::WrapProverMissing`. A dev/test build opts into simulated proofs
with `--features mock`. A build NEVER silently substitutes a simulated proof
for a real one.

The predecessor SP1 RISC-V-zkVM wrap was deleted (2026-07): it verified the
pre-Plonky3 legacy `GuestStarkProof` format — an artifact dregg no longer
produces — and paid a 1–2 order-of-magnitude interpreter tax on top
(`docs/deos/ETH-NATIVE-WRAP.md` §1). The contracts still expose the
`verifyProof(bytes32,bytes,bytes)` / `sp1Proof` ABI shape; that surface gets
renamed when the gnark-generated verifier contract replaces the gateway
(ETH-NATIVE-WRAP milestone 4).

## Building

```bash
# Standalone workspace (keeps the heavy alloy tree out of the main workspace)
cd chain && cargo check

# Tests (mock proofs, explicit opt-in)
cargo test --features mock

# Fail-closed behavior without features
cargo test

# With on-chain submission via alloy
cargo check --features mock,on-chain

# Solidity
forge build && forge test
```

## What settles where

- **Whole-history settlement** (`IDreggSettlement`): calldata encoding, public
  input binding, and the continuity/monotone-height state machine live in
  `bridge/src/ethereum.rs` (main workspace) — this crate carries the contract.
- **Vault withdrawals / credential presentations**: driven from `src/` here
  (`generate_withdrawal_proof`, `wrap_credential_for_chain`), both blocked on
  the wrap prover, mock-testable end-to-end today.
