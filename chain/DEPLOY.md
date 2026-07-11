# EVM Bridge Deployment (Base Sepolia)

Deploys DreggVault and DreggCredentialGate to Base Sepolia testnet.

## Prerequisites

- Foundry installed: `curl -L https://foundry.paradigm.xyz | bash && foundryup`
- Base Sepolia ETH (faucets: https://www.coinbase.com/faucets/base-ethereum-sepolia-faucet)

> **Verifier slot:** the contracts take `(verifier, programVkey)` at construction.
> The real values come from the native gnark wrap circuit
> (`docs/deos/ETH-NATIVE-WRAP.md`, milestone 4: `gnark-solidity-verifier` emits a
> concrete verifier contract + VK). Until then, deploy with `SP1MockVerifier`
> (always-accept, testnet only) to exercise the flow end-to-end.

## Setup

```bash
cd chain

# Install forge-std
forge install foundry-rs/forge-std --no-commit

# Copy env and fill in values
cp .env.example .env
# Edit .env with your deployer key, program vkey, etc.
source .env
```

## The verifier contract

The contracts call a verifier through the `verifyProof(bytes32,bytes,bytes)`
interface (named `ISP1Verifier` in the sources — the ABI shape predates the
gnark switch and gets renamed with the milestone-4 verifier swap):

```solidity
ISP1Verifier(verifier).verifyProof(vkey, publicValues, proofBytes)
```

The production verifier + `DREGG_PROGRAM_VKEY` are produced by the gnark wrap
circuit's setup (ETH-NATIVE-WRAP milestone 4). For testnet dry-runs, use
`SP1MockVerifier` (always-accept) as the verifier address.

## Build

```bash
forge build
```

## Test

```bash
forge test -vvv
```

## Deploy

```bash
forge script script/Deploy.s.sol \
  --rpc-url base_sepolia \
  --broadcast \
  --verify
```

The script will:
1. Deploy `DreggVault` (shielded deposit/withdraw, incremental Merkle tree)
2. Deploy `DreggCredentialGate` (credential-gated minting/voting, VK governance)
3. Log both deployed addresses

## Post-Deployment

1. **Verify on BaseScan** (if `--verify` didn't work):
   ```bash
   forge verify-contract <VAULT_ADDRESS> DreggVault \
     --chain base-sepolia \
     --constructor-args $(cast abi-encode "constructor(address,bytes32)" $SP1_VERIFIER_ADDRESS $DREGG_PROGRAM_VKEY)

   forge verify-contract <GATE_ADDRESS> DreggCredentialGate \
     --chain base-sepolia \
     --constructor-args $(cast abi-encode "constructor(address,bytes32,address)" $SP1_VERIFIER_ADDRESS $DREGG_PROGRAM_VKEY <DEPLOYER_ADDRESS>)
   ```

2. **Set trusted federation roots** on the credential gate:
   ```bash
   cast send <GATE_ADDRESS> "setFederationTrust(bytes32,bool)" <FEDERATION_ROOT> true \
     --rpc-url $BASE_SEPOLIA_RPC_URL \
     --private-key $DEPLOYER_PRIVATE_KEY
   ```

3. **Configure the dregg node** with the deployed vault address:
   ```toml
   # In dregg node config
   [bridge]
   rpc_url = "https://sepolia.base.org"
   vault_address = "<VAULT_ADDRESS>"
   ```

## Architecture

```
User deposits ETH/ERC-20 to DreggVault on Base
  -> Deposit event emitted with noteCommitment
  -> dregg bridge relay observes event
  -> Corresponding note created in dregg's private ledger

User wants to withdraw from dregg to Base:
  -> dregg wraps the STARK proof of note validity into Groth16 (native gnark wrap)
  -> User submits proof to DreggVault.withdraw()
  -> the deployed verifier contract checks the Groth16 proof on-chain
  -> Vault releases funds to recipient
  -> Nullifier recorded (prevents double-spend)
```
