# chain/gnark — dregg's native Ethereum wrap circuit

The modern replacement for the SP1 RISC-V-zkVM bridge (`chain/program/`,
`chain/src/prove.rs`). A **native gnark circuit over BN254** that verifies the
dregg shrink proof directly — no RISC-V emulation — and emits a Groth16/BN254
proof checked by `IDreggSettlement.settle`.

Design + rationale: **`docs/deos/ETH-NATIVE-WRAP.md`** and
**`docs/deos/WRAP-NATIVE-HASH-DECISION.md`**.

## Status

The REAL verifying circuit is **`SettlementCircuit`**
(`settlement_circuit.go`): one Define that, over the REAL exposed shrink proof
(`circuit-prove/src/apex_shrink_gnark_export.rs
shrink_apex_to_outer_exposed`, fixture `fixtures/apex_shrink_fri_real.json`):

1. replays the pre-FRI Fiat–Shamir transcript (MultiField challenger, every
   sampled challenge pinned);
2. runs the full batch-STARK algebra — constraint evaluation at zeta for all
   6 instances via the emitted symbolic AIR DAGs
   (`fixtures/shrink_symbolic_constraints.json`), quotient identities, global
   LogUp balance (`stark_verify_native.go`, `stark_constraint_interp.go`);
3. verifies the FRI core (`fri_verify_native.go`);
4. closes the open_input seam — input-batch Merkle openings against the
   transcript-observed commitments, reduced openings re-derived in-circuit
   (`stark_open_input.go`);
5. **binds the pinned 25-lane public settlement statement**
   (`genesis_root[8] ++ final_root[8] ++ num_turns ++ chain_digest[8]`,
   `fri_verifier.go Publics`) to the shrink proof's `expose_claim` public
   values — transcript-absorbed AND AIR-constrained, so the circuit cannot be
   satisfied for a root the proof does not attest; and
6. pins the shrink proof's preprocessed (op-list) commitment as a circuit
   constant (the shrink-VK core); and
7. **pins the APEX's VK identity** (the apex-VK pin): the apex's preprocessed
   commitment — in-circuit constrained by the Rust shrink
   (`pin_preprocessed_commit`) and re-exposed as `expose_claim` lanes 25..33 —
   is asserted equal to the DEPLOYED dregg apex's commitment as baked
   constants, so a same-shape malicious apex (doctored preprocessed columns,
   arbitrary false claim) cannot settle.

Compiled: **~12.2M R1CS** over BN254. `settlement_snark_test.go`
(`DREGG_SNARK=1`) runs the full Groth16 flow — compile, (dev/unsafe) setup,
prove the real witness, verify, reject a forged statement — and emits the
Solidity verifier (`chain/contracts/DreggGroth16Verifier25.sol`) plus the
calldata fixture for `chain/test/DreggSettlementRealProof.t.sol`, which
settles a REAL proof against the REAL generated verifier (no mock on the
accept path).

NAMED RESIDUALS (honest scope): the Groth16 setup is a single-party DEV
ceremony (a production VK needs an MPC).

## Why native, not zkVM

SP1 proves *RISC-V execution of* the verifier — every BabyBear op becomes ~10–40
constrained zkVM cycles (the emulation tax), ballooning millions of native ops
into tens-to-hundreds of millions of cycles. The native circuit makes one
BabyBear op ≈ one constraint. It also verifies the **current** fork proof
shape (the BN254-native-hash shrink of a `BatchStarkProof<DreggRecursionConfig>`
at `ir2_leaf_wrap_config`), not the legacy `GuestStarkProof` the SP1 guest
still encodes.

## What's reused

The entire non-cryptographic seam is already built and unchanged:
`bridge/src/ethereum.rs` (calldata, public-input binding, settlement state
machine) and `chain/contracts/IDreggSettlement.sol`. This module replaces the
*wrap prover*.
