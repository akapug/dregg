// Package friverifier is dregg's native Ethereum wrap circuit.
//
// It verifies, as a gnark circuit over BN254, a REAL dregg shrink proof (the
// BN254-native-hash re-proof of an `ir2_leaf_wrap` apex —
// circuit-prove/src/apex_shrink.rs) NATIVELY — one BabyBear field op per
// circuit constraint, no RISC-V emulation (contrast the legacy SP1 guest,
// chain/program/src/main.rs). The resulting Groth16/BN254 proof is checked by
// IDreggSettlement.settle. See docs/deos/ETH-NATIVE-WRAP.md and
// docs/deos/WRAP-NATIVE-HASH-DECISION.md.
//
// The REAL verifying circuit is SettlementCircuit (settlement_circuit.go):
// transcript replay + full batch-STARK algebra (symbolic constraint
// evaluation for all 6 instances) + FRI core + open_input commitment binding
// + THE 25-LANE PUBLIC SETTLEMENT STATEMENT below, bound to the verified
// proof's expose_claim channel. This file pins the shared public-input
// contract (lane order, count, canonicity law) used by both the circuit and
// the Solidity side.
//
// HISTORICAL NOTE: an earlier revision of this file carried a placeholder
// `Circuit`/`RootProofWitness` whose Define checked ONLY lane canonicity and
// the segment tooth over an unconstrained witness — a stub that could be
// mistaken for a verifier. It was REMOVED when SettlementCircuit landed; no
// non-verifying circuit exposes this public contract anymore.
package friverifier

import "github.com/consensys/gnark/frontend"

// DigestWidth is the number of BabyBear lanes in each root/digest of the
// pinned 25-lane public-input contract (see Publics).
const DigestWidth = 8

// NumPublicInputs is the pinned public-input lane count:
// genesis_root[8] ++ final_root[8] ++ num_turns ++ chain_digest[8] = 25.
const NumPublicInputs = 3*DigestWidth + 1

// Publics are the wrap circuit's Groth16 public inputs, in the EXACT pinned
// 25-lane order shared with the Solidity side:
//
//	genesis_root[0..8] ++ final_root[0..8] ++ num_turns ++ chain_digest[0..8]
//
// Every lane is a canonical BabyBear residue (strictly < 0x78000001 =
// 2013265921); SettlementCircuit.Define enforces this fail-closed. The
// Solidity ABI shape is (uint32[8] genesisRoot, uint32[8] finalRoot,
// uint32 numTurns, uint32[8] chainDigest). gnark exposes public inputs in
// struct field order, which matches the pinned order below (Publics is the
// FIRST field of SettlementCircuit).
type Publics struct {
	GenesisRoot [DigestWidth]frontend.Variable `gnark:",public"`
	FinalRoot   [DigestWidth]frontend.Variable `gnark:",public"`
	NumTurns    frontend.Variable              `gnark:",public"`
	ChainDigest [DigestWidth]frontend.Variable `gnark:",public"`
}
