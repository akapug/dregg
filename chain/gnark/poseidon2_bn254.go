// Poseidon2 width-3 permutation over the NATIVE BN254 scalar field, as a
// circuit gadget. This is the compression primitive for the re-architected
// STARK->EVM wrap (docs/deos/WRAP-NATIVE-HASH-DECISION.md): the emulated
// BabyBear Poseidon2 (poseidon2_w16.go, ~16,837 R1CS/perm) is replaced by a
// hash whose field of definition IS the proving field, so every S-box is a
// handful of native multiplications instead of a limbed emulated mul.
//
// Ground truth is dregg's pinned Poseidon2Bn254<3>:
//
//	~/.cargo/git/checkouts/plonky3-*/82cfad7/bn254/src/poseidon2.rs
//
// with parameters (Poseidon2 paper Table 1, (n,t,d)=(256,3,5)):
//
//	WIDTH = 3, S_BOX_DEGREE = 5, R_F = 8 (4 initial + 4 terminal), R_P = 56.
//
// The round constants (rc3ExtInitial / rc3Internal / rc3ExtTerminal in
// poseidon2_bn254_constants.go) are machine-extracted from HorizenLabs
// poseidon2_instance_bn256.rs RC3 — the exact table plonky3 pins as its zkhash
// reference.
//
// Permutation shape (external.rs external_initial_permute_state +
// internal.rs internal_permute_state):
//
//	extLinear(state)                       // initial external linear layer
//	4 × { +RC_init[r]; x^5 (all 3); extLinear }
//	56 × { state[0]+=RC; state[0]=x^5; intLinear }
//	4 × { +RC_term[r]; x^5 (all 3); extLinear }
//
// External linear layer for t=3 (mds_light_permutation, external.rs:130): the
// matrix circ-ish M_E = [[2,1,1],[1,2,1],[1,1,2]], computed as
// sum=s0+s1+s2; s_i += sum. Internal linear layer (bn254_matmul_internal,
// 1+diag([1,1,2]) = [[2,1,1],[1,2,1],[1,1,3]]): sum=s0+s1+s2;
// s0+=sum; s1+=sum; s2=2*s2+sum. Both are pure linear combinations, so they
// cost ZERO R1CS constraints — the whole permutation cost is the S-boxes.
package friverifier

import (
	"math/big"
	"sync"

	"github.com/consensys/gnark/frontend"
)

// bn254P3Width is the Poseidon2 state width for the BN254 instance.
const bn254P3Width = 3

// bn254P3HalfFull is R_F/2 — the number of initial (and terminal) full rounds.
const bn254P3HalfFull = 4

// bn254P3Partial is R_P — the number of partial (internal) rounds.
const bn254P3Partial = 56

// parsed round constants, materialised once from the hex tables.
var (
	bn254RCOnce        sync.Once
	bn254RCExtInitial  [bn254P3HalfFull][bn254P3Width]*big.Int
	bn254RCInternalBig [bn254P3Partial]*big.Int
	bn254RCExtTerminal [bn254P3HalfFull][bn254P3Width]*big.Int
)

func mustHex(s string) *big.Int {
	n, ok := new(big.Int).SetString(s, 0)
	if !ok {
		panic("poseidon2 bn254: bad constant " + s)
	}
	return n
}

func bn254InitRC() {
	bn254RCOnce.Do(func() {
		for r := 0; r < bn254P3HalfFull; r++ {
			for i := 0; i < bn254P3Width; i++ {
				bn254RCExtInitial[r][i] = mustHex(rc3ExtInitial[r][i])
				bn254RCExtTerminal[r][i] = mustHex(rc3ExtTerminal[r][i])
			}
		}
		for r := 0; r < bn254P3Partial; r++ {
			bn254RCInternalBig[r] = mustHex(rc3Internal[r])
		}
	})
}

// bn254Sbox raises x to the 5th power in the native field: x2 = x*x,
// x4 = x2*x2, x5 = x4*x — three R1CS multiplication constraints.
func bn254Sbox(api frontend.API, x frontend.Variable) frontend.Variable {
	x2 := api.Mul(x, x)
	x4 := api.Mul(x2, x2)
	return api.Mul(x4, x)
}

// bn254ExtLinear applies the t=3 external MDS light layer (pure linear).
func bn254ExtLinear(api frontend.API, s *[bn254P3Width]frontend.Variable) {
	sum := api.Add(s[0], s[1], s[2])
	s[0] = api.Add(s[0], sum)
	s[1] = api.Add(s[1], sum)
	s[2] = api.Add(s[2], sum)
}

// bn254IntLinear applies the internal diffusion matrix
// 1 + diag([1,1,2]) = [[2,1,1],[1,2,1],[1,1,3]] (pure linear).
func bn254IntLinear(api frontend.API, s *[bn254P3Width]frontend.Variable) {
	sum := api.Add(s[0], s[1], s[2])
	s[0] = api.Add(s[0], sum)
	s[1] = api.Add(s[1], sum)
	// s2 = 2*s2 + sum
	s[2] = api.Add(api.Mul(s[2], big.NewInt(2)), sum) // Mul by constant is linear, no constraint
}

// Poseidon2Bn254 applies the native BN254 Poseidon2 permutation (WIDTH=3,
// d=5) in place. Inputs and outputs are native field elements.
func Poseidon2Bn254(api frontend.API, state *[bn254P3Width]frontend.Variable) {
	bn254InitRC()

	// initial external linear layer
	bn254ExtLinear(api, state)

	// initial full rounds
	for r := 0; r < bn254P3HalfFull; r++ {
		for i := 0; i < bn254P3Width; i++ {
			state[i] = api.Add(state[i], bn254RCExtInitial[r][i])
		}
		for i := 0; i < bn254P3Width; i++ {
			state[i] = bn254Sbox(api, state[i])
		}
		bn254ExtLinear(api, state)
	}

	// partial rounds: RC + S-box on lane 0 only, then internal diffusion
	for r := 0; r < bn254P3Partial; r++ {
		state[0] = api.Add(state[0], bn254RCInternalBig[r])
		state[0] = bn254Sbox(api, state[0])
		bn254IntLinear(api, state)
	}

	// terminal full rounds
	for r := 0; r < bn254P3HalfFull; r++ {
		for i := 0; i < bn254P3Width; i++ {
			state[i] = api.Add(state[i], bn254RCExtTerminal[r][i])
		}
		for i := 0; i < bn254P3Width; i++ {
			state[i] = bn254Sbox(api, state[i])
		}
		bn254ExtLinear(api, state)
	}
}

// Poseidon2Bn254Compress is the 2-to-1 compression used for Merkle nodes:
// absorb (left, right) into a rate-2 sponge state (capacity 0) and squeeze
// lane 0. This is the standard fixed-length two-field compression built on the
// width-3 permutation.
func Poseidon2Bn254Compress(api frontend.API, left, right frontend.Variable) frontend.Variable {
	state := [bn254P3Width]frontend.Variable{left, right, 0}
	Poseidon2Bn254(api, &state)
	return state[0]
}
