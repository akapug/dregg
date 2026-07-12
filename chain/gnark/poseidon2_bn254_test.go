package friverifier

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/test"
)

// Gold KAT: Poseidon2Bn254<3> permutation of [0,1,2], produced by the
// HorizenLabs zkhash plain implementation (the exact reference plonky3 pins),
// run at ~/.cargo/git/checkouts/poseidon2-*/plain_implementations against
// POSEIDON2_BN256_PARAMS. This pins the constants, S-box, layer order, and
// both linear layers simultaneously.
var bn254KATOutHex = [3]string{
	"0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033",
	"0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570",
	"0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8",
}

func frFromU64(x uint64) fr.Element {
	var e fr.Element
	e.SetUint64(x)
	return e
}

// The reference permutation reproduces the zkhash gold vector exactly.
func TestPoseidon2Bn254RefMatchesGoldKAT(t *testing.T) {
	state := [3]fr.Element{frFromU64(0), frFromU64(1), frFromU64(2)}
	poseidon2Bn254Ref(&state)
	for i := 0; i < 3; i++ {
		want := frFromHex(bn254KATOutHex[i])
		if !state[i].Equal(&want) {
			t.Fatalf("lane %d: reference diverges from zkhash gold KAT:\n got %s\nwant %s",
				i, state[i].String(), want.String())
		}
	}
}

// REJECT-polarity for the KAT itself (guard against a vacuous comparison).
func TestPoseidon2Bn254RefKATBites(t *testing.T) {
	state := [3]fr.Element{frFromU64(0), frFromU64(1), frFromU64(3)} // last lane tampered
	poseidon2Bn254Ref(&state)
	want := frFromHex(bn254KATOutHex[0])
	if state[0].Equal(&want) {
		t.Fatal("tampered input still produced the gold KAT output")
	}
}

// --- circuit vs reference (independent implementations must agree) ---

type poseidon2Bn254Circuit struct {
	In  [3]frontend.Variable
	Out [3]frontend.Variable
}

func (c *poseidon2Bn254Circuit) Define(api frontend.API) error {
	state := c.In
	Poseidon2Bn254(api, &state)
	for i := range state {
		api.AssertIsEqual(state[i], c.Out[i])
	}
	return nil
}

func bn254PermWitness(in [3]uint64) *poseidon2Bn254Circuit {
	state := [3]fr.Element{frFromU64(in[0]), frFromU64(in[1]), frFromU64(in[2])}
	poseidon2Bn254Ref(&state)
	w := &poseidon2Bn254Circuit{}
	for i := 0; i < 3; i++ {
		w.In[i] = new(big.Int).SetUint64(in[i])
		w.Out[i] = state[i].BigInt(new(big.Int))
	}
	return w
}

func TestPoseidon2Bn254CircuitMatchesGoldAndRef(t *testing.T) {
	field := ecc.BN254.ScalarField()

	// Gold vector straight through the circuit.
	w := &poseidon2Bn254Circuit{}
	w.In[0], w.In[1], w.In[2] = 0, 1, 2
	for i := 0; i < 3; i++ {
		v, _ := new(big.Int).SetString(bn254KATOutHex[i], 0)
		w.Out[i] = v
	}
	if err := test.IsSolved(&poseidon2Bn254Circuit{}, w, field); err != nil {
		t.Fatalf("circuit rejects the zkhash gold KAT: %v", err)
	}

	// Randomized differential vs the reference twin.
	inputs := [][3]uint64{{0, 0, 0}, {1, 2, 3}, {7, 42, 999}, {1 << 40, 1 << 50, 1 << 60}}
	for _, in := range inputs {
		if err := test.IsSolved(&poseidon2Bn254Circuit{}, bn254PermWitness(in), field); err != nil {
			t.Fatalf("circuit diverges from reference on %v: %v", in, err)
		}
	}
}

// REJECT polarity: a tampered output lane must fail.
func TestPoseidon2Bn254CircuitRejectsTamperedOutput(t *testing.T) {
	field := ecc.BN254.ScalarField()
	w := bn254PermWitness([3]uint64{7, 42, 999})
	// bump lane 1
	bad := new(big.Int).Add(w.Out[1].(*big.Int), big.NewInt(1))
	w.Out[1] = bad
	if err := test.IsSolved(&poseidon2Bn254Circuit{}, w, field); err == nil {
		t.Fatal("circuit accepted a tampered permutation output")
	}
}

// The permutation circuit compiles to R1CS (the Groth16 target shape); report
// the native constraint cost per permutation.
func TestPoseidon2Bn254Compiles(t *testing.T) {
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &poseidon2Bn254Circuit{})
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	t.Logf("Poseidon2-BN254 (t=3) NATIVE permutation circuit: %d R1CS constraints", cs.GetNbConstraints())
}

// The 2-to-1 compression cost (one permutation, squeeze one lane).
type bn254CompressCircuit struct {
	L, R frontend.Variable
	Out  frontend.Variable
}

func (c *bn254CompressCircuit) Define(api frontend.API) error {
	api.AssertIsEqual(Poseidon2Bn254Compress(api, c.L, c.R), c.Out)
	return nil
}

func TestPoseidon2Bn254CompressCompiles(t *testing.T) {
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &bn254CompressCircuit{})
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	t.Logf("Poseidon2-BN254 (t=3) NATIVE 2-to-1 compression: %d R1CS constraints", cs.GetNbConstraints())
}
