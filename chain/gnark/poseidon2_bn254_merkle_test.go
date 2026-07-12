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

// bn254MerkleOpenCircuit verifies a depth-D Merkle authentication path built
// from the native BN254 Poseidon2 2-to-1 compression against a committed root.
// This is the exact primitive a native-hash FRI verifier repeats for every
// query (input-codeword opening + per-round folding openings).
type bn254MerkleOpenCircuit struct {
	Leaf     frontend.Variable
	Siblings []frontend.Variable // length D
	PathBits []frontend.Variable // length D, each boolean; 0 => current node is left
	Root     frontend.Variable   `gnark:",public"`
}

func (c *bn254MerkleOpenCircuit) Define(api frontend.API) error {
	node := c.Leaf
	for i := range c.Siblings {
		api.AssertIsBoolean(c.PathBits[i])
		// bit==0: node is left, sibling right; bit==1: swapped.
		left := api.Select(c.PathBits[i], c.Siblings[i], node)
		right := api.Select(c.PathBits[i], node, c.Siblings[i])
		node = Poseidon2Bn254Compress(api, left, right)
	}
	api.AssertIsEqual(node, c.Root)
	return nil
}

// buildMerkleWitness computes a consistent depth-D path with the reference
// compression so the circuit has something valid to accept.
func buildMerkleWitness(depth int) *bn254MerkleOpenCircuit {
	leaf := frFromU64(0xC0FFEE)
	sibs := make([]fr.Element, depth)
	bits := make([]uint64, depth)
	node := leaf
	for i := 0; i < depth; i++ {
		sibs[i] = frFromU64(uint64(1000 + i))
		bits[i] = uint64(i % 2)
		var l, r fr.Element
		if bits[i] == 0 {
			l, r = node, sibs[i]
		} else {
			l, r = sibs[i], node
		}
		node = poseidon2Bn254RefCompress(l, r)
	}
	w := &bn254MerkleOpenCircuit{
		Leaf:     new(big.Int).SetUint64(0xC0FFEE),
		Siblings: make([]frontend.Variable, depth),
		PathBits: make([]frontend.Variable, depth),
		Root:     node.BigInt(new(big.Int)),
	}
	for i := 0; i < depth; i++ {
		w.Siblings[i] = sibs[i].BigInt(new(big.Int))
		w.PathBits[i] = new(big.Int).SetUint64(bits[i])
	}
	return w
}

func emptyMerkleCircuit(depth int) *bn254MerkleOpenCircuit {
	return &bn254MerkleOpenCircuit{
		Siblings: make([]frontend.Variable, depth),
		PathBits: make([]frontend.Variable, depth),
	}
}

func TestBn254MerkleOpenCircuitSolves(t *testing.T) {
	field := ecc.BN254.ScalarField()
	for _, depth := range []int{20, 24} {
		w := buildMerkleWitness(depth)
		if err := test.IsSolved(emptyMerkleCircuit(depth), w, field); err != nil {
			t.Fatalf("depth %d: valid path rejected: %v", depth, err)
		}
		// REJECT polarity: corrupt the root.
		bad := *buildMerkleWitness(depth)
		bad.Root = new(big.Int).Add(w.Root.(*big.Int), big.NewInt(1))
		if err := test.IsSolved(emptyMerkleCircuit(depth), &bad, field); err == nil {
			t.Fatalf("depth %d: circuit accepted a corrupted root", depth)
		}
	}
}

func TestBn254MerkleOpenConstraints(t *testing.T) {
	field := ecc.BN254.ScalarField()
	var prev int
	for _, depth := range []int{20, 22, 24} {
		cs, err := frontend.Compile(field, r1cs.NewBuilder, emptyMerkleCircuit(depth))
		if err != nil {
			t.Fatalf("depth %d compile: %v", depth, err)
		}
		n := cs.GetNbConstraints()
		perLevel := 0
		if prev != 0 {
			perLevel = (n - prev) / 2
		}
		t.Logf("Poseidon2-BN254 NATIVE Merkle opening depth=%d: %d R1CS constraints (per-level delta ~%d)", depth, n, perLevel)
		prev = n
	}
}
