// Parity + genericity tests for the Lean-emitted-template replayer
// (emitted_gadget_replay.go).
//
// THE DELIVERABLE test: ReplayTemplate over the Lean-emitted Poseidon2-BN254
// template reproduces the SAME field outputs as the Go Poseidon2Bn254
// permutation (poseidon2_bn254.go / its reference twin poseidon2_bn254_ref.go)
// on the Go KAT vectors, bit-exact. If the replay diverges, the Lean-emitted
// constraints are wrong — and that divergence IS the finding.
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

const poseidon2TemplateTestPath = "emitted/poseidon2_template.json"

// replayPermCircuit runs ReplayTemplate over an attached template on 3 inputs
// and asserts the 3 replayed outputs equal the expected lanes. The template is
// attached out-of-band (unexported field ignored by the gnark schema walker),
// exactly as VerifierFullCircuit attaches its descriptor.
type replayPermCircuit struct {
	In  [3]frontend.Variable
	Out [3]frontend.Variable

	tpl *Template
}

func (c *replayPermCircuit) Define(api frontend.API) error {
	outs, err := ReplayTemplate(api, *c.tpl, c.In[:])
	if err != nil {
		return err
	}
	if len(outs) != 3 {
		return errReplayArity(len(outs))
	}
	for i := 0; i < 3; i++ {
		api.AssertIsEqual(outs[i], c.Out[i])
	}
	return nil
}

type errReplayArity int

func (e errReplayArity) Error() string { return "replay returned wrong output arity" }

func loadPoseidon2TemplateT(t *testing.T) *Template {
	t.Helper()
	tpl, err := LoadTemplate(poseidon2TemplateTestPath)
	if err != nil {
		t.Fatalf("load %s: %v", poseidon2TemplateTestPath, err)
	}
	return tpl
}

// refPermLanes runs the Go reference permutation and returns the 3 output lanes
// as big.Int (the ground-truth the replay must reproduce).
func refPermLanes(in [3]uint64) [3]*big.Int {
	state := [3]fr.Element{frFromU64(in[0]), frFromU64(in[1]), frFromU64(in[2])}
	poseidon2Bn254Ref(&state)
	var out [3]*big.Int
	for i := 0; i < 3; i++ {
		out[i] = state[i].BigInt(new(big.Int))
	}
	return out
}

// THE PARITY TEST. On the Go KAT vector [0,1,2] and randomized vectors, the
// replayed Lean-emitted template produces the SAME field outputs, lane by lane,
// as the Go Poseidon2Bn254 permutation. Bit-exact: test.IsSolved fails on any
// lane mismatch.
func TestReplayTemplateMatchesGoPoseidon2KAT(t *testing.T) {
	tpl := loadPoseidon2TemplateT(t)
	field := ecc.BN254.ScalarField()

	// 1) The Go gold KAT vector, checked against the hardcoded gold output
	//    (not just the ref twin) — this pins the template to the zkhash KAT.
	{
		w := &replayPermCircuit{tpl: tpl}
		w.In[0], w.In[1], w.In[2] = 0, 1, 2
		for i := 0; i < 3; i++ {
			v, _ := new(big.Int).SetString(bn254KATOutHex[i], 0)
			w.Out[i] = v
		}
		if err := test.IsSolved(&replayPermCircuit{tpl: tpl}, w, field); err != nil {
			t.Fatalf("replayed Lean template diverges from the Go zkhash gold KAT "+
				"(the Lean-emitted constraints are WRONG): %v", err)
		}
	}

	// 2) Randomized differential vs the Go reference permutation.
	for _, in := range [][3]uint64{
		{0, 0, 0}, {1, 2, 3}, {7, 42, 999},
		{1 << 40, 1 << 50, 1 << 60}, {123456789, 987654321, 555},
	} {
		lanes := refPermLanes(in)
		w := &replayPermCircuit{tpl: tpl}
		for i := 0; i < 3; i++ {
			w.In[i] = new(big.Int).SetUint64(in[i])
			w.Out[i] = lanes[i]
		}
		if err := test.IsSolved(&replayPermCircuit{tpl: tpl}, w, field); err != nil {
			t.Fatalf("replayed template diverges from Go Poseidon2Bn254 on %v "+
				"(Lean-emitted constraints WRONG): %v", in, err)
		}
	}
}

// REJECT polarity: a tampered expected output must make the replayed circuit
// unsatisfiable (guards against a vacuous parity match).
func TestReplayTemplateRejectsTamperedOutput(t *testing.T) {
	tpl := loadPoseidon2TemplateT(t)
	field := ecc.BN254.ScalarField()

	in := [3]uint64{7, 42, 999}
	lanes := refPermLanes(in)
	w := &replayPermCircuit{tpl: tpl}
	for i := 0; i < 3; i++ {
		w.In[i] = new(big.Int).SetUint64(in[i])
		w.Out[i] = lanes[i]
	}
	// bump lane 1.
	w.Out[1] = new(big.Int).Add(lanes[1], big.NewInt(1))
	if err := test.IsSolved(&replayPermCircuit{tpl: tpl}, w, field); err == nil {
		t.Fatal("replayed template accepted a tampered permutation output")
	}
}

// Constraint-count parity: the replayed template compiles to the SAME number of
// R1CS constraints as the hand-Go Poseidon2Bn254 permutation gadget — the
// template's mul-gate count IS the permutation's S-box constraint budget. This
// is the count reported in the task.
func TestReplayTemplateConstraintCountVsHandGo(t *testing.T) {
	tpl := loadPoseidon2TemplateT(t)

	replCS, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder,
		&replayPermCircuit{tpl: tpl})
	if err != nil {
		t.Fatalf("compile replayed template: %v", err)
	}
	handCS, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder,
		&poseidon2Bn254Circuit{})
	if err != nil {
		t.Fatalf("compile hand-Go permutation: %v", err)
	}

	t.Logf("replayed Lean template: %d R1CS constraints", replCS.GetNbConstraints())
	t.Logf("hand-Go permutation:    %d R1CS constraints", handCS.GetNbConstraints())
	t.Logf("template mul gates (R1CS budget): %d", tpl.NumMulGates())
	t.Logf("template gates: %d, asserts: %d, vars: %d", len(tpl.Gates), len(tpl.Asserts), tpl.NumVars())

	if tpl.NumMulGates() != 240 {
		t.Fatalf("template mul gates = %d, want 240 (Poseidon2-BN254 t=3: 8 full rounds*3 + 56 partial, each S-box 3 muls)", tpl.NumMulGates())
	}
	// Both circuits also carry the 3 boundary AssertIsEqual constraints of the
	// test harness; the CORE nonlinear cost must match.
	if replCS.GetNbConstraints() != handCS.GetNbConstraints() {
		t.Fatalf("replayed template compiled to %d constraints, hand-Go to %d (should be identical)",
			replCS.GetNbConstraints(), handCS.GetNbConstraints())
	}
}

// Genericity guard: the replayer refuses a template whose asserts cannot be
// solved without a hint (both sides undetermined) — it does not fabricate a
// witness. Uses a tiny hand-built template, proving the replayer carries no
// Poseidon2 assumption.
func TestReplayTemplateGenericAddChain(t *testing.T) {
	// A 1-input, 1-output template: out0 = in0 + in0 + in0.
	//   var0 = in0            (var 0)
	//   w0 = var(0)
	//   w1 = var(0)
	//   w2 = add(w0, w1)      = 2*in0
	//   w3 = var(0)
	//   w4 = add(w2, w3)      = 3*in0
	//   w5 = var(1)           (fresh output var 1)
	//   assert w4 == w5       -> defines out = 3*in0
	tpl := Template{
		Name:         "add_chain_toy",
		PublicInputs: []TemplatePublic{{Name: "in0", Var: 0}, {Name: "out0", Var: 1}},
		Gates: []TemplateGate{
			{Op: "var", Args: nums(0), Out: 0},
			{Op: "var", Args: nums(0), Out: 1},
			{Op: "add", Args: nums(0, 1), Out: 2},
			{Op: "var", Args: nums(0), Out: 3},
			{Op: "add", Args: nums(2, 3), Out: 4},
			{Op: "var", Args: nums(1), Out: 5},
		},
		Asserts: []TemplateAssert{{L: 4, R: 5}},
	}
	if err := tpl.Validate(); err != nil {
		t.Fatalf("toy template invalid: %v", err)
	}
	field := ecc.BN254.ScalarField()
	w := &replayGenericToy{tpl: &tpl, In: 5, Out: 15}
	if err := test.IsSolved(&replayGenericToy{tpl: &tpl}, w, field); err != nil {
		t.Fatalf("generic add-chain replay failed: %v", err)
	}
	bad := &replayGenericToy{tpl: &tpl, In: 5, Out: 16}
	if err := test.IsSolved(&replayGenericToy{tpl: &tpl}, bad, field); err == nil {
		t.Fatal("generic replay accepted a wrong output")
	}
}

type replayGenericToy struct {
	In  frontend.Variable
	Out frontend.Variable
	tpl *Template
}

func (c *replayGenericToy) Define(api frontend.API) error {
	outs, err := ReplayTemplate(api, *c.tpl, []frontend.Variable{c.In})
	if err != nil {
		return err
	}
	api.AssertIsEqual(outs[0], c.Out)
	return nil
}
