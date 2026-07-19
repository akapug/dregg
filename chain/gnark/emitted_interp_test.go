// Tests for the Lean-emitted-circuit interpreter (emitted_interp.go).
//
// The circuit under test is loaded from the ACTUAL committed Lean artifact
// chain/gnark/emitted/canonicity_toy.json — the byte-for-byte #guard-pinned
// output of emitGnarkJson (EmitJson.lean §3) — never re-authored here. The
// witness fill is the Go twin of the Lean honest hint fill `canonAsg`
// (CanonicityToy.lean §1): var 0 = v, vars 1–31 = bits of v, vars 32–62 =
// bits of the ℕ-truncated (p−1)−v.
package friverifier

import (
	"encoding/json"
	"math/big"
	"math/rand"
	"strconv"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/test"
)

// emittedToyPath is the committed Lean-emitted artifact — the same bytes the
// Lean #guard in EmitJson.lean pins.
const emittedToyPath = "emitted/canonicity_toy.json"

func loadToy(t *testing.T) *Emitted {
	t.Helper()
	e, err := LoadEmitted(emittedToyPath)
	if err != nil {
		t.Fatalf("load %s: %v", emittedToyPath, err)
	}
	if e.Name != "babybear_assert_is_canonical_v1" {
		t.Fatalf("unexpected circuit name %q", e.Name)
	}
	// The layout this harness wires: exactly one public input at var 0.
	if len(e.PublicInputs) != 1 || e.PublicInputs[0].Var != 0 {
		t.Fatalf("unexpected public-input layout %+v", e.PublicInputs)
	}
	return e
}

// emittedJSONCircuit hosts the replay: V is the public input (var 0 per the
// JSON), Hints are the secret frontend vars 1..NumVars-1 (the bit hints).
type emittedJSONCircuit struct {
	V       frontend.Variable `gnark:",public"`
	Hints   []frontend.Variable
	emitted *Emitted
}

func (c *emittedJSONCircuit) Define(api frontend.API) error {
	e := *c.emitted
	e.Vars = make([]frontend.Variable, 1+len(c.Hints))
	e.Vars[0] = c.V
	copy(e.Vars[1:], c.Hints)
	return BuildFromEmitted(api, e)
}

// canonHintFill is the Go twin of Lean's canonAsg honest hint fill: bits 0–30
// of v at hints[0..30], bits 0–30 of the ℕ-truncated (p−1)−v at hints[31..61].
// For non-canonical v the truncation (or the missing high bits of v) makes a
// recomposition assert fail — the reject polarity, exactly as in Lean.
func canonHintFill(v *big.Int) []frontend.Variable {
	hints := make([]frontend.Variable, 62)
	for i := 0; i < 31; i++ {
		hints[i] = v.Bit(i)
	}
	d := new(big.Int).Sub(new(big.Int).SetUint64(BabyBearP-1), v)
	if d.Sign() < 0 {
		d = big.NewInt(0) // ℕ-truncation, as canonAsg
	}
	for i := 0; i < 31; i++ {
		hints[31+i] = d.Bit(i)
	}
	return hints
}

func toyTemplate(e *Emitted) *emittedJSONCircuit {
	return &emittedJSONCircuit{Hints: make([]frontend.Variable, 62), emitted: e}
}

func toyAssignment(e *Emitted, v *big.Int) *emittedJSONCircuit {
	return &emittedJSONCircuit{V: v, Hints: canonHintFill(v), emitted: e}
}

// --- (a) both polarities on the real emitted artifact ---

func TestEmittedCanonicityToyAccepts(t *testing.T) {
	e := loadToy(t)
	if n := e.NumVars(); n != 63 {
		t.Fatalf("NumVars = %d, want 63 (v + 2×31 bit hints)", n)
	}
	rng := rand.New(rand.NewSource(3))
	cases := []*big.Int{
		big.NewInt(0),
		big.NewInt(1),
		new(big.Int).SetUint64(BabyBearP - 1),
	}
	for i := 0; i < 8; i++ {
		cases = append(cases, new(big.Int).SetUint64(rng.Uint64()%BabyBearP))
	}
	for _, v := range cases {
		if err := test.IsSolved(toyTemplate(e), toyAssignment(e, v), ecc.BN254.ScalarField()); err != nil {
			t.Fatalf("canonical %v REJECTED by emitted circuit: %v", v, err)
		}
	}
}

func TestEmittedCanonicityToyRejects(t *testing.T) {
	e := loadToy(t)
	huge := new(big.Int).Sub(ecc.BN254.ScalarField(), big.NewInt(5))
	cases := []*big.Int{
		new(big.Int).SetUint64(BabyBearP),         // exactly p
		new(big.Int).SetUint64(BabyBearP + 12345), // the [p, 2^31) gap
		new(big.Int).Lsh(big.NewInt(1), 31),       // 2^31
		new(big.Int).Lsh(big.NewInt(1), 40),       // far out
		huge,                                      // rBN254 − 5: (p−1)−v wraps back small
	}
	for _, v := range cases {
		if err := test.IsSolved(toyTemplate(e), toyAssignment(e, v), ecc.BN254.ScalarField()); err == nil {
			t.Fatalf("non-canonical %v was ACCEPTED by emitted circuit", v)
		}
	}
}

// --- (b) constraint-count parity ---

// The compiled count must equal the count PREDICTED from the emitted DAG
// alone (each var·var mul + each assert = one R1C; const-scaled muls and adds
// are free) — no constraint content dropped or invented by the replay. The
// absolute numbers are pinned to the Lean-side #guards (EmitJson.lean: 504
// gates, 64 asserts) plus the 62 booleanity products: 62 + 64 = 126.
func TestEmittedCanonicityToyConstraintParity(t *testing.T) {
	e := loadToy(t)
	if got := len(e.Gates); got != 504 {
		t.Fatalf("gate count %d, want 504 (the Lean #guard pin)", got)
	}
	if got := len(e.Asserts); got != 64 {
		t.Fatalf("assert count %d, want 64 (the Lean #guard pin)", got)
	}
	predicted := e.PredictedR1CSConstraints()
	if predicted != 126 {
		t.Fatalf("predicted constraint count %d, want 126 (62 booleanity muls + 64 asserts)", predicted)
	}
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, toyTemplate(e))
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	if got := cs.GetNbConstraints(); got != predicted {
		t.Fatalf("compiled %d constraints, predicted %d from the emitted DAG", got, predicted)
	}
	t.Logf("emitted canonicity toy: %d R1CS constraints (parity with DAG-derived prediction)", cs.GetNbConstraints())
}

// --- (c) per-op unit tests: each interpreter op vs frontend.API semantics ---

// opCircuit hosts a hand-assembled Emitted program over secret vars Ws.
// (These programs test the INTERPRETER's op semantics — the toy circuit above
// remains loaded solely from the Lean artifact.)
type opCircuit struct {
	Ws      []frontend.Variable
	emitted *Emitted
}

func (c *opCircuit) Define(api frontend.API) error {
	e := *c.emitted
	e.Vars = c.Ws
	return BuildFromEmitted(api, e)
}

func nums(xs ...int) []json.Number {
	out := make([]json.Number, len(xs))
	for i, x := range xs {
		out[i] = json.Number(strconv.Itoa(x))
	}
	return out
}

func gate(op string, out int, args ...int) EmittedGate {
	return EmittedGate{Op: op, Args: nums(args...), Out: out}
}

func constGate(out int, c *big.Int) EmittedGate {
	return EmittedGate{Op: "const", Args: []json.Number{json.Number(c.String())}, Out: out}
}

func opProgram(gates []EmittedGate, asserts []EmittedAssert) *Emitted {
	return &Emitted{Name: "op_test", Gates: gates, Asserts: asserts}
}

func runOp(t *testing.T, e *Emitted, ws []frontend.Variable, wantSolved bool, label string) {
	t.Helper()
	template := &opCircuit{Ws: make([]frontend.Variable, len(ws)), emitted: e}
	assignment := &opCircuit{Ws: ws, emitted: e}
	err := test.IsSolved(template, assignment, ecc.BN254.ScalarField())
	if wantSolved && err != nil {
		t.Fatalf("%s: unexpectedly REJECTED: %v", label, err)
	}
	if !wantSolved && err == nil {
		t.Fatalf("%s: unexpectedly ACCEPTED", label)
	}
}

func randFr(rng *rand.Rand, field *big.Int) *big.Int {
	return new(big.Int).Rand(rng, field)
}

// var: two var gates asserted equal — accepts equal witnesses, rejects unequal.
func TestEmittedOpVar(t *testing.T) {
	e := opProgram([]EmittedGate{gate("var", 0, 0), gate("var", 1, 1)},
		[]EmittedAssert{{L: 0, R: 1}})
	field := ecc.BN254.ScalarField()
	rng := rand.New(rand.NewSource(10))
	for i := 0; i < 20; i++ {
		x := randFr(rng, field)
		xPlus1 := new(big.Int).Mod(new(big.Int).Add(x, big.NewInt(1)), field)
		runOp(t, e, []frontend.Variable{x, x}, true, "var equal")
		runOp(t, e, []frontend.Variable{x, xPlus1}, false, "var unequal")
	}
}

// const: a big-residue constant asserted equal to a var — exercises the
// big.Int decimal parse path (values beyond int64/float64).
func TestEmittedOpConst(t *testing.T) {
	field := ecc.BN254.ScalarField()
	rng := rand.New(rand.NewSource(11))
	for i := 0; i < 20; i++ {
		c := randFr(rng, field)
		e := opProgram([]EmittedGate{constGate(0, c), gate("var", 1, 0)},
			[]EmittedAssert{{L: 0, R: 1}})
		cPlus1 := new(big.Int).Mod(new(big.Int).Add(c, big.NewInt(1)), field)
		runOp(t, e, []frontend.Variable{c}, true, "const match")
		runOp(t, e, []frontend.Variable{cPlus1}, false, "const mismatch")
	}
	// The residue of −1 mod rBN254 — the exact huge constant the toy carries.
	minusOne := new(big.Int).Sub(field, big.NewInt(1))
	e := opProgram([]EmittedGate{constGate(0, minusOne), gate("var", 1, 0)},
		[]EmittedAssert{{L: 0, R: 1}})
	runOp(t, e, []frontend.Variable{minusOne}, true, "const -1 residue")
}

// add: add(var0,var1) asserted equal to var2 — vs big.Int field addition.
func TestEmittedOpAdd(t *testing.T) {
	e := opProgram([]EmittedGate{gate("var", 0, 0), gate("var", 1, 1), gate("add", 2, 0, 1), gate("var", 3, 2)},
		[]EmittedAssert{{L: 2, R: 3}})
	field := ecc.BN254.ScalarField()
	rng := rand.New(rand.NewSource(12))
	for i := 0; i < 20; i++ {
		x, y := randFr(rng, field), randFr(rng, field)
		want := new(big.Int).Mod(new(big.Int).Add(x, y), field)
		wrong := new(big.Int).Mod(new(big.Int).Add(want, big.NewInt(1)), field)
		runOp(t, e, []frontend.Variable{x, y, want}, true, "add correct")
		runOp(t, e, []frontend.Variable{x, y, wrong}, false, "add wrong")
	}
}

// mul: mul(var0,var1) asserted equal to var2 — vs big.Int field multiplication.
func TestEmittedOpMul(t *testing.T) {
	e := opProgram([]EmittedGate{gate("var", 0, 0), gate("var", 1, 1), gate("mul", 2, 0, 1), gate("var", 3, 2)},
		[]EmittedAssert{{L: 2, R: 3}})
	field := ecc.BN254.ScalarField()
	rng := rand.New(rand.NewSource(13))
	for i := 0; i < 20; i++ {
		x, y := randFr(rng, field), randFr(rng, field)
		want := new(big.Int).Mod(new(big.Int).Mul(x, y), field)
		wrong := new(big.Int).Mod(new(big.Int).Add(want, big.NewInt(1)), field)
		runOp(t, e, []frontend.Variable{x, y, want}, true, "mul correct")
		runOp(t, e, []frontend.Variable{x, y, wrong}, false, "mul wrong")
	}
}

// select: select(b,x,y) asserted equal to var3 — gnark semantics b=1 → x,
// b=0 → y, both polarities.
func TestEmittedOpSelect(t *testing.T) {
	e := opProgram([]EmittedGate{
		gate("var", 0, 0), gate("var", 1, 1), gate("var", 2, 2),
		gate("select", 3, 0, 1, 2), gate("var", 4, 3),
	},
		[]EmittedAssert{{L: 3, R: 4}})
	field := ecc.BN254.ScalarField()
	rng := rand.New(rand.NewSource(14))
	for i := 0; i < 20; i++ {
		x, y := randFr(rng, field), randFr(rng, field)
		if x.Cmp(y) == 0 {
			continue
		}
		runOp(t, e, []frontend.Variable{1, x, y, x}, true, "select b=1 -> x")
		runOp(t, e, []frontend.Variable{0, x, y, y}, true, "select b=0 -> y")
		runOp(t, e, []frontend.Variable{1, x, y, y}, false, "select b=1 wrong arm")
		runOp(t, e, []frontend.Variable{0, x, y, x}, false, "select b=0 wrong arm")
	}
}

// Mixed-op parity: the DAG-derived prediction matches the compiled count on a
// program exercising every op (var·var mul = 1, const-scaled mul = 0, add =
// 0, first select on a selector = 2 [AssertIsBoolean + product], a second
// select on the SAME selector variable = 1, asserts = 1 each).
func TestEmittedOpConstraintPrediction(t *testing.T) {
	e := opProgram([]EmittedGate{
		gate("var", 0, 0),           // v0
		gate("var", 1, 1),           // v1
		gate("mul", 2, 0, 1),        // var·var: 1
		constGate(3, big.NewInt(7)), // const
		gate("mul", 4, 3, 0),        // const·var: 0
		gate("add", 5, 2, 4),        // add: 0
		gate("var", 6, 2),           // v2 (selector)
		gate("select", 7, 6, 5, 2),  // select, fresh selector: 2
		gate("var", 8, 0),
		gate("var", 9, 2),           // v2 again (same variable, new node)
		gate("select", 10, 9, 0, 1), // select, selector already marked: 1
		gate("var", 11, 3),          // v3
	},
		[]EmittedAssert{{L: 7, R: 8}, {L: 2, R: 2}, {L: 10, R: 11}}) // asserts: 3
	predicted := e.PredictedR1CSConstraints()
	if predicted != 7 { // 1 mul + 2 first-select + 1 second-select + 3 asserts
		t.Fatalf("predicted %d, want 7", predicted)
	}
	template := &opCircuit{Ws: make([]frontend.Variable, 4), emitted: e}
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, template)
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	if got := cs.GetNbConstraints(); got != predicted {
		t.Fatalf("compiled %d constraints, predicted %d", got, predicted)
	}
}

// --- fail-closed validation teeth ---

func TestEmittedValidateFailClosed(t *testing.T) {
	cases := []struct {
		label string
		e     Emitted
	}{
		{"unknown op", Emitted{Gates: []EmittedGate{gate("sub", 0, 0, 0)}}},
		{"out != index", Emitted{Gates: []EmittedGate{gate("var", 1, 0)}}},
		{"non-topological child", Emitted{Gates: []EmittedGate{gate("add", 0, 0, 0)}}},
		{"assert out of range", Emitted{Gates: []EmittedGate{gate("var", 0, 0)}, Asserts: []EmittedAssert{{L: 0, R: 5}}}},
		{"unknown gadget", Emitted{
			Gates:   []EmittedGate{gate("var", 0, 0)},
			Gadgets: []EmittedGadget{{Gadget: "AssertIsTotallyFine", Args: []int{0}}},
		}},
		{"negative const", Emitted{Gates: []EmittedGate{constGate(0, big.NewInt(-3))}}},
	}
	for _, c := range cases {
		if err := c.e.Validate(); err == nil {
			t.Fatalf("%s: Validate ACCEPTED", c.label)
		}
	}
}

// A const ≥ the compile field must fail-close at build time.
func TestEmittedConstAboveFieldFailsClosed(t *testing.T) {
	field := ecc.BN254.ScalarField()
	e := opProgram([]EmittedGate{constGate(0, new(big.Int).Add(field, big.NewInt(1))), gate("var", 1, 0)},
		[]EmittedAssert{{L: 0, R: 1}})
	template := &opCircuit{Ws: make([]frontend.Variable, 1), emitted: e}
	if _, err := frontend.Compile(field, r1cs.NewBuilder, template); err == nil {
		t.Fatal("const above the compile field was ACCEPTED")
	}
}
