package friverifier

import (
	"encoding/json"
	"math/big"
	"os"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
)

// loadRawWitnessList reads a Lean-dumped var-index-ordered witness array.
func loadRawWitnessList(t *testing.T, path string) []*big.Int {
	t.Helper()
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var nums []json.Number
	if err := json.Unmarshal(raw, &nums); err != nil {
		t.Fatalf("unmarshal %s: %v", path, err)
	}
	out := make([]*big.Int, len(nums))
	for i, n := range nums {
		v, ok := new(big.Int).SetString(n.String(), 10)
		if !ok {
			t.Fatalf("%s: bad number %q", path, n.String())
		}
		out[i] = v
	}
	return out
}

// TestFriFoldWitnessSolverMatchesLeanFixture pins the FRI-stage fold witness SOURCE
// (the native templateSolver behind friFoldWitnessHint) to the committed Lean
// artifact: binding only the 12 sibling0/sibling1/beta limbs + the 17 parent bits
// from fri_fold_witness.json, the solver must DERIVE folded_claim and reproduce every
// one of the template's 4721 variables byte-for-byte. fri_fold_witness.json is the
// exact honest hint fill `friFold_leaf_refines` (FriFoldEmit.lean) quantifies over,
// so reproducing it is evidence the untrusted hint matches the ∀-covered witness.
func TestFriFoldWitnessSolverMatchesLeanFixture(t *testing.T) {
	tpl, err := LoadTemplate(friFoldTemplatePath())
	if err != nil {
		t.Fatal(err)
	}
	if err := checkFriFoldTemplateShape(tpl); err != nil {
		t.Fatal(err)
	}
	fixture := loadRawWitnessList(t, friFoldWitnessPath())
	if len(fixture) != tpl.NumVars() {
		t.Fatalf("fixture %d vars != template %d", len(fixture), tpl.NumVars())
	}
	plan, err := loadFriFoldHintPlan()
	if err != nil {
		t.Fatal(err)
	}
	mod := ecc.BN254.ScalarField()
	s := newTemplateSolver(tpl, mod)
	// Bind ONLY 12 inputs + 17 parent bits from the fixture; solver derives the rest.
	for _, v := range plan.inputVars {
		s.bind(v, fixture[v])
	}
	for _, v := range plan.parentVars {
		s.bind(v, fixture[v])
	}
	s.solve()
	for v := 0; v < tpl.NumVars(); v++ {
		if !s.varSet[v] {
			t.Fatalf("var %d unsolved (want %s)", v, fixture[v])
		}
		if s.vars[v].Cmp(fixture[v]) != 0 {
			t.Fatalf("var %d: solver got %s, fixture %s", v, s.vars[v], fixture[v])
		}
	}
	// The solver must derive folded_claim (public inputs 12..15) too.
	for i := 12; i < 16; i++ {
		v := tpl.PublicInputs[i].Var
		if s.vars[v].Cmp(fixture[v]) != 0 {
			t.Fatalf("folded_claim limb %d: solver %s != fixture %s", i-12, s.vars[v], fixture[v])
		}
	}
}

// TestFriFoldWitnessHintMatchesLeanFixture exercises the registered gnark hint end
// to end: fed the 12 limbs + 17 parent bits (from the committed fixture), its
// ClassifyVars(12).Witness outputs must equal the fixture at those indices — the
// values ReplayTemplateWithWitness binds on the emit path.
func TestFriFoldWitnessHintMatchesLeanFixture(t *testing.T) {
	tpl, err := LoadTemplate(friFoldTemplatePath())
	if err != nil {
		t.Fatal(err)
	}
	fixture := loadRawWitnessList(t, friFoldWitnessPath())
	plan, err := loadFriFoldHintPlan()
	if err != nil {
		t.Fatal(err)
	}
	inputs := make([]*big.Int, 0, friFoldHintInputLimbs+friFoldParentBits)
	for _, v := range plan.inputVars {
		inputs = append(inputs, new(big.Int).Set(fixture[v]))
	}
	for _, v := range plan.parentVars {
		inputs = append(inputs, new(big.Int).Set(fixture[v]))
	}
	outputs := make([]*big.Int, len(plan.witnessIdx))
	for i := range outputs {
		outputs[i] = new(big.Int)
	}
	if err := friFoldWitnessHint(ecc.BN254.ScalarField(), inputs, outputs); err != nil {
		t.Fatal(err)
	}
	for k, idx := range plan.witnessIdx {
		if outputs[k].Cmp(fixture[idx]) != 0 {
			t.Fatalf("witness %d (var %d): hint %s != fixture %s", k, idx, outputs[k], fixture[idx])
		}
	}
	_ = tpl
}
