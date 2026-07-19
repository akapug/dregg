// Tests for the CLOSED-template extensions of the Lean-emitted-template replayer
// (emitted_gadget_replay.go): the `select` field-mux op and the ReplayClosed
// bind-by-variable-index entry point.
//
// A closed template — the input-open MMCS opening (InputOpenEmit.lean,
// emitted/inputopen_template.json) — cannot be solved from an I/O boundary: its
// only public input is the root, while the opened row limbs, sibling nodes, and
// path bits are internal variables at a fixed layout, and the path walk spends
// `select` muxes the I/O-shaped Poseidon2 template never uses. These tests pin
// the mux semantics to gnark's api.Select on both polarities, and drive the real
// depth-18 committed input-open template through ReplayClosed against a root
// recomputed by the native reference (mfRefSpongeHash + poseidon2Bn254RefCompress
// — the same sponge + compression the emitted template is proven to denote).
package friverifier

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// ---------------------------------------------------------------------------
// (a) The `select` op — arity 3, api.Select(cond, ifTrue, ifFalse).
// ---------------------------------------------------------------------------

// replaySelectToy drives a 3-input, 1-output template whose single non-trivial
// gate is a `select`: out = select(cond, ifTrue, ifFalse).
type replaySelectToy struct {
	Cond    frontend.Variable
	IfTrue  frontend.Variable
	IfFalse frontend.Variable
	Out     frontend.Variable

	tpl *Template
}

func (c *replaySelectToy) Define(api frontend.API) error {
	outs, err := ReplayTemplate(api, *c.tpl, []frontend.Variable{c.Cond, c.IfTrue, c.IfFalse})
	if err != nil {
		return err
	}
	api.AssertIsEqual(outs[0], c.Out)
	return nil
}

// TestReplayTemplateSelectMuxBothPolarities: the replayed `select` gate is
// gnark's api.Select — cond=1 picks ifTrue, cond=0 picks ifFalse — matching the
// Lean Wire.select b x y (b·(x−y)+y) and the emitter's [cond,ifTrue,ifFalse] arg
// order. Both polarities accept the right branch and REJECT the crossed one.
func TestReplayTemplateSelectMuxBothPolarities(t *testing.T) {
	// out = select(cond, ifTrue, ifFalse):
	//   w0 = var(0) cond, w1 = var(1) ifTrue, w2 = var(2) ifFalse
	//   w3 = select(w0, w1, w2)
	//   w4 = var(3)             (fresh output var 3)
	//   assert w3 == w4         -> defines out = select(cond, ifTrue, ifFalse)
	tpl := Template{
		Name: "select_mux_toy",
		PublicInputs: []TemplatePublic{
			{Name: "cond", Var: 0},
			{Name: "ifTrue", Var: 1},
			{Name: "ifFalse", Var: 2},
			{Name: "out", Var: 3},
		},
		Gates: []TemplateGate{
			{Op: "var", Args: nums(0), Out: 0},
			{Op: "var", Args: nums(1), Out: 1},
			{Op: "var", Args: nums(2), Out: 2},
			{Op: "select", Args: nums(0, 1, 2), Out: 3},
			{Op: "var", Args: nums(3), Out: 4},
		},
		Asserts: []TemplateAssert{{L: 3, R: 4}},
	}
	if err := tpl.Validate(); err != nil {
		t.Fatalf("select toy invalid (is `select` in templateOpArity?): %v", err)
	}
	field := ecc.BN254.ScalarField()

	// cond = 1 selects ifTrue (= 7).
	if err := test.IsSolved(&replaySelectToy{tpl: &tpl},
		&replaySelectToy{tpl: &tpl, Cond: 1, IfTrue: 7, IfFalse: 9, Out: 7}, field); err != nil {
		t.Fatalf("select cond=1 should pick ifTrue: %v", err)
	}
	if err := test.IsSolved(&replaySelectToy{tpl: &tpl},
		&replaySelectToy{tpl: &tpl, Cond: 1, IfTrue: 7, IfFalse: 9, Out: 9}, field); err == nil {
		t.Fatal("select cond=1 wrongly accepted the ifFalse branch")
	}

	// cond = 0 selects ifFalse (= 9).
	if err := test.IsSolved(&replaySelectToy{tpl: &tpl},
		&replaySelectToy{tpl: &tpl, Cond: 0, IfTrue: 7, IfFalse: 9, Out: 9}, field); err != nil {
		t.Fatalf("select cond=0 should pick ifFalse: %v", err)
	}
	if err := test.IsSolved(&replaySelectToy{tpl: &tpl},
		&replaySelectToy{tpl: &tpl, Cond: 0, IfTrue: 7, IfFalse: 9, Out: 7}, field); err == nil {
		t.Fatal("select cond=0 wrongly accepted the ifTrue branch")
	}
}

// ---------------------------------------------------------------------------
// (b) ReplayClosed on the deployed input-open template.
// ---------------------------------------------------------------------------

// The committed instance emitted/inputopen_template.json = `inputOpenData 8 18`
// (InputOpenEmit.lean §7): a single-slot leaf (W=8 opened row limbs) laddered up
// a depth-18 native Merkle path. The variable layout (InputOpenEmit.lean §4):
// var 0..W-1 = row limbs; var W = root; var W+1+2i = sibling i; var W+1+2i+1 =
// path bit i; Poseidon internals mint from W+1+2d.
const (
	ioW = 8
	ioD = 18
)

const inputOpenTemplateTestPath = "emitted/inputopen_template.json"

// replayClosedIOCircuit binds the input-open template's named internal variables
// by index and drives the whole closed circuit through ReplayClosed.
type replayClosedIOCircuit struct {
	Rows [ioW]frontend.Variable
	Root frontend.Variable
	Sibs [ioD]frontend.Variable
	Bits [ioD]frontend.Variable

	tpl *Template
}

func (c *replayClosedIOCircuit) Define(api frontend.API) error {
	b := make(map[int]frontend.Variable, ioW+1+2*ioD)
	for i := 0; i < ioW; i++ {
		b[i] = c.Rows[i]
	}
	b[ioW] = c.Root
	for i := 0; i < ioD; i++ {
		b[ioW+1+2*i] = c.Sibs[i]
		b[ioW+1+2*i+1] = c.Bits[i]
	}
	return ReplayClosed(api, *c.tpl, b)
}

// ioExpectedRoot recomputes the input-open root the SAME way the emitted template
// is proven to (InputOpenEmit.lean: refRoot ∘ multiFieldHashRef): the multi-block
// sponge over the opened rows, laddered bottom-up by the native 2-to-1 compress,
// bit steering left/right (bit 0 => node left, matching stepFr/refRoot). If this
// diverges from what the template's final wire computes, the accept test below
// fails — that divergence would itself be the finding.
func ioExpectedRoot(rows []uint32, sibs []fr.Element, bits []bool) fr.Element {
	node := mfRefSpongeHash(rows)
	for i := range sibs {
		if bits[i] {
			node = poseidon2Bn254RefCompress(sibs[i], node)
		} else {
			node = poseidon2Bn254RefCompress(node, sibs[i])
		}
	}
	return node
}

func mkIOWitness(tpl *Template, rows []uint32, sibs []fr.Element, bits []bool, root fr.Element) *replayClosedIOCircuit {
	w := &replayClosedIOCircuit{tpl: tpl}
	for i := 0; i < ioW; i++ {
		w.Rows[i] = new(big.Int).SetUint64(uint64(rows[i]))
	}
	w.Root = root.BigInt(new(big.Int))
	for i := 0; i < ioD; i++ {
		w.Sibs[i] = sibs[i].BigInt(new(big.Int))
		if bits[i] {
			w.Bits[i] = 1
		} else {
			w.Bits[i] = 0
		}
	}
	return w
}

// TestReplayClosedInputOpenBindsAndRuns: LoadTemplate now accepts the closed
// input-open template (its `select` gates are in the vocabulary), and ReplayClosed
// binds the rows/root/siblings/bits by index, solves the define-chain internals,
// and keeps the real checks (bit booleanity + recomputed-root == root). A correct
// opening solves; a tampered root and a tampered opened row are both rejected.
func TestReplayClosedInputOpenBindsAndRuns(t *testing.T) {
	tpl, err := LoadTemplate(inputOpenTemplateTestPath)
	if err != nil {
		// Before `select` support LoadTemplate fail-closed here ("unknown op").
		t.Fatalf("load %s (does the vocabulary carry `select`?): %v", inputOpenTemplateTestPath, err)
	}
	// Pin the boundary this closed template exposes: a single root at var W.
	if len(tpl.PublicInputs) != 1 || tpl.PublicInputs[0].Var != ioW {
		t.Fatalf("unexpected boundary %v (want a single root at var %d)", tpl.PublicInputs, ioW)
	}
	field := ecc.BN254.ScalarField()

	// A concrete opening: katLeafA's 8 limbs, deterministic siblings, and path
	// bits that exercise BOTH compression orders (alternating true/false).
	rows := append([]uint32{}, katLeafA...)
	sibs := make([]fr.Element, ioD)
	bits := make([]bool, ioD)
	for i := 0; i < ioD; i++ {
		sibs[i] = frFromU64(uint64(1000 + i*7))
		bits[i] = i%2 == 0
	}
	root := ioExpectedRoot(rows, sibs, bits)

	// ACCEPT: the correct opening solves the whole closed circuit.
	if err := test.IsSolved(&replayClosedIOCircuit{tpl: tpl},
		mkIOWitness(tpl, rows, sibs, bits, root), field); err != nil {
		t.Fatalf("ReplayClosed did not solve on a correct input-open opening "+
			"(emitted template diverges from the native reference?): %v", err)
	}

	// REJECT: a tampered root does not equal the recomputed root.
	{
		var one fr.Element
		one.SetUint64(1)
		bumped := root
		bumped.Add(&bumped, &one)
		bad := mkIOWitness(tpl, rows, sibs, bits, root)
		bad.Root = bumped.BigInt(new(big.Int))
		if err := test.IsSolved(&replayClosedIOCircuit{tpl: tpl}, bad, field); err == nil {
			t.Fatal("ReplayClosed accepted a tampered root")
		}
	}

	// REJECT: a tampered opened row moves the leaf hash, hence the recomputed
	// root, while the claimed root is held at the untampered value — proving the
	// opened rows are actually bound into the leaf-hash region.
	{
		tamperedRows := append([]uint32{}, rows...)
		tamperedRows[0] ^= 1
		badRow := mkIOWitness(tpl, tamperedRows, sibs, bits, root)
		if err := test.IsSolved(&replayClosedIOCircuit{tpl: tpl}, badRow, field); err == nil {
			t.Fatal("ReplayClosed accepted a tampered opened row (leaf hash not bound)")
		}
	}
}
