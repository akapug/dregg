// THE WRAP END-TO-END (open_input seam closure): the FRI reduced openings of
// the REAL shrink proof are RE-DERIVED from the committed columns — the
// input-batch Merkle openings against the trace/quotient/preprocessed/
// permutation commitments plus the alpha-combination — and bound to the fold
// seeds, on real data, ref twin and gnark gadget both, with tamper canaries
// on every leg (a wrong opened column, a wrong Merkle node, a wrong root, a
// wrong opened-at-zeta value, a wrong seed each REJECT).
//
// This is the binding the HONEST SCOPE notes named as the last soundness
// seam: before it, the constraint/quotient identity rode host-computed
// reduced openings that were transcript-bound but not commitment-bound.
package friverifier

import (
	"reflect"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// ----------------------------------------------------------------------------
// Fixture → shape/witness conversion (shared with the FullVerify circuit)
// ----------------------------------------------------------------------------

// shrinkInputRoundsFromFixture converts the exported structural input rounds
// and CROSS-CHECKS them against the structure derived from the pinned
// instance shapes (BuildExpectedInputRounds — the projection of the same
// accounting buildStarkOpenedSpans pins against the opened-values stream).
// Fail-closed: any drift between the exporter's PCS round structure and the
// pinned VK shape dies here, before anything reaches a circuit.
func shrinkInputRoundsFromFixture(t *testing.T, fx *shrinkRealFixture, shapes []StarkInstanceShape) []OpenInputRoundShape {
	t.Helper()
	got := make([]OpenInputRoundShape, len(fx.InputRounds))
	for ri, r := range fx.InputRounds {
		for _, m := range r.Matrices {
			got[ri].Matrices = append(got[ri].Matrices,
				OpenInputMatrixShape{m.LogHeight, m.Width, m.NumPoints, m.NextPointBits})
		}
	}
	want := BuildExpectedInputRounds(shapes, fx.Fri.LogBlowup)
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("exported input-round structure drifted from the pinned shape:\n got %+v\nwant %+v",
			got, want)
	}
	return got
}

// allocShrinkInputOpenings builds the witness shape template.
func allocShrinkInputOpenings(fx *shrinkRealFixture) [][]OpenInputBatchOpening {
	out := make([][]OpenInputBatchOpening, len(fx.Queries))
	for qi, q := range fx.Queries {
		out[qi] = make([]OpenInputBatchOpening, len(q.InputOpenings))
		for ri, b := range q.InputOpenings {
			rows := make([][]frontend.Variable, len(b.Rows))
			for mi, row := range b.Rows {
				rows[mi] = make([]frontend.Variable, len(row))
			}
			out[qi][ri] = OpenInputBatchOpening{
				Rows: rows,
				Path: make([]frontend.Variable, len(b.Path)),
			}
		}
	}
	return out
}

// assignShrinkInputOpenings fills the witness from the fixture.
func assignShrinkInputOpenings(t *testing.T, fx *shrinkRealFixture) [][]OpenInputBatchOpening {
	t.Helper()
	out := allocShrinkInputOpenings(fx)
	for qi, q := range fx.Queries {
		for ri, b := range q.InputOpenings {
			for mi, row := range b.Rows {
				for k, v := range row {
					out[qi][ri].Rows[mi][k] = v
				}
			}
			for l, node := range b.Path {
				out[qi][ri].Path[l] = frToBig(parseBn254Hex(t, node))
			}
		}
	}
	return out
}

// shrinkInputOpeningsRef builds one query's host-side openings.
func shrinkInputOpeningsRef(t *testing.T, fx *shrinkRealFixture, qi int) []openInputBatchRef {
	t.Helper()
	q := fx.Queries[qi]
	out := make([]openInputBatchRef, len(q.InputOpenings))
	for ri, b := range q.InputOpenings {
		rows := make([][]uint32, len(b.Rows))
		for mi, row := range b.Rows {
			rows[mi] = append([]uint32(nil), row...)
		}
		path := make([]fr.Element, len(b.Path))
		for l, node := range b.Path {
			path[l] = parseBn254Hex(t, node)
		}
		out[ri] = openInputBatchRef{rows: rows, path: path}
	}
	return out
}

// shrinkInputRootsRef extracts the four input-round commitment roots from the
// transcript prefix digests, in PCS round order (trace, quotient,
// preprocessed, permutation) via the anchored digest offsets.
func shrinkInputRootsRef(t *testing.T, fx *shrinkRealFixture, loc shrinkStarkPrefixLoc) []fr.Element {
	t.Helper()
	var words []fr.Element
	for _, ev := range fx.PrefixEvents {
		if ev.Kind == "observe_digest" {
			for _, w := range ev.Words {
				words = append(words, parseBn254Hex(t, w))
			}
		}
	}
	roots := make([]fr.Element, len(loc.inputRootDigOff))
	for i, off := range loc.inputRootDigOff {
		roots[i] = words[off]
	}
	return roots
}

// ----------------------------------------------------------------------------
// Host-reference checks on the REAL proof
// ----------------------------------------------------------------------------

// ACCEPT: for EVERY query of the real shrink proof, the input-batch Merkle
// openings verify against the transcript-observed commitments and the derived
// reduced openings EQUAL the FRI fold seeds (initial eval + both roll-ins).
// This is the ~124-bit-per-height equation that pins the whole seam: a wrong
// alpha-combination order, a wrong evaluation point x, a wrong batch-tree
// walk, or a wrong opened-values slicing cannot survive it on real data.
func TestApexShrinkRealFixtureOpenInputRefAccepts(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	rounds := shrinkInputRoundsFromFixture(t, fx, ex.shapes)
	roots := shrinkInputRootsRef(t, fx, ex.loc)
	for qi, q := range fx.Queries {
		rollIns := make([]bbExtRef, len(q.RollIns))
		for j, ri := range q.RollIns {
			rollIns[j] = bbExtRef(ri)
		}
		if err := openInputVerifyQueryRef(rounds, roots, shrinkInputOpeningsRef(t, fx, qi),
			ex.openedEF, ex.ch.zeta, ex.friAlpha, q.ExpectedIndex, fx.Fri.LogGlobalMaxHeight,
			bbExtRef(q.InitialEval), rollIns, fx.RollInRounds); err != nil {
			t.Fatalf("query %d: open_input reference REJECTED the real shrink proof: %v", qi, err)
		}
	}
}

// REJECT canaries, reference side: each single tamper of query 0 must fail.
func TestApexShrinkRealFixtureOpenInputRefRejectsTampers(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	rounds := shrinkInputRoundsFromFixture(t, fx, ex.shapes)
	one := fr.One()

	type state struct {
		roots    []fr.Element
		openings []openInputBatchRef
		openedEF []bbExtRef
		zeta     bbExtRef
		alpha    bbExtRef
		initial  bbExtRef
		rollIns  []bbExtRef
	}
	mk := func() *state {
		q := fx.Queries[0]
		rollIns := make([]bbExtRef, len(q.RollIns))
		for j, ri := range q.RollIns {
			rollIns[j] = bbExtRef(ri)
		}
		return &state{
			roots:    shrinkInputRootsRef(t, fx, ex.loc),
			openings: shrinkInputOpeningsRef(t, fx, 0),
			openedEF: append([]bbExtRef(nil), ex.openedEF...),
			zeta:     ex.ch.zeta,
			alpha:    ex.friAlpha,
			initial:  bbExtRef(q.InitialEval),
			rollIns:  rollIns,
		}
	}
	cases := []struct {
		name   string
		tamper func(s *state)
	}{
		{"tampered-input-row-value", func(s *state) {
			s.openings[0].rows[2][0] = bbAddRef(s.openings[0].rows[2][0], 1)
		}},
		{"tampered-input-row-low-matrix", func(s *state) {
			// A matrix BELOW the max height: binds the injected row hashes.
			s.openings[0].rows[0][0] = bbAddRef(s.openings[0].rows[0][0], 1)
		}},
		{"tampered-merkle-path-node", func(s *state) {
			s.openings[1].path[0].Add(&s.openings[1].path[0], &one)
		}},
		{"tampered-commitment-root", func(s *state) {
			s.roots[3].Add(&s.roots[3], &one)
		}},
		{"tampered-opened-at-zeta", func(s *state) {
			s.openedEF[0][0] = bbAddRef(s.openedEF[0][0], 1)
		}},
		{"tampered-initial-eval", func(s *state) {
			s.initial[0] = bbAddRef(s.initial[0], 1)
		}},
		{"tampered-roll-in", func(s *state) {
			s.rollIns[1][0] = bbAddRef(s.rollIns[1][0], 1)
		}},
		{"tampered-fri-alpha", func(s *state) {
			s.alpha[0] = bbAddRef(s.alpha[0], 1)
		}},
		{"tampered-zeta", func(s *state) {
			s.zeta[1] = bbAddRef(s.zeta[1], 1)
		}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			s := mk()
			tc.tamper(s)
			if err := openInputVerifyQueryRef(rounds, s.roots, s.openings, s.openedEF,
				s.zeta, s.alpha, fx.Queries[0].ExpectedIndex, fx.Fri.LogGlobalMaxHeight,
				s.initial, s.rollIns, fx.RollInRounds); err == nil {
				t.Fatalf("%s: open_input reference ACCEPTED tampered real data", tc.name)
			}
		})
	}
}

// DIFFERENTIAL, evaluation-order cross: the ref (pinned per-column alpha_pow
// form) and the fixture (the real p3 open_input) agree on every query and
// every height — with the gadget's Horner regrouping checked against the same
// seeds below, the three evaluation orders of the alpha-combination meet on
// real data.
func TestApexShrinkRealFixtureOpenInputRefMatchesAllHeights(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	rounds := shrinkInputRoundsFromFixture(t, fx, ex.shapes)
	heights := openInputLogHeights(rounds)
	if len(heights) != 1+len(fx.RollInRounds) {
		t.Fatalf("input heights %v vs roll-in schedule %v", heights, fx.RollInRounds)
	}
	for qi, q := range fx.Queries {
		derived, err := openInputReducedRef(rounds, shrinkInputOpeningsRef(t, fx, qi),
			ex.openedEF, ex.ch.zeta, ex.friAlpha, q.ExpectedIndex, fx.Fri.LogGlobalMaxHeight)
		if err != nil {
			t.Fatalf("query %d: %v", qi, err)
		}
		if derived[0] != bbExtRef(q.InitialEval) {
			t.Fatalf("query %d: derived initial %v != exported %v", qi, derived[0], q.InitialEval)
		}
		for j := range fx.RollInRounds {
			if derived[j+1] != bbExtRef(q.RollIns[j]) {
				t.Fatalf("query %d roll-in %d: derived %v != exported %v",
					qi, j, derived[j+1], q.RollIns[j])
			}
		}
	}
}

// ----------------------------------------------------------------------------
// The gnark gadget in isolation (raw witnesses)
// ----------------------------------------------------------------------------

// shrinkOpenInputCircuit runs the open_input binding for a SUBSET of queries
// from raw witnesses (index bits, roots, challenges, opened values, seeds),
// isolating the seam gadget from the transcript replay (the FullVerify
// circuit covers the assembled binding).
type shrinkOpenInputCircuit struct {
	rounds       []OpenInputRoundShape // structural
	rollInRounds []int
	logMax       int

	Zeta          BBExt
	Alpha         BBExt
	Roots         []frontend.Variable
	OpenedEF      []BBExt
	IdxBits       [][]frontend.Variable // [query][logMax], LSB-first
	InitialEvals  []BBExt
	RollIns       [][]BBExt
	InputOpenings [][]OpenInputBatchOpening
}

func (c *shrinkOpenInputCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	bb.ExtAssertIsCanonical(c.Zeta)
	bb.ExtAssertIsCanonical(c.Alpha)
	for i := range c.OpenedEF {
		bb.ExtAssertIsCanonical(c.OpenedEF[i])
	}
	pre := NewOpenInputPrecomp(bb, c.rounds, c.Zeta, c.Alpha, c.OpenedEF, c.logMax)
	for qi := range c.IdxBits {
		bb.ExtAssertIsCanonical(c.InitialEvals[qi])
		for j := range c.RollIns[qi] {
			bb.ExtAssertIsCanonical(c.RollIns[qi][j])
		}
		BindOpenInputToFriSeedsNative(bb, c.rounds, pre, c.IdxBits[qi], c.Roots,
			c.InputOpenings[qi],
			FriNativeQueryOpening{InitialEval: c.InitialEvals[qi], RollIns: c.RollIns[qi]},
			c.rollInRounds)
	}
	return nil
}

func allocShrinkOpenInputCircuit(t *testing.T, fx *shrinkRealFixture, ex *shrinkStarkExtract, queries []int) *shrinkOpenInputCircuit {
	t.Helper()
	all := allocShrinkInputOpenings(fx)
	c := &shrinkOpenInputCircuit{
		rounds:       shrinkInputRoundsFromFixture(t, fx, ex.shapes),
		rollInRounds: append([]int(nil), fx.RollInRounds...),
		logMax:       fx.Fri.LogGlobalMaxHeight,
		Roots:        make([]frontend.Variable, 4),
		OpenedEF:     make([]BBExt, len(ex.openedEF)),
	}
	for _, qi := range queries {
		c.IdxBits = append(c.IdxBits, make([]frontend.Variable, fx.Fri.LogGlobalMaxHeight))
		c.InitialEvals = append(c.InitialEvals, BBExt{})
		c.RollIns = append(c.RollIns, make([]BBExt, len(fx.RollInRounds)))
		c.InputOpenings = append(c.InputOpenings, all[qi])
	}
	return c
}

func assignShrinkOpenInputCircuit(t *testing.T, fx *shrinkRealFixture, ex *shrinkStarkExtract, queries []int) *shrinkOpenInputCircuit {
	t.Helper()
	c := allocShrinkOpenInputCircuit(t, fx, ex, queries)
	roots := shrinkInputRootsRef(t, fx, ex.loc)
	for i := range roots {
		c.Roots[i] = frToBig(roots[i])
	}
	c.Zeta = extToVars(ex.ch.zeta)
	c.Alpha = extToVars(ex.friAlpha)
	for i, e := range ex.openedEF {
		c.OpenedEF[i] = extToVars(e)
	}
	filled := assignShrinkInputOpenings(t, fx)
	for slot, qi := range queries {
		q := fx.Queries[qi]
		for b := 0; b < fx.Fri.LogGlobalMaxHeight; b++ {
			c.IdxBits[slot][b] = (q.ExpectedIndex >> uint(b)) & 1
		}
		c.InitialEvals[slot] = extVars(q.InitialEval)
		for j, ri := range q.RollIns {
			c.RollIns[slot][j] = extVars(ri)
		}
		c.InputOpenings[slot] = filled[qi]
	}
	return c
}

// ACCEPT: the gadget derives and binds the reduced openings of the REAL
// shrink proof for every query.
func TestApexShrinkRealFixtureOpenInputGadgetAccepts(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	all := make([]int, len(fx.Queries))
	for i := range all {
		all[i] = i
	}
	if err := test.IsSolved(allocShrinkOpenInputCircuit(t, fx, ex, all),
		assignShrinkOpenInputCircuit(t, fx, ex, all), ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("open_input gadget rejected the REAL shrink proof's input openings: %v", err)
	}
}

// REJECT canaries, gadget side (query 0; every leg of the binding).
func TestApexShrinkRealFixtureOpenInputGadgetRejectsTampers(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	field := ecc.BN254.ScalarField()
	one := fr.One()
	q0 := []int{0}

	cases := []struct {
		name   string
		tamper func(c *shrinkOpenInputCircuit)
	}{
		{"tampered-input-row-value", func(c *shrinkOpenInputCircuit) {
			c.InputOpenings[0][0].Rows[2][0] =
				bbAddRef(fx.Queries[0].InputOpenings[0].Rows[2][0], 1)
		}},
		{"tampered-input-row-low-matrix", func(c *shrinkOpenInputCircuit) {
			c.InputOpenings[0][0].Rows[0][0] =
				bbAddRef(fx.Queries[0].InputOpenings[0].Rows[0][0], 1)
		}},
		{"tampered-merkle-path-node", func(c *shrinkOpenInputCircuit) {
			e := parseBn254Hex(t, fx.Queries[0].InputOpenings[1].Path[0])
			e.Add(&e, &one)
			c.InputOpenings[0][1].Path[0] = frToBig(e)
		}},
		{"tampered-commitment-root", func(c *shrinkOpenInputCircuit) {
			roots := shrinkInputRootsRef(t, fx, ex.loc)
			roots[3].Add(&roots[3], &one)
			c.Roots[3] = frToBig(roots[3])
		}},
		{"tampered-opened-at-zeta", func(c *shrinkOpenInputCircuit) {
			c.OpenedEF[0][0] = bbAddRef(ex.openedEF[0][0], 1)
		}},
		{"tampered-initial-eval", func(c *shrinkOpenInputCircuit) {
			c.InitialEvals[0][0] = bbAddRef(fx.Queries[0].InitialEval[0], 1)
		}},
		{"tampered-roll-in", func(c *shrinkOpenInputCircuit) {
			c.RollIns[0][1][0] = bbAddRef(fx.Queries[0].RollIns[1][0], 1)
		}},
		{"flipped-index-bit", func(c *shrinkOpenInputCircuit) {
			c.IdxBits[0][fx.Fri.LogGlobalMaxHeight-1] =
				1 - ((fx.Queries[0].ExpectedIndex >> uint(fx.Fri.LogGlobalMaxHeight-1)) & 1)
		}},
		{"non-boolean-index-bit", func(c *shrinkOpenInputCircuit) {
			c.IdxBits[0][0] = 2
		}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			w := assignShrinkOpenInputCircuit(t, fx, ex, q0)
			tc.tamper(w)
			if err := test.IsSolved(allocShrinkOpenInputCircuit(t, fx, ex, q0), w, field); err == nil {
				t.Fatalf("%s: open_input gadget ACCEPTED tampered real data", tc.name)
			}
		})
	}
}

// ----------------------------------------------------------------------------
// The assembled FullVerify binding
// ----------------------------------------------------------------------------

// BINDING canary, assembled circuit: a tampered input-batch row (the opened
// column at the query point) must fail the ASSEMBLED verify — the seam this
// closure exists for: openings consistent with the transcript but not with
// the committed trace REJECT.
func TestApexShrinkRealFixtureFullVerifyRejectsTamperedInputOpening(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	w := assignSettlementCircuit(t, fx, ex, sym)
	w.InputOpenings[0][0].Rows[2][0] = bbAddRef(fx.Queries[0].InputOpenings[0].Rows[2][0], 1)
	if err := test.IsSolved(allocSettlementCircuit(t, fx, ex, sym), w,
		ecc.BN254.ScalarField()); err == nil {
		t.Fatal("assembled circuit ACCEPTED a tampered input-batch opening")
	}
}
