// THE WRAP END-TO-END (STARK-algebra layer): gnark verifies the batch-STARK
// algebra of the REAL shrink proof — quotient identities at zeta with FULL
// in-circuit constraint evaluation for all 5 instances (via the emitted
// symbolic AIR DAGs; the 3 simple instances also by an independent
// hand-derived path), plus the global LogUp balance — on top of the SAME
// transcript replay + FRI core the existing real-fixture test drives.
//
// The fixture (fixtures/apex_shrink_fri_real.json) ALREADY carries the whole
// STARK-algebra input: the pre-FRI transcript prefix contains the opened
// values at zeta (pcs.verify observes every opened value before sampling the
// FRI alpha — two_adic_pcs.rs:687-694, mirrored by the exporter at
// apex_shrink_gnark_export.rs:571-580) and every sampled challenge
// (perm alpha/beta, the constraint-folding alpha, zeta). This file locates
// them by the ANCHORED tail structure of the event stream and slices them by
// the pinned 5-instance shape (see stark_verify_native.go ShrinkVk).
//
// HONEST SCOPE: see stark_verify_native.go — the constraint evaluation and
// quotient identity are REAL checks for all 5 instances; the remaining
// soundness seam is the in-circuit derivation of the FRI reduced openings
// from these same opened values (open_input), which still enter the FRI
// core as host-computed witnesses.
package friverifier

import (
	"fmt"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// ----------------------------------------------------------------------------
// Anchored prefix location + shape decoding
// ----------------------------------------------------------------------------

// shrinkStarkPrefixLoc holds flat offsets into the prefix observe/sample
// streams for the STARK-algebra inputs.
type shrinkStarkPrefixLoc struct {
	permChSampleOff int // 8 values: perm alpha then perm beta coords
	alphaSampleOff  int // 4 values
	zetaSampleOff   int // 4 values
	openedObsOff    int // 4*totalEF values
	openedObsLen    int
	cumObsOff       int // 4*numGlobalLookups values
	cumObsLen       int
}

// locateShrinkStarkPrefix walks the fixture's event stream and anchors the
// STARK-algebra events by the tail structure of verify_batch's transcript
// (batch-stark verifier/mod.rs:288-300 + pcs.verify observes + FRI alpha):
//
//	..., sample(perm challenges), observe_digest(perm cap),
//	observe_bb(cumulative sums), sample(alpha), observe_digest(quotient cap),
//	sample(zeta), observe_bb(opened values), sample(FRI alpha)
//
// Fail-closed on any kind/length mismatch.
func locateShrinkStarkPrefix(fx *shrinkRealFixture) (shrinkStarkPrefixLoc, error) {
	evs := fx.PrefixEvents
	n := len(evs)
	if n < 8 {
		return shrinkStarkPrefixLoc{}, fmt.Errorf("prefix has only %d events", n)
	}
	// Cumulative flat offsets per event.
	obsOff := make([]int, n)
	sampOff := make([]int, n)
	obs, samp := 0, 0
	for i, ev := range evs {
		obsOff[i] = obs
		sampOff[i] = samp
		switch ev.Kind {
		case "observe_bb":
			obs += len(ev.Values)
		case "sample_bb":
			samp += len(ev.Values)
		}
	}
	check := func(i int, kind string, vals int) error {
		if evs[i].Kind != kind {
			return fmt.Errorf("event %d: kind %q, want %q", i, evs[i].Kind, kind)
		}
		if vals >= 0 && len(evs[i].Values) != vals {
			return fmt.Errorf("event %d: %d values, want %d", i, len(evs[i].Values), vals)
		}
		return nil
	}
	for _, e := range []error{
		check(n-1, "sample_bb", 4),      // FRI batch-combination alpha
		check(n-2, "observe_bb", -1),    // opened values at zeta
		check(n-3, "sample_bb", 4),      // zeta
		check(n-4, "observe_digest", 0), // quotient commitment
		check(n-5, "sample_bb", 4),      // constraint-folding alpha
		check(n-6, "observe_bb", -1),    // cumulative sums
		check(n-7, "observe_digest", 0), // permutation commitment
		check(n-8, "sample_bb", 8),      // WitnessChecks (alpha, beta)
	} {
		if e != nil {
			return shrinkStarkPrefixLoc{}, e
		}
	}
	if len(evs[n-2].Values)%4 != 0 || len(evs[n-6].Values)%4 != 0 {
		return shrinkStarkPrefixLoc{}, fmt.Errorf("opened/cum streams not EF-aligned")
	}
	return shrinkStarkPrefixLoc{
		permChSampleOff: sampOff[n-8],
		alphaSampleOff:  sampOff[n-5],
		zetaSampleOff:   sampOff[n-3],
		openedObsOff:    obsOff[n-2],
		openedObsLen:    len(evs[n-2].Values),
		cumObsOff:       obsOff[n-6],
		cumObsLen:       len(evs[n-6].Values),
	}, nil
}

// shrinkShapesFromFixture decodes the transcript-bound binding block
// (event 0: instance count + per-instance ext_db/base_db/width/n_chunks,
// each usize-lifted to [v,0,0,0]) and the preprocessed widths (event 2 tail)
// and merges them with the pinned VK flags. Fail-closed on any drift.
func shrinkShapesFromFixture(t *testing.T, fx *shrinkRealFixture) []StarkInstanceShape {
	t.Helper()
	evs := fx.PrefixEvents
	if len(evs) < 3 || evs[0].Kind != "observe_bb" || evs[2].Kind != "observe_bb" {
		t.Fatal("prefix head structure drifted (binding block / widths block)")
	}
	e0 := evs[0].Values
	lift := func(off int, what string) int {
		if off+4 > len(e0) {
			t.Fatalf("binding block truncated reading %s", what)
		}
		if e0[off+1] != 0 || e0[off+2] != 0 || e0[off+3] != 0 {
			t.Fatalf("binding block %s is not a usize lift: %v", what, e0[off:off+4])
		}
		return int(e0[off])
	}
	nInst := lift(0, "instance count")
	if nInst != 5 || len(e0) != 4+16*nInst {
		t.Fatalf("binding block: %d instances / %d values (want 5 / 84)", nInst, len(e0))
	}
	e2 := evs[2].Values
	if len(e2) != 4*nInst {
		t.Fatalf("widths block has %d values (want %d: no public values in the shrink scope)",
			len(e2), 4*nInst)
	}
	shapes := make([]StarkInstanceShape, nInst)
	for i := 0; i < nInst; i++ {
		extDb := lift(4+16*i, "ext_db")
		baseDb := lift(8+16*i, "base_db")
		width := lift(12+16*i, "width")
		nChunks := lift(16+16*i, "n_chunks")
		if extDb != baseDb || extDb != fx.DegreeBits[i] {
			t.Fatalf("instance %d: degree bits %d/%d vs fixture %d",
				i, extDb, baseDb, fx.DegreeBits[i])
		}
		if e2[4*i+1] != 0 || e2[4*i+2] != 0 || e2[4*i+3] != 0 {
			t.Fatalf("preprocessed width %d is not a usize lift", i)
		}
		shapes[i] = StarkInstanceShape{
			DegreeBits:        extDb,
			Width:             width,
			PreWidth:          int(e2[4*i]),
			NumQuotientChunks: nChunks,
			NumLookups:        ShrinkVk.NumLookups[i],
			NumGlobalLookups:  ShrinkVk.NumLookups[i],
			HasTraceNext:      ShrinkVk.TraceNext[i],
			HasPreNext:        ShrinkVk.PreNext[i],
		}
	}
	return shapes
}

// shrinkStarkExtract is the host-side extraction of the algebra inputs.
type shrinkStarkExtract struct {
	shapes   []StarkInstanceShape
	loc      shrinkStarkPrefixLoc
	openedEF []bbExtRef
	cumSums  []bbExtRef
	ch       shrinkStarkChallengesRef
}

func extractShrinkStark(t *testing.T, fx *shrinkRealFixture) *shrinkStarkExtract {
	t.Helper()
	loc, err := locateShrinkStarkPrefix(fx)
	if err != nil {
		t.Fatalf("anchored prefix location failed: %v", err)
	}
	shapes := shrinkShapesFromFixture(t, fx)
	_, totalEF := buildStarkOpenedSpans(shapes)
	if loc.openedObsLen != 4*totalEF {
		t.Fatalf("opened-values stream: %d values, pinned shape requires %d "+
			"(the 5-instance shape accounting must be EXACT)", loc.openedObsLen, 4*totalEF)
	}
	if want := 4 * totalGlobalLookups(shapes); loc.cumObsLen != want {
		t.Fatalf("cumulative-sums stream: %d values, want %d", loc.cumObsLen, want)
	}

	// Flatten the observe/sample streams.
	var obs, samp []uint32
	for _, ev := range fx.PrefixEvents {
		switch ev.Kind {
		case "observe_bb":
			obs = append(obs, ev.Values...)
		case "sample_bb":
			samp = append(samp, ev.Values...)
		}
	}
	groupEF := func(vals []uint32) []bbExtRef {
		out := make([]bbExtRef, len(vals)/4)
		for i := range out {
			copy(out[i][:], vals[4*i:4*i+4])
		}
		return out
	}
	ext := func(off int) bbExtRef {
		var e bbExtRef
		copy(e[:], samp[off:off+4])
		return e
	}
	return &shrinkStarkExtract{
		shapes:   shapes,
		loc:      loc,
		openedEF: groupEF(obs[loc.openedObsOff : loc.openedObsOff+loc.openedObsLen]),
		cumSums:  groupEF(obs[loc.cumObsOff : loc.cumObsOff+loc.cumObsLen]),
		ch: shrinkStarkChallengesRef{
			permAlpha: ext(loc.permChSampleOff),
			permBeta:  ext(loc.permChSampleOff + 4),
			alpha:     ext(loc.alphaSampleOff),
			zeta:      ext(loc.zetaSampleOff),
		},
	}
}

// ----------------------------------------------------------------------------
// Host-reference checks on the REAL proof
// ----------------------------------------------------------------------------

// ACCEPT: the reference algebra layer accepts the real shrink proof — the
// quotient identity HOLDS on the real openings for the three fully-evaluated
// instances, and the global WitnessChecks sums balance.
func TestApexShrinkRealFixtureStarkAlgebraRefAccepts(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	heavy, err := verifyShrinkStarkAlgebraRef(ex.shapes, ex.openedEF, ex.cumSums, ex.ch, nil)
	if err != nil {
		t.Fatalf("reference STARK algebra REJECTED the real shrink proof: %v", err)
	}
	if len(heavy) != 2 {
		t.Fatalf("expected 2 heavy instances (Alu, Poseidon2), got %d", len(heavy))
	}
}

// REJECT canaries, reference side: single tampers of the real openings must
// fail the identity or the balance (the accept above is not vacuous).
func TestApexShrinkRealFixtureStarkAlgebraRefRejectsTampers(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	base := extractShrinkStark(t, fx)
	spans, _ := buildStarkOpenedSpans(base.shapes)

	cases := []struct {
		name   string
		tamper func(ex *shrinkStarkExtract)
	}{
		{"tampered-const-trace-value", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[0].traceLocal.off][0] =
				bbAddRef(ex.openedEF[spans[0].traceLocal.off][0], 1)
		}},
		{"tampered-const-quotient-chunk", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[0].quotientChunks[0].off][2] =
				bbAddRef(ex.openedEF[spans[0].quotientChunks[0].off][2], 1)
		}},
		{"tampered-public-perm-column", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[1].permLocal.off][1] =
				bbAddRef(ex.openedEF[spans[1].permLocal.off][1], 1)
		}},
		{"tampered-recompose-pre-mult", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[4].preLocal.off+1][0] =
				bbAddRef(ex.openedEF[spans[4].preLocal.off+1][0], 1)
		}},
		{"tampered-const-cum-sum", func(ex *shrinkStarkExtract) {
			ex.cumSums[spans[0].cumSums.off][0] =
				bbAddRef(ex.cumSums[spans[0].cumSums.off][0], 1)
		}},
		{"tampered-alu-cum-sum-balance", func(ex *shrinkStarkExtract) {
			// Alu's identity is witness-derived (not a ref check), so this
			// canary isolates the GLOBAL BALANCE tooth.
			ex.cumSums[spans[2].cumSums.off][0] =
				bbAddRef(ex.cumSums[spans[2].cumSums.off][0], 1)
		}},
		{"tampered-zeta", func(ex *shrinkStarkExtract) {
			ex.ch.zeta[0] = bbAddRef(ex.ch.zeta[0], 1)
		}},
		{"tampered-perm-beta", func(ex *shrinkStarkExtract) {
			ex.ch.permBeta[3] = bbAddRef(ex.ch.permBeta[3], 1)
		}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			ex := extractShrinkStark(t, fx)
			tc.tamper(ex)
			if _, err := verifyShrinkStarkAlgebraRef(ex.shapes, ex.openedEF, ex.cumSums, ex.ch, nil); err == nil {
				t.Fatalf("%s: reference ACCEPTED tampered real openings", tc.name)
			}
		})
	}
}

// ----------------------------------------------------------------------------
// The gnark gadget, algebra layer in isolation (raw witnesses)
// ----------------------------------------------------------------------------

// shrinkStarkAlgebraCircuit feeds VerifyShrinkStarkAlgebra from raw witness
// arrays (canonicity asserted at ingestion), isolating the algebra teeth
// from the transcript binding (which the integration circuit below covers).
type shrinkStarkAlgebraCircuit struct {
	shapes []StarkInstanceShape // structural
	sym    *SymbolicConstraints // structural; nil = hand mode

	OpenedEF             []BBExt
	CumSums              []BBExt
	PermAlpha            BBExt
	PermBeta             BBExt
	Alpha                BBExt
	Zeta                 BBExt
	HeavyFoldedAlu       BBExt
	HeavyFoldedPoseidon2 BBExt
}

func (c *shrinkStarkAlgebraCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	for i := range c.OpenedEF {
		bb.ExtAssertIsCanonical(c.OpenedEF[i])
	}
	for i := range c.CumSums {
		bb.ExtAssertIsCanonical(c.CumSums[i])
	}
	for _, e := range []BBExt{c.PermAlpha, c.PermBeta, c.Alpha, c.Zeta} {
		bb.ExtAssertIsCanonical(e)
	}
	VerifyShrinkStarkAlgebra(bb, c.shapes, c.OpenedEF, c.CumSums,
		ShrinkStarkChallenges{
			PermAlpha: c.PermAlpha, PermBeta: c.PermBeta,
			Alpha: c.Alpha, Zeta: c.Zeta,
		},
		c.sym,
		map[int]BBExt{2: c.HeavyFoldedAlu, 3: c.HeavyFoldedPoseidon2})
	return nil
}

func allocShrinkStarkAlgebraCircuit(ex *shrinkStarkExtract) *shrinkStarkAlgebraCircuit {
	return allocShrinkStarkAlgebraCircuitSym(ex, nil)
}

func allocShrinkStarkAlgebraCircuitSym(ex *shrinkStarkExtract, sym *SymbolicConstraints) *shrinkStarkAlgebraCircuit {
	return &shrinkStarkAlgebraCircuit{
		shapes:   ex.shapes,
		sym:      sym,
		OpenedEF: make([]BBExt, len(ex.openedEF)),
		CumSums:  make([]BBExt, len(ex.cumSums)),
	}
}

func assignShrinkStarkAlgebraCircuit(t *testing.T, ex *shrinkStarkExtract) *shrinkStarkAlgebraCircuit {
	return assignShrinkStarkAlgebraCircuitSym(t, ex, nil)
}

func assignShrinkStarkAlgebraCircuitSym(t *testing.T, ex *shrinkStarkExtract, sym *SymbolicConstraints) *shrinkStarkAlgebraCircuit {
	t.Helper()
	heavy, err := verifyShrinkStarkAlgebraRef(ex.shapes, ex.openedEF, ex.cumSums, ex.ch, nil)
	if err != nil {
		t.Fatalf("host reference must accept before circuit assignment: %v", err)
	}
	c := allocShrinkStarkAlgebraCircuitSym(ex, sym)
	for i, e := range ex.openedEF {
		c.OpenedEF[i] = extToVars(e)
	}
	for i, e := range ex.cumSums {
		c.CumSums[i] = extToVars(e)
	}
	c.PermAlpha = extToVars(ex.ch.permAlpha)
	c.PermBeta = extToVars(ex.ch.permBeta)
	c.Alpha = extToVars(ex.ch.alpha)
	c.Zeta = extToVars(ex.ch.zeta)
	c.HeavyFoldedAlu = extToVars(heavy[2])
	c.HeavyFoldedPoseidon2 = extToVars(heavy[3])
	return c
}

// ACCEPT: the gadget verifies the real proof's STARK algebra.
func TestApexShrinkRealFixtureStarkAlgebraGadgetAccepts(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	if err := test.IsSolved(allocShrinkStarkAlgebraCircuit(ex),
		assignShrinkStarkAlgebraCircuit(t, ex), ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("gadget rejected the REAL shrink proof's STARK algebra: %v", err)
	}
}

// REJECT canaries, gadget side.
func TestApexShrinkRealFixtureStarkAlgebraGadgetRejectsTampers(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	field := ecc.BN254.ScalarField()
	baseEx := extractShrinkStark(t, fx)
	spans, _ := buildStarkOpenedSpans(baseEx.shapes)

	cases := []struct {
		name   string
		tamper func(c *shrinkStarkAlgebraCircuit)
	}{
		{"tampered-const-quotient-chunk", func(c *shrinkStarkAlgebraCircuit) {
			c.OpenedEF[spans[0].quotientChunks[0].off][0] =
				bbAddRef(baseEx.openedEF[spans[0].quotientChunks[0].off][0], 1)
		}},
		{"tampered-public-perm-column", func(c *shrinkStarkAlgebraCircuit) {
			c.OpenedEF[spans[1].permLocal.off][2] =
				bbAddRef(baseEx.openedEF[spans[1].permLocal.off][2], 1)
		}},
		{"tampered-recompose-trace-value", func(c *shrinkStarkAlgebraCircuit) {
			c.OpenedEF[spans[4].traceLocal.off][0] =
				bbAddRef(baseEx.openedEF[spans[4].traceLocal.off][0], 1)
		}},
		{"tampered-alu-cum-sum-balance", func(c *shrinkStarkAlgebraCircuit) {
			c.CumSums[spans[2].cumSums.off][0] =
				bbAddRef(baseEx.cumSums[spans[2].cumSums.off][0], 1)
		}},
		{"tampered-heavy-folded-witness", func(c *shrinkStarkAlgebraCircuit) {
			var e bbExtRef
			for i := range e {
				e[i] = 0
			}
			// A wrong witnessed folded value must fail its (consistency)
			// identity against the real quotient openings.
			c.HeavyFoldedAlu = extToVars(bbExtRef{1, 2, 3, 4})
			_ = e
		}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			ex := extractShrinkStark(t, fx)
			w := assignShrinkStarkAlgebraCircuit(t, ex)
			tc.tamper(w)
			if err := test.IsSolved(allocShrinkStarkAlgebraCircuit(ex), w, field); err == nil {
				t.Fatalf("%s: gadget ACCEPTED tampered real openings", tc.name)
			}
		})
	}
}

// ----------------------------------------------------------------------------
// The assembled native verify: transcript replay + STARK algebra + FRI core
// ----------------------------------------------------------------------------

// apexShrinkFullVerifyCircuit is the fullest assembled native-verify shape so
// far: ONE Define that replays the real pre-FRI transcript (pinning every
// challenge), runs the STARK-algebra layer over the SAME transcript-bound
// opened values, and verifies the FRI core — everything on the real proof.
// (The remaining gap to a full batch-STARK verify is named in
// stark_verify_native.go HONEST SCOPE.)
type apexShrinkFullVerifyCircuit struct {
	script           []shrinkPrefixOp
	cfg              FriConfig
	r                int
	rollInAfterRound []int
	shapes           []StarkInstanceShape
	loc              shrinkStarkPrefixLoc
	sym              *SymbolicConstraints // structural: FULL constraint eval

	PrefixObs     []frontend.Variable
	PrefixDigests []frontend.Variable
	PrefixSamples []frontend.Variable
	CommitRoots   []frontend.Variable
	FinalPoly     []BBExt
	PowWitness    frontend.Variable
	Queries       []FriNativeQueryOpening
}

func (c *apexShrinkFullVerifyCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	ch := NewMultiFieldChallenger(bb)

	// Transcript replay — every observed value canonicity-bound by the
	// challenger, every sampled challenge pinned to the Rust value.
	io, id, is := 0, 0, 0
	for _, op := range c.script {
		switch op.kind {
		case "observe_bb":
			ch.ObserveBabyBearSlice(c.PrefixObs[io : io+op.n])
			io += op.n
		case "observe_digest":
			ch.ObserveBn254Digest(c.PrefixDigests[id : id+op.n])
			id += op.n
		case "sample_bb":
			for k := 0; k < op.n; k++ {
				api.AssertIsEqual(ch.SampleBabyBear(), c.PrefixSamples[is])
				is++
			}
		}
	}

	// STARK-algebra layer over the transcript-bound opened values.
	groupEF := func(vars []frontend.Variable) []BBExt {
		out := make([]BBExt, len(vars)/4)
		for i := range out {
			copy(out[i][:], vars[4*i:4*i+4])
		}
		return out
	}
	sampleExt := func(off int) BBExt {
		var e BBExt
		copy(e[:], c.PrefixSamples[off:off+4])
		return e
	}
	VerifyShrinkStarkAlgebra(bb, c.shapes,
		groupEF(c.PrefixObs[c.loc.openedObsOff:c.loc.openedObsOff+c.loc.openedObsLen]),
		groupEF(c.PrefixObs[c.loc.cumObsOff:c.loc.cumObsOff+c.loc.cumObsLen]),
		ShrinkStarkChallenges{
			PermAlpha: sampleExt(c.loc.permChSampleOff),
			PermBeta:  sampleExt(c.loc.permChSampleOff + 4),
			Alpha:     sampleExt(c.loc.alphaSampleOff),
			Zeta:      sampleExt(c.loc.zetaSampleOff),
		},
		c.sym, nil)

	// FRI core, drawing betas and query indices live from the same
	// transcript.
	VerifyFriNative(bb, c.cfg, c.r, c.CommitRoots, c.FinalPoly, c.PowWitness,
		c.Queries, c.rollInAfterRound, ch)
	return nil
}

func allocApexShrinkFullVerifyCircuit(t *testing.T, fx *shrinkRealFixture, ex *shrinkStarkExtract, sym *SymbolicConstraints) *apexShrinkFullVerifyCircuit {
	t.Helper()
	inner := allocApexShrinkRealCircuit(fx)
	return &apexShrinkFullVerifyCircuit{
		script:           inner.script,
		cfg:              inner.cfg,
		r:                inner.r,
		rollInAfterRound: inner.rollInAfterRound,
		shapes:           ex.shapes,
		loc:              ex.loc,
		sym:              sym,
		PrefixObs:        inner.PrefixObs,
		PrefixDigests:    inner.PrefixDigests,
		PrefixSamples:    inner.PrefixSamples,
		CommitRoots:      inner.CommitRoots,
		FinalPoly:        inner.FinalPoly,
		Queries:          inner.Queries,
	}
}

func assignApexShrinkFullVerifyCircuit(t *testing.T, fx *shrinkRealFixture, ex *shrinkStarkExtract, sym *SymbolicConstraints) *apexShrinkFullVerifyCircuit {
	t.Helper()
	if _, err := verifyShrinkStarkAlgebraRef(ex.shapes, ex.openedEF, ex.cumSums, ex.ch, sym); err != nil {
		t.Fatalf("host reference must accept before circuit assignment: %v", err)
	}
	inner := assignApexShrinkRealCircuit(t, fx)
	return &apexShrinkFullVerifyCircuit{
		script:           inner.script,
		cfg:              inner.cfg,
		r:                inner.r,
		rollInAfterRound: inner.rollInAfterRound,
		shapes:           ex.shapes,
		loc:              ex.loc,
		sym:              sym,
		PrefixObs:        inner.PrefixObs,
		PrefixDigests:    inner.PrefixDigests,
		PrefixSamples:    inner.PrefixSamples,
		CommitRoots:      inner.CommitRoots,
		FinalPoly:        inner.FinalPoly,
		PowWitness:       inner.PowWitness,
		Queries:          inner.Queries,
	}
}

// ACCEPT: the assembled circuit (replay + STARK algebra + FRI core) verifies
// the REAL shrink proof end to end.
func TestApexShrinkRealFixtureFullVerifyGadgetAccepts(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	if err := test.IsSolved(allocApexShrinkFullVerifyCircuit(t, fx, ex, sym),
		assignApexShrinkFullVerifyCircuit(t, fx, ex, sym), ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("assembled circuit rejected the REAL shrink proof: %v", err)
	}
}

// BINDING canary: tampering an opened trace value INSIDE the transcript
// stream must fail — the algebra layer consumes the same variables the
// challenger absorbed, so the transcript pin catches in-stream tampering.
func TestApexShrinkRealFixtureFullVerifyGadgetBindsOpenings(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	w := assignApexShrinkFullVerifyCircuit(t, fx, ex, sym)
	tampered := ex.loc.openedObsOff // first coordinate of the first opened value
	w.PrefixObs[tampered] = bbAddRef(ex.openedEF[0][0], 1)
	if err := test.IsSolved(allocApexShrinkFullVerifyCircuit(t, fx, ex, sym), w,
		ecc.BN254.ScalarField()); err == nil {
		t.Fatal("assembled circuit ACCEPTED a tampered in-transcript opened value")
	}
}

// ----------------------------------------------------------------------------
// FULL constraint evaluation via the emitted symbolic AIR DAGs
// ----------------------------------------------------------------------------

const shrinkSymbolicConstraintsPath = "fixtures/shrink_symbolic_constraints.json"

func loadShrinkSymbolicConstraints(t *testing.T) *SymbolicConstraints {
	t.Helper()
	sym, err := LoadSymbolicConstraints(shrinkSymbolicConstraintsPath)
	if err != nil {
		t.Fatalf("emitted symbolic constraints must load (emit via "+
			"plonky3-recursion/circuit-prover/tests/emit_shrink_symbolic.rs): %v", err)
	}
	return sym
}

// THE CLOSURE CHECK: with the interpreted (emitted, not hand-coded)
// constraints, the quotient identity holds on the REAL shrink proof for ALL
// FIVE instances — including Alu (146 constraints) and Poseidon2 (337
// constraints). A wrong emitted tree, wrong AIR knob, or wrong interpreter
// semantics cannot pass this (~124-bit equation per instance on real data).
func TestApexShrinkRealFixtureSymbolicConstraintsRefAccepts(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	if _, err := verifyShrinkStarkAlgebraRef(ex.shapes, ex.openedEF, ex.cumSums, ex.ch, sym); err != nil {
		t.Fatalf("interpreted constraints REJECTED the real shrink proof: %v", err)
	}
}

// DIFFERENTIAL: for the three simple instances the interpreted folded value
// must equal the INDEPENDENT hand-derived LogUp evaluation — two disjoint
// paths (emitted-DAG interpreter vs hand-ported logup.rs algebra) agreeing
// on real data.
func TestApexShrinkRealFixtureSymbolicVsHandFolded(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	spans, _ := buildStarkOpenedSpans(ex.shapes)
	slice := func(s efSpan) []bbExtRef { return ex.openedEF[s.off : s.off+s.len] }
	for i, spec := range ShrinkVk.SimpleSpecs {
		sh := ex.shapes[i]
		sp := spans[i]
		sel, err := computeStarkSelectorsRef(ex.ch.zeta, sh.DegreeBits)
		if err != nil {
			t.Fatal(err)
		}
		pre := slice(sp.preLocal)
		trace := slice(sp.traceLocal)
		perm := slice(sp.permLocal)
		permNext := slice(sp.permNext)
		elems := append([]bbExtRef{pre[spec.idxPreCol]}, trace...)
		hand := evalWitnessBusFoldedRef(
			sel, ex.ch.alpha, ex.ch.permAlpha, ex.ch.permBeta,
			elems, pre[spec.multPreCol],
			bbExtFromBasisRef([4]bbExtRef(perm[0:4])),
			bbExtFromBasisRef([4]bbExtRef(permNext[0:4])),
			ex.cumSums[sp.cumSums.off],
		)
		interp, err := evalSymbolicFoldedRef(&sym.Instances[i],
			shrinkSymInputsRef(sh, sp, slice, ex.cumSums, ex.ch, sel), ex.ch.alpha)
		if err != nil {
			t.Fatalf("instance %d: %v", i, err)
		}
		if hand != interp {
			t.Fatalf("instance %d (%s): hand-derived folded %v != interpreted %v",
				i, sym.Instances[i].Name, hand, interp)
		}
	}
}

// REJECT canaries with the interpreted constraints: tampering the HEAVY
// instances' openings must now fail (these values were unchecked witnesses
// before the symbolic closure).
func TestApexShrinkRealFixtureSymbolicConstraintsRefRejectsTampers(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	base := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	spans, _ := buildStarkOpenedSpans(base.shapes)

	cases := []struct {
		name   string
		tamper func(ex *shrinkStarkExtract)
	}{
		{"tampered-alu-trace-value", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[2].traceLocal.off+10][0] =
				bbAddRef(ex.openedEF[spans[2].traceLocal.off+10][0], 1)
		}},
		{"tampered-alu-trace-next", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[2].traceNext.off+3][2] =
				bbAddRef(ex.openedEF[spans[2].traceNext.off+3][2], 1)
		}},
		{"tampered-alu-preprocessed", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[2].preLocal.off+5][1] =
				bbAddRef(ex.openedEF[spans[2].preLocal.off+5][1], 1)
		}},
		{"tampered-poseidon2-trace-value", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[3].traceLocal.off+123][0] =
				bbAddRef(ex.openedEF[spans[3].traceLocal.off+123][0], 1)
		}},
		{"tampered-poseidon2-perm-column", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[3].permLocal.off+8][3] =
				bbAddRef(ex.openedEF[spans[3].permLocal.off+8][3], 1)
		}},
		{"tampered-poseidon2-quotient-chunk", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[3].quotientChunks[1].off][1] =
				bbAddRef(ex.openedEF[spans[3].quotientChunks[1].off][1], 1)
		}},
		{"tampered-alu-cum-sum", func(ex *shrinkStarkExtract) {
			ex.cumSums[spans[2].cumSums.off+4][0] =
				bbAddRef(ex.cumSums[spans[2].cumSums.off+4][0], 1)
		}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			ex := extractShrinkStark(t, fx)
			tc.tamper(ex)
			if _, err := verifyShrinkStarkAlgebraRef(ex.shapes, ex.openedEF, ex.cumSums, ex.ch, sym); err == nil {
				t.Fatalf("%s: interpreted constraints ACCEPTED tampered real openings", tc.name)
			}
		})
	}
}

// ACCEPT + REJECT, gadget side, full symbolic mode: the in-circuit
// interpreter evaluates ALL FIVE instances' constraints on the real proof.
func TestApexShrinkRealFixtureSymbolicGadgetAccepts(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	if err := test.IsSolved(allocShrinkStarkAlgebraCircuitSym(ex, sym),
		assignShrinkStarkAlgebraCircuitSym(t, ex, sym), ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("in-circuit interpreted constraints rejected the REAL proof: %v", err)
	}
}

func TestApexShrinkRealFixtureSymbolicGadgetRejectsTampers(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	field := ecc.BN254.ScalarField()
	baseEx := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	spans, _ := buildStarkOpenedSpans(baseEx.shapes)

	cases := []struct {
		name   string
		tamper func(c *shrinkStarkAlgebraCircuit)
	}{
		{"tampered-alu-trace-value", func(c *shrinkStarkAlgebraCircuit) {
			c.OpenedEF[spans[2].traceLocal.off+10][0] =
				bbAddRef(baseEx.openedEF[spans[2].traceLocal.off+10][0], 1)
		}},
		{"tampered-poseidon2-perm-column", func(c *shrinkStarkAlgebraCircuit) {
			c.OpenedEF[spans[3].permLocal.off+8][3] =
				bbAddRef(baseEx.openedEF[spans[3].permLocal.off+8][3], 1)
		}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			ex := extractShrinkStark(t, fx)
			w := assignShrinkStarkAlgebraCircuitSym(t, ex, sym)
			tc.tamper(w)
			if err := test.IsSolved(allocShrinkStarkAlgebraCircuitSym(ex, sym), w, field); err == nil {
				t.Fatalf("%s: gadget ACCEPTED tampered real openings", tc.name)
			}
		})
	}
}
