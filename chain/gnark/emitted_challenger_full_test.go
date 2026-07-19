// THE FULL-TRANSCRIPT CHALLENGER RE-DERIVATION GATE, driven by the LEAN-EMITTED
// permutation.
//
// emitted_challenger_replay_diff_test.go proved the committed capacity-0 duplex
// template (ChallengerReplayEmit.lean) binds the sponge CORE on the real roots but
// — measured on the real proof — reproduces NONE of the deployed shrink challenges,
// because those come from the MultiField adapter over a CHAINED sponge, not a
// fresh capacity-0 duplexing (that file's §3 residual). This file closes that gap
// at FULL real-transcript scale: it drives the SAME deployed MultiField adapter
// (multifield_challenger.go — pack/split/tag/flush unchanged) through the LEAN-
// EMITTED Poseidon2 permutation (emitted/poseidon2_template.json via ReplayTemplate,
// installed by NewMultiFieldChallengerWithPerm) and re-derives EVERY challenge the
// verifier consumes, in-circuit, on the real apex-shrink proof:
//
//   - PermAlpha, PermBeta, the constraint-folding alpha, zeta, the FRI batch alpha
//     (the prefix sample_bb challenges) — asserted equal to their pinned values;
//   - the per-round FRI betas and the per-query indices — drawn LIVE inside
//     VerifyFriNative and bound by the fold-chain + Merkle-opening checks.
//
// This is the emitted-permutation twin of the deployed apexShrinkRealCircuit
// (apex_shrink_real_fixture_test.go): identical transcript replay, permutation
// swapped hand-Go -> Lean-emitted. So the crypto primitive re-deriving the
// challenges is the Lean-authored R1CS, not a hand-Go say-so. The NAMED residual
// is the MultiField pack/split adapter and its split-soundness range checks, which
// remain hand-Go (emitted_challenger.go package doc).
package friverifier

import (
	"fmt"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	fr "github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// emittedShrinkTranscriptCircuit re-derives the full real shrink transcript's
// challenges through the MultiField adapter over the LEAN-EMITTED permutation. Its
// witness fields mirror apexShrinkRealCircuit exactly (so the deployed assign path
// populates it); only the permutation the sponge duplexes through differs.
type emittedShrinkTranscriptCircuit struct {
	// Structural (unexported: ignored by the gnark schema walker).
	script           []shrinkPrefixOp
	cfg              FriConfig
	r                int
	rollInAfterRound []int
	tpl              *Template

	PrefixObs     []frontend.Variable
	PrefixDigests []frontend.Variable
	PrefixSamples []frontend.Variable
	CommitRoots   []frontend.Variable
	FinalPoly     []BBExt
	PowWitness    frontend.Variable
	Queries       []FriNativeQueryOpening
}

func (c *emittedShrinkTranscriptCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	ch := NewMultiFieldChallengerWithPerm(bb, newEmittedPoseidon2Perm(c.tpl))
	rederiveShrinkChallenges(bb, ch, &shrinkTranscriptInputs{
		script: c.script, cfg: c.cfg, r: c.r, rollInAfterRound: c.rollInAfterRound,
		PrefixObs: c.PrefixObs, PrefixDigests: c.PrefixDigests, PrefixSamples: c.PrefixSamples,
		CommitRoots: c.CommitRoots, FinalPoly: c.FinalPoly, PowWitness: c.PowWitness, Queries: c.Queries,
	}, nil)
	return nil
}

// fromApexShrinkReal wraps a populated apexShrinkRealCircuit (alloc or assign) as
// the emitted-permutation twin, attaching the Lean-emitted permutation template.
func fromApexShrinkReal(a *apexShrinkRealCircuit, tpl *Template) *emittedShrinkTranscriptCircuit {
	return &emittedShrinkTranscriptCircuit{
		script: a.script, cfg: a.cfg, r: a.r, rollInAfterRound: a.rollInAfterRound, tpl: tpl,
		PrefixObs: a.PrefixObs, PrefixDigests: a.PrefixDigests, PrefixSamples: a.PrefixSamples,
		CommitRoots: a.CommitRoots, FinalPoly: a.FinalPoly, PowWitness: a.PowWitness, Queries: a.Queries,
	}
}

// countPrefixSamples returns how many sample_bb challenges the prefix pins
// (PermAlpha/PermBeta = 8, alpha = 4, zeta = 4, FRI batch alpha = 4, ... one lane
// each) — for the report of which challenges are re-derived + bound.
func countPrefixSamples(fx *shrinkRealFixture) int {
	n := 0
	for _, ev := range fx.PrefixEvents {
		if ev.Kind == "sample_bb" {
			n += len(ev.Values)
		}
	}
	return n
}

// TestEmittedChallengerFullTranscriptRederivesAndBinds is the full-scale closure.
// The Lean-emitted permutation drives the deployed MultiField adapter over the
// REAL apex-shrink transcript and:
//
//  1. ACCEPT: re-derives + binds every consumed challenge (all prefix samples =
//     PermAlpha/PermBeta/alpha/zeta/FRI-alpha; all R FRI betas; all query indices)
//     on the honest proof — the whole constraint system solves.
//  2. REJECT: a tampered commitment root moves the live-drawn betas, and a
//     tampered pinned prefix challenge breaks its squeeze assert — both UNSAT.
//     The challenges are bound to the transcript, not supplied freely.
//
// Native ground truth (the guard): the deployed multiFieldChallengerRef reproduces
// every FRI beta from the real transcript, so a circuit divergence would be a real
// permutation/adapter bug, not a missing binding.
func TestEmittedChallengerFullTranscriptRederivesAndBinds(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	tpl := loadPoseidon2TemplateT(t)
	field := ecc.BN254.ScalarField()

	// Native ground truth: the reference MultiField challenger reproduces every
	// beta from the real transcript (indices covered by the sibling
	// TestApexShrinkRealFixtureRefAcceptsAndPinsTranscript). A circuit rejection
	// below is therefore a real divergence, never a missing binding.
	ref := newMultiFieldChallengerRef()
	replayShrinkPrefixRef(t, ref, fx)
	for r := 0; r < fx.Fri.Rounds; r++ {
		ref.observeBn254Digest([]fr.Element{parseBn254Hex(t, fx.CommitRoots[r])})
		if beta := ref.sampleExt(); beta != bbExtRef(fx.ExpectedBetas[r]) {
			t.Fatalf("native ground truth: round %d beta %v != fixture %v", r, beta, fx.ExpectedBetas[r])
		}
	}

	nPrefix := countPrefixSamples(fx)
	t.Logf("re-deriving + binding IN-CIRCUIT via the Lean-emitted permutation: "+
		"%d prefix challenge lanes (PermAlpha/PermBeta/alpha/zeta/FRI-alpha), "+
		"%d FRI betas, %d query indices", nPrefix, fx.Fri.Rounds, len(fx.Queries))

	// (1) ACCEPT — the Lean-emitted permutation drives the real transcript.
	alloc := fromApexShrinkReal(allocApexShrinkRealCircuit(fx), tpl)
	assign := fromApexShrinkReal(assignApexShrinkRealCircuit(t, fx), tpl)
	if err := test.IsSolved(alloc, assign, field); err != nil {
		t.Fatalf("emitted-permutation transcript replay REJECTED the honest real proof "+
			"(the Lean-emitted permutation diverges from the deployed sponge?): %v", err)
	}
	t.Logf("(1) ACCEPT: every consumed challenge re-derived + bound in-circuit through the Lean-emitted permutation")

	// (2) REJECT — a tampered commitment root moves the live-drawn betas.
	one := fr.One()
	badRoot := fromApexShrinkReal(assignApexShrinkRealCircuit(t, fx), tpl)
	e := parseBn254Hex(t, fx.CommitRoots[0])
	e.Add(&e, &one)
	badRoot.CommitRoots[0] = frToBig(e)
	if err := test.IsSolved(alloc, badRoot, field); err == nil {
		t.Fatal("emitted-permutation replay ACCEPTED a tampered commitment root — " +
			"the live-drawn betas are not bound to the roots")
	}

	// (2) REJECT — a tampered pinned prefix challenge breaks its squeeze assert.
	badSample := fromApexShrinkReal(assignApexShrinkRealCircuit(t, fx), tpl)
	var first uint32
	for _, ev := range fx.PrefixEvents {
		if ev.Kind == "sample_bb" {
			first = ev.Values[0]
			break
		}
	}
	badSample.PrefixSamples[0] = bbAddRef(first, 1)
	if err := test.IsSolved(alloc, badSample, field); err == nil {
		t.Fatal("emitted-permutation replay ACCEPTED a tampered prefix challenge — the squeeze pin does not bind")
	}
	t.Logf("(2) REJECT: tampered commit root and tampered prefix challenge both UNSAT (non-vacuous bind)")
	t.Logf("VERDICT: the arbitrary-challenge hole is closed at FULL real-transcript scale in-circuit — " +
		"every consumed challenge is the sponge squeeze of the real roots, with the Lean-emitted " +
		"permutation as the crypto primitive; the hand-Go MultiField pack/split adapter is the named residual.")
}

// allocVerifierFullWithTranscript builds the MAIN emit-driven circuit WITH the
// emitted-permutation transcript re-derivation stage attached.
func allocVerifierFullWithTranscript(t *testing.T, fx *shrinkRealFixture, sym *SymbolicConstraints) *VerifierFullCircuit {
	t.Helper()
	a := allocApexShrinkRealCircuit(fx)
	loc, err := locateShrinkStarkPrefix(fx)
	if err != nil {
		t.Fatalf("anchored prefix location (for the block-3 challenge link offsets): %v", err)
	}
	shapes := shrinkShapesFromFixture(t, fx)
	meta := &shrinkTranscriptMeta{
		script: a.script, cfg: a.cfg, r: a.r, rollInAfterRound: a.rollInAfterRound,
		tpl:             loadPoseidon2TemplateT(t),
		permChSampleOff: loc.permChSampleOff,
		alphaSampleOff:  loc.alphaSampleOff,
		// THE ZETA BIND: the squeeze-asserted zeta the selectors are re-derived at,
		// and the observed streams the openings-at-zeta are equated against.
		zetaSampleOff: loc.zetaSampleOff,
		openedObsOff:  loc.openedObsOff,
		cumObsOff:     loc.cumObsOff,
		pubObsOff:     loc.pubObsOff,
		shapes:        shapes,
	}
	c, err := AllocVerifierFullCircuitWithTranscript(loadVerifierFullT(t), sym, meta,
		len(a.PrefixObs), len(a.PrefixDigests), len(a.PrefixSamples),
		fx.Fri.Rounds, len(fx.Queries), fx.Fri.LogGlobalMaxHeight)
	if err != nil {
		t.Fatalf("alloc emit circuit with transcript stage: %v", err)
	}
	return c
}

// assignVerifierFullWithTranscript fills the block witness bank (assignVerifierFull)
// and overlays the real transcript witness (the deployed apex-shrink assign path).
func assignVerifierFullWithTranscript(t *testing.T, fx *shrinkRealFixture, ex *shrinkStarkExtract, sym *SymbolicConstraints) *VerifierFullCircuit {
	t.Helper()
	c := assignVerifierFull(t, fx, ex, sym)
	ac := assignApexShrinkRealCircuit(t, fx)
	c.TxPrefixObs = ac.PrefixObs
	c.TxPrefixDig = ac.PrefixDigests
	c.TxPrefixSamp = ac.PrefixSamples
	c.TxCommitRoots = ac.CommitRoots
	c.TxPow = []frontend.Variable{ac.PowWitness}
	c.TxFinalPoly = ac.FinalPoly
	c.TxQueries = ac.Queries
	fillSelectorWitness(t, c)
	return c
}

// fillSelectorWitness threads the HONEST selector-derivation intermediate bits into
// the ζ-selector replay's witness bank (VerifierFullCircuit.SelectorWitness). The
// bind (bindBlockZeta -> replaySelectorsWitness) feeds these to the Lean-emitted
// selector template as its free internal witnesses; their honest values are the
// Lean-generated assignment selectorsAsg (SelectorEmit.lean), dumped var-index-ordered
// to emitted/selectors_witness_db{db}.json — committed at katZeta, which IS the real
// fixture ζ (SelectorEmit.lean §8), so the honest fixture's transcript-squeezed ζ
// gives a satisfiable emitted R1CS. The per-db layout mirrors the structural circuit's
// AllocVerifierFullCircuitWithTranscript so the assignment schema aligns.
func fillSelectorWitness(t *testing.T, c *VerifierFullCircuit) {
	t.Helper()
	plan, err := loadSelectorReplayPlan(c.vf)
	if err != nil {
		t.Fatalf("selector replay plan: %v", err)
	}
	sw := make([]frontend.Variable, plan.total)
	for db, e := range plan.entries {
		witPath := selectorWitnessPath(db)
		vals, verr := loadWitnessValues(witPath)
		if verr != nil {
			t.Fatalf("load %s: %v", witPath, verr)
		}
		if len(vals) != e.tpl.NumVars() {
			t.Fatalf("%s: %d witness values, template db%d has %d variables",
				witPath, len(vals), db, e.tpl.NumVars())
		}
		for k, idx := range e.witnessIdx {
			sw[e.offset+k] = vals[idx]
		}
	}
	c.SelectorWitness = sw
}

// selectorWitnessPath is the committed Lean-dumped honest assignment for the selector
// template at degree bits db (SelectorEmit.lean selectorsAsg, var-index-ordered).
func selectorWitnessPath(db int) string {
	return fmt.Sprintf("emitted/selectors_witness_db%d.json", db)
}

// TestEmittedVerifierFullTranscriptRederivesChallenges runs the MAIN emit-driven
// VerifierFullCircuit WITH the emitted-permutation transcript re-derivation stage
// on the real proof. The stage re-derives every challenge the verifier consumes
// through the Lean-emitted permutation and binds it to the commitment roots, so
// the whole descriptor circuit (structural blocks + the re-derivation) solves on
// the honest proof and rejects a tampered transcript root.
func TestEmittedVerifierFullTranscriptRederivesChallenges(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	field := ecc.BN254.ScalarField()

	alloc := allocVerifierFullWithTranscript(t, fx, sym)

	// ACCEPT: the emit circuit + the in-circuit re-derivation both clear the real proof.
	if err := test.IsSolved(alloc, assignVerifierFullWithTranscript(t, fx, ex, sym), field); err != nil {
		t.Fatalf("MAIN emit circuit WITH transcript stage REJECTED the honest proof: %v", err)
	}
	t.Logf("ACCEPT: VerifierFullCircuit re-derives + binds every consumed challenge in-circuit on the real proof")

	// REJECT: tamper a commitment root in the transcript feed — the re-derived
	// betas + the round-0 Merkle opening no longer match, so the stage is UNSAT.
	one := fr.One()
	bad := assignVerifierFullWithTranscript(t, fx, ex, sym)
	e := parseBn254Hex(t, fx.CommitRoots[0])
	e.Add(&e, &one)
	bad.TxCommitRoots[0] = frToBig(e)
	if err := test.IsSolved(alloc, bad, field); err == nil {
		t.Fatal("MAIN emit circuit ACCEPTED a tampered transcript commitment root — " +
			"the in-circuit challenge re-derivation does not bind")
	}
	t.Logf("REJECT: a tampered transcript commitment root is UNSAT — the challenges are bound to the roots")
}

// gadgetWitnessStartT returns the flat W offset at which `gadget`'s witness feed
// begins — the WitnessLen of every gadget the interpreter consumes before it (the
// same prefix-walk TestEmittedVerifierFullBlock3BindsRealProof uses to locate
// block 3).
func gadgetWitnessStartT(t *testing.T, vf *VerifierFull, sym *SymbolicConstraints, gadget string) int {
	t.Helper()
	prefix := &VerifierFull{Schema: vf.Schema, Shape: vf.Shape}
	for _, g := range vf.Gadgets {
		if g.Gadget == gadget {
			n, err := prefix.WitnessLen(sym)
			if err != nil {
				t.Fatalf("witness offset for %s: %v", gadget, err)
			}
			return n
		}
		prefix.Gadgets = append(prefix.Gadgets, g)
	}
	t.Fatalf("gadget %s not in descriptor", gadget)
	return 0
}

// TestEmittedVerifierFullTranscriptLinkIsLoadBearing is the mutation canary that
// proves the LOAD-BEARING LINK (bindBlockChallengesToTranscript) is non-vacuous —
// that it, and not some other constraint, is what forces the descriptor blocks to
// consume the transcript squeeze. The transcript-root tamper in the test above is
// rejected by the STAGE ITSELF (the live-drawn betas move), so it does not isolate
// the link. This test instead tampers a challenge the blocks consume as FREE
// WITNESS and shows the differential: with the link off the tamper is
// otherwise-valid (the block alone accepts it), with the link on it is UNSAT.
//
// COVERAGE — every challenge the descriptor blocks consume, one two-polarity
// canary each:
//
//   - block1-fold-beta (FRI round-0 fold beta): block 1's flat-bank operand `b` is
//     the inert transcript-link carrier — the fold ARITHMETIC is a self-contained
//     replay of the Lean-emitted friFoldData template over its OWN witness bank
//     (unfused from `b`), so a lone bumped `b` felt is otherwise-valid as-is;
//   - block4-query-index: block 4 (SampleBitsDecomposed) is a bare 31-bit range
//     check — any well-formed index passes as-is;
//   - block3-folding-alpha / block3-permAlpha / block3-permBeta: block 3 consumes
//     these as witness. They feed the alpha-folded constraint value, but that value
//     is no longer bound to a fresh `out` inside the block (the placeholder is gone;
//     the folded == quotient·Z_H identity lives in bindBlockZeta tooth 3 on the
//     transcript side). So a LONE bump is otherwise-valid stage OFF — the block
//     leaves folded unconstrained — and only the transcript LINK, asserting the
//     block's alpha/permAlpha/permBeta equal the squeeze, rejects it (stage ON). No
//     `out` recompute is needed to keep the tamper otherwise-valid.
//
// FINDINGS (named, not skipped) — challenge types NOT closed by the block link:
//
//   - zeta: block 3 never consumes zeta as a challenge witness; it consumes
//     Lean-emitted Lagrange selectors + openings AT zeta. The block CHALLENGE link
//     has no zeta slot to equate, so zeta is not closed by THAT link; it is closed
//     separately by bindBlockZeta (selector replay + openings/quotient bind).
//     Demonstrated below: a self-consistent wrong-zeta selector set is accepted with
//     the block link alone (and with bindBlockZeta disabled), and rejected only once
//     bindBlockZeta is on — the attribution the three-polarity zeta canary asserts;
//   - the FRI batch-combination alpha is a prefix sample bound by the stage
//     squeeze-assert but consumed by no block — outside the block link;
//   - only betas[0] and query-index[0] are block witnesses; the other 14 FRI betas
//     and 37 query indices are drawn LIVE in the transcript stage and bound there by
//     the fold-chain + Merkle-opening checks (the root-tamper test), not the block link.
func TestEmittedVerifierFullTranscriptLinkIsLoadBearing(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	field := ecc.BN254.ScalarField()
	vf := loadVerifierFullT(t)

	offAlloc, err := AllocVerifierFullCircuit(vf, sym) // stage OFF: no transcript link
	if err != nil {
		t.Fatalf("alloc stage-off circuit: %v", err)
	}
	onAlloc := allocVerifierFullWithTranscript(t, fx, sym) // stage ON: the link is present

	// --- offsets into the flat witness bank W ---
	// block 1's flat-bank record is now just its `b` fold-beta operand (the fold
	// ARITHMETIC moved to the FriFoldWitness replay bank); block 4's single
	// query-index witness starts the SampleBitsDecomposed record.
	betaStart := gadgetWitnessStartT(t, vf, sym, "FriFoldRowArity2")
	idxStart := gadgetWitnessStartT(t, vf, sym, "SampleBitsDecomposed")

	// block 3 per-instance start offsets + the challenge / selector slots (the
	// per-instance witness order VerifierFullCircuit.starkInstance consumes:
	// Trace/Pre/Perm rows, the WitnessChecks Challenges bus, PermValues, selectors,
	// PublicValues, alpha — symInstanceVars). There is NO `out` slot any more: the
	// folded value is bound to quotient(zeta)·Z_H by bindBlockZeta tooth 3, not to a
	// fresh output, so a block-3 challenge/selector/opening tamper needs no `out`
	// recompute to stay otherwise-valid — the block alone leaves folded unconstrained.
	block3Start := gadgetWitnessStartT(t, vf, sym, "BatchTableInstance")
	instStart := make([]int, len(ex.shapes))
	acc := block3Start
	for i := range ex.shapes {
		instStart[i] = acc
		acc += symInstanceVars(&sym.Instances[i])
	}
	// Instance 0 (const): the smallest instance carrying the LogUp bus (NL=1, NPV=0).
	const i0 = 0
	sh0 := ex.shapes[i0]
	chStart0 := instStart[i0] + 4*(2*sh0.Width+2*sh0.PreWidth+2*sh0.NumLookups)  // permAlpha lane 0
	selStart0 := instStart[i0] + 4*(2*sh0.Width+2*sh0.PreWidth+5*sh0.NumLookups) // isFirstRow lane 0
	alphaStart0 := instStart[i0] + 4*(2*sh0.Width+2*sh0.PreWidth+5*sh0.NumLookups+3) + sh0.NumPublicValues

	putExt := func(w []frontend.Variable, base int, e bbExtRef) {
		for k := 0; k < 4; k++ {
			w[base+k] = e[k]
		}
	}
	bumpLane := func(w []frontend.Variable, off int) {
		v, ok := w[off].(uint32)
		if !ok {
			t.Fatalf("witness slot %d is not a base-field felt (%T)", off, w[off])
		}
		w[off] = bbAddRef(v, 1)
	}

	// -----------------------------------------------------------------------
	// LINKED challenges — one two-polarity canary each (stage-OFF ACCEPT of the
	// otherwise-valid tamper, stage-ON REJECT of the SAME tamper).
	// -----------------------------------------------------------------------
	linked := []struct {
		name   string
		tamper func(w []frontend.Variable)
	}{
		{"block1-fold-beta", func(w []frontend.Variable) { bumpLane(w, betaStart) }},
		{"block4-query-index", func(w []frontend.Variable) { bumpLane(w, idxStart) }},
		{"block3-folding-alpha", func(w []frontend.Variable) {
			bumpLane(w, alphaStart0)
		}},
		{"block3-permAlpha", func(w []frontend.Variable) {
			for l := 0; l < sh0.NumLookups; l++ { // every lookup's permAlpha the link binds
				bumpLane(w, chStart0+8*l)
			}
		}},
		{"block3-permBeta", func(w []frontend.Variable) {
			for l := 0; l < sh0.NumLookups; l++ { // every lookup's permBeta the link binds
				bumpLane(w, chStart0+8*l+4)
			}
		}},
		// THE OPENINGS BIND (bindBlockZeta tooth 2 + tooth 3): bump the first felt of
		// instance i0's first opened trace value. Stage OFF that is a valid witness —
		// the block leaves folded unconstrained (no `out`, no in-circuit identity). Stage
		// ON the opened-value bind equates it with the transcript-observed opened stream
		// (tooth 2) and the tampered opening also diverges folded from quotient·Z_H
		// (tooth 3), so it is UNSAT.
		{"block3-opened-trace-at-zeta", func(w []frontend.Variable) {
			bumpLane(w, instStart[i0]) // TraceLocal[0] lane 0 — the first ext starkInstance draws
		}},
	}
	for _, tc := range linked {
		// (a) stage OFF — the tamper is otherwise valid: the block alone accepts it.
		off := assignVerifierFull(t, fx, ex, sym)
		tc.tamper(off.W)
		if err := test.IsSolved(offAlloc, off, field); err != nil {
			t.Fatalf("%s: stage-OFF circuit REJECTED the tamper — it is not otherwise-valid, so the "+
				"differential does not isolate the link: %v", tc.name, err)
		}
		// (b) stage ON — the SAME tamper: the link asserts the block challenge equals
		// the transcript squeeze, so a different value is UNSAT.
		on := assignVerifierFullWithTranscript(t, fx, ex, sym)
		tc.tamper(on.W)
		if err := test.IsSolved(onAlloc, on, field); err == nil {
			t.Fatalf("%s: stage-ON circuit ACCEPTED a challenge that differs from the transcript "+
				"squeeze — the LOAD-BEARING LINK is vacuous for this challenge", tc.name)
		}
		t.Logf("%s: stage-OFF ACCEPT, stage-ON REJECT on the same tamper — load-bearing", tc.name)
	}

	// -----------------------------------------------------------------------
	// FINDINGS — challenge types the block-challenge link does NOT close.
	// -----------------------------------------------------------------------

	// (F1) zeta — CLOSED (was: RESIDUAL, hole partly open). Block 3 consumes zeta
	// only INDIRECTLY, through the Lagrange selectors and the openings-at-zeta, so
	// the block-challenge link has no zeta slot to equate. bindBlockZeta closes it
	// by RE-DERIVATION instead: it re-derives the selectors in-circuit from the
	// squeeze-asserted zeta by REPLAYING the Lean-emitted selector template
	// (replaySelectorsWitness at each instance's degree_bits) and asserts the block's
	// supplied selectors equal the replayed outputs.
	//
	// The canary below is the exact favorable-zeta forgery: pick a zeta the
	// transcript never sampled and supply the matching selector triple. Stage OFF the
	// block accepts it (the selectors feed only the now-unconstrained folded value —
	// no `out`, no local identity); stage ON it must be UNSAT (tooth 1 asserts the
	// block's selectors equal the Lean-template replay at the squeeze-asserted zeta,
	// and tooth 3's quotient identity diverges under the wrong zH). Both polarities
	// are ASSERTED, so a regression that drops the bind fails here.
	zetaTamper := func(w []frontend.Variable) {
		badZeta := bbExtRef{bbAddRef(ex.ch.zeta[0], 1), ex.ch.zeta[1], ex.ch.zeta[2], ex.ch.zeta[3]}
		sel, serr := computeStarkSelectorsRef(badZeta, sh0.DegreeBits)
		if serr != nil {
			t.Fatalf("zeta finding: selectors: %v", serr)
		}
		putExt(w, selStart0, sel.isFirstRow)
		putExt(w, selStart0+4, sel.isLastRow)
		putExt(w, selStart0+8, sel.isTransition)
	}
	offZ := assignVerifierFull(t, fx, ex, sym)
	zetaTamper(offZ.W)
	if err := test.IsSolved(offAlloc, offZ, field); err != nil {
		t.Fatalf("zeta finding: stage-OFF rejected a self-consistent wrong-zeta selector set "+
			"(the demonstration is malformed, not a real result): %v", err)
	}
	// ATTRIBUTION polarity. `offAlloc` carries no transcript stage AT ALL, so the
	// stage-OFF/stage-ON pair alone only shows "some constraint in the stage" rejects
	// the tamper — it does not pin WHICH. This third polarity runs the SAME tamper on
	// the SAME stage-ON circuit with only bindBlockZeta disabled (zetaSampleOff < 0,
	// the early return), and requires it to ACCEPT. That isolates the rejection to
	// bindBlockZeta specifically: with every other stage constraint present and only
	// the zeta bind removed, the wrong-zeta selector forgery goes through again.
	bindOffAlloc := allocVerifierFullWithTranscript(t, fx, sym)
	bindOffAlloc.txMeta.zetaSampleOff = -1
	bindOffZ := assignVerifierFullWithTranscript(t, fx, ex, sym)
	zetaTamper(bindOffZ.W)
	if err := test.IsSolved(bindOffAlloc, bindOffZ, field); err != nil {
		t.Fatalf("zeta: stage-ON with the zeta bind DISABLED rejected the wrong-zeta selector set — "+
			"the rejection below is therefore NOT attributable to bindBlockZeta, and this canary "+
			"does not prove the zeta forgery vector is what closed it: %v", err)
	}
	onZ := assignVerifierFullWithTranscript(t, fx, ex, sym)
	zetaTamper(onZ.W)
	if err := test.IsSolved(onAlloc, onZ, field); err == nil {
		t.Fatal("zeta: stage-ON ACCEPTED a self-consistent wrong-zeta selector/out set — " +
			"bindBlockZeta does not bind block 3's selectors to the transcript-squeezed zeta")
	}
	// The ACCEPT half of the honest path is asserted by
	// TestEmittedVerifierFullTranscriptRederivesChallenges, which solves this same
	// stage-ON circuit (zeta bind ON) on the untampered real proof — without it, a
	// bind that rejected EVERYTHING would pass the reject polarity above vacuously.
	t.Logf("zeta: CLOSED (stage-OFF ACCEPT / stage-ON+bind-OFF ACCEPT / stage-ON+bind-ON REJECT) — " +
		"the rejection is attributable to bindBlockZeta alone: the selectors are forced to be the " +
		"Lean-emitted selector template's replayed derivation at the squeeze-asserted zeta, so a " +
		"selector set at any other point is UNSAT; the openings-at-zeta are additionally equated " +
		"against the transcript-observed opened stream (bindBlockZeta tooth 2).")

	// (F2) FRI betas / query indices: the descriptor consumes a SINGLE representative
	// of each — one fold-beta operand and one query-index sample — so only betas[0]
	// and query-index[0] are block witnesses (canaried load-bearing above). Pin the
	// single-representative shape so a descriptor change that widens it is caught here.
	if g, ok := vf.gadget("SampleBitsDecomposed"); !ok || g.Count != 1 {
		t.Fatalf("FINDING (query indices): expected exactly ONE block-4 query-index witness "+
			"(SampleBitsDecomposed count 1), got %+v — the single-representative finding is stale", g)
	}
	t.Logf("FINDING FRI betas / query indices: only betas[0] (block 1) and query-index[0] (block 4) are " +
		"block witnesses (canaried above); the other 14 betas + 37 indices are drawn live in the transcript " +
		"stage and bound there by the fold-chain + Merkle-opening checks (root-tamper test), not the block link.")

	// (F3) the FRI batch-combination alpha is a prefix sample squeeze-asserted by the
	// stage but consumed by no block — transcript-bound at the stage level, not by the
	// block-challenge link.
	t.Logf("FINDING FRI batch-alpha: prefix sample bound by the stage squeeze-assert; no descriptor " +
		"block consumes it, so it is outside the block-challenge link (stage-bound, not block-linked).")

	t.Logf("VERDICT: block-linked challenges proven load-bearing (stage-OFF ACCEPT / stage-ON REJECT): " +
		"block1-fold-beta, block4-query-index, block3-folding-alpha, block3-permAlpha, block3-permBeta, " +
		"and zeta (bound by RE-DERIVATION, not equality: the selectors ARE the derivation at the squeeze). " +
		"Residual (not block-linked): FRI-batch-alpha (prefix sample, no block witness) and the " +
		"non-representative FRI betas / query indices (stage-bound). Residual on zeta, at current " +
		"resolution: the openings are bound to the TRANSCRIPT, not proven to BE the committed " +
		"polynomials' evaluations at zeta — that is the DEEP/PCS reduction, still seam #2.")
}

// TestEmittedVerifierFullQuotientIdentityIsLoadBearing is the mutation canary that
// proves bindBlockZeta TOOTH 3 — the DEEP quotient identity folded ==
// quotient(zeta)·Z_H(zeta) (emitted_verifier_full.go:1190) — is LOAD-BEARING, i.e.
// that it genuinely CLOSED the former vacuous placeholder. The placeholder bound
// folded to a fresh `out` witness (folded == out), which any prover satisfied by
// setting out := folded — the recomposed quotient never entered the circuit, so the
// constraint algebra was never forced to match the committed quotient. Tooth 3 now
// asserts folded equals quotient(zeta)·Z_H(zeta), with quotient(zeta) recomposed
// in-circuit from the transcript-observed opened chunks. This canary shows that
// equality is not vacuous: a folded value that does NOT equal the recomposed
// quotient·Z_H is UNSAT.
//
// THE ISOLATION SUBTLETY (why a naive quotient-CHUNK tamper is NOT the proof): the
// quotient CHUNKS tooth 3 recomposes are read from the transcript-OBSERVED opened
// stream (event n-2, observed BEFORE the FRI batch-alpha squeeze at n-1). So a
// tampered chunk moves the sponge and is rejected by the PREFIX SQUEEZE regardless of
// tooth 3 — over-determined, it re-proves the transcript bind, not the identity.
// (Measured below: bind-ON and bind-OFF both reject a chunk tamper at
// rederiveShrinkChallenges' squeeze, not at the tooth-3 assert.) To isolate tooth 3 we
// free the FOLDED side instead: the isolateQuotientIdentity structural probe (the
// deployed lane leaves it false, like zetaSampleOff<0's cost differential) runs tooth 1
// (the selector re-derivation, needed for Z_H) and tooth 3 with tooth 2 (the
// opened-value equality binds) OFF. With the block-3 trace witness no longer pinned to
// the transcript, the ONLY remaining constraint on folded is the quotient identity, so
// a folded-side tamper is attributable to tooth 3 alone.
//
// NATIVE GROUND TRUTH: on the honest proof folded == quotient(zeta)·Z_H(zeta) for
// instance 0 (the deployed VerifyShrinkStarkAlgebra identity), and bumping instance 0's
// first opened trace value moves the symbolic-folded value (evalSymbolicFoldedRef) away
// from that honest quotient·Z_H — so the tamper genuinely violates the identity, not
// some incidental constraint. A circuit rejection is therefore the identity firing.
//
// THREE-POLARITY ISOLATION (tooth 3):
//
//  1. ISOLATE-HONEST (floor): tooth3 ON / tooth2 OFF, honest proof → ACCEPT — so a
//     bind that rejected everything cannot pass the reject polarity vacuously;
//  2. ISOLATE-TAMPER: tooth3 ON / tooth2 OFF, folded-side tamper → REJECT, at the
//     quotient-identity assert (emitted_verifier_full.go:1190) — the wrong folded is
//     UNSAT with tooth 3 as the sole remaining constraint on folded;
//  3. ATTRIBUTION: tooth3 OFF (shapes=nil ⇒ tooth 2+3 off, tooth 1 stays on), the SAME
//     folded-side tamper → ACCEPT — with the identity removed, folded is free again
//     (exactly the vacuous placeholder behaviour), so the reject in (2) IS tooth 3.
//
// DEFENSE IN DEPTH: a quotient-CHUNK tamper in the transcript-observed opened stream is
// ALSO rejected (bind-ON) — but by the prefix squeeze (over-determined), demonstrated
// below to reject even bind-OFF; it is reported as defense in depth, not the isolation.
//
// RESIDUAL (named, NOT closed): tooth 3 binds folded to the quotient recomposed from
// the transcript-observed chunks; it does not prove those chunks ARE the committed
// polynomials' low-degree evaluations at zeta. That is the FRI/PCS low-degree
// (openings = evaluations) floor — seam #2 — still the named crypto assumption.
func TestEmittedVerifierFullQuotientIdentityIsLoadBearing(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	field := ecc.BN254.ScalarField()
	vf := loadVerifierFullT(t)

	// --- NATIVE GROUND TRUTH: the honest identity holds, and the folded-side tamper
	// moves folded off quotient·Z_H (so the circuit reject below IS the identity). ---
	spans, _ := buildStarkOpenedSpans(ex.shapes)
	const i0 = 0
	sp0, sh0, inst0 := spans[i0], ex.shapes[i0], &sym.Instances[i0]
	sel0, err := computeStarkSelectorsRef(ex.ch.zeta, sh0.DegreeBits)
	if err != nil {
		t.Fatalf("instance %d selectors: %v", i0, err)
	}
	slice := func(s efSpan) []bbExtRef { return ex.openedEF[s.off : s.off+s.len] }
	chunks := make([][4]bbExtRef, len(sp0.quotientChunks))
	for c, qs := range sp0.quotientChunks {
		copy(chunks[c][:], slice(qs))
	}
	rhs := bbExtMulRef(recomposeQuotientRef(sel0.zetaPow2Db, chunks,
		shrinkQuotientDomainConsts(sh0.DegreeBits, sh0.NumQuotientChunks)), sel0.zH)
	foldHonest, err := evalSymbolicFoldedRef(inst0,
		shrinkSymInputsRef(sh0, sp0, slice, ex.cumSums, ex.pubVals[i0], ex.ch, sel0), ex.ch.alpha)
	if err != nil {
		t.Fatalf("instance %d host folded: %v", i0, err)
	}
	if foldHonest != rhs {
		t.Fatalf("native ground truth: honest folded %v != quotient·Z_H %v for instance %d — "+
			"the identity does not hold on the real proof (extraction bug, not a bind result)", foldHonest, rhs, i0)
	}
	saved := ex.openedEF[sp0.traceLocal.off][0]
	ex.openedEF[sp0.traceLocal.off][0] = bbAddRef(saved, 1)
	foldTamper, err := evalSymbolicFoldedRef(inst0,
		shrinkSymInputsRef(sh0, sp0, slice, ex.cumSums, ex.pubVals[i0], ex.ch, sel0), ex.ch.alpha)
	ex.openedEF[sp0.traceLocal.off][0] = saved
	if err != nil {
		t.Fatalf("instance %d tampered folded: %v", i0, err)
	}
	if foldTamper == rhs {
		t.Fatalf("native ground truth: bumping the first opened trace value left folded == quotient·Z_H "+
			"(instance %d column 0 is unconstrained) — pick a folded-moving tamper, the isolation is malformed", i0)
	}
	t.Logf("native: honest folded == quotient·Z_H; folded-side tamper moves folded off it (%v -> %v) — "+
		"the reject below is the identity firing", foldHonest, foldTamper)

	// The folded-side tamper target in the flat bank: instance 0's TraceLocal[0] lane 0
	// (the first ext starkInstance draws for block 3) — a folded INPUT, not a quotient chunk.
	block3Start := gadgetWitnessStartT(t, vf, sym, "BatchTableInstance")
	foldedTamper := func(w []frontend.Variable) {
		v, ok := w[block3Start].(uint32)
		if !ok {
			t.Fatalf("block-3 slot %d is not a base-field felt (%T)", block3Start, w[block3Start])
		}
		w[block3Start] = bbAddRef(v, 1)
	}

	// (1) ISOLATE-HONEST floor: tooth 3 ON, tooth 2 OFF — the honest proof still solves.
	isoAlloc := allocVerifierFullWithTranscript(t, fx, sym)
	isoAlloc.txMeta.isolateQuotientIdentity = true
	if err := test.IsSolved(isoAlloc, assignVerifierFullWithTranscript(t, fx, ex, sym), field); err != nil {
		t.Fatalf("ISOLATE-HONEST: tooth3-on/tooth2-off circuit REJECTED the honest proof — the quotient "+
			"identity does not hold in isolation, so the reject polarity would be vacuous: %v", err)
	}
	t.Logf("(1) ISOLATE-HONEST: tooth3 ON / tooth2 OFF accepts the honest proof (identity holds in isolation)")

	// (2) ISOLATE-TAMPER: same circuit, folded-side tamper → UNSAT at the quotient identity.
	isoBad := assignVerifierFullWithTranscript(t, fx, ex, sym)
	foldedTamper(isoBad.W)
	if err := test.IsSolved(isoAlloc, isoBad, field); err == nil {
		t.Fatal("ISOLATE-TAMPER: tooth3-on/tooth2-off circuit ACCEPTED a folded value that does not equal " +
			"quotient(zeta)·Z_H(zeta) — TOOTH 3 IS VACUOUS (the fresh-out placeholder is not closed)")
	}
	t.Logf("(2) ISOLATE-TAMPER: a folded != quotient·Z_H is UNSAT with tooth 3 the sole constraint on folded")

	// (3) ATTRIBUTION: tooth 3 OFF (shapes=nil) — the SAME folded tamper is now ACCEPTED,
	// because folded is free again. So the reject in (2) is attributable to tooth 3 alone.
	offAlloc := allocVerifierFullWithTranscript(t, fx, sym)
	offAlloc.txMeta.shapes = nil // tooth 2 + tooth 3 off; tooth 1 (selectors) unaffected
	offBad := assignVerifierFullWithTranscript(t, fx, ex, sym)
	foldedTamper(offBad.W)
	if err := test.IsSolved(offAlloc, offBad, field); err != nil {
		t.Fatalf("ATTRIBUTION: with tooth 3 OFF the folded-side tamper was still REJECTED — the reject in "+
			"(2) is NOT attributable to tooth 3 (something else constrains folded): %v", err)
	}
	t.Logf("(3) ATTRIBUTION: with tooth 3 OFF the same folded tamper is ACCEPTED — the reject IS tooth 3 " +
		"(quotient identity, emitted_verifier_full.go:1190), not the transcript or another block")

	// --- DEFENSE IN DEPTH: a quotient-CHUNK tamper in the transcript-observed opened
	// stream. Rejected bind-ON — but ALSO bind-OFF (the transcript prefix squeeze catches
	// it), so this is over-determined and does NOT isolate tooth 3; recorded as defense in
	// depth, and as the reason the folded-side isolation above is the actual identity proof. ---
	chunkFelt := ex.loc.openedObsOff + 4*sp0.quotientChunks[0].off // first limb of instance 0's chunk 0
	onAlloc := allocVerifierFullWithTranscript(t, fx, sym)
	onChunk := assignVerifierFullWithTranscript(t, fx, ex, sym)
	onChunk.TxPrefixObs[chunkFelt] = bbAddRef(ex.openedEF[sp0.quotientChunks[0].off][0], 1)
	if err := test.IsSolved(onAlloc, onChunk, field); err == nil {
		t.Fatal("DEFENSE-IN-DEPTH: a tampered quotient chunk in the observed opened stream was ACCEPTED bind-ON")
	}
	bindOffAlloc := allocVerifierFullWithTranscript(t, fx, sym)
	bindOffAlloc.txMeta.zetaSampleOff = -1 // whole zeta bind (teeth 1/2/3) OFF
	offChunk := assignVerifierFullWithTranscript(t, fx, ex, sym)
	offChunk.TxPrefixObs[chunkFelt] = bbAddRef(ex.openedEF[sp0.quotientChunks[0].off][0], 1)
	if err := test.IsSolved(bindOffAlloc, offChunk, field); err == nil {
		t.Fatal("DEFENSE-IN-DEPTH: a tampered quotient chunk was ACCEPTED with the whole zeta bind OFF — the " +
			"transcript prefix squeeze does not absorb the opened chunks (the over-determination claim is false)")
	}
	t.Logf("DEFENSE IN DEPTH: a quotient-chunk tamper is rejected bind-ON AND bind-OFF — over-determined by " +
		"the transcript prefix squeeze (the chunks are transcript-observed), so it is NOT the identity proof.")

	t.Logf("VERDICT: bindBlockZeta tooth 3 (folded == quotient(zeta)·Z_H(zeta)) is LOAD-BEARING — a wrong " +
		"folded is UNSAT with the identity ON and SAT with it OFF (tooth 3 alone, isolated from tooth 2 and the " +
		"transcript). The vacuous fresh-out placeholder is CLOSED. RESIDUAL (named, open): the opened chunks are " +
		"bound to the transcript, NOT proven to be the committed polynomials' low-degree evaluations at zeta — " +
		"the FRI/PCS openings=evaluations floor (seam #2), still the named crypto assumption.")
}
