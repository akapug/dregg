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
	})
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
	meta := &shrinkTranscriptMeta{
		script: a.script, cfg: a.cfg, r: a.r, rollInAfterRound: a.rollInAfterRound,
		tpl:             loadPoseidon2TemplateT(t),
		permChSampleOff: loc.permChSampleOff,
		alphaSampleOff:  loc.alphaSampleOff,
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
	return c
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
// WITNESS, choosing two blocks whose own constraints DO NOT pin it:
//
//   - block 1 (FriFoldRowArity2) is an inert cost-model — the fold-beta operand `b`
//     only feeds an ExtMul chain closed by ExtAssertIsEqual(x, x) (trivially true),
//     so `b` is unconstrained by the block;
//   - block 4 (SampleBitsDecomposed) is a bare 31-bit range check — any well-formed
//     index passes.
//
// So a wrong-but-well-formed value for either is ACCEPTED with the stage OFF, and
// the ONLY thing that can reject it with the stage ON is the transcript link. The
// differential (stage-OFF ACCEPT, stage-ON REJECT on the SAME tamper) is the proof
// the link binds each block challenge to the sponge squeeze. (Block 3's
// alpha/permAlpha/permBeta are bound by the same mechanism but cannot be isolated
// this cleanly — they also feed the DAG folded == out identity, which is exactly
// the forgery the link prevents.)
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

	// betaStart: block 1's `b` operand follows its `x` operand (4 ext lanes).
	betaStart := gadgetWitnessStartT(t, vf, sym, "FriFoldRowArity2") + 4
	idxStart := gadgetWitnessStartT(t, vf, sym, "SampleBitsDecomposed")

	for _, tc := range []struct {
		name   string
		offset int
	}{
		{"block1-fold-beta", betaStart},
		{"block4-query-index", idxStart},
	} {
		// (a) stage OFF — the tamper is otherwise valid: the block alone accepts it.
		off := assignVerifierFull(t, fx, ex, sym)
		orig, ok := off.W[tc.offset].(uint32)
		if !ok {
			t.Fatalf("%s: witness slot %d is not a base-field felt (%T)", tc.name, tc.offset, off.W[tc.offset])
		}
		off.W[tc.offset] = bbAddRef(orig, 1)
		if err := test.IsSolved(offAlloc, off, field); err != nil {
			t.Fatalf("%s: stage-OFF circuit REJECTED the wrong challenge — the tamper is not "+
				"otherwise-valid, so the differential does not isolate the link: %v", tc.name, err)
		}

		// (b) stage ON — the SAME tamper: the link asserts the block challenge equals
		// the transcript squeeze, so a different value is UNSAT.
		on := assignVerifierFullWithTranscript(t, fx, ex, sym)
		on.W[tc.offset] = bbAddRef(orig, 1)
		if err := test.IsSolved(onAlloc, on, field); err == nil {
			t.Fatalf("%s: stage-ON circuit ACCEPTED a block challenge that differs from the "+
				"transcript squeeze — the LOAD-BEARING LINK is vacuous", tc.name)
		}
		t.Logf("%s: stage-OFF ACCEPT, stage-ON REJECT on the same tamper — the transcript link is load-bearing", tc.name)
	}
}
