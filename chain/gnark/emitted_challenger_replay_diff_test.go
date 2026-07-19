// THE CHALLENGER-REPLAY DIFFERENTIAL GATE.
//
// This drives the Lean-emitted Fiat-Shamir duplex template
// (ChallengerReplayEmit.lean `emitChallengerReplay`, committed at
// emitted/challenger_replay_template.json — the `challenger_bn254_duplex_replay_v1`
// gadget) through the extended replayer (ReplayClosed, emitted_gadget_replay.go)
// against the REAL apex-shrink fixture, so the "does the emit re-derive the
// challenges in-circuit and bind them, and does a tampered challenge reject" gate
// is RUNNABLE on real proof data — not a fixture-pinned feed.
//
// WHAT THIS TEMPLATE IS (said at the correct resolution). The Lean template is ONE
// plain BN254 duplexing: a FRESH sponge state [a0, a1, 0] (capacity the constant
// 0), one width-3 Poseidon2Bn254 permutation, squeeze the two rate lanes in draw
// order (lane 1 then lane 0). Its refinement (`challengerReplay_refines`) proves
// the emitted R1CS accepts a claimed challenge pair IFF it equals that squeeze —
// the Fiat-Shamir binding property. So bound against real commitment roots it is a
// genuine in-circuit re-derivation of a challenge FROM those roots, with real
// teeth (a tampered challenge or a tampered root is UNSAT).
//
// WHAT THIS TEMPLATE IS NOT (the residual that keeps it out of blocks 1/3/4). The
// DEPLOYED shrink transcript (settlement_circuit.go + multifield_challenger.go) is
// the MultiField32Challenger<BabyBear, Bn254>: every consumed challenge (the FRI
// betas, zeta, the constraint-folding alpha, permAlpha/permBeta, the query index)
// is squeezed through the BabyBear<->BN254 pack/split adapter over a CHAINED sponge
// — a nonzero carried capacity, a length TAG added to the capacity on absorb, a
// single-word (root) absorb, and a 7-limb base-p SPLIT of each squeezed BN254 cell
// (popped from the end). The plain one-duplexing template models NONE of that: it
// is the sponge CORE those layers drive (ChallengerReplayEmit.lean §residual (3)).
// This test MEASURES that gap on the real proof: the plain-duplex squeeze of the
// real roots is provably NOT the fixture's real beta, while the native MultiField
// reference reproduces the fixture beta exactly. So the plain template cannot feed
// blocks 1/3/4, and their challenge inputs remain fixture-pinned this cycle.
package friverifier

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

const challengerReplayTemplatePath = "emitted/challenger_replay_template.json"

// duplexDraw2Ref is the native twin of the Lean `duplexDraw2` (ChallengerReplayEmit
// §1): a fresh sponge [a0, a1, 0], one Poseidon2Bn254 permutation, squeeze rate
// lane 1 (first draw) then lane 0 (second draw). This is exactly what a fresh
// native ChallengerBn254 (challenger_bn254.go) draws after absorbing [a0, a1].
func duplexDraw2Ref(a0, a1 fr.Element) (fr.Element, fr.Element) {
	var zero fr.Element
	state := [bn254P3Width]fr.Element{a0, a1, zero}
	poseidon2Bn254Ref(&state)
	return state[1], state[0]
}

// challengerReplayBindCircuit binds the Lean-emitted duplex template's four
// boundary variables by index (absorb0, absorb1, challenge0, challenge1) and drives
// the whole closed circuit through ReplayClosed: the permutation define-chain is
// solved, and the two squeeze pins become KEPT equality asserts (rate lane 1 ==
// challenge0, rate lane 0 == challenge1). A claimed challenge that is not the true
// squeeze of the absorbed pair is UNSAT.
type challengerReplayBindCircuit struct {
	Absorb0, Absorb1 frontend.Variable
	Challenge0       frontend.Variable
	Challenge1       frontend.Variable

	tpl *Template
}

func (c *challengerReplayBindCircuit) Define(api frontend.API) error {
	return ReplayClosed(api, *c.tpl, map[int]frontend.Variable{
		0: c.Absorb0, 1: c.Absorb1, 2: c.Challenge0, 3: c.Challenge1,
	})
}

// TestEmittedChallengerReplayBindsRealRootsDiff is the challenger-replay half of
// the emit-driven differential gate. It absorbs the REAL fixture commitment roots
// into the Lean-emitted duplex template via ReplayClosed and re-derives the two
// challenges in-circuit, then checks:
//
//  1. ACCEPT: the honest native squeeze (duplexDraw2Ref of the real roots) SOLVES
//     the closed template — the emit re-derives a challenge in-circuit from the real
//     transcript roots and binds it.
//  2. REJECT: a tampered challenge, and a tampered absorbed root, are both UNSAT —
//     the squeeze pin genuinely binds the challenge to the roots (the soundness gain,
//     non-vacuous: a prover cannot supply an arbitrary challenge for given roots).
//  3. RESIDUAL: the plain-duplex squeeze is NOT the deployed shrink transcript's
//     real challenge. The native MultiField challenger reference reproduces the
//     fixture beta exactly (ground truth); the plain-duplex squeeze of the same
//     roots does not — because the real derivation is a MultiField pack/split/tag
//     squeeze over a chained sponge, not a fresh capacity-0 plain duplexing. So this
//     bind does NOT close the arbitrary-challenge hole for the challenges blocks
//     1/3/4 consume; those stay fixture-pinned pending a Lean-emitted MultiField
//     adapter.
func TestEmittedChallengerReplayBindsRealRootsDiff(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	tpl, err := LoadTemplate(challengerReplayTemplatePath)
	if err != nil {
		t.Fatalf("load %s: %v", challengerReplayTemplatePath, err)
	}
	if len(tpl.PublicInputs) != 4 ||
		tpl.PublicInputs[0].Var != 0 || tpl.PublicInputs[1].Var != 1 ||
		tpl.PublicInputs[2].Var != 2 || tpl.PublicInputs[3].Var != 3 {
		t.Fatalf("unexpected challenger template boundary %v (want absorb0,absorb1,challenge0,challenge1 at vars 0..3)",
			tpl.PublicInputs)
	}
	field := ecc.BN254.ScalarField()

	// The REAL commitment roots (BN254 Merkle roots the FRI commit phase opens
	// against — the same roots settlement_circuit.go observes into the transcript
	// before drawing each fold beta).
	root0 := parseBn254Hex(t, fx.CommitRoots[0])
	root1 := parseBn254Hex(t, fx.CommitRoots[1])

	// Native self-check (the guard, mirroring the other assign self-checks in this
	// package): the native duplexDraw2 of the real roots is what the circuit must
	// re-derive, so if the closed template does not solve on these values the
	// divergence is a real one, not a wiring bug.
	c0, c1 := duplexDraw2Ref(root0, root1)

	// (1) ACCEPT — the emit re-derives the plain-duplex challenge in-circuit from
	// the real roots and binds it.
	honest := &challengerReplayBindCircuit{
		tpl:     tpl,
		Absorb0: frToBig(root0), Absorb1: frToBig(root1),
		Challenge0: frToBig(c0), Challenge1: frToBig(c1),
	}
	if err := test.IsSolved(&challengerReplayBindCircuit{tpl: tpl}, honest, field); err != nil {
		t.Fatalf("ReplayClosed REJECTED the honest squeeze of the real roots "+
			"(emitted duplex template diverges from the native reference?): %v", err)
	}
	t.Logf("(1) ACCEPT: emit re-derives + binds the plain-duplex challenge of the real roots")

	// (2) REJECT — a tampered challenge does not equal the squeeze.
	badChal := &challengerReplayBindCircuit{
		tpl:     tpl,
		Absorb0: frToBig(root0), Absorb1: frToBig(root1),
		Challenge0: new(big.Int).Add(frToBig(c0), big.NewInt(1)), Challenge1: frToBig(c1),
	}
	if err := test.IsSolved(&challengerReplayBindCircuit{tpl: tpl}, badChal, field); err == nil {
		t.Fatal("ReplayClosed ACCEPTED a tampered challenge (c0+1) — the squeeze pin does not bind")
	}
	// A tampered absorbed root moves the squeeze, so the honest challenge no longer
	// matches — the challenge is bound to the roots.
	badRoot := &challengerReplayBindCircuit{
		tpl:     tpl,
		Absorb0: new(big.Int).Add(frToBig(root0), big.NewInt(1)), Absorb1: frToBig(root1),
		Challenge0: frToBig(c0), Challenge1: frToBig(c1),
	}
	if err := test.IsSolved(&challengerReplayBindCircuit{tpl: tpl}, badRoot, field); err == nil {
		t.Fatal("ReplayClosed ACCEPTED a tampered absorbed root — the challenge is not bound to the roots")
	}
	t.Logf("(2) REJECT: tampered challenge and tampered absorbed root both UNSAT (non-vacuous bind)")

	// (3) RESIDUAL — the plain-duplex squeeze is NOT the deployed shrink challenge.
	// Ground truth: the native MultiField challenger reference reproduces the
	// fixture beta[0] exactly.
	ref := newMultiFieldChallengerRef()
	replayShrinkPrefixRef(t, ref, fx)
	ref.observeBn254Digest([]fr.Element{root0})
	realBeta0 := ref.sampleExt()
	if realBeta0 != bbExtRef(fx.ExpectedBetas[0]) {
		t.Fatalf("native MultiField beta[0] %v != fixture %v — extraction bug", realBeta0, fx.ExpectedBetas[0])
	}
	// The plain-duplex squeeze of the same root, split the MultiField way, does not
	// reproduce that beta: the real transcript carries a nonzero capacity, a length
	// tag, a single-word absorb, and a 7-limb base-p split, none of which the plain
	// fresh-state capacity-0 template models.
	plainSplit := mfRefSplitToFieldOrderLimbs(c0)
	var plainBeta bbExtRef
	copy(plainBeta[:], plainSplit[:4])
	if plainBeta == realBeta0 {
		t.Fatal("UNEXPECTED: the plain-duplex squeeze reproduced the MultiField beta — " +
			"the residual would be closed; re-verify the transcript model")
	}
	t.Logf("(3) RESIDUAL: native MultiField beta[0]=%v reproduces the fixture; "+
		"plain-duplex(split)=%v does NOT — the MultiField pack/split/tag boundary is the gap",
		realBeta0, plainBeta)
	t.Logf("VERDICT: challenger-replay MECHANISM binds the sponge core on the real roots " +
		"(accept + tamper-reject); the deployed shrink challenges (betas/zeta/alpha/query) remain " +
		"fixture-pinned pending a Lean-emitted MultiField adapter over this core.")
}
