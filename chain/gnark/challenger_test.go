// Tests for the Fiat-Shamir DuplexChallenger: the native-Go reference
// (challenger_ref.go) and the circuit gadget (challenger.go), cross-checked
// against each other via the gnark test engine and against the Rust-emitted
// fixtures/transcript_w16.json. These COMPLEMENT transcript_fixture_test.go
// (which pins the raw sponge protocol); here we drive the actual Challenger
// gadget API (Observe/Sample/SampleExt/SampleBits) end to end.
package friverifier

import (
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// --- gadget-level fixture fidelity: the real Challenger API vs the Rust oracle ---

// challengerFixtureCircuit replays the fixture protocol through the Challenger
// gadget (16 Observes at rate 8, then 8 Samples) and asserts every squeezed
// challenge and the full final sponge state equal the Rust-emitted values.
type challengerFixtureCircuit struct {
	Absorbed   [16]frontend.Variable
	Challenges [8]frontend.Variable
	FinalState [16]frontend.Variable
}

func (c *challengerFixtureCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	ch := NewChallenger(bb)
	ch.ObserveSlice(c.Absorbed[:])
	for i := 0; i < 8; i++ {
		api.AssertIsEqual(ch.Sample(), c.Challenges[i])
	}
	// After 16 observes (two duplexings) and 8 samples (which drain the output
	// buffer without a further permutation), the sponge state is the final
	// state — capacity lanes included.
	for i := range ch.state {
		api.AssertIsEqual(ch.state[i], c.FinalState[i])
	}
	return nil
}

func challengerFixtureWitness(t *testing.T, fx *transcriptFixture) *challengerFixtureCircuit {
	t.Helper()
	w := &challengerFixtureCircuit{}
	for i, v := range parseCanonicalSlice(t, fx.Absorbed) {
		w.Absorbed[i] = v
	}
	for i, v := range parseCanonicalSlice(t, fx.Challenges) {
		w.Challenges[i] = v
	}
	for i, v := range parseCanonicalSlice(t, fx.FinalSpongeState) {
		w.FinalState[i] = v
	}
	return w
}

// The gadget, driven through its public Observe/Sample API, must reproduce the
// Rust challenger verbatim.
func TestChallengerGadgetMatchesFixture(t *testing.T) {
	fx := loadTranscriptFixture(t)
	w := challengerFixtureWitness(t, fx)
	if err := test.IsSolved(&challengerFixtureCircuit{}, w, ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("Challenger gadget diverges from the Rust challenger: %v", err)
	}
}

// REJECT polarity: a tampered challenge lane must fail the gadget replay.
func TestChallengerGadgetRejectsTamperedChallenge(t *testing.T) {
	fx := loadTranscriptFixture(t)
	w := challengerFixtureWitness(t, fx)
	w.Challenges[3] = bbAddRef(parseCanonical(t, fx.Challenges[3]), 1)
	if err := test.IsSolved(&challengerFixtureCircuit{}, w, ecc.BN254.ScalarField()); err == nil {
		t.Fatal("Challenger gadget accepted a tampered challenge")
	}
}

// --- native vs gadget differential over the full API surface ---

const diffNBits = 11 // a representative FRI query-index width (2^11 < p)

// diffAbsorb is a canonical, non-trivial absorb sequence (10 elements: one
// full-rate duplexing at 8, two left buffered).
func diffAbsorb() []uint32 {
	return []uint32{101, 202, 303, 404, 505, 606, 707, 808, 909, 1010}
}

const diffExtra = uint32(424242)

// computeDiffExpected runs the differential protocol through the native
// reference: observe the absorb run, sample a base element, an extension
// element, a query index, then observe one more element and sample again.
func computeDiffExpected() (s0 uint32, e bbExtRef, idx uint, s1 uint32, e2 bbExtRef) {
	c := newChallengerRef()
	c.observeSlice(diffAbsorb())
	s0 = c.sample()
	e = c.sampleExt()
	idx = c.sampleBits(diffNBits)
	c.observe(diffExtra)
	s1 = c.sample()
	e2 = c.sampleExt()
	return
}

type challengerDiffCircuit struct {
	Absorbed [10]frontend.Variable
	Extra    frontend.Variable
	S0       frontend.Variable
	E        [4]frontend.Variable
	Idx      frontend.Variable
	S1       frontend.Variable
	E2       [4]frontend.Variable
}

func (c *challengerDiffCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	ch := NewChallenger(bb)
	ch.ObserveSlice(c.Absorbed[:])
	api.AssertIsEqual(ch.Sample(), c.S0)
	e := ch.SampleExt()
	for i := 0; i < 4; i++ {
		api.AssertIsEqual(e[i], c.E[i])
	}
	api.AssertIsEqual(ch.SampleBits(diffNBits), c.Idx)
	ch.Observe(c.Extra)
	api.AssertIsEqual(ch.Sample(), c.S1)
	e2 := ch.SampleExt()
	for i := 0; i < 4; i++ {
		api.AssertIsEqual(e2[i], c.E2[i])
	}
	return nil
}

func challengerDiffWitness() *challengerDiffCircuit {
	s0, e, idx, s1, e2 := computeDiffExpected()
	w := &challengerDiffCircuit{Extra: diffExtra, S0: s0, Idx: idx, S1: s1}
	for i, v := range diffAbsorb() {
		w.Absorbed[i] = v
	}
	for i := 0; i < 4; i++ {
		w.E[i] = e[i]
		w.E2[i] = e2[i]
	}
	return w
}

// The gadget's Observe/Sample/SampleExt/SampleBits must agree with the native
// reference across a protocol that exercises buffering, mid-duplex sampling,
// re-observe (output-buffer invalidation) and re-sampling.
func TestChallengerGadgetMatchesNativeReference(t *testing.T) {
	if err := test.IsSolved(&challengerDiffCircuit{}, challengerDiffWitness(), ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("gadget vs native reference diverge: %v", err)
	}
}

// REJECT polarity: a tampered expected extension coefficient must fail.
func TestChallengerGadgetDiffRejectsTamperedExt(t *testing.T) {
	w := challengerDiffWitness()
	w.E[2] = bbAddRef(w.E[2].(uint32), 1)
	if err := test.IsSolved(&challengerDiffCircuit{}, w, ecc.BN254.ScalarField()); err == nil {
		t.Fatal("gadget accepted a tampered extension challenge")
	}
}

// REJECT polarity: a tampered expected query index must fail.
func TestChallengerGadgetDiffRejectsTamperedIdx(t *testing.T) {
	w := challengerDiffWitness()
	w.Idx = w.Idx.(uint) + 1
	if err := test.IsSolved(&challengerDiffCircuit{}, w, ecc.BN254.ScalarField()); err == nil {
		t.Fatal("gadget accepted a tampered query index")
	}
}

// --- native reference properties ---

// observe-changes-output: absorbing one extra element changes the next sample
// (the challenger actually binds its inputs; non-degenerate).
func TestChallengerRefObserveChangesOutput(t *testing.T) {
	base := diffAbsorb()

	a := newChallengerRef()
	a.observeSlice(base)
	sa := a.sample()

	b := newChallengerRef()
	b.observeSlice(base)
	b.observe(777) // one extra observe
	sb := b.sample()

	if sa == sb {
		t.Fatalf("an extra observe did not change the next sample (%d); transcript is degenerate", sa)
	}
}

// sample_bits determinism + range: identical challengers yield identical query
// indices, and every index is within [0, 2^n).
func TestChallengerRefSampleBitsDeterminismAndRange(t *testing.T) {
	for n := 1; n <= 30; n++ {
		a := newChallengerRef()
		a.observeSlice(diffAbsorb())
		b := newChallengerRef()
		b.observeSlice(diffAbsorb())

		ia := a.sampleBits(n)
		ib := b.sampleBits(n)
		if ia != ib {
			t.Fatalf("sampleBits(%d) not deterministic: %d vs %d", n, ia, ib)
		}
		if ia >= (uint(1) << uint(n)) {
			t.Fatalf("sampleBits(%d) = %d out of range [0, 2^%d)", n, ia, n)
		}
	}
}

// sample_bits is the low-n-bits reduction of the same base sample (matches
// duplex_challenger.rs:264 rand & ((1<<bits)-1)).
func TestChallengerRefSampleBitsIsLowBitsOfSample(t *testing.T) {
	c := newChallengerRef()
	c.observeSlice(diffAbsorb())
	base := c.sample() // the very sample sampleBits would draw

	const n = 13
	d := newChallengerRef()
	d.observeSlice(diffAbsorb())
	idx := d.sampleBits(n)

	want := uint(base) & ((uint(1) << n) - 1)
	if idx != want {
		t.Fatalf("sampleBits(%d)=%d, want low %d bits of %d = %d", n, idx, n, base, want)
	}
}

// canary: a tampered absorbed value changes the base sample, the extension
// sample AND the query index (the transcript binds every input).
func TestChallengerRefTamperedAbsorbBites(t *testing.T) {
	base := diffAbsorb()
	tampered := append([]uint32(nil), base...)
	tampered[0] = bbAddRef(tampered[0], 1)

	orig := newChallengerRef()
	orig.observeSlice(base)
	tamp := newChallengerRef()
	tamp.observeSlice(tampered)

	if orig.sample() == tamp.sample() {
		t.Fatal("tampered absorb produced the same base sample")
	}
	if orig.sampleExt() == tamp.sampleExt() {
		t.Fatal("tampered absorb produced the same extension sample")
	}
	if orig.sampleBits(diffNBits) == tamp.sampleBits(diffNBits) {
		t.Fatal("tampered absorb produced the same query index")
	}
}

// sample_ext draws four base coefficients in order (coefficient 0 first): the
// four coefficients are exactly four successive base samples.
func TestChallengerRefSampleExtIsFourSamples(t *testing.T) {
	a := newChallengerRef()
	a.observeSlice(diffAbsorb())
	ext := a.sampleExt()

	b := newChallengerRef()
	b.observeSlice(diffAbsorb())
	var want bbExtRef
	for i := range want {
		want[i] = b.sample()
	}
	if ext != want {
		t.Fatalf("sampleExt=%v, four successive samples=%v", ext, want)
	}
}
