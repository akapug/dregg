// Tests for the BabyBear<->BN254 MultiField challenger.
//
// The gold KAT below was EXECUTED BY THE FORK ITSELF: a Rust harness running
// p3_challenger::MultiField32Challenger<BabyBear, Bn254, Poseidon2Bn254<3>,
// WIDTH=3, RATE=2> at rev 82cfad73cd734d37a0d51953094f970c531817ec, with the
// Poseidon2Bn254 permutation built from the same HorizenLabs RC3 constants
// this package pins (the harness also re-verified that permutation against
// the zkhash gold vector bn254KATOutHex). Fork-reported parameters:
// absorb_radix_bits=31, absorb_num_f_elms=8, squeeze_num_f_elms=7.
//
// Layers: ref == fork KAT (gold) -> gadget == ref in-circuit (differential,
// pinned + randomized) -> REJECT canaries (tampered absorb / digest /
// challenge / index / order, wrong pack order, wrong length tag,
// non-canonical ingestion) -> MultiField vs emulated constraint measurement.
package friverifier

import (
	"math/big"
	"math/rand"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/test"
)

// --- the fork-executed gold KAT ---

// Protocol: observe BabyBear [11,22,33] (partial chunk) -> s0,s1,s2 ->
// observe one native BN254 digest word -> s3 -> observe a full 16-element
// batch (auto-flush; includes p-1 and 2^30) plus one straggler -> s4 ->
// 13 buffered pops (mid) -> s5 (the pop that crosses a squeeze-batch
// boundary and forces a fresh duplexing) -> sampleBits(20).

const mfKATDigestWord = uint64(12345678901234567890)

func mfKATAbsorb() []uint32 { return []uint32{11, 22, 33} }

func mfKATBatch() []uint32 {
	batch := []uint32{2013265920, 1 << 30} // p-1 and 2^30: high-limb boundary values
	for v := uint32(100); v < 114; v++ {
		batch = append(batch, v)
	}
	// 16 values so far: exactly one auto-flush; the straggler is flushed by s4.
	return append(batch, 424242)
}

// Pinned outputs of the Rust fork harness (BabyBear canonical values).
var mfForkKATS = [6]uint32{1330327576, 1916157604, 1399880191, 412774374, 436327734, 1700675939}

const (
	mfForkKATIdxBits = 20
	mfForkKATIdx     = uint64(31374)
)

func multiFieldRefGoldTranscript() (s [6]uint32, mid [13]uint32, idx uint64) {
	c := newMultiFieldChallengerRef()
	c.observeBabyBearSlice(mfKATAbsorb())
	s[0] = c.sampleBabyBear()
	s[1] = c.sampleBabyBear()
	s[2] = c.sampleBabyBear()
	c.observeBn254Digest([]fr.Element{frFromU64(mfKATDigestWord)})
	s[3] = c.sampleBabyBear()
	c.observeBabyBearSlice(mfKATBatch())
	s[4] = c.sampleBabyBear()
	for i := range mid {
		mid[i] = c.sampleBabyBear()
	}
	s[5] = c.sampleBabyBear()
	idx = c.sampleBits(mfForkKATIdxBits)
	return
}

// The native reference reproduces the fork-executed transcript exactly.
func TestMultiFieldRefMatchesForkKAT(t *testing.T) {
	s, _, idx := multiFieldRefGoldTranscript()
	for i := range s {
		if s[i] != mfForkKATS[i] {
			t.Fatalf("s%d drifted from the fork KAT: got %d want %d", i, s[i], mfForkKATS[i])
		}
	}
	if idx != mfForkKATIdx {
		t.Fatalf("idx drifted from the fork KAT: got %d want %d", idx, mfForkKATIdx)
	}
}

// REJECT polarity for the KAT: a tampered absorbed BabyBear value changes the
// first sampled challenge (the packed transcript binds its inputs).
func TestMultiFieldRefTamperedAbsorbBites(t *testing.T) {
	c := newMultiFieldChallengerRef()
	abs := mfKATAbsorb()
	abs[0]++
	c.observeBabyBearSlice(abs)
	if got := c.sampleBabyBear(); got == mfForkKATS[0] {
		t.Fatal("tampered absorb still produced the pinned first challenge")
	}
}

// REJECT polarity for observe ORDER: swapping two absorbed values lands them
// in different radix-2^31 limb positions and diverges the transcript.
func TestMultiFieldRefAbsorbOrderBinds(t *testing.T) {
	c := newMultiFieldChallengerRef()
	c.observeBabyBearSlice([]uint32{22, 11, 33})
	if got := c.sampleBabyBear(); got == mfForkKATS[0] {
		t.Fatal("swapped absorb order still produced the pinned first challenge")
	}
}

// REJECT polarity for the PACK ORDER itself: packing the pending values
// big-endian (vals[0] as the HIGH limb) instead of the fork's little-endian
// Horner diverges the transcript. This is the canary for the exact
// reduce_packed limb convention (helpers.rs:171).
func TestMultiFieldRefWrongPackOrderDiverges(t *testing.T) {
	abs := mfKATAbsorb()

	// Wrong pack: vals in forward Horner order (vals[0] high).
	wrong := new(big.Int)
	for _, v := range abs {
		wrong.Lsh(wrong, mfAbsorbRadixBits)
		wrong.Add(wrong, new(big.Int).SetUint64(uint64(v)))
	}
	right := mfRefReducePacked(abs)
	var wrongFr fr.Element
	wrongFr.SetBigInt(wrong)
	if wrongFr.Equal(&right) {
		t.Fatal("big-endian and little-endian packing coincide; canary is vacuous")
	}

	c := &multiFieldChallengerRef{}
	c.absorbRatePaddedWithTag([]fr.Element{wrongFr}, uint8(len(abs)))
	limbs := mfRefSplitToFieldOrderLimbs(c.outBuf[len(c.outBuf)-1])
	if limbs[len(limbs)-1] == mfForkKATS[0] {
		t.Fatal("wrong pack order still produced the pinned first challenge")
	}
}

// REJECT polarity for the LENGTH TAG: absorbing the same packed word with a
// wrong count tag diverges (partial batches are length-bound; the fork's
// test_partial_absorb_length_distinct_from_padded_equivalent analog).
func TestMultiFieldRefWrongLengthTagDiverges(t *testing.T) {
	abs := mfKATAbsorb()
	packed := mfRefReducePacked(abs)
	c := &multiFieldChallengerRef{}
	c.absorbRatePaddedWithTag([]fr.Element{packed}, uint8(len(abs))+1)
	limbs := mfRefSplitToFieldOrderLimbs(c.outBuf[len(c.outBuf)-1])
	if limbs[len(limbs)-1] == mfForkKATS[0] {
		t.Fatal("wrong length tag still produced the pinned first challenge")
	}
}

// The ref rejects non-canonical BabyBear ingestion (fail-closed twin of the
// gadget's AssertIsCanonical).
func TestMultiFieldRefRejectsNonCanonical(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Fatal("observeBabyBear(p) did not panic")
		}
	}()
	newMultiFieldChallengerRef().observeBabyBear(uint32(BabyBearP))
}

// --- gadget vs reference: the full gold protocol in-circuit ---

type multiFieldKATCircuit struct {
	Absorbed [3]frontend.Variable
	Digest   frontend.Variable
	Batch    [17]frontend.Variable
	S        [6]frontend.Variable
	Mid      [13]frontend.Variable
	Idx      frontend.Variable
}

func (c *multiFieldKATCircuit) Define(api frontend.API) error {
	ch := NewMultiFieldChallenger(NewBBApi(api))
	ch.ObserveBabyBearSlice(c.Absorbed[:])
	for i := 0; i < 3; i++ {
		api.AssertIsEqual(ch.SampleBabyBear(), c.S[i])
	}
	ch.ObserveBn254Digest([]frontend.Variable{c.Digest})
	api.AssertIsEqual(ch.SampleBabyBear(), c.S[3])
	ch.ObserveBabyBearSlice(c.Batch[:])
	api.AssertIsEqual(ch.SampleBabyBear(), c.S[4])
	for i := range c.Mid {
		api.AssertIsEqual(ch.SampleBabyBear(), c.Mid[i])
	}
	api.AssertIsEqual(ch.SampleBabyBear(), c.S[5])
	api.AssertIsEqual(ch.SampleBits(mfForkKATIdxBits), c.Idx)
	return nil
}

func multiFieldKATWitness() *multiFieldKATCircuit {
	s, mid, idx := multiFieldRefGoldTranscript()
	digest := frFromU64(mfKATDigestWord)
	w := &multiFieldKATCircuit{
		Digest: digest.BigInt(new(big.Int)),
		Idx:    idx,
	}
	for i, v := range mfKATAbsorb() {
		w.Absorbed[i] = v
	}
	for i, v := range mfKATBatch() {
		w.Batch[i] = v
	}
	for i := range s {
		w.S[i] = s[i]
	}
	for i := range mid {
		w.Mid[i] = mid[i]
	}
	return w
}

// The gadget reproduces the (fork-pinned) reference transcript in-circuit:
// pack, tag, digest absorb, split, pop order, batch boundary, sampleBits.
func TestMultiFieldGadgetMatchesForkKAT(t *testing.T) {
	if err := test.IsSolved(&multiFieldKATCircuit{}, multiFieldKATWitness(), ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("gadget diverges from the fork-pinned reference transcript: %v", err)
	}
}

// REJECT canaries: each tamper must make the circuit unsatisfiable. The
// tampered-absorb/digest/order cases keep the GOLD expected challenges (a
// prover feeding different proof data cannot reach the honest challenges);
// the tampered-challenge/index cases keep the gold transcript (a prover
// cannot claim different challenges for the honest transcript).
func TestMultiFieldGadgetRejectsTampering(t *testing.T) {
	field := ecc.BN254.ScalarField()
	cases := []struct {
		name   string
		tamper func(w *multiFieldKATCircuit)
	}{
		{"tampered absorbed BabyBear", func(w *multiFieldKATCircuit) { w.Absorbed[0] = uint32(12) }},
		{"swapped absorb order", func(w *multiFieldKATCircuit) { w.Absorbed[0], w.Absorbed[1] = w.Absorbed[1], w.Absorbed[0] }},
		{"tampered digest word", func(w *multiFieldKATCircuit) {
			w.Digest = new(big.Int).Add(w.Digest.(*big.Int), big.NewInt(1))
		}},
		{"tampered late batch value", func(w *multiFieldKATCircuit) { w.Batch[16] = uint32(424243) }},
		{"tampered challenge", func(w *multiFieldKATCircuit) { w.S[1] = mfForkKATS[1] + 1 }},
		{"tampered post-boundary challenge", func(w *multiFieldKATCircuit) { w.S[5] = mfForkKATS[5] + 1 }},
		{"tampered query index", func(w *multiFieldKATCircuit) { w.Idx = mfForkKATIdx + 1 }},
		{"non-canonical observe (v = p)", func(w *multiFieldKATCircuit) { w.Absorbed[0] = uint32(BabyBearP) }},
		{"non-canonical observe (v = p + s0 shift)", func(w *multiFieldKATCircuit) {
			// p + original value: same residue mod p, DIFFERENT packing if it
			// slipped through — must be rejected at ingestion.
			w.Absorbed[0] = uint64(BabyBearP) + 11
		}},
	}
	for _, tc := range cases {
		w := multiFieldKATWitness()
		tc.tamper(w)
		if err := test.IsSolved(&multiFieldKATCircuit{}, w, field); err == nil {
			t.Fatalf("%s: gadget accepted the tampered witness", tc.name)
		}
	}
}

// --- randomized differential: gadget == ref over arbitrary op sequences ---

// mfDiffOp tapes: 0 = observe BabyBear, 1 = observe digest word, 2 = sample.
type multiFieldDiffCircuit struct {
	Ops      []int `gnark:"-"`
	Observed []frontend.Variable
	Digests  []frontend.Variable
	Samples  []frontend.Variable
}

func (c *multiFieldDiffCircuit) Define(api frontend.API) error {
	ch := NewMultiFieldChallenger(NewBBApi(api))
	oi, di, si := 0, 0, 0
	for _, op := range c.Ops {
		switch op {
		case 0:
			ch.ObserveBabyBear(c.Observed[oi])
			oi++
		case 1:
			ch.ObserveBn254Digest([]frontend.Variable{c.Digests[di]})
			di++
		default:
			api.AssertIsEqual(ch.SampleBabyBear(), c.Samples[si])
			si++
		}
	}
	return nil
}

func TestMultiFieldGadgetRefDifferentialRandomized(t *testing.T) {
	field := ecc.BN254.ScalarField()
	for seed := int64(1); seed <= 3; seed++ {
		rng := rand.New(rand.NewSource(seed))
		ref := newMultiFieldChallengerRef()
		var ops []int
		var observed, digests, samples []frontend.Variable
		for i := 0; i < 60; i++ {
			switch op := rng.Intn(3); op {
			case 0:
				v := uint32(rng.Uint64() % BabyBearP)
				ref.observeBabyBear(v)
				ops = append(ops, 0)
				observed = append(observed, v)
			case 1:
				var d fr.Element
				d.SetUint64(rng.Uint64())
				ref.observeBn254Digest([]fr.Element{d})
				ops = append(ops, 1)
				digests = append(digests, d.BigInt(new(big.Int)))
			default:
				got := ref.sampleBabyBear()
				ops = append(ops, 2)
				samples = append(samples, got)
			}
		}
		// The circuit shape needs at least one entry per slice.
		if len(observed) == 0 || len(digests) == 0 || len(samples) == 0 {
			t.Fatalf("seed %d: degenerate op tape", seed)
		}
		shape := &multiFieldDiffCircuit{
			Ops:      ops,
			Observed: make([]frontend.Variable, len(observed)),
			Digests:  make([]frontend.Variable, len(digests)),
			Samples:  make([]frontend.Variable, len(samples)),
		}
		w := &multiFieldDiffCircuit{Ops: ops, Observed: observed, Digests: digests, Samples: samples}
		if err := test.IsSolved(shape, w, field); err != nil {
			t.Fatalf("seed %d: gadget diverges from reference: %v", seed, err)
		}
	}
}

// --- adversarial split: a MALICIOUS HINT tries to forge the decomposition ---
//
// The split limbs come from an untrusted hint; the honest-solver tests above
// never exercise the canonicity bound because the honest hint always returns
// the canonical decomposition. Here we attack the REAL compiled circuit by
// overriding mfSplitHint with one that decomposes v + p_BN254 instead of v:
// the recomposition constraint still holds (mod p_BN254 the two are equal —
// this is exactly the challenge-forgery aliasing), every limb is still a
// canonical BabyBear element, and for small v the remainder still passes its
// 38-bit range check — ONLY the lexicographic bound (d) rejects it. If these
// solves succeed, a malicious prover can choose its own FRI challenges.

// mfSplitShiftedEvilHint: the canonical decomposition of inputs[0] + p_BN254.
func mfSplitShiftedEvilHint(_ *big.Int, inputs, outputs []*big.Int) error {
	rem := new(big.Int).Add(inputs[0], fr.Modulus())
	for i := 0; i < mfSqueezeNumFElms; i++ {
		q := new(big.Int)
		q.DivMod(rem, bbPBig, outputs[i])
		rem = q
	}
	outputs[mfSqueezeNumFElms].Set(rem)
	return nil
}

// mfSplitProbeCircuit: one bare split of a value, with the limbs deliberately
// UNPINNED — any rejection can come only from the split's internal
// constraints. v = 5 keeps the shifted remainder equal to the top digit of
// p_BN254-1, so the range checks and the recomposition pass and the lex bound
// alone must bite.
type mfSplitProbeCircuit struct {
	V frontend.Variable
}

func (c *mfSplitProbeCircuit) Define(api frontend.API) error {
	ch := NewMultiFieldChallenger(NewBBApi(api))
	ch.splitToFieldOrderLimbs(c.V)
	return nil
}

func TestMultiFieldSplitRejectsShiftedDecomposition(t *testing.T) {
	field := ecc.BN254.ScalarField()
	evil := solver.OverrideHint(solver.GetHintID(mfSplitHint), mfSplitShiftedEvilHint)

	// The bare-split probe: honest solve passes, evil solve must fail on the
	// lex bound alone (v = 5: limbs [5,0,...,0]).
	probe, err := frontend.Compile(field, r1cs.NewBuilder, &mfSplitProbeCircuit{})
	if err != nil {
		t.Fatalf("compile probe: %v", err)
	}
	w, err := frontend.NewWitness(&mfSplitProbeCircuit{V: 5}, field)
	if err != nil {
		t.Fatalf("witness: %v", err)
	}
	if _, err := probe.Solve(w); err != nil {
		t.Fatalf("honest split solve failed: %v", err)
	}
	if _, err := probe.Solve(w, evil); err == nil {
		t.Fatal("FORGERY: the shifted split decomposition satisfied the circuit")
	}

	// Defense in depth: the full KAT transcript with the evil hint must also
	// be unsatisfiable (the shifted decomposition trips the lex bound or the
	// remainder range check, and the forged limbs the pinned challenges).
	kat, err := frontend.Compile(field, r1cs.NewBuilder, &multiFieldKATCircuit{})
	if err != nil {
		t.Fatalf("compile KAT: %v", err)
	}
	kw, err := frontend.NewWitness(multiFieldKATWitness(), field)
	if err != nil {
		t.Fatalf("KAT witness: %v", err)
	}
	if _, err := kat.Solve(kw); err != nil {
		t.Fatalf("honest KAT solve failed: %v", err)
	}
	if _, err := kat.Solve(kw, evil); err == nil {
		t.Fatal("FORGERY: the shifted decompositions satisfied the full transcript")
	}
}

// --- constraint measurement: MultiField vs emulated challenger ---

type multiFieldCostCircuit struct {
	In       []frontend.Variable
	Out      frontend.Variable
	NSamples int
}

func (c *multiFieldCostCircuit) Define(api frontend.API) error {
	ch := NewMultiFieldChallenger(NewBBApi(api))
	ch.ObserveBabyBearSlice(c.In)
	var last frontend.Variable
	for i := 0; i < c.NSamples; i++ {
		last = ch.SampleBabyBear()
	}
	api.AssertIsEqual(last, c.Out)
	return nil
}

func TestMultiFieldVsEmulatedConstraints(t *testing.T) {
	field := ecc.BN254.ScalarField()
	compile := func(c frontend.Circuit) int {
		cs, err := frontend.Compile(field, r1cs.NewBuilder, c)
		if err != nil {
			t.Fatalf("compile: %v", err)
		}
		return cs.GetNbConstraints()
	}
	vars := func(n int) []frontend.Variable { return make([]frontend.Variable, n) }

	// MultiField: 16 observes = one packed duplexing; the first sample splits
	// both rate cells (14 limbs); samples 2..14 are buffered pops.
	m1 := compile(&multiFieldCostCircuit{In: vars(16), NSamples: 1})
	m14 := compile(&multiFieldCostCircuit{In: vars(16), NSamples: 14})
	t.Logf("MULTIFIELD: observe16+sample1 %d R1CS, observe16+sample14 %d R1CS (samples 2..14 add %d)",
		m1, m14, m14-m1)

	// Emulated: 16 observes = two width-16 duplexings, sample = buffered pop.
	e1 := compile(&challengerEmulatedCostCircuit{In: vars(16)})
	t.Logf("EMULATED: observe16+sample1 %d R1CS", e1)
	t.Logf("SWING: emulated/multifield for observe16+sample1 = %.1fx", float64(e1)/float64(m1))

	// 16 BabyBear observations reach the transcript through ONE native
	// permutation (~243 R1CS) + one 2-cell split, vs TWO emulated width-16
	// permutations. The re-architecture premise for the boundary.
	if m1 >= e1 {
		t.Fatalf("MultiField observe16+sample (%d) is not below emulated (%d); the wrap premise fails", m1, e1)
	}
}
