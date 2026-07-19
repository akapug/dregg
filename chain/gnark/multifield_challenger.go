// BabyBear<->BN254 MultiField Fiat-Shamir challenger — the transcript boundary
// of the re-architected wrap (docs/deos/WRAP-NATIVE-HASH-DECISION.md). The
// sponge state is BN254-NATIVE (the width-3 duplex of challenger_bn254.go, one
// Poseidon2Bn254 per duplexing at ~243 R1CS), while the OBSERVED proof values
// and the SAMPLED challenges (FRI betas, query indices) are BabyBear. This
// gadget is the in-circuit twin of the Rust shrink layer's challenger, so the
// pack/split must match the fork EXACTLY — a divergence silently breaks the
// transcript and the circuit would accept proofs Rust rejects (or vice versa).
//
// Ground truth: p3_challenger::MultiField32Challenger<F=BabyBear, PF=Bn254,
// P=Poseidon2Bn254<3>, WIDTH=3, RATE=2> at the workspace-pinned Plonky3 rev
// 82cfad73cd734d37a0d51953094f970c531817ec
// (challenger/src/multi_field_challenger.rs), lane-for-lane:
//
//   - PACK (absorb, F->PF): pending BabyBear values are packed with
//     reduce_packed (field/src/helpers.rs:171) in radix
//     2^absorb_radix_bits::<BabyBear>() = 2^31 (helpers.rs:162: bit length of
//     p-1), max_absorb_injective_limbs::<BabyBear, Bn254>() = 8 limbs per
//     BN254 element (helpers.rs:236 via :195: largest k with
//     (p-1)·Σ_{i<k} 2^{31i} < p_BN254), little-endian Horner
//     (multi_field_challenger.rs:106-114). The packed words are absorbed via
//     absorb_rate_padded_with_tag (duplex_challenger.rs:113): rate slots
//     overwritten, zero-padded tail, length tag (= number of BabyBear values)
//     ADDED to the capacity slot state[RATE], then one permutation.
//   - SPLIT (squeeze, PF->F): after each duplexing every rate cell is split
//     with split_pf_to_field_order_limbs (helpers.rs:338) into
//     squeeze_field_order_num_limbs::<Bn254, BabyBear>() = 7 little-endian
//     base-p limbs (helpers.rs:317; bias < 1/p per limb — near-uniform over
//     ALL of BabyBear, unlike a radix-2^30 split), queued in rate order and
//     popped from the END (multi_field_challenger.rs:120-131, :246-259).
//   - Flush discipline: observe buffers BabyBear values and auto-flushes at
//     8·RATE = 16 (rs:150-157); sample flushes any pending partial batch first
//     (rs:248); digest words (BN254 Merkle roots) are absorbed NATIVELY in
//     RATE-chunks with the chunk length as tag, after flushing pending F
//     (rs:181-193) — no PF->F->repack detour.
//   - SampleBits (rs:277-283): one BabyBear sample, canonical value, low n
//     bits (requires 2^n < p, i.e. n ≤ 30).
//
// In-circuit split soundness: each squeezed BN254 cell v is decomposed by an
// UNTRUSTED hint into 7 base-p limbs plus a remainder r, then pinned by (a)
// canonicity range checks on every limb, (b) r < 2^38, (c) the linear
// recomposition v == Σ c_i·p^i + r·p^7, and (d) a lexicographic bound
// (r, c6..c0) ≤ base-p digits of (p_BN254 - 1). (d) forces the integer value
// of the decomposition below p_BN254, so the recomposition cannot wrap and the
// decomposition is the UNIQUE canonical one — without it a malicious prover
// could shift the limbs by p_BN254 and choose its own challenges. This is
// exact (no completeness gap): the canonical decomposition of any v always
// satisfies the bound.
package friverifier

import (
	"errors"
	"math/big"
	"sync"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
)

const (
	// mfAbsorbRadixBits: absorb_radix_bits::<BabyBear>() — bit length of p-1
	// (helpers.rs:162). Canonical BabyBear digits are valid base-2^31 digits.
	mfAbsorbRadixBits = 31
	// mfAbsorbNumFElms: max_absorb_injective_limbs::<BabyBear, Bn254>()
	// (helpers.rs:236) — 8 BabyBear limbs pack injectively into one BN254
	// element: (p-1)·Σ_{i<8} 2^{31i} < 2^248 < p_BN254 < (p-1)·Σ_{i<9} 2^{31i}.
	mfAbsorbNumFElms = 8
	// mfSqueezeNumFElms: squeeze_field_order_num_limbs::<Bn254, BabyBear>()
	// (helpers.rs:317) — largest k with p^(k+1) < p_BN254 is 7 (p^8 ≈ 2^247.3,
	// and the k+1-th limb would carry bias ≥ 1/p).
	mfSqueezeNumFElms = 7
	// mfSplitRemBits bounds the split remainder r = v div p^7:
	// r ≤ (p_BN254-1)/p^7 = 163268688284 < 2^38.
	mfSplitRemBits = 38
)

// mfSplit constants, derived once from the BN254 scalar modulus: the powers
// p^i used in recomposition and the base-p digits of p_BN254 - 1 used by the
// lexicographic canonicity bound (digit index 7 = the remainder digit).
var (
	mfSplitOnce   sync.Once
	mfSplitPPow   [mfSqueezeNumFElms + 1]*big.Int // p^0 .. p^7
	mfSplitDigits [mfSqueezeNumFElms + 1]*big.Int // base-p digits of p_BN254-1
)

func mfSplitInit() {
	mfSplitOnce.Do(func() {
		pow := big.NewInt(1)
		for i := range mfSplitPPow {
			mfSplitPPow[i] = new(big.Int).Set(pow)
			pow = new(big.Int).Mul(pow, bbPBig)
		}
		rem := new(big.Int).Sub(fr.Modulus(), big.NewInt(1))
		for i := 0; i < mfSqueezeNumFElms; i++ {
			digit := new(big.Int)
			rem.DivMod(rem, bbPBig, digit)
			mfSplitDigits[i] = digit
		}
		mfSplitDigits[mfSqueezeNumFElms] = rem
	})
}

func init() {
	solver.RegisterHint(mfSplitHint)
}

// mfSplitHint decomposes one canonical BN254 sponge cell into 7 little-endian
// base-p BabyBear limbs plus the remainder r = v div p^7. The output is
// UNTRUSTED; splitToFieldOrderLimbs constrains it (see the package comment).
func mfSplitHint(_ *big.Int, inputs, outputs []*big.Int) error {
	if len(inputs) != 1 || len(outputs) != mfSqueezeNumFElms+1 {
		return errors.New("mfSplitHint: expected 1 input, 8 outputs")
	}
	if inputs[0].Sign() < 0 {
		return errors.New("mfSplitHint: negative input")
	}
	rem := new(big.Int).Set(inputs[0])
	for i := 0; i < mfSqueezeNumFElms; i++ {
		q := new(big.Int)
		q.DivMod(rem, bbPBig, outputs[i])
		rem = q
	}
	outputs[mfSqueezeNumFElms].Set(rem)
	return nil
}

// MultiFieldChallenger is the in-circuit BabyBear-over-BN254 challenger: a
// native BN254 duplex sponge (ChallengerBn254) with the MultiField pack/split
// adapter. Observed BabyBear values and sampled challenges are canonical
// BabyBear variables; observed digests are native BN254 variables.
type MultiFieldChallenger struct {
	api   frontend.API
	bb    *BBApi
	inner *ChallengerBn254
	// fBuf holds observed-but-unflushed BabyBear values (≤ 16).
	fBuf []frontend.Variable
	// fSqueezeBuf holds split BabyBear limbs pending consumption, popped from
	// the END (multi_field_challenger.rs f_squeeze_buffer pop order).
	fSqueezeBuf []frontend.Variable
}

// NewMultiFieldChallenger builds a fresh challenger over the given BabyBear
// gadget context (inner sponge state = [0; 3], all buffers empty).
func NewMultiFieldChallenger(bb *BBApi) *MultiFieldChallenger {
	mfSplitInit()
	return &MultiFieldChallenger{
		api:   bb.API(),
		bb:    bb,
		inner: NewChallengerBn254(bb.API()),
	}
}

// NewMultiFieldChallengerWithPerm builds a challenger whose inner sponge
// duplexings run through `perm` instead of the hand-Go Poseidon2Bn254. Every
// other layer — the radix-2^31 8-limb PACK, the length-tagged rate-padded
// absorb, the 7-limb base-p SPLIT and its canonicity/lex soundness, and the
// observe/sample flush discipline — is the SAME deployed adapter (this is the
// deployed oracle with its permutation swapped for the Lean-emitted replay).
func NewMultiFieldChallengerWithPerm(bb *BBApi,
	perm func(frontend.API, *[bn254SpongeWidth]frontend.Variable)) *MultiFieldChallenger {
	c := NewMultiFieldChallenger(bb)
	c.inner.perm = perm
	return c
}

// absorbRatePaddedWithTag mirrors duplex_challenger.rs:113: overwrite the rate
// slots with values (zero-padded), ADD the length tag to the capacity slot
// state[RATE], permute, refill the inner output buffer. Inner input/output
// buffers are cleared first.
func (c *MultiFieldChallenger) absorbRatePaddedWithTag(values []frontend.Variable, lengthTag int) {
	if len(values) > bn254SpongeRate {
		panic("MultiFieldChallenger.absorbRatePaddedWithTag: too many values for rate")
	}
	c.inner.inBuf = c.inner.inBuf[:0]
	c.inner.outBuf = c.inner.outBuf[:0]
	for i, v := range values {
		c.inner.state[i] = v
	}
	for i := len(values); i < bn254SpongeRate; i++ {
		c.inner.state[i] = frontend.Variable(0)
	}
	c.inner.state[bn254SpongeRate] = c.api.Add(c.inner.state[bn254SpongeRate], lengthTag)
	c.inner.applyPerm()
	c.inner.outBuf = append(c.inner.outBuf, c.inner.state[:bn254SpongeRate]...)
}

// reducePacked packs ≤ 8 canonical BabyBear values into one BN254 element:
// little-endian Horner in radix 2^31 (helpers.rs:171, reduce_packed). A pure
// linear combination — zero multiplication constraints.
func (c *MultiFieldChallenger) reducePacked(vals []frontend.Variable) frontend.Variable {
	base := new(big.Int).Lsh(big.NewInt(1), mfAbsorbRadixBits)
	acc := frontend.Variable(0)
	for i := len(vals) - 1; i >= 0; i-- {
		acc = c.api.Add(c.api.Mul(acc, base), vals[i])
	}
	return acc
}

// flushFIfNonEmpty mirrors multi_field_challenger.rs:102: pack the pending
// BabyBear values in chunks of 8 and absorb them with the count as length tag.
func (c *MultiFieldChallenger) flushFIfNonEmpty() {
	if len(c.fBuf) == 0 {
		return
	}
	nIn := len(c.fBuf)
	if nIn > mfAbsorbNumFElms*bn254SpongeRate {
		panic("MultiFieldChallenger.flushFIfNonEmpty: pending buffer overflow")
	}
	var packed []frontend.Variable
	for start := 0; start < nIn; start += mfAbsorbNumFElms {
		end := min(start+mfAbsorbNumFElms, nIn)
		packed = append(packed, c.reducePacked(c.fBuf[start:end]))
	}
	c.absorbRatePaddedWithTag(packed, nIn)
	c.fBuf = c.fBuf[:0]
	c.fSqueezeBuf = c.fSqueezeBuf[:0]
}

// ObserveBabyBear absorbs one BabyBear proof value
// (multi_field_challenger.rs:150): stale squeeze output is dropped, the value
// is buffered, and a full 16-element batch auto-flushes. The value is asserted
// canonical at the boundary (fail-closed ingestion; canonicity is also what
// makes the radix-2^31 packing injective).
func (c *MultiFieldChallenger) ObserveBabyBear(v frontend.Variable) {
	c.bb.AssertIsCanonical(v)
	c.inner.outBuf = c.inner.outBuf[:0]
	c.fSqueezeBuf = c.fSqueezeBuf[:0]
	c.fBuf = append(c.fBuf, v)
	if len(c.fBuf) == mfAbsorbNumFElms*bn254SpongeRate {
		c.flushFIfNonEmpty()
	}
}

// ObserveBabyBearSlice absorbs a run of BabyBear values in order.
func (c *MultiFieldChallenger) ObserveBabyBearSlice(vs []frontend.Variable) {
	for _, v := range vs {
		c.ObserveBabyBear(v)
	}
}

// ObserveBabyBearExt absorbs a degree-4 extension element as its four base
// coefficients in order (observe_algebra_element: coefficient 0 first).
func (c *MultiFieldChallenger) ObserveBabyBearExt(e BBExt) {
	for i := range e {
		c.ObserveBabyBear(e[i])
	}
}

// ObserveBn254Digest absorbs native BN254 digest words (a Merkle root / cap)
// per multi_field_challenger.rs:181: pending BabyBear values are flushed
// through the packed absorb, then the words are absorbed NATIVELY in
// RATE-chunks with the chunk length as tag — no PF->F->repack detour.
func (c *MultiFieldChallenger) ObserveBn254Digest(words []frontend.Variable) {
	c.inner.outBuf = c.inner.outBuf[:0]
	c.fSqueezeBuf = c.fSqueezeBuf[:0]
	c.flushFIfNonEmpty()
	for start := 0; start < len(words); start += bn254SpongeRate {
		end := min(start+bn254SpongeRate, len(words))
		chunk := words[start:end]
		c.absorbRatePaddedWithTag(chunk, len(chunk))
		c.fSqueezeBuf = c.fSqueezeBuf[:0]
	}
}

// splitToFieldOrderLimbs splits one squeezed BN254 sponge cell into 7
// canonical little-endian base-p BabyBear limbs (helpers.rs:338,
// split_pf_to_field_order_limbs), constrained to be the unique canonical
// decomposition (see the package comment for the soundness argument).
func (c *MultiFieldChallenger) splitToFieldOrderLimbs(v frontend.Variable) []frontend.Variable {
	res, err := c.api.Compiler().NewHint(mfSplitHint, mfSqueezeNumFElms+1, v)
	if err != nil {
		panic(err)
	}
	limbs, r := res[:mfSqueezeNumFElms], res[mfSqueezeNumFElms]

	// (a) every limb is a canonical BabyBear element; (b) r < 2^38.
	for _, l := range limbs {
		c.bb.AssertIsCanonical(l)
	}
	c.bb.rc.Check(r, mfSplitRemBits)

	// (c) recomposition: v == Σ c_i·p^i + r·p^7. Cannot wrap: (d) bounds the
	// integer value below p_BN254.
	acc := frontend.Variable(0)
	for i := 0; i < mfSqueezeNumFElms; i++ {
		acc = c.api.Add(acc, c.api.Mul(limbs[i], mfSplitPPow[i]))
	}
	acc = c.api.Add(acc, c.api.Mul(r, mfSplitPPow[mfSqueezeNumFElms]))
	c.api.AssertIsEqual(v, acc)

	// (d) lexicographic canonicity: (r, c6, ..., c0) ≤ the base-p digits of
	// p_BN254 - 1, most-significant first. While the prefix is tied, the
	// current digit may not exceed the modulus digit (enforced by
	// range-checking eq·(D_i - l_i): a wrap on excess blows the range check);
	// once strictly below, the remaining digits are free.
	eq := frontend.Variable(1)
	lexStep := func(l frontend.Variable, digit *big.Int, bits int) {
		sel := c.api.Mul(eq, c.api.Sub(digit, l))
		c.bb.rc.Check(sel, bits)
		isEq := c.api.IsZero(c.api.Sub(l, digit))
		eq = c.api.Mul(eq, isEq)
	}
	lexStep(r, mfSplitDigits[mfSqueezeNumFElms], mfSplitRemBits)
	for i := mfSqueezeNumFElms - 1; i >= 0; i-- {
		lexStep(limbs[i], mfSplitDigits[i], 31)
	}

	return limbs
}

// refillFSqueezeFromInner mirrors multi_field_challenger.rs:120: split every
// inner rate cell IN ORDER into the squeeze queue, then drain the inner output
// buffer so the next empty batch triggers a fresh duplexing.
func (c *MultiFieldChallenger) refillFSqueezeFromInner() {
	c.fSqueezeBuf = c.fSqueezeBuf[:0]
	for _, pf := range c.inner.outBuf {
		c.fSqueezeBuf = append(c.fSqueezeBuf, c.splitToFieldOrderLimbs(pf)...)
	}
	c.inner.outBuf = c.inner.outBuf[:0]
}

// SampleBabyBear squeezes one canonical BabyBear challenge
// (multi_field_challenger.rs:246): flush pending observes, refill the limb
// queue from a duplexing if drained, pop from the END.
func (c *MultiFieldChallenger) SampleBabyBear() frontend.Variable {
	c.flushFIfNonEmpty()
	if len(c.fSqueezeBuf) == 0 {
		if len(c.inner.inBuf) > 0 || len(c.inner.outBuf) == 0 {
			c.inner.duplexing()
		}
		c.refillFSqueezeFromInner()
	}
	n := len(c.fSqueezeBuf)
	v := c.fSqueezeBuf[n-1]
	c.fSqueezeBuf = c.fSqueezeBuf[:n-1]
	return v
}

// SampleBabyBearExt squeezes a degree-4 extension challenge: four base
// samples, the first popped becoming coefficient 0 (sample_algebra_element).
func (c *MultiFieldChallenger) SampleBabyBearExt() BBExt {
	var e BBExt
	for i := range e {
		e[i] = c.SampleBabyBear()
	}
	return e
}

// SampleBits draws an n-bit query index (multi_field_challenger.rs:277): one
// BabyBear sample, low n bits of the canonical value. Requires 2^n < p
// (n ≤ 30). The sample is canonical (< p < 2^31) by the split constraints, so
// the 31-bit decomposition is exact and the low-n reconstruction unique.
func (c *MultiFieldChallenger) SampleBits(n int) frontend.Variable {
	bits := c.SampleBitsDecomposed(n)
	if n == 0 {
		return frontend.Variable(0)
	}
	return c.api.FromBinary(bits...)
}

// SampleBitsDecomposed is SampleBits returning the low n bits individually
// (LSB first), the form Merkle-path index steering consumes.
func (c *MultiFieldChallenger) SampleBitsDecomposed(n int) []frontend.Variable {
	if n < 0 || uint64(1)<<uint(n) >= BabyBearP {
		panic("MultiFieldChallenger.SampleBitsDecomposed: bit count out of range for BabyBear")
	}
	base := c.SampleBabyBear()
	if n == 0 {
		return nil
	}
	bits := c.api.ToBinary(base, 31) // exact: base < p < 2^31
	return bits[:n]
}
