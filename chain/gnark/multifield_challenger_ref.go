// Native-Go reference twin for the BabyBear<->BN254 MultiField challenger
// (multifield_challenger.go). Plain fr.Element / big.Int arithmetic, an
// independent implementation of the same fork semantics
// (p3_challenger::MultiField32Challenger<BabyBear, Bn254, Poseidon2Bn254<3>,
// WIDTH=3, RATE=2> at rev 82cfad73cd734d37a0d51953094f970c531817ec), checked
// in the tests against a KAT EXECUTED BY THE FORK ITSELF (the Rust
// MultiField32Challenger over the same HorizenLabs constants), and
// differentially against the circuit gadget.
//
// The inner sponge input buffer is intentionally absent: the MultiField
// adapter never routes values through the inner observe path — every absorb
// goes through absorb_rate_padded_with_tag, which clears the inner input
// buffer (multi_field_challenger.rs:115, :188), so the fork's
// `!inner.input_buffer.is_empty()` duplexing condition (rs:250) is always
// false and the sample condition reduces to an empty output buffer.
package friverifier

import (
	"math/big"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

// multiFieldChallengerRef mirrors MultiField32Challenger: a native BN254
// duplex sponge plus the BabyBear pack/split adapter. BabyBear values are
// canonical uint32 (< BabyBearP).
type multiFieldChallengerRef struct {
	state       [bn254SpongeWidth]fr.Element
	outBuf      []fr.Element
	fBuf        []uint32
	fSqueezeBuf []uint32
}

func newMultiFieldChallengerRef() *multiFieldChallengerRef {
	return &multiFieldChallengerRef{}
}

// duplexing with no pending inner input (duplex_challenger.rs:86 with an empty
// input buffer): permute, refill the output buffer from the rate slots.
func (c *multiFieldChallengerRef) duplexing() {
	poseidon2Bn254Ref(&c.state)
	c.outBuf = append(c.outBuf[:0], c.state[:bn254SpongeRate]...)
}

// absorbRatePaddedWithTag mirrors duplex_challenger.rs:113: rate slots
// overwritten (zero-padded), length tag ADDED to the capacity slot, permute,
// refill the output buffer.
func (c *multiFieldChallengerRef) absorbRatePaddedWithTag(values []fr.Element, lengthTag uint8) {
	if len(values) > bn254SpongeRate {
		panic("multiFieldChallengerRef.absorbRatePaddedWithTag: too many values for rate")
	}
	copy(c.state[:], values)
	for i := len(values); i < bn254SpongeRate; i++ {
		c.state[i].SetZero()
	}
	var tag fr.Element
	tag.SetUint64(uint64(lengthTag))
	c.state[bn254SpongeRate].Add(&c.state[bn254SpongeRate], &tag)
	poseidon2Bn254Ref(&c.state)
	c.outBuf = append(c.outBuf[:0], c.state[:bn254SpongeRate]...)
}

// mfRefReducePacked packs ≤ 8 canonical BabyBear values into one BN254
// element: little-endian radix-2^31 (reduce_packed, helpers.rs:171).
func mfRefReducePacked(vals []uint32) fr.Element {
	acc := new(big.Int)
	for i := len(vals) - 1; i >= 0; i-- {
		acc.Lsh(acc, mfAbsorbRadixBits)
		acc.Add(acc, new(big.Int).SetUint64(uint64(vals[i])))
	}
	var e fr.Element
	e.SetBigInt(acc)
	return e
}

// mfRefSplitToFieldOrderLimbs splits one BN254 element into 7 little-endian
// base-p BabyBear limbs (split_pf_to_field_order_limbs, helpers.rs:338); the
// div-p^7 remainder is discarded, exactly as in the fork.
func mfRefSplitToFieldOrderLimbs(v fr.Element) []uint32 {
	rem := v.BigInt(new(big.Int))
	limbs := make([]uint32, mfSqueezeNumFElms)
	mod := new(big.Int)
	for i := range limbs {
		rem.DivMod(rem, bbPBig, mod)
		limbs[i] = uint32(mod.Uint64())
	}
	return limbs
}

func (c *multiFieldChallengerRef) flushFIfNonEmpty() {
	if len(c.fBuf) == 0 {
		return
	}
	nIn := len(c.fBuf)
	if nIn > mfAbsorbNumFElms*bn254SpongeRate {
		panic("multiFieldChallengerRef.flushFIfNonEmpty: pending buffer overflow")
	}
	var packed []fr.Element
	for start := 0; start < nIn; start += mfAbsorbNumFElms {
		end := min(start+mfAbsorbNumFElms, nIn)
		packed = append(packed, mfRefReducePacked(c.fBuf[start:end]))
	}
	c.absorbRatePaddedWithTag(packed, uint8(nIn))
	c.fBuf = c.fBuf[:0]
	c.fSqueezeBuf = c.fSqueezeBuf[:0]
}

// observeBabyBear mirrors multi_field_challenger.rs:150.
func (c *multiFieldChallengerRef) observeBabyBear(v uint32) {
	if uint64(v) >= BabyBearP {
		panic("multiFieldChallengerRef.observeBabyBear: non-canonical BabyBear value")
	}
	c.outBuf = c.outBuf[:0]
	c.fSqueezeBuf = c.fSqueezeBuf[:0]
	c.fBuf = append(c.fBuf, v)
	if len(c.fBuf) == mfAbsorbNumFElms*bn254SpongeRate {
		c.flushFIfNonEmpty()
	}
}

func (c *multiFieldChallengerRef) observeBabyBearSlice(vs []uint32) {
	for _, v := range vs {
		c.observeBabyBear(v)
	}
}

// observeBn254Digest mirrors multi_field_challenger.rs:181 (observe(Hash)).
func (c *multiFieldChallengerRef) observeBn254Digest(words []fr.Element) {
	c.outBuf = c.outBuf[:0]
	c.fSqueezeBuf = c.fSqueezeBuf[:0]
	c.flushFIfNonEmpty()
	for start := 0; start < len(words); start += bn254SpongeRate {
		end := min(start+bn254SpongeRate, len(words))
		chunk := words[start:end]
		c.absorbRatePaddedWithTag(chunk, uint8(len(chunk)))
		c.fSqueezeBuf = c.fSqueezeBuf[:0]
	}
}

// sampleBabyBear mirrors multi_field_challenger.rs:246: flush, refill from a
// duplexing if drained (splitting every rate cell in order), pop from the END.
func (c *multiFieldChallengerRef) sampleBabyBear() uint32 {
	c.flushFIfNonEmpty()
	if len(c.fSqueezeBuf) == 0 {
		if len(c.outBuf) == 0 {
			c.duplexing()
		}
		for _, pf := range c.outBuf {
			c.fSqueezeBuf = append(c.fSqueezeBuf, mfRefSplitToFieldOrderLimbs(pf)...)
		}
		c.outBuf = c.outBuf[:0]
	}
	n := len(c.fSqueezeBuf)
	v := c.fSqueezeBuf[n-1]
	c.fSqueezeBuf = c.fSqueezeBuf[:n-1]
	return v
}

// sampleBits mirrors multi_field_challenger.rs:277: low n bits of one
// canonical BabyBear sample; requires 2^n < p.
func (c *multiFieldChallengerRef) sampleBits(n int) uint64 {
	if n < 0 || uint64(1)<<uint(n) >= BabyBearP {
		panic("multiFieldChallengerRef.sampleBits: bit count out of range for BabyBear")
	}
	v := c.sampleBabyBear()
	return uint64(v) & ((uint64(1) << uint(n)) - 1)
}
