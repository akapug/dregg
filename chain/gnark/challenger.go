// Fiat-Shamir DuplexChallenger as a gnark circuit gadget — the load-bearing
// soundness component of the native ETH-wrap FRI verifier. Every challenge the
// in-circuit verifier draws (the FRI folding betas, the DEEP/quotient alpha and
// zeta, and the query indices) is squeezed here, so this gadget MUST reproduce
// the exact byte stream of the Rust p3_challenger::DuplexChallenger<BabyBear,
// Poseidon2BabyBear<16>, WIDTH=16, RATE=8> at the workspace-pinned Plonky3 rev
// 82cfad73cd734d37a0d51953094f970c531817ec. A divergence is a silent soundness
// break: the circuit would draw different query positions / betas than the Rust
// verifier and accept proofs Rust rejects.
//
// Semantics are pinned lane-for-lane to challenger/src/duplex_challenger.rs at
// that rev (line cites in challenger_ref.go, the plain-Go twin this gadget is
// differentially tested against). The sponge permutation is Poseidon2W16
// (poseidon2_w16.go), which asserts its inputs canonical at the gadget boundary.
package friverifier

import "github.com/consensys/gnark/frontend"

// Challenger is the in-circuit duplex sponge (rate 8, width 16, capacity 8).
// A fresh challenger holds sponge_state = [0; 16]. Field elements flowing
// through it are canonical BabyBear variables.
type Challenger struct {
	bb     *BBApi
	state  [spongeWidth]frontend.Variable
	inBuf  []frontend.Variable
	outBuf []frontend.Variable
}

// NewChallenger builds a fresh challenger over the given BabyBear gadget
// context (sponge_state = [0; 16], empty input/output buffers).
func NewChallenger(bb *BBApi) *Challenger {
	c := &Challenger{bb: bb}
	for i := range c.state {
		c.state[i] = frontend.Variable(0)
	}
	return c
}

// duplexing mirrors duplex_challenger.rs:86: the buffered inputs OVERWRITE
// state[0..len(inBuf)] (capacity lanes carry over), the width-16 permutation is
// applied, and the output buffer is refilled from state[0..RATE]. Poseidon2W16
// asserts every state lane canonical, which is the fail-closed ingestion point
// for absorbed witness values.
func (c *Challenger) duplexing() {
	if len(c.inBuf) > spongeRate {
		panic("Challenger.duplexing: input buffer overflow")
	}
	for i, v := range c.inBuf {
		c.state[i] = v
	}
	c.inBuf = c.inBuf[:0]
	c.bb.Poseidon2W16(&c.state)
	c.outBuf = c.outBuf[:0]
	c.outBuf = append(c.outBuf, c.state[:spongeRate]...)
}

// Observe absorbs one field element (duplex_challenger.rs:148): stale output is
// dropped, the value is buffered, and a full rate triggers a duplexing. The
// value is asserted canonical at the boundary (fail-closed ingestion).
func (c *Challenger) Observe(v frontend.Variable) {
	c.bb.AssertIsCanonical(v)
	c.outBuf = c.outBuf[:0] // any buffered output is now stale
	c.inBuf = append(c.inBuf, v)
	if len(c.inBuf) == spongeRate {
		c.duplexing()
	}
}

// ObserveSlice absorbs a run of elements in order (CanObserve<[F; N]>).
func (c *Challenger) ObserveSlice(vs []frontend.Variable) {
	for _, v := range vs {
		c.Observe(v)
	}
}

// ObserveExt absorbs a degree-4 extension element as its four base coefficients
// in order (observe_algebra_element: coefficient 0 first).
func (c *Challenger) ObserveExt(e BBExt) {
	for i := range e {
		c.Observe(e[i])
	}
}

// Sample squeezes one base-field challenge (duplex_challenger.rs:235): duplex if
// there is pending input or the output buffer is drained, then pop from the END
// of the output buffer. The result is a canonical BabyBear variable.
func (c *Challenger) Sample() frontend.Variable {
	if len(c.inBuf) > 0 || len(c.outBuf) == 0 {
		c.duplexing()
	}
	n := len(c.outBuf)
	v := c.outBuf[n-1]
	c.outBuf = c.outBuf[:n-1]
	return v
}

// SampleExt squeezes a degree-4 extension challenge: four base samples, the
// first popped becoming coefficient 0 (sample_algebra_element, X^4 = 11).
// Mirrored by the recursion fork's in-circuit challenger
// (recursion/src/challenger/circuit.rs:354).
func (c *Challenger) SampleExt() BBExt {
	var e BBExt
	for i := range e {
		e[i] = c.Sample()
	}
	return e
}

// SampleBits draws an n-bit query index (duplex_challenger.rs:264): one base
// sample reduced to its low n bits. Returned as a single canonical variable
// equal to sample & (2^n - 1); the caller obtains a value in [0, 2^n). This is
// the CanSampleBits path the FRI query phase uses (fri/src/verifier.rs:268), NOT
// the rejection-sampled sample_uniform_bits.
//
// n must satisfy 2^n < p (BabyBear has 31 bits; the largest power of two below
// p is 2^30). The base sample is < p < 2^31, so a 31-bit decomposition is exact
// and the low-n reconstruction is unique.
func (c *Challenger) SampleBits(n int) frontend.Variable {
	if n < 0 || uint64(1)<<uint(n) >= BabyBearP {
		panic("Challenger.SampleBits: bit count out of range for BabyBear")
	}
	base := c.Sample()
	if n == 0 {
		return frontend.Variable(0)
	}
	bits := c.bb.api.ToBinary(base, 31) // exact: base < p < 2^31
	return c.bb.api.FromBinary(bits[:n]...)
}

// SampleBitsDecomposed is SampleBits returning the low n bits individually (each
// a boolean variable), for callers that consume the query index bit-by-bit
// (e.g. Merkle path index steering). bits[0] is the least-significant bit.
func (c *Challenger) SampleBitsDecomposed(n int) []frontend.Variable {
	if n < 0 || uint64(1)<<uint(n) >= BabyBearP {
		panic("Challenger.SampleBitsDecomposed: bit count out of range for BabyBear")
	}
	base := c.Sample()
	if n == 0 {
		return nil
	}
	bits := c.bb.api.ToBinary(base, 31)
	return bits[:n]
}
