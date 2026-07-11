// Plain-Go (non-circuit) reference of the Fiat-Shamir DuplexChallenger the
// dregg verifier drives during whole-history FRI verification. The circuit
// gadget in challenger.go is differentially tested against this, and this is
// pinned byte-for-byte against the Rust-emitted fixtures/transcript_w16.json.
//
// Ground truth is p3_challenger::DuplexChallenger<BabyBear, Poseidon2BabyBear<16>,
// WIDTH=16, RATE=8> at the workspace-pinned Plonky3 rev
// 82cfad73cd734d37a0d51953094f970c531817ec:
//
//   - challenger/src/duplex_challenger.rs:86  duplexing():  the buffered inputs
//     OVERWRITE sponge_state[0..len(inBuf)] (capacity untouched), the width-16
//     permutation is applied, then output_buffer = sponge_state[0..RATE].
//   - duplex_challenger.rs:148 observe(): clear the output buffer (any buffered
//     output is now stale), push the value into the input buffer, and when RATE
//     inputs are buffered, duplex.
//   - duplex_challenger.rs:235 sample() (CanSample, base field EF=F): duplex iff
//     the input buffer is non-empty OR the output buffer is empty, then POP FROM
//     THE END of the output buffer.
//   - duplex_challenger.rs:264 sample_bits(): let rand_f = self.sample();
//     rand_f.as_canonical_u64() as usize & ((1 << bits) - 1)  — one base sample,
//     take its low `bits` bits. This is the CanSampleBits impl the FRI query
//     phase uses (fri/src/verifier.rs:268 challenger.sample_bits(...)).
//   - sample_ext() = FieldChallenger::sample_algebra_element = D base samples
//     recomposed as extension coefficients 0..D-1 in order (the first pop is
//     coefficient 0). D=4 here (X^4 = 11). Confirmed by the recursion fork's
//     in-circuit mirror recursion/src/challenger/circuit.rs:354-362.
package friverifier

const (
	spongeWidth = 16
	spongeRate  = 8
)

// challengerRef is the native-Go DuplexChallenger reference (rate 8, width 16,
// capacity 8). A fresh challenger starts with sponge_state = [0; 16].
type challengerRef struct {
	state  [spongeWidth]uint32
	inBuf  []uint32
	outBuf []uint32
}

func newChallengerRef() *challengerRef { return &challengerRef{} }

// duplexing mirrors duplex_challenger.rs:86: overwrite state[0..len(inBuf)] with
// the buffered inputs, drain the input buffer, permute, refill the output buffer
// from state[0..RATE].
func (c *challengerRef) duplexing() {
	if len(c.inBuf) > spongeRate {
		panic("challengerRef.duplexing: input buffer overflow")
	}
	copy(c.state[:], c.inBuf)
	c.inBuf = c.inBuf[:0]
	poseidon2W16Ref(&c.state)
	c.outBuf = append(c.outBuf[:0], c.state[:spongeRate]...)
}

// observe absorbs one field element (duplex_challenger.rs:148).
func (c *challengerRef) observe(v uint32) {
	c.outBuf = c.outBuf[:0] // any buffered output is now stale
	c.inBuf = append(c.inBuf, v)
	if len(c.inBuf) == spongeRate {
		c.duplexing()
	}
}

// observeSlice absorbs a run of elements in order (CanObserve<[F; N]>).
func (c *challengerRef) observeSlice(vs []uint32) {
	for _, v := range vs {
		c.observe(v)
	}
}

// sample squeezes one base-field challenge (duplex_challenger.rs:235): duplex if
// there is pending input or the output buffer is drained, then pop from the end.
func (c *challengerRef) sample() uint32 {
	if len(c.inBuf) > 0 || len(c.outBuf) == 0 {
		c.duplexing()
	}
	v := c.outBuf[len(c.outBuf)-1]
	c.outBuf = c.outBuf[:len(c.outBuf)-1]
	return v
}

// sampleExt squeezes a degree-4 extension challenge: four base samples, the
// first popped becoming coefficient 0 (sample_algebra_element / X^4 = 11).
func (c *challengerRef) sampleExt() bbExtRef {
	var e bbExtRef
	for i := range e {
		e[i] = c.sample()
	}
	return e
}

// sampleBits draws a query index: one base sample reduced to its low n bits
// (duplex_challenger.rs:264). n must satisfy 2^n < p; the FRI query phase always
// calls it with n = log2(domain) + extra_query_index_bits ≤ 31.
func (c *challengerRef) sampleBits(n int) uint {
	if n < 0 || n >= 31 || uint64(1)<<uint(n) >= BabyBearP {
		panic("challengerRef.sampleBits: bit count out of range for BabyBear")
	}
	v := uint64(c.sample())
	return uint(v & ((uint64(1) << uint(n)) - 1))
}
