// THE QUERY SWEEP — the gnark half of the shrink blowup/queries tradeoff
// measurement (circuit-prove/tests/apex_shrink_blowup_sweep.rs).
//
// The shrink prover's FRI shape trades LDE size (log_blowup — the PROVE-side
// NTT + native-BN254 Merkle hashing of the whole LDE) against query count
// (the gnark VERIFY-side cost: one fold chain + one native Merkle walk per
// query). All candidate shapes hold the same 130-conjectured-bit bar
// (log_blowup·queries + query_pow ≥ 130). This test compiles VerifyFriNative
// at each candidate's shape and reports R1CS constraint counts, so each sweep
// row has BOTH sides measured.
//
// Shape convention — the SAME one TestWrapNativeHashConstraintMeasurement
// uses (fri_verify_native_test.go): the gadget is the single-round-set
// LogBlowup=0 scope, so R stands in for log_global_max_height =
// max_degree_bits + log_blowup (deepest Merkle path = R-1 levels). The
// measured shrink proof's max degree_bits is 12 (apex_shrink_bn254_tooth /
// the sweep), so R = 12 + log_blowup per setting. This convention slightly
// OVERSTATES the cost (it runs R fold rounds instead of max_degree_bits, and
// its Merkle paths sum a touch deeper) — conservative in the right direction
// for a "still Groth16-feasible?" check.
//
// Compilation only — no witness solving, so no PoW grind is needed.
package friverifier

import (
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

// shrinkMaxDegreeBits is the measured max degree_bits of the real shrink
// proof (circuit-prove sweep prints degree_bits per setting; the verifier
// circuit's tables are the same at every FRI shape, so this is one number).
const shrinkMaxDegreeBits = 12

func TestWrapNativeHashQuerySweep(t *testing.T) {
	const prefixLen = 9
	field := ecc.BN254.ScalarField()

	settings := []struct {
		label      string
		logBlowup  int
		numQueries int
		queryPow   int
	}{
		{"baseline (production)", 6, 19, 16},
		{"blowup 16", 4, 29, 16},
		{"blowup 8", 3, 38, 16},
		{"blowup 4", 2, 57, 16},
		{"blowup 4 + grind 20", 2, 55, 20},
	}

	t.Logf("%-22s %10s %8s %10s %6s %3s %14s", "label", "log_blowup", "queries", "query_pow", "bits", "R", "R1CS")
	for _, s := range settings {
		bits := s.logBlowup*s.numQueries + s.queryPow
		if bits < 130 {
			t.Fatalf("%s: %d conjectured bits < 130 — refuse to measure an unsound shape", s.label, bits)
		}
		// R stands in for log_global_max_height (LogBlowup 0 in the gadget's
		// single-round-set scope — same convention as the 19-query baseline
		// measurement, which used R=18 = 12 + 6).
		R := shrinkMaxDegreeBits + s.logBlowup
		cfg := FriConfig{QueryPowBits: s.queryPow, CommitPowBits: 0,
			ExtraQueryIndexBits: 0, LogBlowup: 0, LogFinalPolyLen: 0}

		start := time.Now()
		cs, err := frontend.Compile(field, r1cs.NewBuilder,
			allocFriVerifyNativeCircuit(R, prefixLen, s.numQueries, cfg, false))
		if err != nil {
			t.Fatalf("%s: compile failed: %v", s.label, err)
		}
		n := cs.GetNbConstraints()
		t.Logf("%-22s %10d %8d %10d %6d %3d %14d   (compiled in %s)",
			s.label, s.logBlowup, s.numQueries, s.queryPow, bits, R, n,
			time.Since(start).Round(time.Millisecond))

		// Groth16-feasibility bar for the sweep: every candidate must stay
		// well inside a provable Groth16 size (~5M R1CS for this component).
		if n >= 5_000_000 {
			t.Errorf("%s: %d R1CS ≥ 5M — this query count is NOT cheap enough to trade for", s.label, n)
		}
	}
}
