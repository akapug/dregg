// G1 MEASUREMENT HARNESS — THROWAWAY, NOT PRODUCTION.
//
// FRI-CUTOVER-PLAN.md Phase 1 / gate G1: measure what the proven-122.60
// (extension-degree-8) config costs, so ember can decide the FRI cutover.
//
// This file is a MEASUREMENT prototype, deliberately self-contained: a minimal
// degree-8 BabyBear-extension multiply kernel (BBExt8, ExtMul8) alongside the
// deployed degree-4 kernel, so the MARGINAL R1CS cost of the d² arithmetic can
// be measured at d=8 WITHOUT the full Phase-3 gnark rewrite (W1–W11).
//
// d=8 kernel ground truth: BabyBear[X]/(X^8 - 11), W = 11 (d=8 keeps W=11,
// PROVEN-120 §6). Schoolbook multiply with wraparound X^8 = 11:
//
//	c_k = Σ_{i+j=k} a_i·b_j  +  W · Σ_{i+j=k+8} a_i·b_j      (k = 0..7)
//
// Widest accumulation is c_0 = a0b0 + W·(a1b7+…+a7b1): 1 + 11·7 = 78 raw
// products each < 2^62 ⟹ < 78·2^62 < 2^69, so ReduceBounded(·, 69) per coeff
// (boundBits(8) = 62 + ⌈log₂(1 + 11·7)⌉ = 62 + 7 = 69, PROVEN-120 §4.2).
//
// Run:  cd chain/gnark && DREGG_G1=1 go test -run TestG1 -v -timeout 60m
package friverifier

import (
	"os"
	"testing"

	"github.com/consensys/gnark/frontend"
)

// BBExt8 is a degree-8 extension element, coefficients little-endian in X.
type BBExt8 [8]frontend.Variable

// ExtMul8 returns a·b in BabyBear[X]/(X^8 - 11), schoolbook with X^8 = 11.
func (bb *BBApi) ExtMul8(a, b BBExt8) BBExt8 {
	api := bb.api
	var p [8][8]frontend.Variable
	for i := 0; i < 8; i++ {
		for j := 0; j < 8; j++ {
			p[i][j] = api.Mul(a[i], b[j])
		}
	}
	sum := func(vs []frontend.Variable) frontend.Variable {
		switch len(vs) {
		case 0:
			return frontend.Variable(0)
		case 1:
			return vs[0]
		default:
			return api.Add(vs[0], vs[1], vs[2:]...)
		}
	}
	var r BBExt8
	for k := 0; k < 8; k++ {
		// low part: i+j == k  (i = 0..k, always ≥1 term since k≥0)
		low := make([]frontend.Variable, 0, 8)
		for i := 0; i <= k; i++ {
			low = append(low, p[i][k-i])
		}
		// high part: i+j == k+8  (i = k+1..7), folded by W
		high := make([]frontend.Variable, 0, 8)
		for i := k + 1; i < 8; i++ {
			high = append(high, p[i][k+8-i])
		}
		acc := sum(low)
		if len(high) > 0 {
			acc = api.Add(acc, api.Mul(BBExtW, sum(high)))
		}
		r[k] = bb.ReduceBounded(acc, 69)
	}
	return r
}

func (bb *BBApi) ExtAdd8(a, b BBExt8) BBExt8 {
	var r BBExt8
	for i := range r {
		r[i] = bb.Add(a[i], b[i])
	}
	return r
}

func (bb *BBApi) ExtAssertIsEqual8(a, b BBExt8) {
	for i := range a {
		bb.api.AssertIsEqual(a[i], b[i])
	}
}

// ext8OpChainCircuit mirrors extOpChainCircuit (settlement_profile_test.go) at
// d=8: n chained ExtMul8/ExtAdd8, so the marginal R1CS/op is (hi−lo)-scaled and
// the fixed rangecheck-table costs cancel in the subtraction.
type ext8OpChainCircuit struct {
	op   string
	n    int
	A, B BBExt8
}

func (c *ext8OpChainCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	x := c.A
	for i := 0; i < c.n; i++ {
		switch c.op {
		case "mul":
			x = bb.ExtMul8(x, c.B)
		case "add":
			x = bb.ExtAdd8(x, c.B)
		}
	}
	bb.ExtAssertIsEqual8(x, c.B)
	return nil
}

// TestG1MarginalExtMul measures the marginal R1CS/op of ExtMul at d=4 (must
// reproduce the deployed 92, validating the harness) and d=8 (the number the
// gate estimate rides on). Same chained-delta method as
// TestSettlementGadgetMarginalCosts.
func TestG1MarginalExtMul(t *testing.T) {
	if os.Getenv("DREGG_G1") == "" {
		t.Skip("G1 measurement; run with DREGG_G1=1")
	}
	marginal := func(name string, mk func(n int) frontend.Circuit) float64 {
		t.Helper()
		lo, hi := 64, 192
		a := compileCount(t, mk(lo))
		b := compileCount(t, mk(hi))
		m := float64(b-a) / float64(hi-lo)
		t.Logf("%-24s marginal %.2f R1CS/op   (compile lo=%d:%d hi=%d:%d)", name, m, lo, a, hi, b)
		return m
	}
	d4 := marginal("d=4 ExtMul (deployed)", func(n int) frontend.Circuit {
		return &extOpChainCircuit{op: "mul", n: n}
	})
	d8 := marginal("d=8 ExtMul (candidate)", func(n int) frontend.Circuit {
		return &ext8OpChainCircuit{op: "mul", n: n}
	})
	d4add := marginal("d=4 ExtAdd (deployed)", func(n int) frontend.Circuit {
		return &extOpChainCircuit{op: "add", n: n}
	})
	d8add := marginal("d=8 ExtAdd (candidate)", func(n int) frontend.Circuit {
		return &ext8OpChainCircuit{op: "add", n: n}
	})
	t.Logf("=== G1 marginal ratios ===")
	t.Logf("ExtMul d=8/d=4 = %.3f  (PROVEN-120 expects ~2.35x)", d8/d4)
	t.Logf("ExtAdd d=8/d=4 = %.3f  (expected ~2.0x, coefficient-wise)", d8add/d4add)
}
