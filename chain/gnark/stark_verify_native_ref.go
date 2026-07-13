// Plain-Go reference twin of the batch-STARK algebra layer
// (stark_verify_native.go) — the same slicing, selectors, quotient
// recomposition, LogUp folding and identity checks over uint32 BabyBear,
// used to validate the layer against the real fixture before circuit
// solving, and to derive the heavy instances' witnessed folded values.
package friverifier

import (
	"errors"
	"fmt"
	"math/big"
)

// bbExtFromBasisRef mirrors ExtFromBasisCoefficients.
func bbExtFromBasisRef(c [4]bbExtRef) bbExtRef {
	x := bbExtRef{0, 1, 0, 0}
	acc := bbExtRef{}
	pow := bbExtRef{1, 0, 0, 0}
	for k := 0; k < 4; k++ {
		acc = bbExtAddRef(acc, bbExtMulRef(c[k], pow))
		pow = bbExtMulRef(pow, x)
	}
	return acc
}

func bbExtExpPow2Ref(a bbExtRef, k int) bbExtRef {
	r := a
	for i := 0; i < k; i++ {
		r = bbExtMulRef(r, r)
	}
	return r
}

func bbExtScaleBaseRef(s uint32, a bbExtRef) bbExtRef {
	var r bbExtRef
	for i := range r {
		r[i] = bbMulRef(s, a[i])
	}
	return r
}

// bbExtInvRef inverts in BabyBear[X]/(X^4-11) by Fermat: a^(p^4 - 2).
func bbExtInvRef(a bbExtRef) (bbExtRef, error) {
	if a == (bbExtRef{}) {
		return bbExtRef{}, errors.New("bbExtInvRef: zero has no inverse")
	}
	p := new(big.Int).SetUint64(BabyBearP)
	exp := new(big.Int).Exp(p, big.NewInt(4), nil)
	exp.Sub(exp, big.NewInt(2))
	r := bbExtRef{1, 0, 0, 0}
	for i := exp.BitLen() - 1; i >= 0; i-- {
		r = bbExtMulRef(r, r)
		if exp.Bit(i) == 1 {
			r = bbExtMulRef(r, a)
		}
	}
	return r, nil
}

// starkSelectorsRef mirrors computeStarkSelectorsNative.
type starkSelectorsRef struct {
	zetaPow2Db, zH, isFirstRow, isLastRow, isTransition bbExtRef
}

func computeStarkSelectorsRef(zeta bbExtRef, db int) (starkSelectorsRef, error) {
	one := bbExtRef{1, 0, 0, 0}
	gInv := bbInvRef(bbTwoAdicGeneratorRef(db))
	e := bbExtExpPow2Ref(zeta, db)
	zh := bbExtSubRef(e, one)
	trans := bbExtSubRef(zeta, bbExtRef{gInv, 0, 0, 0})
	invZm1, err := bbExtInvRef(bbExtSubRef(zeta, one))
	if err != nil {
		return starkSelectorsRef{}, err
	}
	invTrans, err := bbExtInvRef(trans)
	if err != nil {
		return starkSelectorsRef{}, err
	}
	return starkSelectorsRef{
		zetaPow2Db:   e,
		zH:           zh,
		isFirstRow:   bbExtMulRef(zh, invZm1),
		isLastRow:    bbExtMulRef(zh, invTrans),
		isTransition: trans,
	}, nil
}

func recomposeQuotientRef(zetaPow2Db bbExtRef, chunks [][4]bbExtRef, dc quotientDomainConsts) bbExtRef {
	one := bbExtRef{1, 0, 0, 0}
	zAt := make([]bbExtRef, len(chunks))
	for j := range chunks {
		zAt[j] = bbExtSubRef(bbExtScaleBaseRef(dc.kPow[j], zetaPow2Db), one)
	}
	acc := bbExtRef{}
	for i := range chunks {
		zps := bbExtRef{dc.zpsConst[i], 0, 0, 0}
		for j := range chunks {
			if j != i {
				zps = bbExtMulRef(zps, zAt[j])
			}
		}
		acc = bbExtAddRef(acc, bbExtMulRef(zps, bbExtFromBasisRef(chunks[i])))
	}
	return acc
}

func evalWitnessBusFoldedRef(
	sel starkSelectorsRef,
	alphaFold, alphaCh, betaCh bbExtRef,
	elems []bbExtRef, mult bbExtRef,
	sLocal, sNext, cum bbExtRef,
) bbExtRef {
	combined := elems[0]
	for k := 1; k < len(elems); k++ {
		combined = bbExtAddRef(elems[k], bbExtMulRef(combined, betaCh))
	}
	denom := bbExtSubRef(alphaCh, combined)

	c1 := bbExtMulRef(sel.isFirstRow, sLocal)
	c2 := bbExtMulRef(sel.isTransition,
		bbExtSubRef(bbExtMulRef(bbExtSubRef(sNext, sLocal), denom), mult))
	c3 := bbExtMulRef(sel.isLastRow,
		bbExtSubRef(bbExtMulRef(bbExtSubRef(cum, sLocal), denom), mult))

	folded := c1
	folded = bbExtAddRef(bbExtMulRef(folded, alphaFold), c2)
	folded = bbExtAddRef(bbExtMulRef(folded, alphaFold), c3)
	return folded
}

// shrinkStarkChallengesRef mirrors ShrinkStarkChallenges.
type shrinkStarkChallengesRef struct {
	permAlpha, permBeta, alpha, zeta bbExtRef
}

// verifyShrinkStarkAlgebraRef runs the host twin of VerifyShrinkStarkAlgebra
// over the real opened data: EVERY instance's folded constraints are
// evaluated by the symbolic interpreter (public values substituted into the
// DAG's `pub` leaves) and the quotient identity is a REAL check for all 6,
// plus the global cumulative-sum balance.
//
// The former `sym == nil` hand mode (heavy instances DERIVED, not checked)
// was removed — see VerifyShrinkStarkAlgebra. `sym` is required.
func verifyShrinkStarkAlgebraRef(
	shapes []StarkInstanceShape,
	openedEF []bbExtRef,
	cumSums []bbExtRef,
	pubVals [][]uint32,
	ch shrinkStarkChallengesRef,
	sym *SymbolicConstraints,
) error {
	if len(shapes) != ShrinkNumInstances {
		return errors.New("shrink scope is exactly 6 instances")
	}
	if sym == nil {
		return errors.New("emitted symbolic constraints are required (no hand fallback)")
	}
	if len(sym.Instances) != len(shapes) {
		return errors.New("symbolic constraint file instance count mismatch")
	}
	if len(pubVals) != len(shapes) {
		return errors.New("public-value stream instance count mismatch")
	}
	spans, totalEF := buildStarkOpenedSpans(shapes)
	if len(openedEF) != totalEF {
		return fmt.Errorf("opened-values stream has %d EF values, shape requires %d",
			len(openedEF), totalEF)
	}
	if want := totalGlobalLookups(shapes); len(cumSums) != want {
		return fmt.Errorf("cumulative-sums stream has %d values, shape requires %d",
			len(cumSums), want)
	}

	slice := func(s efSpan) []bbExtRef { return openedEF[s.off : s.off+s.len] }

	for i, sh := range shapes {
		sp := spans[i]
		sel, serr := computeStarkSelectorsRef(ch.zeta, sh.DegreeBits)
		if serr != nil {
			return fmt.Errorf("instance %d selectors: %w", i, serr)
		}

		chunks := make([][4]bbExtRef, len(sp.quotientChunks))
		for c, qs := range sp.quotientChunks {
			copy(chunks[c][:], slice(qs))
		}
		quotient := recomposeQuotientRef(sel.zetaPow2Db, chunks,
			shrinkQuotientDomainConsts(sh.DegreeBits, sh.NumQuotientChunks))
		rhs := bbExtMulRef(quotient, sel.zH)

		inst := &sym.Instances[i]
		if inst.Width != sh.Width || inst.PreWidth != sh.PreWidth ||
			inst.NumLookups != sh.NumLookups || inst.NumPublicValues != sh.NumPublicValues {
			return fmt.Errorf("instance %d: emitted constraint shape drifted", i)
		}
		if len(pubVals[i]) != sh.NumPublicValues {
			return fmt.Errorf("instance %d: %d public values, shape requires %d",
				i, len(pubVals[i]), sh.NumPublicValues)
		}
		folded, ferr := evalSymbolicFoldedRef(inst,
			shrinkSymInputsRef(sh, sp, slice, cumSums, pubVals[i], ch, sel), ch.alpha)
		if ferr != nil {
			return fmt.Errorf("instance %d: symbolic eval: %w", i, ferr)
		}
		if folded != rhs {
			return fmt.Errorf(
				"instance %d (%s): quotient identity FAILED with interpreted constraints "+
					"(folded %v != quotient*Z_H %v)", i, inst.Name, folded, rhs)
		}
	}

	sum := bbExtRef{}
	for _, cs := range cumSums {
		sum = bbExtAddRef(sum, cs)
	}
	if sum != (bbExtRef{}) {
		return fmt.Errorf("global WitnessChecks cumulative sums do not balance: %v", sum)
	}
	return nil
}

// shrinkSymInputsRef mirrors shrinkSymInputsNative.
func shrinkSymInputsRef(
	sh StarkInstanceShape,
	sp starkInstanceSpans,
	slice func(efSpan) []bbExtRef,
	cumSums []bbExtRef,
	pubVals []uint32,
	ch shrinkStarkChallengesRef,
	sel starkSelectorsRef,
) symEvalInputsRef {
	recompose := func(flat []bbExtRef) []bbExtRef {
		out := make([]bbExtRef, len(flat)/4)
		for c := range out {
			out[c] = bbExtFromBasisRef([4]bbExtRef(flat[4*c : 4*c+4]))
		}
		return out
	}
	in := symEvalInputsRef{
		TraceLocal: slice(sp.traceLocal),
		PreLocal:   slice(sp.preLocal),
		PermLocal:  recompose(slice(sp.permLocal)),
		PermNext:   recompose(slice(sp.permNext)),
		PermValues: cumSums[sp.cumSums.off : sp.cumSums.off+sp.cumSums.len],
		Sel:        sel,
	}
	if sh.NumPublicValues > 0 {
		in.PublicValues = make([]bbExtRef, len(pubVals))
		for k, v := range pubVals {
			in.PublicValues[k] = bbExtRef{v, 0, 0, 0}
		}
	}
	if sh.HasTraceNext {
		in.TraceNext = slice(sp.traceNext)
	}
	if sh.HasPreNext {
		in.PreNext = slice(sp.preNext)
	}
	in.Challenges = make([]bbExtRef, 2*sh.NumLookups)
	for l := 0; l < sh.NumLookups; l++ {
		in.Challenges[2*l] = ch.permAlpha
		in.Challenges[2*l+1] = ch.permBeta
	}
	return in
}
