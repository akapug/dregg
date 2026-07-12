// Plain-Go (non-circuit) reference twin of the open_input gadget
// (stark_open_input.go): the input-batch Merkle verification
// (MerkleTreeMmcs::verify_batch, mmcs.rs:1052-1180) and the alpha-combination
// that turns the opened columns into the FRI reduced openings
// (fri/src/verifier.rs:524-618 at the pinned rev 82cfad73).
//
// The reduction here follows the pinned PER-COLUMN form (alpha_pow multiplied
// into every term, then advanced once per column) — deliberately NOT the
// gadget's Horner regrouping — so the ref/gadget parity tests on real data
// cross two independent evaluation orders of the same sum.
package friverifier

import (
	"fmt"
	"sort"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

// openInputBatchRef is one query's opening of one input round (host side).
type openInputBatchRef struct {
	rows [][]uint32
	path []fr.Element
}

// bbExtMulBaseConstRef returns c·a for a base constant c.
func bbExtMulBaseConstRef(c uint32, a bbExtRef) bbExtRef {
	var r bbExtRef
	for i := range r {
		r[i] = bbMulRef(c, a[i])
	}
	return r
}

// openInputBatchRootRef reconstructs the batch-tree root from one round's
// opened rows and path — the reference twin of verifyOpenInputBatchNative.
// index is the FULL query index (the reduced index is derived per the round's
// max height, verifier.rs:576-580).
func openInputBatchRootRef(
	round OpenInputRoundShape,
	opening openInputBatchRef,
	index uint64,
	logMax int,
) (fr.Element, error) {
	if len(opening.rows) != len(round.Matrices) {
		return fr.Element{}, fmt.Errorf("row count %d != %d matrices",
			len(opening.rows), len(round.Matrices))
	}
	for mi, row := range opening.rows {
		if len(row) != round.Matrices[mi].Width {
			return fr.Element{}, fmt.Errorf("matrix %d: row width %d != %d",
				mi, len(row), round.Matrices[mi].Width)
		}
		for _, v := range row {
			if uint64(v) >= BabyBearP {
				return fr.Element{}, fmt.Errorf("matrix %d: non-canonical opened value %d", mi, v)
			}
		}
	}
	groups := openInputHeightGroupsOf(round)
	maxLh := groups[0].logHeight
	if len(opening.path) != maxLh {
		return fr.Element{}, fmt.Errorf("path depth %d != tree height %d", len(opening.path), maxLh)
	}
	hashGroup := func(g openInputHeightGroup) fr.Element {
		var limbs []uint32
		for _, mi := range g.mats {
			limbs = append(limbs, opening.rows[mi]...)
		}
		return mfRefSpongeHash(limbs)
	}
	digest := hashGroup(groups[0])
	reduced := index >> uint(logMax-maxLh)
	next := 1
	for step := 0; step < maxLh; step++ {
		if reduced&1 == 0 {
			digest = poseidon2Bn254RefCompress(digest, opening.path[step])
		} else {
			digest = poseidon2Bn254RefCompress(opening.path[step], digest)
		}
		reduced >>= 1
		if next < len(groups) && groups[next].logHeight == maxLh-step-1 {
			digest = poseidon2Bn254RefCompress(digest, hashGroup(groups[next]))
			next++
		}
	}
	if next != len(groups) {
		return fr.Element{}, fmt.Errorf("unconsumed height groups")
	}
	return digest, nil
}

// openInputReducedRef derives the per-height reduced openings for one query —
// the reference twin of deriveOpenInputReducedNative in the PINNED per-column
// form (verifier.rs:600-616). openedAtZ is consumed sequentially in
// round/matrix/point/column order. Returns values aligned with
// openInputLogHeights(rounds) (descending).
func openInputReducedRef(
	rounds []OpenInputRoundShape,
	openings []openInputBatchRef,
	openedAtZ []bbExtRef,
	zeta, alpha bbExtRef,
	index uint64,
	logMax int,
) ([]bbExtRef, error) {
	if len(openings) != len(rounds) {
		return nil, fmt.Errorf("opening count %d != %d rounds", len(openings), len(rounds))
	}
	heights := openInputLogHeights(rounds)
	hIdx := map[int]int{}
	for i, h := range heights {
		hIdx[h] = i
	}
	ro := make([]bbExtRef, len(heights))
	alphaPow := make([]bbExtRef, len(heights))
	for i := range heights {
		alphaPow[i] = bbExtRef{1, 0, 0, 0}
	}
	pos := 0
	for ri, round := range rounds {
		for mi, m := range round.Matrices {
			// x = GENERATOR · g_lh^{rev_bits(index >> (logMax−lh), lh)}.
			revIdx := reverseBitsRef(uint(index>>uint(logMax-m.LogHeight)), m.LogHeight)
			x := bbMulRef(bbGenerator,
				bbPowRef(bbTwoAdicGeneratorRef(m.LogHeight), uint64(revIdx)))
			hi := hIdx[m.LogHeight]
			for pt := 0; pt < m.NumPoints; pt++ {
				z := zeta
				if pt == 1 {
					z = bbExtMulBaseConstRef(bbTwoAdicGeneratorRef(m.NextPointBits), zeta)
				}
				zmx := z
				zmx[0] = bbSubRef(z[0], x)
				qinv, err := bbExtInvRef(zmx)
				if err != nil {
					return nil, fmt.Errorf("z - x is zero (zeta collides with the domain)")
				}
				if pos+m.Width > len(openedAtZ) {
					return nil, fmt.Errorf("opened-values stream underflow")
				}
				pz := openedAtZ[pos : pos+m.Width]
				pos += m.Width
				px := openings[ri].rows[mi]
				for k := 0; k < m.Width; k++ {
					d := pz[k]
					d[0] = bbSubRef(pz[k][0], px[k])
					ro[hi] = bbExtAddRef(ro[hi], bbExtMulRef(alphaPow[hi], bbExtMulRef(d, qinv)))
					alphaPow[hi] = bbExtMulRef(alphaPow[hi], alpha)
				}
			}
		}
	}
	if pos != len(openedAtZ) {
		return nil, fmt.Errorf("opened-values stream not consumed exactly: %d of %d", pos, len(openedAtZ))
	}
	return ro, nil
}

// openInputVerifyQueryRef is the full host-side seam check for one query:
// every input batch's Merkle root matches its commitment, and the derived
// reduced openings equal the FRI fold seeds (initialEval + rollIns aligned
// with rollInRounds).
func openInputVerifyQueryRef(
	rounds []OpenInputRoundShape,
	roots []fr.Element,
	openings []openInputBatchRef,
	openedAtZ []bbExtRef,
	zeta, alpha bbExtRef,
	index uint64,
	logMax int,
	initialEval bbExtRef,
	rollIns []bbExtRef,
	rollInRounds []int,
) error {
	if len(roots) != len(rounds) {
		return fmt.Errorf("root count %d != %d rounds", len(roots), len(rounds))
	}
	for ri, round := range rounds {
		got, err := openInputBatchRootRef(round, openings[ri], index, logMax)
		if err != nil {
			return fmt.Errorf("input round %d: %v", ri, err)
		}
		if !got.Equal(&roots[ri]) {
			return fmt.Errorf("input round %d: Merkle root mismatch", ri)
		}
	}
	derived, err := openInputReducedRef(rounds, openings, openedAtZ, zeta, alpha, index, logMax)
	if err != nil {
		return err
	}
	heights := openInputLogHeights(rounds)
	sorted := []int{logMax}
	for _, r := range rollInRounds {
		sorted = append(sorted, logMax-r-1)
	}
	sort.Sort(sort.Reverse(sort.IntSlice(sorted)))
	if len(heights) != len(sorted) {
		return fmt.Errorf("derived %d heights, schedule has %d", len(heights), len(sorted))
	}
	for i := range heights {
		if heights[i] != sorted[i] {
			return fmt.Errorf("derived height set %v != schedule %v", heights, sorted)
		}
	}
	if derived[0] != initialEval {
		return fmt.Errorf("derived initial reduced opening %v != FRI seed %v", derived[0], initialEval)
	}
	if len(rollIns) != len(rollInRounds) {
		return fmt.Errorf("roll-in count mismatch")
	}
	for j, r := range rollInRounds {
		lh := logMax - r - 1
		var got bbExtRef
		found := false
		for i, h := range heights {
			if h == lh {
				got, found = derived[i], true
			}
		}
		if !found {
			return fmt.Errorf("no derived opening at roll-in height %d", lh)
		}
		if got != rollIns[j] {
			return fmt.Errorf("derived roll-in at height %d %v != FRI seed %v", lh, got, rollIns[j])
		}
	}
	return nil
}
