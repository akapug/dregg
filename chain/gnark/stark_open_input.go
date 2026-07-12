// THE LAST SOUNDNESS SEAM of the native STARK verify: open_input — the
// in-circuit derivation of the FRI reduced openings from the COMMITTED
// columns, binding the opened-values-at-zeta (which the STARK-algebra layer
// consumes, stark_verify_native.go) to the trace/quotient/preprocessed/
// permutation COMMITMENTS.
//
// Ground truth (pinned Plonky3 rev 82cfad73, ~/.cargo/git/checkouts/
// plonky3-7d8a3b21a665a86f/82cfad7):
//
//   - fri/src/verifier.rs:524-618 open_input: per query, verify each input
//     batch's Merkle opening against its round commitment
//     (input_mmcs.verify_batch, :591-598), then combine the opened rows into
//     per-height reduced openings: for each matrix (batch order), each
//     opening point z, each column k,
//         ro[log_height] += alpha_pow · (p(z) − p(x)) / (z − x),
//         alpha_pow      *= alpha                        (:600-616)
//     with x = GENERATOR · g_lh^{rev_bits(index >> (logMax−lh), lh)}
//     (:552-556) — the LDE evaluation point the query indexes.
//   - merkle-tree/src/mmcs.rs:1052-1180 verify_batch (the multi-height batch
//     tree): matrices sorted tallest-first (STABLE, so batch order survives
//     within a height, :1065-1069); the leaf digest hashes ALL rows at the
//     max height concatenated (hash_iter_slices, :1100-1104); one arity-2
//     compression per level with the sibling from the proof (:1128-1141);
//     when the walk reaches a height that carries more matrices, their row
//     hash is INJECTED via an extra compression digest = C(digest, rowsHash)
//     that consumes NO path node and NO index bit (:1146-1167); the final
//     digest must equal the committed root (cap height 0: one root).
//   - The row hash is the SAME MultiField32PaddingFreeSponge as the FRI
//     commit-phase leaves (multiField32HashNative, fri_verify_native.go) —
//     here over the concatenation of all opened rows at one height, which
//     exercises the multi-block absorb path (widths up to 388 base values).
//
// The derived reduced openings are asserted EQUAL to the fold seeds
// (InitialEval / RollIns) that VerifyFriNative consumes, so a prover cannot
// supply openings consistent with the transcript but not with the committed
// trace: the seeds are now commitment-bound, not witnessed.
//
// Alpha-combination rewrite (algebraic identity, not a semantic change): the
// pinned loop multiplies alpha_pow into every column term; here each
// (matrix, point) block is evaluated as
//
//	alpha_pow · qinv · Σ_k alpha^k·(p(z)_k − p(x)_k)   [Horner in alpha]
//
// followed by alpha_pow *= alpha^width — the same sum with one ExtMul per
// column instead of three. The host reference twin (stark_open_input_ref.go)
// implements the pinned per-column form, so the parity tests cross the two
// evaluation orders on real data.
package friverifier

import (
	"sort"

	"github.com/consensys/gnark/frontend"
)

// ============================================================================
// Structural shapes (VK-side; mirrored from apex_shrink_gnark_export.rs)
// ============================================================================

// OpenInputMatrixShape is one committed matrix's shape inside a PCS input
// round: the log2 of its LDE height, its opened width, its opening-point
// count (1 = zeta only, 2 = zeta then zeta_next), and — for two points — the
// log2 trace-domain size whose subgroup generator advances zeta to zeta_next
// (domain.rs:169 next_point).
type OpenInputMatrixShape struct {
	LogHeight     int
	Width         int
	NumPoints     int
	NextPointBits int
}

// OpenInputRoundShape is one input round's matrices, in verify_batch's
// coms_to_verify order — the SAME order the opened-values-at-zeta stream
// flattens in (buildStarkOpenedSpans), so the alpha-combination consumes that
// stream sequentially.
type OpenInputRoundShape struct {
	Matrices []OpenInputMatrixShape
}

// OpenInputBatchOpening is one query's opening of one input round: the opened
// rows at the query point (one per matrix, batch order) and the native Merkle
// path (bottom-up, max(LogHeight) levels; lower matrices inject via row
// hashes, not path nodes).
type OpenInputBatchOpening struct {
	Rows [][]frontend.Variable
	Path []frontend.Variable
}

// BuildExpectedInputRounds derives the input-round structure from the pinned
// instance shapes — the projection of buildStarkOpenedSpans' accounting onto
// the PCS batch structure (trace, quotient, preprocessed, permutation). The
// caller cross-checks this against the exporter-emitted structure: any drift
// (a preprocessed matrix at a different degree, a reordered round) is
// fail-closed at fixture load, before anything reaches the circuit.
func BuildExpectedInputRounds(shapes []StarkInstanceShape, logBlowup int) []OpenInputRoundShape {
	var trace, quot, pre, perm []OpenInputMatrixShape
	for _, sh := range shapes {
		lh := sh.DegreeBits + logBlowup
		np, nb := 1, 0
		if sh.HasTraceNext {
			np, nb = 2, sh.DegreeBits
		}
		trace = append(trace, OpenInputMatrixShape{lh, sh.Width, np, nb})
		for c := 0; c < sh.NumQuotientChunks; c++ {
			quot = append(quot, OpenInputMatrixShape{lh, 4, 1, 0})
		}
		if sh.PreWidth > 0 {
			np, nb = 1, 0
			if sh.HasPreNext {
				np, nb = 2, sh.DegreeBits
			}
			pre = append(pre, OpenInputMatrixShape{lh, sh.PreWidth, np, nb})
		}
		if sh.NumLookups > 0 {
			perm = append(perm, OpenInputMatrixShape{lh, 4 * sh.NumLookups, 2, sh.DegreeBits})
		}
	}
	return []OpenInputRoundShape{{trace}, {quot}, {pre}, {perm}}
}

// openInputHeightGroup is one height class of a round's matrices, in batch
// order (the stable tallest-first sort of mmcs.rs:1065-1069).
type openInputHeightGroup struct {
	logHeight int
	mats      []int
}

// openInputHeightGroupsOf groups a round's matrices by LogHeight descending.
// Fail-closed structural panics: an empty round or a non-power-of-two-
// compatible height set is a circuit-construction bug, not a witness.
func openInputHeightGroupsOf(round OpenInputRoundShape) []openInputHeightGroup {
	if len(round.Matrices) == 0 {
		panic("openInputHeightGroupsOf: empty input round")
	}
	byH := map[int][]int{}
	var hs []int
	for mi, m := range round.Matrices {
		if _, ok := byH[m.LogHeight]; !ok {
			hs = append(hs, m.LogHeight)
		}
		byH[m.LogHeight] = append(byH[m.LogHeight], mi)
	}
	sort.Sort(sort.Reverse(sort.IntSlice(hs)))
	groups := make([]openInputHeightGroup, len(hs))
	for i, h := range hs {
		groups[i] = openInputHeightGroup{h, byH[h]}
	}
	return groups
}

// openInputLogHeights returns the distinct LogHeights across ALL rounds,
// descending — the reduced-opening keys (the BTreeMap of verifier.rs:547).
func openInputLogHeights(rounds []OpenInputRoundShape) []int {
	seen := map[int]bool{}
	var hs []int
	for _, r := range rounds {
		for _, m := range r.Matrices {
			if !seen[m.LogHeight] {
				seen[m.LogHeight] = true
				hs = append(hs, m.LogHeight)
			}
		}
	}
	sort.Sort(sort.Reverse(sort.IntSlice(hs)))
	return hs
}

// ============================================================================
// Per-circuit precomputation (query-independent)
// ============================================================================

// openInputPrecomp carries the query-independent derived values: zeta_next
// per generator-bits (zeta · g_bits, an ext × base-constant product) and
// alpha^width per distinct width (the per-(matrix,point) alpha_pow advance).
type openInputPrecomp struct {
	zeta, alpha        BBExt
	zetaNext           map[int]BBExt
	alphaPowW          map[int]BBExt
	logGlobalMaxHeight int
}

// extPowConst returns a^e for a variable ext element and a fixed exponent
// (square-and-multiply; e ≥ 1).
func extPowConst(bb *BBApi, a BBExt, e int) BBExt {
	if e < 1 {
		panic("extPowConst: exponent must be >= 1")
	}
	// Highest bit first.
	top := 0
	for 1<<(top+1) <= e {
		top++
	}
	r := a
	for i := top - 1; i >= 0; i-- {
		r = bb.ExtMul(r, r)
		if e&(1<<i) != 0 {
			r = bb.ExtMul(r, a)
		}
	}
	return r
}

// NewOpenInputPrecomp builds the shared derivation context. zeta and alpha
// are the transcript challenges (the OOD point and the FRI batch-combination
// alpha); the caller binds them to the live Fiat-Shamir replay.
func NewOpenInputPrecomp(
	bb *BBApi, rounds []OpenInputRoundShape, zeta, alpha BBExt, logGlobalMaxHeight int,
) *openInputPrecomp {
	p := &openInputPrecomp{
		zeta:               zeta,
		alpha:              alpha,
		zetaNext:           map[int]BBExt{},
		alphaPowW:          map[int]BBExt{},
		logGlobalMaxHeight: logGlobalMaxHeight,
	}
	for _, r := range rounds {
		for _, m := range r.Matrices {
			if m.LogHeight <= 0 || m.LogHeight > logGlobalMaxHeight {
				panic("NewOpenInputPrecomp: matrix height outside the query-index range")
			}
			if m.NumPoints != 1 && m.NumPoints != 2 {
				panic("NewOpenInputPrecomp: opening-point count must be 1 or 2")
			}
			if m.NumPoints == 2 {
				if _, ok := p.zetaNext[m.NextPointBits]; !ok {
					g := bbTwoAdicGeneratorRef(m.NextPointBits)
					p.zetaNext[m.NextPointBits] = bb.ExtMulBaseConst(g, zeta)
				}
			}
			if _, ok := p.alphaPowW[m.Width]; !ok {
				p.alphaPowW[m.Width] = extPowConst(bb, alpha, m.Width)
			}
		}
	}
	return p
}

// ============================================================================
// The per-query gadget
// ============================================================================

// openInputQueryPointX derives the LDE evaluation point x for a matrix of
// log-height lh at the sampled query index (verifier.rs:552-556):
//
//	x = GENERATOR · g_lh^{rev_bits(index >> (logMax−lh), lh)}
//
// Bit algebra: bit i of the reversed reduced index is idxBits[logMax−1−i],
// so x = 31 · Π_{i<lh} (g_lh^{2^i})^{idxBits[logMax−1−i]} — one Select and
// one base Mul per bit, over the SAME boolean index bits the FRI fold walks.
func openInputQueryPointX(bb *BBApi, idxBits []frontend.Variable, lh, logMax int) frontend.Variable {
	g := bbTwoAdicGeneratorRef(lh)
	acc := frontend.Variable(1)
	sq := g // g^(2^i)
	for i := 0; i < lh; i++ {
		acc = bb.Mul(acc, bb.api.Select(idxBits[logMax-1-i], sq, 1))
		sq = bbMulRef(sq, sq)
	}
	return bb.MulConst(bbGenerator, acc)
}

// verifyOpenInputBatchNative constrains one query's opening of one input
// round against the round's committed root — the in-circuit twin of
// MerkleTreeMmcs::verify_batch (mmcs.rs:1052-1180) for the arity-2 /
// cap-height-0 shape. Every opened row value is canonicity-bound first
// (canonicity is the injectivity of the shifted packing — the leaf binding).
func verifyOpenInputBatchNative(
	bb *BBApi,
	round OpenInputRoundShape,
	opening OpenInputBatchOpening,
	idxBits []frontend.Variable,
	logMax int,
	root frontend.Variable,
) {
	api := bb.API()
	if len(opening.Rows) != len(round.Matrices) {
		panic("verifyOpenInputBatchNative: row count does not match the round shape")
	}
	for mi, row := range opening.Rows {
		if len(row) != round.Matrices[mi].Width {
			panic("verifyOpenInputBatchNative: row width does not match the matrix shape")
		}
		for _, v := range row {
			bb.AssertIsCanonical(v)
		}
	}
	groups := openInputHeightGroupsOf(round)
	maxLh := groups[0].logHeight
	if len(opening.Path) != maxLh {
		panic("verifyOpenInputBatchNative: path depth does not match the batch tree height")
	}

	// hash_iter_slices over the rows of one height class: the concatenated
	// canonical values through the padding-free MultiField sponge.
	hashGroup := func(g openInputHeightGroup) frontend.Variable {
		var limbs []frontend.Variable
		for _, mi := range g.mats {
			limbs = append(limbs, opening.Rows[mi]...)
		}
		return multiField32HashNative(api, limbs)
	}

	digest := hashGroup(groups[0])
	next := 1
	bitsOff := logMax - maxLh
	for step := 0; step < maxLh; step++ {
		bit := idxBits[bitsOff+step]
		api.AssertIsBoolean(bit)
		sib := opening.Path[step]
		left := api.Select(bit, sib, digest)
		right := api.Select(bit, digest, sib)
		digest = Poseidon2Bn254Compress(api, left, right)
		// Inject the next height class's row hash when the walk reaches it
		// (mmcs.rs:1146-1167): an extra compression, no path node, no bit.
		if next < len(groups) && groups[next].logHeight == maxLh-step-1 {
			digest = Poseidon2Bn254Compress(api, digest, hashGroup(groups[next]))
			next++
		}
	}
	if next != len(groups) {
		panic("verifyOpenInputBatchNative: unconsumed height groups (heights below the walk)")
	}
	api.AssertIsEqual(digest, root)
}

// deriveOpenInputReducedNative computes the per-height reduced openings from
// the (Merkle-verified) opened rows and the transcript-bound opened values at
// zeta — the alpha-combination of verifier.rs:600-616. openedAtZ is consumed
// SEQUENTIALLY in round/matrix/point/column order (the exact flattening of
// the opened-values observe stream) and must be consumed exactly.
//
// Returns the reduced openings aligned with openInputLogHeights(rounds)
// (descending log height).
func deriveOpenInputReducedNative(
	bb *BBApi,
	rounds []OpenInputRoundShape,
	pre *openInputPrecomp,
	idxBits []frontend.Variable,
	openings []OpenInputBatchOpening,
	openedAtZ []BBExt,
) []BBExt {
	if len(openings) != len(rounds) {
		panic("deriveOpenInputReducedNative: opening count does not match the round count")
	}
	logMax := pre.logGlobalMaxHeight
	heights := openInputLogHeights(rounds)
	hIdx := map[int]int{}
	for i, h := range heights {
		hIdx[h] = i
	}
	zero := BBExt{0, 0, 0, 0}
	one := BBExt{1, 0, 0, 0}
	ro := make([]BBExt, len(heights))
	alphaPow := make([]BBExt, len(heights))
	for i := range heights {
		ro[i], alphaPow[i] = zero, one
	}

	// x per log height (query-dependent, matrix-independent).
	xAt := map[int]frontend.Variable{}
	// 1/(z − x) per (log height, point id); point id −1 = zeta, else the
	// zeta_next generator bits.
	type qinvKey struct{ lh, zid int }
	qinvAt := map[qinvKey]BBExt{}

	pos := 0
	for ri, round := range rounds {
		for mi, m := range round.Matrices {
			x, ok := xAt[m.LogHeight]
			if !ok {
				x = openInputQueryPointX(bb, idxBits, m.LogHeight, logMax)
				xAt[m.LogHeight] = x
			}
			hi := hIdx[m.LogHeight]
			for pt := 0; pt < m.NumPoints; pt++ {
				z, zid := pre.zeta, -1
				if pt == 1 {
					z, zid = pre.zetaNext[m.NextPointBits], m.NextPointBits
				}
				qinv, ok := qinvAt[qinvKey{m.LogHeight, zid}]
				if !ok {
					// z − x: only coordinate 0 carries the base value.
					qinv = bb.ExtInv(BBExt{bb.Sub(z[0], x), z[1], z[2], z[3]})
					qinvAt[qinvKey{m.LogHeight, zid}] = qinv
				}
				// Horner in alpha over the columns: Σ_k α^k (p(z)_k − p(x)_k).
				pz := openedAtZ[pos : pos+m.Width]
				pos += m.Width
				px := openings[ri].Rows[mi]
				var horner BBExt
				for k := m.Width - 1; k >= 0; k-- {
					d := BBExt{bb.Sub(pz[k][0], px[k]), pz[k][1], pz[k][2], pz[k][3]}
					if k == m.Width-1 {
						horner = d
					} else {
						horner = bb.ExtAdd(bb.ExtMul(horner, pre.alpha), d)
					}
				}
				ro[hi] = bb.ExtAdd(ro[hi], bb.ExtMul(alphaPow[hi], bb.ExtMul(qinv, horner)))
				alphaPow[hi] = bb.ExtMul(alphaPow[hi], pre.alphaPowW[m.Width])
			}
		}
	}
	if pos != len(openedAtZ) {
		panic("deriveOpenInputReducedNative: opened-values stream not consumed exactly")
	}
	return ro
}

// BindOpenInputToFriSeedsNative is the SEAM CLOSURE for one query: verify the
// four input-batch Merkle openings against the round commitments, derive the
// reduced openings from the opened columns, and assert them EQUAL to the FRI
// fold seeds (InitialEval at the max height; RollIns at each roll-in height,
// verifier.rs:471-480). After this, the fold seeds VerifyFriNative consumes
// are bound to the committed trace — a prover cannot ride host-computed
// openings that diverge from the commitments.
//
// idxBits are the SAME live-sampled index bits the FRI fold walked (returned
// by VerifyFriNative), roots the SAME transcript-observed commitment digests.
func BindOpenInputToFriSeedsNative(
	bb *BBApi,
	rounds []OpenInputRoundShape,
	pre *openInputPrecomp,
	idxBits []frontend.Variable,
	roots []frontend.Variable,
	openings []OpenInputBatchOpening,
	openedAtZ []BBExt,
	q FriNativeQueryOpening,
	rollInAfterRound []int,
) {
	if len(roots) != len(rounds) {
		panic("BindOpenInputToFriSeedsNative: root count does not match the round count")
	}
	logMax := pre.logGlobalMaxHeight
	for ri, round := range rounds {
		verifyOpenInputBatchNative(bb, round, openings[ri], idxBits, logMax, roots[ri])
	}
	derived := deriveOpenInputReducedNative(bb, rounds, pre, idxBits, openings, openedAtZ)

	// The derived height set must BE {logMax} ∪ {logMax−r−1 : roll-ins} —
	// the structural agreement between the input heights and the roll-in
	// schedule (verifier.rs:449-455: the initial eval is the max-height
	// entry; each further entry rolls in as the fold passes its height).
	heights := openInputLogHeights(rounds)
	if len(heights) != 1+len(rollInAfterRound) {
		panic("BindOpenInputToFriSeedsNative: height count does not match the roll-in schedule")
	}
	if heights[0] != logMax {
		panic("BindOpenInputToFriSeedsNative: no input batch at the max height")
	}
	if len(q.RollIns) != len(rollInAfterRound) {
		panic("BindOpenInputToFriSeedsNative: query roll-ins do not match the schedule")
	}
	bb.ExtAssertIsEqual(derived[0], q.InitialEval)
	for j, r := range rollInAfterRound {
		if heights[j+1] != logMax-r-1 {
			panic("BindOpenInputToFriSeedsNative: input height does not match its roll-in round")
		}
		bb.ExtAssertIsEqual(derived[j+1], q.RollIns[j])
	}
}
