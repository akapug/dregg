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
//	alpha_pow · qinv · (S_z − S_x)
//	S_z = Σ_k alpha^k·p(z)_k        S_x = Σ_k alpha^k·p(x)_k
//
// followed by alpha_pow *= alpha^width — the split of the pinned difference
// sum Σ_k alpha^k·(p(z)_k − p(x)_k) into its two halves. The split is THE
// R1CS lever of the whole settlement wrap (measured: open_input was 10.35M of
// the 12.87M total, ~80%, dominated by the per-query per-column Horner):
//
//	S_z depends only on the transcript-bound opened-at-zeta values, so it is
//	computed ONCE per (matrix, point) in NewOpenInputPrecomp and HOISTED out
//	of the 38-query loop entirely;
//	S_x has BASE-field p(x)_k (the Merkle-opened rows), so with the alpha
//	powers precomputed it is 4 raw products per column accumulated as
//	bound-tracked linear combinations (babybear.go ReduceBounded discipline)
//	with ONE reduction per block — not a full ExtMul + ExtAdd chain per
//	column.
//
// The host reference twin (stark_open_input_ref.go) implements the pinned
// per-column form, so the parity tests cross the two evaluation orders on
// real data (accept + reject canaries, apex_shrink_open_input_test.go).
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
// per generator-bits (zeta · g_bits, an ext × base-constant product),
// alpha^width per distinct width (the per-(matrix,point) alpha_pow advance),
// the alpha-power ladder alpha^0..alpha^maxWidth, and — the hoisted half of
// the alpha-combination — S_z = Σ_k alpha^k·p(z)_k per (round, matrix,
// point), computed ONCE over the transcript-bound opened-at-zeta stream.
type openInputPrecomp struct {
	zeta, alpha        BBExt
	zetaNext           map[int]BBExt
	alphaPowW          map[int]BBExt
	alphaPows          []BBExt     // alpha^k, k = 0..maxWidth
	sz                 [][][]BBExt // [round][matrix][point]
	logGlobalMaxHeight int
}

// extMulRawInto accumulates the schoolbook product a·b (BabyBear[X]/(X^4−11))
// into acc as RAW, UNREDUCED linear combinations — no per-column reduction.
// BOUND OBLIGATION (babybear.go ReduceBounded discipline): with canonical
// inputs each accumulated term is < 34·2^62 < 2^68, so n accumulations stay
// < n·2^68; every caller documents its n and reduces with the matching bound.
func extMulRawInto(api frontend.API, acc *[4]frontend.Variable, a, b BBExt) {
	var p [4][4]frontend.Variable
	for i := 0; i < 4; i++ {
		for j := 0; j < 4; j++ {
			p[i][j] = api.Mul(a[i], b[j])
		}
	}
	acc[0] = api.Add(acc[0], p[0][0], api.Mul(BBExtW, api.Add(p[1][3], p[2][2], p[3][1])))
	acc[1] = api.Add(acc[1], p[0][1], p[1][0], api.Mul(BBExtW, api.Add(p[2][3], p[3][2])))
	acc[2] = api.Add(acc[2], p[0][2], p[1][1], p[2][0], api.Mul(BBExtW, p[3][3]))
	acc[3] = api.Add(acc[3], p[0][3], p[1][2], p[2][1], p[3][0])
}

// NewOpenInputPrecomp builds the shared derivation context. zeta and alpha
// are the transcript challenges (the OOD point and the FRI batch-combination
// alpha); openedAtZ is the transcript-bound opened-values-at-zeta stream
// (already canonicity-bound by the caller), consumed EXACTLY in round/matrix/
// point/column order — the same flattening the observe stream pins. The
// caller binds all three to the live Fiat-Shamir replay.
func NewOpenInputPrecomp(
	bb *BBApi, rounds []OpenInputRoundShape, zeta, alpha BBExt, openedAtZ []BBExt,
	logGlobalMaxHeight int,
) *openInputPrecomp {
	p := &openInputPrecomp{
		zeta:               zeta,
		alpha:              alpha,
		zetaNext:           map[int]BBExt{},
		alphaPowW:          map[int]BBExt{},
		logGlobalMaxHeight: logGlobalMaxHeight,
	}
	maxWidth := 0
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
			if m.Width > maxWidth {
				maxWidth = m.Width
			}
		}
	}

	// The alpha-power ladder: alpha^0 = 1 (a constant), alpha^k = alpha^(k-1)·alpha.
	// alpha^width for the per-block alpha_pow advance reads the same ladder.
	p.alphaPows = make([]BBExt, maxWidth+1)
	p.alphaPows[0] = BBExt{1, 0, 0, 0}
	for k := 1; k <= maxWidth; k++ {
		p.alphaPows[k] = bb.ExtMul(p.alphaPows[k-1], alpha)
	}
	for _, r := range rounds {
		for _, m := range r.Matrices {
			p.alphaPowW[m.Width] = p.alphaPows[m.Width]
		}
	}

	// S_z per (round, matrix, point): Σ_k alpha^k·p(z)_k over the opened-at-
	// zeta stream — query-independent, computed ONCE, hoisted out of the query
	// loop. Raw ext×ext accumulation: each column adds terms < 34·2^62 < 2^68
	// per coordinate; widths are ≤ maxWidth ≤ 512, so the accumulator stays
	// < 512·2^68 = 2^77 — ONE ReduceBounded(77) per coordinate per block.
	if maxWidth > 512 {
		panic("NewOpenInputPrecomp: width exceeds the documented 2^77 accumulation bound")
	}
	pos := 0
	p.sz = make([][][]BBExt, len(rounds))
	for ri, r := range rounds {
		p.sz[ri] = make([][]BBExt, len(r.Matrices))
		for mi, m := range r.Matrices {
			p.sz[ri][mi] = make([]BBExt, m.NumPoints)
			for pt := 0; pt < m.NumPoints; pt++ {
				pz := openedAtZ[pos : pos+m.Width]
				pos += m.Width
				acc := [4]frontend.Variable{0, 0, 0, 0}
				for k := 0; k < m.Width; k++ {
					extMulRawInto(bb.API(), &acc, p.alphaPows[k], pz[k])
				}
				p.sz[ri][mi][pt] = BBExt{
					bb.ReduceBounded(acc[0], 77),
					bb.ReduceBounded(acc[1], 77),
					bb.ReduceBounded(acc[2], 77),
					bb.ReduceBounded(acc[3], 77),
				}
			}
		}
	}
	if pos != len(openedAtZ) {
		panic("NewOpenInputPrecomp: opened-values stream not consumed exactly")
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
// the (Merkle-verified) opened rows and the precomputed S_z halves — the
// alpha-combination of verifier.rs:600-616 in the split form
// alpha_pow·qinv·(S_z − S_x). The opened-at-zeta stream was consumed by
// NewOpenInputPrecomp (S_z); here only the query-dependent S_x is evaluated:
// base-field opened rows against the alpha-power ladder, accumulated raw
// (each term < 2^62, width ≤ 512 ⇒ < 2^71) with one ReduceBounded(71) per
// coordinate per block.
//
// Returns the reduced openings aligned with openInputLogHeights(rounds)
// (descending log height).
func deriveOpenInputReducedNative(
	bb *BBApi,
	rounds []OpenInputRoundShape,
	pre *openInputPrecomp,
	idxBits []frontend.Variable,
	openings []OpenInputBatchOpening,
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

	for ri, round := range rounds {
		for mi, m := range round.Matrices {
			x, ok := xAt[m.LogHeight]
			if !ok {
				x = openInputQueryPointX(bb, idxBits, m.LogHeight, logMax)
				xAt[m.LogHeight] = x
			}
			hi := hIdx[m.LogHeight]

			// S_x = Σ_k α^k·p(x)_k, shared by both opening points of this
			// matrix (p(x) is the single Merkle-opened row). p(x)_k is BASE
			// field and canonical (verifyOpenInputBatchNative asserted it),
			// α^k coordinates canonical: each product < 2^62; width ≤ 512 ⇒
			// accumulator < 512·2^62 = 2^71 — ReduceBounded(71) per coord.
			px := openings[ri].Rows[mi]
			if m.Width > 512 {
				panic("deriveOpenInputReducedNative: width exceeds the documented 2^71 accumulation bound")
			}
			accX := [4]frontend.Variable{0, 0, 0, 0}
			for k := 0; k < m.Width; k++ {
				a := pre.alphaPows[k]
				for j := 0; j < 4; j++ {
					accX[j] = bb.api.Add(accX[j], bb.api.Mul(px[k], a[j]))
				}
			}
			sx := BBExt{
				bb.ReduceBounded(accX[0], 71),
				bb.ReduceBounded(accX[1], 71),
				bb.ReduceBounded(accX[2], 71),
				bb.ReduceBounded(accX[3], 71),
			}

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
				// alpha_pow·qinv·(S_z − S_x) — S_z hoisted (precomp).
				d := bb.ExtSub(pre.sz[ri][mi][pt], sx)
				ro[hi] = bb.ExtAdd(ro[hi], bb.ExtMul(alphaPow[hi], bb.ExtMul(qinv, d)))
				alphaPow[hi] = bb.ExtMul(alphaPow[hi], pre.alphaPowW[m.Width])
			}
		}
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
	derived := deriveOpenInputReducedNative(bb, rounds, pre, idxBits, openings)

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
