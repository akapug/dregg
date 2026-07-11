// Plain-Go (non-circuit) reference of the FRI query-phase low-degree test: the
// per-query fold chain + commit-phase Merkle openings + final-polynomial check.
// The circuit gadget in fri_query.go is differentially tested against this
// reference, and this reference is derived line-for-line from the fork verifier
// at the workspace-pinned Plonky3 rev 82cfad73cd734d37a0d51953094f970c531817ec.
//
// GROUND TRUTH (fork file:line, rev 82cfad7):
//
//   - fri/src/verifier.rs:363 verify_query — the per-query fold loop. For each
//     round it: reconstructs the arity-many sibling group from the carried
//     folded_eval + the opening's sibling_values (verifier.rs:422-433), verifies
//     the group against the round's commitment via mmcs.verify_batch
//     (verifier.rs:447), folds with beta via folding.fold_row (verifier.rs:458),
//     and shifts the index down by log_arity (verifier.rs:444).
//
//   - THE FOLD FORMULA (arity 2). fri/src/two_adic_pcs.rs:109 fold_row does
//     Lagrange interpolation at beta over the coset xs = [s, -s] with
//     s = two_adic_generator(log_folded_height + 1)^reverse_bits_len(index,
//     log_folded_height) (two_adic_pcs.rs:123-131). The prover's matching
//     closed form is stated at fri/src/prover.rs:154 and computed in
//     fold_matrix (two_adic_pcs.rs:135):
//
//         f_{i+1}(x^2) = (f_i(x) + f_i(-x))/2 + beta*(f_i(x) - f_i(-x))/(2x)
//
//     i.e. with e0 = f_i(s) = eval at xs[0], e1 = f_i(-s) = eval at xs[1]:
//
//         folded = (e0 + e1)/2 + beta*(e0 - e1) * inv(2s)
//
//     The queried element sits at position index_in_group = start_index % arity
//     (verifier.rs:423); for arity 2 that is the current index bit b_r. So
//     e0 = (b_r==1 ? sibling : carry), e1 = (b_r==1 ? carry : sibling).
//
//   - THE COSET / two_adic_generator. baby-bear/src/baby_bear.rs:46
//     TWO_ADIC_GENERATORS[bits] is the canonical order-2^bits generator
//     (monty-31/src/monty_31.rs:668 two_adic_generator(bits) = the table entry).
//     Squaring drops the index: g_m^2 = g_{m-1}. This lets s be written as a
//     product of generator constants selected by the parent-index bits
//     (see invSFromParentRef), so the fold divisor inv(2s) needs no runtime
//     field inversion in-circuit — only bit-selected constant products.
//
//   - THE MERKLE ARITY. The commit-phase MMCS is
//     ExtensionMmcs<Val, Challenge, ValMmcs> over
//     ValMmcs = MerkleTreeMmcs<.., MyHash, MyCompress, 2, 8> (fri/src/verifier.rs
//     tests:690-693). It is BINARY (const N = 2, one sibling per level) with an
//     8-element BabyBear digest (DIGEST_ELEMS = 8). Leaf hashing is
//     MyHash = PaddingFreeSponge<Perm, 16, 8, 8> (symmetric/src/sponge.rs:172):
//     one full rate-8 block overwrites state[0..8], one width-16 permutation,
//     output state[0..8]. A commit-phase leaf is a matrix row of arity=2
//     EXTENSION evals, flattened by ExtensionMmcs to 8 base coordinates
//     (commit/src/adapters/extension_mmcs.rs:80 flatten_to_base) — exactly one
//     full block. Node compression is
//     MyCompress = TruncatedPermutation<Perm, 2, 8, 16>
//     (symmetric/src/compression.rs:40): pre[0..8]=left, pre[8..16]=right, one
//     width-16 permutation, output post[0..8]. Path direction: at each level the
//     queried child sits at pos_in_group = index % 2 (merkle-tree/src/mmcs.rs
//     :1122 verify_batch), so bit 0 => compress(node, sibling), bit 1 =>
//     compress(sibling, node), then index >>= 1. cap_height = 0 => the tree
//     folds to a single root; a height-1 tree (padded_len(1,2)=1,
//     merkle_tree.rs:453) has an empty schedule so its root IS the leaf hash.
//
//   - THE FINAL CHECK. fri/src/verifier.rs:311-324: eval final_poly at
//     x = two_adic_generator(log_global_max_height)^rev(domain_index, .) by
//     Horner and compare to the fold output. SCOPING (see fri_query.go): this
//     reference builds fixtures with log_blowup = log_final_poly_len = 0, so the
//     final domain has size 1, x = g^0 = 1, and final_poly is a single constant
//     coefficient. The final check is then folded_eval == final_poly[0].
package friverifier

// --- BabyBear two-adic generator table + inverses (canonical residues) -------

// twoAdicGeneratorsRef[bits] = BabyBear::two_adic_generator(bits), the canonical
// order-2^bits generator (baby-bear/src/baby_bear.rs:46 TWO_ADIC_GENERATORS).
var twoAdicGeneratorsRef = [28]uint32{
	0x1, 0x78000000, 0x67055c21, 0x5ee99486, 0xbb4c4e4, 0x2d4cc4da, 0x669d6090,
	0x17b56c64, 0x67456167, 0x688442f9, 0x145e952d, 0x4fe61226, 0x4c734715,
	0x11c33e2a, 0x62c3d2b1, 0x77cad399, 0x54c131f4, 0x4cabd6a6, 0x5cf5713f,
	0x3e9430e8, 0xba067a3, 0x18adc27d, 0x21fd55bc, 0x4b859b3d, 0x3bd57996,
	0x4483d85a, 0x3a26eef8, 0x1a427a41,
}

// twoAdicGenInvRef[bits] = twoAdicGeneratorsRef[bits]^{-1} mod p.
var twoAdicGenInvRef [28]uint32

// bbInv2 = 1/2 mod p = (p+1)/2. 2*bbInv2 = p+1 == 1 (mod p).
const bbInv2 = uint32(1006632961)

func init() {
	for i := range twoAdicGeneratorsRef {
		twoAdicGenInvRef[i] = bbInvRef(twoAdicGeneratorsRef[i])
	}
}

// bbPowRef returns a^e mod p (square-and-multiply, canonical input/output).
func bbPowRef(a uint32, e uint64) uint32 {
	result := uint32(1)
	base := a
	for e > 0 {
		if e&1 == 1 {
			result = bbMulRef(result, base)
		}
		base = bbMulRef(base, base)
		e >>= 1
	}
	return result
}

// bbInvRef returns a^{-1} mod p by Fermat (a != 0).
func bbInvRef(a uint32) uint32 { return bbPowRef(a, BabyBearP-2) }

// reverseBitsRef reverses the low n bits of x (p3_util::reverse_bits_len).
func reverseBitsRef(x uint, n int) uint {
	var r uint
	for i := 0; i < n; i++ {
		r = (r << 1) | ((x >> uint(i)) & 1)
	}
	return r
}

// --- Merkle (binary, Poseidon2-w16) reference --------------------------------

// merkleLeafHashRef hashes a commit-phase leaf row of two extension evals into
// an 8-element digest: PaddingFreeSponge<Perm,16,8,8> over the 8 flattened base
// coordinates [e0[0..4], e1[0..4]] (one full rate-8 block, one permutation).
func merkleLeafHashRef(e0, e1 bbExtRef) [8]uint32 {
	var st [16]uint32
	copy(st[0:4], e0[:])
	copy(st[4:8], e1[:])
	// st[8..16] = 0 (capacity)
	poseidon2W16Ref(&st)
	var d [8]uint32
	copy(d[:], st[0:8])
	return d
}

// merkleCompressRef compresses two child digests into a parent digest:
// TruncatedPermutation<Perm,2,8,16> (pre[0..8]=l, pre[8..16]=r, permute, take
// post[0..8]).
func merkleCompressRef(l, r [8]uint32) [8]uint32 {
	var st [16]uint32
	copy(st[0:8], l[:])
	copy(st[8:16], r[:])
	poseidon2W16Ref(&st)
	var d [8]uint32
	copy(d[:], st[0:8])
	return d
}

// merkleRootFromOpeningRef reconstructs the round's Merkle root from the
// reconstructed sibling group (e0,e1), the path bits (pathBits[l] = query index
// bit for level l, LSB-first), and the sibling digests. Mirrors the per-level
// pos_in_group logic of verify_batch (merkle-tree/src/mmcs.rs:1122).
func merkleRootFromOpeningRef(e0, e1 bbExtRef, pathBits []uint32, siblings [][8]uint32) [8]uint32 {
	digest := merkleLeafHashRef(e0, e1)
	for l := 0; l < len(siblings); l++ {
		if pathBits[l] == 0 {
			digest = merkleCompressRef(digest, siblings[l])
		} else {
			digest = merkleCompressRef(siblings[l], digest)
		}
	}
	return digest
}

// merkleCommitRef builds the whole binary Merkle tree over a commit-phase
// evaluation vector f (RowMajorMatrix of width 2: leaf i = hash(f[2i], f[2i+1]))
// and returns the root plus every layer (layer 0 = leaves) for opening.
func merkleCommitRef(f []bbExtRef) (root [8]uint32, layers [][][8]uint32) {
	h := len(f) / 2
	leaf := make([][8]uint32, h)
	for i := 0; i < h; i++ {
		leaf[i] = merkleLeafHashRef(f[2*i], f[2*i+1])
	}
	layers = append(layers, leaf)
	cur := leaf
	for len(cur) > 1 {
		next := make([][8]uint32, len(cur)/2)
		for i := range next {
			next[i] = merkleCompressRef(cur[2*i], cur[2*i+1])
		}
		layers = append(layers, next)
		cur = next
	}
	return cur[0], layers
}

// merkleOpenRef returns the sibling-digest path for leaf `index`, bottom-up.
func merkleOpenRef(layers [][][8]uint32, index int) [][8]uint32 {
	var path [][8]uint32
	idx := index
	for l := 0; l < len(layers)-1; l++ {
		path = append(path, layers[l][idx^1])
		idx >>= 1
	}
	return path
}

// --- Fold reference ----------------------------------------------------------

// invSFromParentRef computes inv(s) for a commit-phase row `parent` of a tree of
// log-height lfh in round r (global rounds R), where
// s = g_{R-r}^{reverse_bits_len(parent, lfh)}. Using g_m^2 = g_{m-1}, s factors
// as prod_j g_{2+j}^{bit_j(parent)}, so inv(s) = prod_j ginv_{2+j}^{bit_j}. This
// is the exact product the gadget forms from the query-index bits.
func invSFromParentRef(parent uint, lfh, R, r int) uint32 {
	inv := uint32(1)
	for j := 0; j < lfh; j++ {
		if (parent>>uint(j))&1 == 1 {
			inv = bbMulRef(inv, twoAdicGenInvRef[2+j])
		}
	}
	return inv
}

// friFoldCoreRef folds one arity-2 sibling group with beta:
//
//	(e0 + e1)/2 + beta*(e0 - e1) * (invS/2)
//
// where invS = inv(s) and s is the coset point for this row (two_adic_pcs.rs:109
// fold_row, arity 2). Returns the parent-node evaluation.
func friFoldCoreRef(e0, e1, beta bbExtRef, invS uint32) bbExtRef {
	sum := bbExtAddRef(e0, e1)
	diff := bbExtSubRef(e0, e1)
	// (e0+e1)/2
	sumHalf := bbExtScaleRef(bbInv2, sum)
	// beta*(e0-e1)*(invS/2)
	halfInvS := bbMulRef(bbInv2, invS)
	betaTerm := bbExtScaleRef(halfInvS, bbExtMulRef(beta, diff))
	return bbExtAddRef(sumHalf, betaTerm)
}

// bbExtScaleRef multiplies an extension element by a base scalar.
func bbExtScaleRef(s uint32, a bbExtRef) bbExtRef {
	var r bbExtRef
	for i := range r {
		r[i] = bbMulRef(s, a[i])
	}
	return r
}

// foldVectorRef folds a whole commit-phase evaluation vector f (size 2^{R-r})
// down to the next round's vector (size 2^{R-r-1}) using the same per-row fold
// as the verifier — this is the prover's fold_matrix (two_adic_pcs.rs:135)
// expressed row-by-row via the verifier formula, so the committed next vector is
// exactly what the verifier's fold chain reproduces.
func foldVectorRef(f []bbExtRef, beta bbExtRef, R, r int) []bbExtRef {
	lfh := R - r - 1
	n := len(f) / 2
	out := make([]bbExtRef, n)
	for parent := 0; parent < n; parent++ {
		e0 := f[2*parent]
		e1 := f[2*parent+1]
		invS := invSFromParentRef(uint(parent), lfh, R, r)
		out[parent] = friFoldCoreRef(e0, e1, beta, invS)
	}
	return out
}

// --- Query fixture + reference verifier --------------------------------------

// friQueryFixture is one complete FRI query: the commit-phase Merkle roots, the
// per-round betas, the sibling eval + Merkle path per round, the query index
// bits (LSB-first, R of them), the initial reduced-opening eval f0[index], and
// the final constant. R = number of commit rounds.
type friQueryFixture struct {
	R            int
	CommitRoots  [][8]uint32
	Betas        []bbExtRef
	Siblings     []bbExtRef
	MerkleProofs [][][8]uint32 // [R][lfh_r][8]
	IndexBits    []uint32      // R bits, LSB-first
	InitialEval  bbExtRef
	FinalEval    bbExtRef
}

// verifyFriQueryRef is the reference verifier: it recomputes the fold chain and
// Merkle roots and returns true iff every round's Merkle opening matches its
// committed root AND the final folded value equals FinalEval. It is the
// differential oracle for VerifyFriQuery (fri_query.go).
func verifyFriQueryRef(fx *friQueryFixture) bool {
	folded := fx.InitialEval
	for r := 0; r < fx.R; r++ {
		lfh := fx.R - r - 1
		bR := fx.IndexBits[r]
		// Reconstruct the sibling group (verifier.rs:422-433).
		var e0, e1 bbExtRef
		if bR == 1 {
			e0, e1 = fx.Siblings[r], folded
		} else {
			e0, e1 = folded, fx.Siblings[r]
		}
		// Merkle opening against the round's committed root (verifier.rs:447).
		pathBits := fx.IndexBits[r+1 : r+1+lfh]
		root := merkleRootFromOpeningRef(e0, e1, pathBits, fx.MerkleProofs[r])
		if root != fx.CommitRoots[r] {
			return false
		}
		// Fold (verifier.rs:458). parent index for the coset point = index>>(r+1).
		parent := indexFromBits(fx.IndexBits, r+1, lfh)
		invS := invSFromParentRef(parent, lfh, fx.R, r)
		folded = friFoldCoreRef(e0, e1, fx.Betas[r], invS)
	}
	return folded == fx.FinalEval
}

// indexFromBits reconstructs the integer from bits[start..start+n] (LSB-first).
func indexFromBits(bits []uint32, start, n int) uint {
	var v uint
	for j := 0; j < n; j++ {
		v |= uint(bits[start+j]&1) << uint(j)
	}
	return v
}
