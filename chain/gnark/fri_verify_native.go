// NATIVE-HASH single-matrix FRI verifier flow — the first assembled piece of
// the re-architected wrap (docs/deos/WRAP-NATIVE-HASH-DECISION.md) and the
// measured empirical check of its ~1-6M-constraint premise (see
// TestWrapNativeHashConstraintMeasurement in fri_verify_native_test.go).
//
// This is the native-hash TWIN of VerifyFri (fri_verify.go): the SAME flow and
// the SAME fork-faithful observe/sample transcript ORDER (per commit round
// observe root -> commit-PoW -> sample beta; then final poly; arity schedule;
// query grinding; per query sample index -> verify query), with exactly the
// two swaps the wrap decision names:
//
//   - TRANSCRIPT: the emulated BabyBear DuplexChallenger (challenger.go, one
//     emulated Poseidon2W16 per duplexing, ~16,837 R1CS) is replaced by the
//     MultiFieldChallenger (multifield_challenger.go): a NATIVE BN254 width-3
//     duplex sponge (~243 R1CS/permutation) with the fork's MultiField32
//     pack/split adapter. Commit roots are observed as native BN254 digests;
//     betas and query indices are sampled as BabyBear.
//   - MERKLE: the emulated Poseidon2-w16 commit openings (friMerkleLeafHash /
//     friMerkleCompressStep in fri_query.go) are replaced by native BN254
//     Poseidon2 openings (VerifyMerklePathBn254, merkle_bn254.go) — one node =
//     one BN254 element, one level = one ~243-R1CS native compression.
//
// The FOLD ARITHMETIC does NOT move: it is BabyBear field arithmetic (not
// hashing), so it stays on the emulated BabyBear ext-field gadget — literally
// the same code path (friFoldRowArity2, fri_query.go) the emulated verifier
// runs. This is the arithmetic RESIDUAL WRAP-NATIVE-HASH-DECISION.md names as
// untouched by the hash swap.
//
// LEAF PACKING — the Rust shrink layer's MMCS leaf hash, ported exactly. The
// shrink layer (circuit-prove/src/dregg_outer_config.rs, OuterHash) commits
// leaf rows with MultiField32PaddingFreeSponge<BabyBear, Bn254,
// Poseidon2Bn254<3>, 3, 2, 1> (sponge.rs:443 hash_iter at the pinned Plonky3
// rev 82cfad7): the row's canonical BabyBear coordinates are packed with
// reduce_packed_shifted (helpers.rs:147) — little-endian radix-2^31 Horner
// over digits (v_i + 1), the SHIFTED encoding, NOT the challenger's unshifted
// reduce_packed — 8 limbs per BN254 rate slot
// (max_shifted_absorb_injective_limbs, helpers.rs:243: p·Σ_{i<8} 2^{31i} <
// p_BN254), 2 rate slots per permutation, one Poseidon2Bn254 per 16-limb
// block, digest = state[0]. A commit-phase leaf row here is two extension
// evals = 8 coordinates = exactly one packed slot: state = [pack(row), 0, 0],
// one permutation. Canonicity of every packed coordinate is asserted at the
// boundary — canonicity is what makes the shifted packing injective, hence
// the leaf binding. Cross-side agreement is pinned by the leaf-hash/MMCS-root
// KATs in fri_leaf_hash_kat_test.go (digests computed by the REAL fork sponge
// + MerkleTreeMmcs over the pinned permutation).
//
// HONEST SCOPE — what this verifies of a REAL shrink proof, and what remains.
//
// The Rust shrink layer LANDED (circuit-prove/src/apex_shrink.rs: a real
// ir2_leaf_wrap apex re-proven under DreggOuterConfig), and this gadget now
// verifies the FRI CORE of that REAL shrink proof end-to-end
// (apex_shrink_real_fixture_test.go over fixtures/apex_shrink_fri_real.json,
// exported + self-checked by circuit-prove/src/apex_shrink_gnark_export.rs):
//
//   VERIFIED IN-CIRCUIT against real data: the full Fiat–Shamir transcript
//   (the pre-FRI prefix replayed event-for-event with every sampled challenge
//   pinned to the Rust value, then betas/PoW/query indices drawn live), the
//   commit-phase native Merkle openings for every query and round, the fold
//   arithmetic with multi-height ROLL-INS (verifier.rs:471-480: reduced
//   openings entering as the fold passes each input height, scaled by
//   beta^arity), the query grinding, and the final-polynomial check.
//   Arity-2, LogFinalPolyLen = 0 (the DreggOuterConfig shape; blowup/query
//   split as pinned by the fixture).
//
//   SEAM CLOSED (stark_open_input.go): the per-query reduced openings
//   (InitialEval + RollIns) still enter as witnesses for the fold chain, but
//   the open_input layer now RE-DERIVES them in-circuit — the input-batch
//   Merkle openings against the main/quotient/preprocessed/permutation
//   commitments plus the alpha-combination Σ αᵏ(p(z)−p(x))/(z−x) — and
//   asserts equality, so they are commitment-BOUND (the assembled circuit in
//   stark_algebra_real_fixture_test.go wires this via the query bits this
//   function returns). Constraint-eval-at-zeta + quotient recomposition:
//   stark_verify_native.go. Remaining before the Groth16 wrap: bake the
//   shape/DAG as VK constants and size the wrap.
package friverifier

import (
	"math/big"

	"github.com/consensys/gnark/frontend"
)

// FriNativeQueryOpening is one query's opening data for the native-hash flow:
// the initial reduced-opening seed, the roll-in reduced openings (aligned
// with the structural rollInAfterRound schedule; empty when all inputs live
// at the max height), and, per commit round, the sibling evaluation (BabyBear
// ext, folded natively) plus the NATIVE Merkle path (one BN254 sibling node
// per level, bottom-up). The query index is drawn from the challenger inside
// VerifyFriNative, not carried here.
type FriNativeQueryOpening struct {
	InitialEval  BBExt
	RollIns      []BBExt
	Siblings     []BBExt
	MerkleProofs [][]frontend.Variable // [R][lfh_r] native sibling nodes
}

// packShiftedBn254 packs ≤ 8 canonical BabyBear values into one BN254 rate
// slot with the SHIFTED radix-2^31 encoding (reduce_packed_shifted,
// helpers.rs:147-154): little-endian Horner over digits (v_i + 1). The +1
// shift reserves zero as an out-of-band "no digit" value, so limb sequences
// of different lengths stay distinct inside a fixed-width slot. Pure linear
// combination: zero constraints. Callers must have asserted every value
// canonical — a canonical digit +1 is ≤ p < 2^31, and 8 shifted limbs pack
// injectively (p·Σ_{i<8} 2^{31i} < p_BN254, helpers.rs:226-243).
func packShiftedBn254(api frontend.API, vals []frontend.Variable) frontend.Variable {
	if len(vals) == 0 || len(vals) > mfAbsorbNumFElms {
		panic("packShiftedBn254: limb count out of range for one BN254 slot")
	}
	base := new(big.Int).Lsh(big.NewInt(1), mfAbsorbRadixBits)
	acc := frontend.Variable(0)
	for i := len(vals) - 1; i >= 0; i-- {
		acc = api.Add(api.Mul(acc, base), vals[i], 1)
	}
	return acc
}

// multiField32HashNative is the in-circuit twin of the Rust MMCS leaf hasher
// MultiField32PaddingFreeSponge<BabyBear, Bn254, Poseidon2Bn254<3>, 3, 2, 1>
// (sponge.rs:443-483 hash_iter): state = [0, 0, 0]; the limbs are absorbed in
// blocks of RATE·8 = 16, each 8-limb chunk packed SHIFTED into one rate slot
// (a partial block overwrites only the slots it fills — the remaining rate
// slots RETAIN the previous permutation output, overwrite-mode); one native
// Poseidon2Bn254 per block; digest = state[0].
func multiField32HashNative(api frontend.API, limbs []frontend.Variable) frontend.Variable {
	state := [bn254P3Width]frontend.Variable{
		frontend.Variable(0), frontend.Variable(0), frontend.Variable(0),
	}
	const blockLimbs = bn254SpongeRate * mfAbsorbNumFElms
	for start := 0; start < len(limbs); start += blockLimbs {
		block := limbs[start:min(start+blockLimbs, len(limbs))]
		for slot := 0; slot*mfAbsorbNumFElms < len(block); slot++ {
			cs := slot * mfAbsorbNumFElms
			state[slot] = packShiftedBn254(api, block[cs:min(cs+mfAbsorbNumFElms, len(block))])
		}
		Poseidon2Bn254(api, &state)
	}
	return state[0]
}

// friMerkleLeafHashNative hashes a commit-phase leaf row of two extension
// evals (8 canonical BabyBear coordinates, e0's coefficients first — the
// ExtensionMmcs flatten_to_base order) into ONE native BN254 node via the
// MultiField32PaddingFreeSponge — the EXACT MMCS leaf hash of the Rust shrink
// layer (dregg_outer_config.rs OuterHash; mmcs.rs:1100 hash_iter_slices over
// the opened row). 8 coordinates = one packed slot: state = [pack, 0, 0], one
// native permutation, digest = state[0]. Cross-side KAT:
// fri_leaf_hash_kat_test.go.
func friMerkleLeafHashNative(api frontend.API, e0, e1 BBExt) frontend.Variable {
	return multiField32HashNative(api, []frontend.Variable{
		e0[0], e0[1], e0[2], e0[3], e1[0], e1[1], e1[2], e1[3],
	})
}

// VerifyFriQueryNative constrains one FRI query's fold chain with NATIVE
// Merkle openings — the native-hash twin of VerifyFriQuery (fri_query.go).
// The sibling-group reconstruction, the fold (friFoldRowArity2 — the SAME code
// path as the emulated verifier), and the final-poly check are identical; only
// the commitment opening swaps to VerifyMerklePathBn254.
//
// `logMaxHeight` is the log of the initial (largest) evaluation domain
// (R + LogBlowup + LogFinalPolyLen): round r's commit-phase matrix has
// 2^(logMaxHeight-r-1) rows, so its native Merkle path has
// logMaxHeight - r - 1 levels and the fold's parent index is the same bit
// span (with LogBlowup = 0 this degenerates to the old R - r - 1).
//
// `rollInAfterRound` (STRUCTURAL, strictly ascending) lists the rounds after
// whose fold a reduced opening enters the chain (verifier.rs:471-480: an
// input matrix lives at the just-reached height); `rollIns` carries the
// corresponding values, scaled by beta^2 = beta^arity for independence.
func VerifyFriQueryNative(
	bb *BBApi,
	R int,
	logMaxHeight int,
	commitRoots []frontend.Variable, // [R] native BN254 roots
	betas []BBExt,
	siblings []BBExt,
	merkleProofs [][]frontend.Variable, // [R][logMaxHeight-r-1] native sibling nodes
	indexBits []frontend.Variable, // [logMaxHeight]
	initialEval BBExt,
	rollInAfterRound []int,
	rollIns []BBExt,
	finalEval BBExt,
) {
	api := bb.API()
	if len(rollIns) != len(rollInAfterRound) {
		panic("VerifyFriQueryNative: rollIns must align with the rollInAfterRound schedule")
	}

	// Fail-closed witness ingestion (mirrors VerifyFriQuery). The BabyBear
	// values must be canonical — for the packed leaf, canonicity IS the
	// injectivity of the packing. Native digests need no canonicity: every
	// representable BN254 witness value is canonical.
	for i := range indexBits {
		api.AssertIsBoolean(indexBits[i])
	}
	bb.ExtAssertIsCanonical(initialEval)
	bb.ExtAssertIsCanonical(finalEval)
	for r := 0; r < R; r++ {
		bb.ExtAssertIsCanonical(betas[r])
		bb.ExtAssertIsCanonical(siblings[r])
	}
	for i := range rollIns {
		bb.ExtAssertIsCanonical(rollIns[i])
	}

	folded := initialEval
	ri := 0
	for r := 0; r < R; r++ {
		lfh := logMaxHeight - r - 1
		bR := indexBits[r]

		// Reconstruct the arity-2 sibling group (verifier.rs:422-433): the
		// carried value sits at position index_in_group = b_r.
		var e0, e1 BBExt
		for i := 0; i < 4; i++ {
			e0[i] = api.Select(bR, siblings[r][i], folded[i])
			e1[i] = api.Select(bR, folded[i], siblings[r][i])
		}

		// NATIVE Merkle opening against the round's committed root: one leaf
		// permutation + lfh native compressions (the emulated path pays one
		// ~16,837-R1CS emulated permutation per step; this pays ~243).
		leaf := friMerkleLeafHashNative(api, e0, e1)
		VerifyMerklePathBn254(api, leaf, merkleProofs[r], indexBits[r+1:r+1+lfh], commitRoots[r])

		// Fold with beta — the shared emulated-BabyBear fold path (the
		// arithmetic residual; the hash swap does not touch it).
		folded = friFoldRowArity2(bb, e0, e1, betas[r], indexBits[r+1:r+1+lfh])

		// Roll in the reduced opening for the just-reached height
		// (verifier.rs:477-479): folded += beta^2 * ro.
		if ri < len(rollInAfterRound) && rollInAfterRound[ri] == r {
			betaSq := bb.ExtMul(betas[r], betas[r])
			folded = bb.ExtAdd(folded, bb.ExtMul(betaSq, rollIns[ri]))
			ri++
		}
	}
	if ri != len(rollInAfterRound) {
		panic("VerifyFriQueryNative: rollInAfterRound schedule not consumed (round out of range)")
	}

	// Final-polynomial check (LogFinalPolyLen == 0 scope: a single constant).
	bb.ExtAssertIsEqual(folded, finalEval)
}

// CheckWitnessNative enforces the FRI grinding check over the MultiField
// transcript — the native twin of CheckWitness (grinding.go), mirroring
// GrindingChallenger::check_witness (grinding_challenger.rs:40-46): 0 bits is
// a no-op (no observe, no transcript advance); otherwise absorb the witness
// and assert the low powBits bits of the next BabyBear sample are all zero.
func CheckWitnessNative(c *MultiFieldChallenger, powBits int, witness frontend.Variable) {
	if powBits == 0 {
		return
	}
	c.ObserveBabyBear(witness)
	bits := c.SampleBitsDecomposed(powBits)
	for _, b := range bits {
		c.api.AssertIsEqual(b, 0)
	}
}

// VerifyFriNative constrains the batched FRI verifier flow with the
// NATIVE-HASH transcript and commitments, drawing the betas and query indices
// from `ch` in the SAME fork-faithful transcript order as VerifyFri. `ch` is
// the MultiField challenger positioned at the commit phase.
// `rollInAfterRound` is the structural multi-height roll-in schedule (nil for
// the single-height case). A tampered root/opening/witness/final-poly/roll-in,
// or a divergent transcript, yields an unsatisfiable constraint system
// (fail-closed).
//
// Returns each query's live-sampled DOMAIN index bits (LSB-first, the extra
// query-index bits already dropped) so the open_input layer
// (stark_open_input.go) can verify the input-batch openings and derive the
// reduced openings at the SAME query points the fold walked.
func VerifyFriNative(
	bb *BBApi,
	cfg FriConfig,
	R int,
	commitRoots []frontend.Variable, // [R] native BN254 roots
	finalPoly []BBExt,
	powWitness frontend.Variable,
	queries []FriNativeQueryOpening,
	rollInAfterRound []int,
	ch *MultiFieldChallenger,
) [][]frontend.Variable {
	_, queryBits := verifyFriNativeImpl(bb, cfg, R, commitRoots, finalPoly, powWitness, queries, rollInAfterRound, ch, false)
	return queryBits
}

// verifyFriNativeImpl is VerifyFriNative with the same test-only order flag as
// verifyFriImpl: swapOrder=true samples the beta BEFORE observing the root, and
// the transcript-order canary requires that to be UNSATISFIABLE on a valid
// proof — the native transcript binds the observe/sample interleave exactly as
// the emulated one does.
func verifyFriNativeImpl(
	bb *BBApi,
	cfg FriConfig,
	R int,
	commitRoots []frontend.Variable,
	finalPoly []BBExt,
	powWitness frontend.Variable,
	queries []FriNativeQueryOpening,
	rollInAfterRound []int,
	ch *MultiFieldChallenger,
	swapOrder bool,
) ([]BBExt, [][]frontend.Variable) {
	if len(finalPoly) != (1 << cfg.LogFinalPolyLen) {
		panic("VerifyFriNative: len(finalPoly) must equal 2^LogFinalPolyLen")
	}
	if cfg.LogFinalPolyLen != 0 {
		panic("VerifyFriNative: single-round-set scope requires LogFinalPolyLen==0")
	}
	for i := range rollInAfterRound {
		if rollInAfterRound[i] < 0 || rollInAfterRound[i] >= R ||
			(i > 0 && rollInAfterRound[i] <= rollInAfterRound[i-1]) {
			panic("VerifyFriNative: rollInAfterRound must be strictly ascending rounds in [0, R)")
		}
	}

	// Commit phase (verifier.rs:214-227): the root is observed as a NATIVE
	// BN254 digest (multi_field_challenger.rs:181 — no PF->F repack detour);
	// the beta is sampled as BabyBear limbs through the MultiField split.
	betas := make([]BBExt, R)
	for r := 0; r < R; r++ {
		if swapOrder {
			betas[r] = ch.SampleBabyBearExt()
			ch.ObserveBn254Digest([]frontend.Variable{commitRoots[r]})
		} else {
			ch.ObserveBn254Digest([]frontend.Variable{commitRoots[r]})     // verifier.rs:221
			CheckWitnessNative(ch, cfg.CommitPowBits, frontend.Variable(0)) // :222 (0 bits: no-op)
			betas[r] = ch.SampleBabyBearExt()                               // verifier.rs:225
		}
	}

	// verifier.rs:238 observe_algebra_slice(&final_poly).
	for _, coeff := range finalPoly {
		ch.ObserveBabyBearExt(coeff)
	}

	// verifier.rs:249-251 observe the arity schedule (log_arity 1 per round).
	for r := 0; r < R; r++ {
		ch.ObserveBabyBear(frontend.Variable(1))
	}

	// verifier.rs:254 query PoW grinding (fail-closed on a bad witness).
	CheckWitnessNative(ch, cfg.QueryPowBits, powWitness)

	// Per query: sample the index, run the native-hash fold chain.
	logMaxHeight := R + cfg.LogBlowup + cfg.LogFinalPolyLen
	numIndexBits := logMaxHeight + cfg.ExtraQueryIndexBits
	finalEval := finalPoly[0] // LogFinalPolyLen==0: the final poly is a constant.
	queryBits := make([][]frontend.Variable, 0, len(queries))
	for _, q := range queries {
		// verifier.rs:268 index = sample_bits(log_global_max_height + extra).
		idxBits := ch.SampleBitsDecomposed(numIndexBits)
		// verifier.rs:287 domain_index = index >> extra: drop the low extra bits.
		domainBits := idxBits[cfg.ExtraQueryIndexBits:]
		queryBits = append(queryBits, domainBits)
		VerifyFriQueryNative(bb, R, logMaxHeight, commitRoots, betas, q.Siblings, q.MerkleProofs,
			domainBits, q.InitialEval, rollInAfterRound, q.RollIns, finalEval) // verifier.rs:298 verify_query
	}
	// The per-round fold betas (live-sampled from `ch`) are returned alongside the
	// query index bits so a caller re-deriving the transcript can BIND the
	// challenges the descriptor blocks consume (block 1's fold beta, block 4's
	// query index) to the sponge squeeze — not just verify the fold chain here.
	return betas, queryBits
}
