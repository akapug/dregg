// THE DIFFERENTIAL GATE, MADE RUNNABLE.
//
// emitted_verifier_full.go's VerifierFullCircuit is the emit-driven structural
// skeleton (~20% of the verifier: canonicity, FRI fold ext-muls, commit-phase
// Merkle openings, input-open Merkle openings, batch-STARK DAG instances, the
// LogUp balance, the query-PoW sample, and the 25-lane segment binding). It now
// EXPOSES the same 25-lane public settlement statement (Publics) the hand-Go
// SettlementCircuit does, and this file makes the gate RUNNABLE: assignVerifierFull
// ingests the REAL fixture proof (fixtures/apex_shrink_fri_real.json) into the
// skeleton's flat witness bank W, using the hand-Go SettlementCircuit assignment
// path (assignSettlementCircuit in stark_algebra_real_fixture_test.go) as the
// reference for which proof field feeds which witness.
//
// TestEmittedVerifierFullDifferential runs BOTH circuits on the real fixture via
// test.IsSolved and records the RAW result of each. It does NOT require the
// emit-driven skeleton to accept — the skeleton is deliberately partial, and the
// measurement is exactly WHERE it diverges from the hand-Go reference. The
// hand-Go circuit is asserted to accept (a sanity floor); the emit-driven result
// is logged, not gated.
package friverifier

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	fr "github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// realRoundMerkle is one commit-phase Merkle opening of the REAL proof, in the
// exact (leaf, siblings, pathBits, root) shape VerifyMerklePathBn254 checks —
// the reference verifier's per-round tuple (fri_verify_native_ref.go
// verifyFriNativeRefImpl / merkleRootFromOpeningBn254Ref).
type realRoundMerkle struct {
	leaf *big.Int
	sibs []*big.Int          // lfh sibling nodes (== depths[r] == logMax-r-1)
	bits []frontend.Variable // lfh path bits (indexBits[r+1 : r+1+lfh])
	root *big.Int
}

// realQueryMerkle caches one query's per-round commit-phase Merkle openings and
// its final-poly evaluation (the FRI closure value).
type realQueryMerkle struct {
	rounds    []realRoundMerkle
	finalEval bbExtRef
}

// computeRealQueryMerkle replays the REAL FRI fold chain for query qi (a copy of
// verifyFriNativeRefImpl's per-query loop, driven by the fixture's pinned betas
// and expected index), materializing each round's REAL Merkle-opening tuple. It
// self-checks each round natively (merkleRootFromOpeningBn254Ref must reproduce
// the committed root) so a replication bug here fails LOUDLY as a test error,
// never masquerading as an emit-driven-circuit divergence.
func computeRealQueryMerkle(t *testing.T, fx *shrinkRealFixture, qi int) realQueryMerkle {
	t.Helper()
	q := fx.Queries[qi]
	R := fx.Fri.Rounds
	cfg := shrinkCfgRef(fx)
	logMax := fx.Fri.LogGlobalMaxHeight

	domainIndex := uint(q.ExpectedIndex) >> uint(cfg.ExtraQueryIndexBits)
	indexBits := make([]uint32, logMax)
	for i := 0; i < logMax; i++ {
		indexBits[i] = uint32((domainIndex >> uint(i)) & 1)
	}

	folded := bbExtRef(q.InitialEval)
	ri := 0
	out := realQueryMerkle{}
	for r := 0; r < R; r++ {
		lfh := logMax - r - 1
		var e0, e1 bbExtRef
		if indexBits[r] == 1 {
			e0, e1 = bbExtRef(q.Siblings[r]), folded
		} else {
			e0, e1 = folded, bbExtRef(q.Siblings[r])
		}

		pathBits := indexBits[r+1 : r+1+lfh]
		sibElems := make([]fr.Element, lfh)
		sibBigs := make([]*big.Int, lfh)
		for l := 0; l < lfh; l++ {
			sibElems[l] = parseBn254Hex(t, q.MerklePaths[r][l])
			sibBigs[l] = frToBig(sibElems[l])
		}
		leaf := merkleLeafHashBn254Ref(e0, e1)
		root := parseBn254Hex(t, fx.CommitRoots[r])

		// Native self-check: the emitted skeleton's in-circuit
		// ComputeMerkleRootBn254 is the documented twin of this walk, so if the
		// native recomputation matches the committed root, the in-circuit block
		// must accept these values. Guard against a replication bug.
		if got := merkleRootFromOpeningBn254Ref(e0, e1, pathBits, sibElems); !got.Equal(&root) {
			t.Fatalf("query %d round %d: native Merkle recomputation != committed root — "+
				"fold-chain replication bug (NOT an emit-circuit divergence)", qi, r)
		}

		bits := make([]frontend.Variable, lfh)
		for l := 0; l < lfh; l++ {
			bits[l] = pathBits[l]
		}
		out.rounds = append(out.rounds, realRoundMerkle{
			leaf: frToBig(leaf), sibs: sibBigs, bits: bits, root: frToBig(root),
		})

		parent := indexFromBits(indexBits, r+1, lfh)
		folded = friFoldCoreRef(e0, e1, bbExtRef(fx.ExpectedBetas[r]), invSFromParentRef(parent, lfh, R, r))
		if ri < len(fx.RollInRounds) && fx.RollInRounds[ri] == r {
			betaSq := bbExtMulRef(bbExtRef(fx.ExpectedBetas[r]), bbExtRef(fx.ExpectedBetas[r]))
			folded = bbExtAddRef(folded, bbExtMulRef(betaSq, bbExtRef(q.RollIns[ri])))
			ri++
		}
	}
	out.finalEval = finalPolyEvalRef([]bbExtRef{bbExtRef(fx.FinalPoly[0])}, domainIndex, logMax)
	return out
}

// appendExtVars appends an ext residue tuple as 4 witness values (base lanes).
func appendExtVars(e bbExtRef, w *[]frontend.Variable) {
	for i := 0; i < 4; i++ {
		*w = append(*w, e[i])
	}
}

// assignVerifierFull maps the REAL fixture proof into the emit-driven skeleton's
// flat witness bank W, in the EXACT order VerifierFullCircuit.Define consumes it
// (a single walk over vf.Gadgets mirroring §4 of emitted_verifier_full.go). It
// reuses the hand-Go SettlementCircuit assignment path as the reference for which
// proof field feeds which witness:
//
//   - block 0 (canonicity): a real claim lane (SettlementCircuit's AssertIsCanonical
//     over the public statement);
//   - block 1 (fri_fold ext-muls): a real (initial eval, beta) ext pair;
//   - block 1 (ext-eq): per query, both operands = the real final-poly evaluation
//     (the FRI closure value the reference verifier checks folded == finalEval);
//   - block 2 (commit Merkle): the REAL per-query per-round openings (leaf via the
//     replayed fold chain, real path nodes, real index bits, real commit root) —
//     the values the reference verifier's verifyFriNativeRefImpl walks;
//   - block 2 (input-open Merkle): the real input-batch path nodes + input root +
//     index bits, with a PLACEHOLDER leaf (the input MMCS leaf hash and the true
//     per-round tree depth are NOT modeled by the fixed-depth-18 skeleton — the
//     designed seam);
//   - block 3 (batch-STARK DAG, LogUp): real cumulative sums where shaped;
//     otherwise zero fillers sized to the DAG's per-instance budget;
//   - block 4 (query-PoW sample / pow-bits-zero): the real query index sample;
//   - block 5 (segment): the real 25 claim lanes, equated against the EXPOSED
//     public statement (assignSettlementPublics' pinned order).
//
// Blocks the skeleton under-models (input-open leaf, the STARK DAG output binding)
// are filled with real-where-available + zero placeholders so the assignment is
// COMPLETE and the circuit RUNS end-to-end; the differential test then records
// where the first constraint diverges.
func assignVerifierFull(t *testing.T, fx *shrinkRealFixture, ex *shrinkStarkExtract, sym *SymbolicConstraints) *VerifierFullCircuit {
	t.Helper()
	vf := loadVerifierFullT(t)
	c, err := AllocVerifierFullCircuit(vf, sym)
	if err != nil {
		t.Fatalf("alloc emit-driven circuit: %v", err)
	}

	// The pinned 25-lane public statement = the real expose_claim channel.
	claim := fx.TablePublics[fx.ClaimInstance]
	assignVerifierFullPublics(c, claim)

	// Precompute the real per-query commit-phase Merkle openings + final evals.
	qms := make([]realQueryMerkle, len(fx.Queries))
	for qi := range fx.Queries {
		qms[qi] = computeRealQueryMerkle(t, fx, qi)
	}

	logMax := fx.Fri.LogGlobalMaxHeight
	w := make([]frontend.Variable, 0, len(c.W))

	for _, g := range vf.Gadgets {
		switch g.Gadget {

		case "AssertIsCanonical":
			// block 0 — a real canonical public-statement lane.
			for i := 0; i < g.Count; i++ {
				w = append(w, claim[0])
			}

		case "FriFoldRowArity2":
			// block 1 — the chained accumulator (x) + fixed operand (b): a real
			// (initial eval, beta) ext pair. No failing constraint (ExtAssertIsEqual(x,x)).
			appendExtVars(bbExtRef(fx.Queries[0].InitialEval), &w)
			appendExtVars(bbExtRef(fx.ExpectedBetas[0]), &w)

		case "ExtAssertIsEqual":
			// block 1 — per query, a == b == the real final-poly evaluation.
			for i := 0; i < g.Count; i++ {
				fe := qms[i].finalEval
				appendExtVars(fe, &w) // a
				appendExtVars(fe, &w) // b
			}

		case "VerifyMerklePathBn254":
			// block 2 — the REAL commit-phase openings, in merklePath order:
			// leaf, sibs..., bits..., root.
			for qi := 0; qi < g.Count; qi++ {
				for _, rm := range qms[qi].rounds {
					w = append(w, rm.leaf)
					for _, s := range rm.sibs {
						w = append(w, s)
					}
					w = append(w, rm.bits...)
					w = append(w, rm.root)
				}
			}

		case "VerifyMerklePathBn254InputOpen":
			// block 2 — input-batch openings, fixed depth 18. Real path nodes +
			// real input-round root + real index bits, PLACEHOLDER leaf (0): the
			// input MMCS leaf hash and the true per-round depth are the designed,
			// un-modeled seam of the skeleton.
			d := firstParam(g, "depth")
			ir := len(fx.InputRounds)
			for i := 0; i < g.Count; i++ {
				qi := i / ir
				round := i % ir
				w = append(w, big.NewInt(0)) // placeholder leaf
				batch := fx.Queries[qi].InputOpenings[round]
				for l := 0; l < d; l++ {
					if l < len(batch.Path) {
						w = append(w, frToBig(parseBn254Hex(t, batch.Path[l])))
					} else {
						w = append(w, big.NewInt(0))
					}
				}
				domainIndex := uint(fx.Queries[qi].ExpectedIndex)
				for l := 0; l < d; l++ {
					if l < logMax {
						w = append(w, uint32((domainIndex>>uint(l))&1))
					} else {
						w = append(w, 0)
					}
				}
				root := fx.Queries[qi].InputOpenings[round].Path
				if len(root) > 0 {
					w = append(w, frToBig(parseBn254Hex(t, root[len(root)-1])))
				} else {
					w = append(w, big.NewInt(0))
				}
			}

		case "BatchTableInstance":
			// block 3 — the batch-STARK DAG instances. The DAG-input↔witness map
			// is intricate; since the emit-circuit already diverges upstream (the
			// input-open seam), these slots are zero fillers sized to the exact
			// per-instance budget so the assignment is COMPLETE and RUNS.
			for i := range c.sym.Instances {
				n := symInstanceVars(&c.sym.Instances[i])
				for k := 0; k < n; k++ {
					w = append(w, big.NewInt(0))
				}
			}

		case "LogUpBalance":
			// block 3 — one ext per instance summed to zero: real cumulative sums
			// where the count lines up, else zero (sum stays zero).
			for i := 0; i < c.vf.Shape.NumInstances; i++ {
				if i < len(ex.cumSums) {
					appendExtVars(ex.cumSums[i], &w)
				} else {
					for k := 0; k < 4; k++ {
						w = append(w, big.NewInt(0))
					}
				}
			}

		case "SampleBitsDecomposed":
			// block 4 — the real query index sample (< 2^logMax < 2^31).
			for i := 0; i < g.Count; i++ {
				w = append(w, uint32(fx.Queries[0].ExpectedIndex))
			}

		case "AssertPowBitsZero":
			// block 4 — a value whose low pow_bits are zero. The real grinding
			// sample is not a standalone fixture lane; 0 satisfies the shape.
			for i := 0; i < g.Count; i++ {
				w = append(w, big.NewInt(0))
			}

		case "AssertIsEqual":
			// block 5 — the real 25 claim lanes; block-5 Define equates each
			// against the exposed public-statement lane (both = claim), so this
			// segment binding holds.
			for i := 0; i < g.Count; i++ {
				w = append(w, claim[i])
			}
		}
	}

	if len(w) != len(c.W) {
		t.Fatalf("assignVerifierFull produced %d witness values, bank needs %d "+
			"(consumption drift vs Define)", len(w), len(c.W))
	}
	c.W = w
	return c
}

// assignVerifierFullPublics fills the exposed 25-lane statement in the pinned
// genesis8 ++ final8 ++ numTurns ++ chainDigest8 order (the twin of
// assignSettlementPublics for the emit-driven circuit).
func assignVerifierFullPublics(c *VerifierFullCircuit, claim []uint32) {
	k := 0
	for i := 0; i < DigestWidth; i++ {
		c.GenesisRoot[i] = claim[k]
		k++
	}
	for i := 0; i < DigestWidth; i++ {
		c.FinalRoot[i] = claim[k]
		k++
	}
	c.NumTurns = claim[k]
	k++
	for i := 0; i < DigestWidth; i++ {
		c.ChainDigest[i] = claim[k]
		k++
	}
}

// TestEmittedVerifierFullDifferential runs the emit-driven skeleton and the
// hand-Go SettlementCircuit on the SAME real fixture proof via test.IsSolved and
// records the raw result of each. The hand-Go circuit must accept (sanity floor);
// the emit-driven result is measured, not gated.
func TestEmittedVerifierFullDifferential(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	field := ecc.BN254.ScalarField()

	// --- hand-Go reference (the deployed-shape verifier) ---
	handErr := test.IsSolved(allocSettlementCircuit(t, fx, ex, sym),
		assignSettlementCircuit(t, fx, ex, sym), field)
	if handErr != nil {
		t.Fatalf("SANITY FLOOR VIOLATED: hand-Go SettlementCircuit rejected the real "+
			"proof + correct statement: %v", handErr)
	}
	t.Logf("hand-Go SettlementCircuit on real proof: ACCEPT")

	// --- emit-driven skeleton (structural ~20%) ---
	emitAlloc, err := AllocVerifierFullCircuit(loadVerifierFullT(t), sym)
	if err != nil {
		t.Fatalf("alloc emit-driven circuit: %v", err)
	}
	emitErr := test.IsSolved(emitAlloc, assignVerifierFull(t, fx, ex, sym), field)
	if emitErr == nil {
		t.Logf("emit-driven VerifierFullCircuit on real proof: ACCEPT")
	} else {
		t.Logf("emit-driven VerifierFullCircuit on real proof: REJECT — %v", emitErr)
	}

	// --- canary datapoint: a wrong public statement (num_turns tampered) ---
	// On a circuit that already rejects the honest assignment this is vacuous,
	// so we RECORD it rather than assert it.
	canary := assignVerifierFull(t, fx, ex, sym)
	canary.NumTurns = uint32(fx.TablePublics[fx.ClaimInstance][2*DigestWidth]) + 1
	canaryErr := test.IsSolved(emitAlloc, canary, field)
	if canaryErr == nil {
		t.Logf("emit-driven on TAMPERED statement (num_turns+1): ACCEPT (canary NOT caught)")
	} else {
		t.Logf("emit-driven on TAMPERED statement (num_turns+1): REJECT — %v", canaryErr)
	}
}
