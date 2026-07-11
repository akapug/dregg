package friverifier

import (
	"math/rand"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// ---------------------------------------------------------------------------
// Fixture builder: run a tiny single-round-set FRI commit phase in-Go and read
// off one query's openings. With log_blowup = log_final_poly_len = 0 the domain
// of size 2^R folds all the way down to a single constant (the final poly), so
// every query index folds to that same constant and passes by construction —
// an honest, non-vacuous VALID fixture without a full coset IDFT (that, plus a
// realistic blowup, is a named residual — see bottom of file).
// ---------------------------------------------------------------------------

func buildValidFixtureRef(R int, seed int64, index int) *friQueryFixture {
	rng := rand.New(rand.NewSource(seed))
	lane := func() uint32 { return uint32(rng.Uint64() % BabyBearP) }
	ext := func() bbExtRef { return bbExtRef{lane(), lane(), lane(), lane()} }

	N := 1 << R
	f0 := make([]bbExtRef, N)
	for i := range f0 {
		f0[i] = ext()
	}
	betas := make([]bbExtRef, R)
	for i := range betas {
		betas[i] = ext()
	}

	// Fold the whole vector down, keeping each round's committed vector.
	fs := [][]bbExtRef{f0}
	for r := 0; r < R; r++ {
		fs = append(fs, foldVectorRef(fs[r], betas[r], R, r))
	}
	final := fs[R][0] // size-1 final domain

	fx := &friQueryFixture{
		R:           R,
		Betas:       betas,
		InitialEval: f0[index],
		FinalEval:   final,
	}
	fx.IndexBits = make([]uint32, R)
	for i := 0; i < R; i++ {
		fx.IndexBits[i] = uint32((index >> i) & 1)
	}
	for r := 0; r < R; r++ {
		root, layers := merkleCommitRef(fs[r])
		fx.CommitRoots = append(fx.CommitRoots, root)
		parent := index >> (r + 1)
		fx.MerkleProofs = append(fx.MerkleProofs, merkleOpenRef(layers, parent))
		bR := (index >> r) & 1
		fx.Siblings = append(fx.Siblings, fs[r][2*parent+(1-bR)])
	}
	return fx
}

// ---------------------------------------------------------------------------
// gnark wrapper circuit for the gadget.
// ---------------------------------------------------------------------------

type friQueryTestCircuit struct {
	R            int
	CommitRoots  [][DigestWidth]frontend.Variable
	Betas        []BBExt
	Siblings     []BBExt
	MerkleProofs [][][DigestWidth]frontend.Variable
	IndexBits    []frontend.Variable
	InitialEval  BBExt
	FinalEval    BBExt
}

func (c *friQueryTestCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	VerifyFriQuery(bb, c.R, c.CommitRoots, c.Betas, c.Siblings, c.MerkleProofs,
		c.IndexBits, c.InitialEval, c.FinalEval)
	return nil
}

func newFriQueryTestCircuit(R int) *friQueryTestCircuit {
	c := &friQueryTestCircuit{R: R}
	c.CommitRoots = make([][DigestWidth]frontend.Variable, R)
	c.Betas = make([]BBExt, R)
	c.Siblings = make([]BBExt, R)
	c.IndexBits = make([]frontend.Variable, R)
	c.MerkleProofs = make([][][DigestWidth]frontend.Variable, R)
	for r := 0; r < R; r++ {
		c.MerkleProofs[r] = make([][DigestWidth]frontend.Variable, R-r-1)
	}
	return c
}

func extToVars(e bbExtRef) BBExt { return BBExt{e[0], e[1], e[2], e[3]} }

func assignFriQueryTestCircuit(fx *friQueryFixture) *friQueryTestCircuit {
	c := newFriQueryTestCircuit(fx.R)
	for r := 0; r < fx.R; r++ {
		for i := 0; i < DigestWidth; i++ {
			c.CommitRoots[r][i] = fx.CommitRoots[r][i]
		}
		c.Betas[r] = extToVars(fx.Betas[r])
		c.Siblings[r] = extToVars(fx.Siblings[r])
		c.IndexBits[r] = fx.IndexBits[r]
		for l := range fx.MerkleProofs[r] {
			for i := 0; i < DigestWidth; i++ {
				c.MerkleProofs[r][l][i] = fx.MerkleProofs[r][l][i]
			}
		}
	}
	c.InitialEval = extToVars(fx.InitialEval)
	c.FinalEval = extToVars(fx.FinalEval)
	return c
}

// ---------------------------------------------------------------------------
// Table sanity: the two-adic generator constants are canonical and squaring
// drops the index (g_m^2 = g_{m-1}); the inverse table is correct. This anchors
// the whole coset/fold-divisor derivation.
// ---------------------------------------------------------------------------

func TestTwoAdicGeneratorTableRef(t *testing.T) {
	if twoAdicGeneratorsRef[1] != uint32(BabyBearP-1) {
		t.Fatalf("g_1 = %d, want p-1 (the order-2 generator, -1)", twoAdicGeneratorsRef[1])
	}
	for m := 1; m < len(twoAdicGeneratorsRef); m++ {
		if bbMulRef(twoAdicGeneratorsRef[m], twoAdicGeneratorsRef[m]) != twoAdicGeneratorsRef[m-1] {
			t.Fatalf("g_%d^2 != g_%d (table not canonical order-2^m generators)", m, m-1)
		}
		if bbMulRef(twoAdicGeneratorsRef[m], twoAdicGenInvRef[m]) != 1 {
			t.Fatalf("ginv_%d is not the inverse of g_%d", m, m)
		}
	}
}

// ---------------------------------------------------------------------------
// ACCEPT: a valid fixture verifies in BOTH the native reference AND the gadget,
// for every query index (all fold/index-bit patterns).
// ---------------------------------------------------------------------------

func TestFriQueryAcceptsRefAndGadget(t *testing.T) {
	const R = 3
	field := ecc.BN254.ScalarField()
	for index := 0; index < (1 << R); index++ {
		fx := buildValidFixtureRef(R, 100+int64(index), index)

		if !verifyFriQueryRef(fx) {
			t.Fatalf("index %d: valid fixture REJECTED by reference", index)
		}
		if err := test.IsSolved(newFriQueryTestCircuit(R), assignFriQueryTestCircuit(fx), field); err != nil {
			t.Fatalf("index %d: valid fixture rejected by gadget: %v", index, err)
		}
	}
}

// ---------------------------------------------------------------------------
// REJECT (load-bearing): each single tamper must FAIL in both the reference and
// the gadget. Every case is ref-guarded (the untampered fixture passes, the
// tampered one fails the reference) so the gadget reject is non-vacuous.
// ---------------------------------------------------------------------------

func TestFriQueryRejectsTampers(t *testing.T) {
	const R = 3
	const index = 5 // bits 101 — exercises both fold orientations
	field := ecc.BN254.ScalarField()

	cases := []struct {
		name   string
		tamper func(fx *friQueryFixture)
	}{
		{
			// Tampered queried leaf value: round-0 leaf hash diverges.
			name: "leaf-value",
			tamper: func(fx *friQueryFixture) {
				fx.InitialEval[0] = bbAddRef(fx.InitialEval[0], 1)
			},
		},
		{
			// Tampered sibling EVALUATION: round-0 leaf hash diverges.
			name: "sibling-eval",
			tamper: func(fx *friQueryFixture) {
				fx.Siblings[0][0] = bbAddRef(fx.Siblings[0][0], 1)
			},
		},
		{
			// Wrong Merkle authentication path: a corrupted sibling digest
			// makes the recomputed root diverge from the commitment.
			name: "merkle-sibling-digest",
			tamper: func(fx *friQueryFixture) {
				fx.MerkleProofs[0][0][0] = bbAddRef(fx.MerkleProofs[0][0][0], 1)
			},
		},
		{
			// Wrong fold (bad beta) on the LAST round: its Merkle check still
			// passes (uses the carry from the prior round), but the final
			// folded value diverges from the final-poly constant.
			name: "bad-beta-final-round",
			tamper: func(fx *friQueryFixture) {
				fx.Betas[R-1][0] = bbAddRef(fx.Betas[R-1][0], 1)
			},
		},
		{
			// Wrong final-polynomial evaluation.
			name: "final-eval",
			tamper: func(fx *friQueryFixture) {
				fx.FinalEval[0] = bbAddRef(fx.FinalEval[0], 1)
			},
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			// Ref-guard: the untampered fixture passes.
			base := buildValidFixtureRef(R, 7, index)
			if !verifyFriQueryRef(base) {
				t.Fatalf("%s: base fixture rejected — guard broken", tc.name)
			}
			// Tamper and require reference rejection (non-vacuous).
			fx := buildValidFixtureRef(R, 7, index)
			tc.tamper(fx)
			if verifyFriQueryRef(fx) {
				t.Fatalf("%s: reference ACCEPTED a tampered fixture (vacuous reject)", tc.name)
			}
			// The gadget must also reject.
			if err := test.IsSolved(newFriQueryTestCircuit(R), assignFriQueryTestCircuit(fx), field); err == nil {
				t.Fatalf("%s: gadget ACCEPTED a tampered fixture", tc.name)
			}
		})
	}
}

// ---------------------------------------------------------------------------
// Differential: gadget and reference agree (accept/reject) over many random
// valid fixtures and many single-lane tampers.
// ---------------------------------------------------------------------------

func TestFriQueryDifferentialRefVsGadget(t *testing.T) {
	const R = 3
	field := ecc.BN254.ScalarField()
	rng := rand.New(rand.NewSource(2026))

	agree := func(fx *friQueryFixture, label string) {
		refOK := verifyFriQueryRef(fx)
		err := test.IsSolved(newFriQueryTestCircuit(R), assignFriQueryTestCircuit(fx), field)
		gadgetOK := err == nil
		if refOK != gadgetOK {
			t.Fatalf("%s: ref=%v gadget=%v (disagree); gadget err=%v", label, refOK, gadgetOK, err)
		}
	}

	for iter := 0; iter < 12; iter++ {
		index := int(rng.Intn(1 << R))
		fx := buildValidFixtureRef(R, int64(1000+iter), index)
		agree(fx, "valid")

		// A random single-lane tamper somewhere in the proof.
		bad := buildValidFixtureRef(R, int64(1000+iter), index)
		switch rng.Intn(5) {
		case 0:
			bad.InitialEval[rng.Intn(4)] = bbAddRef(bad.InitialEval[rng.Intn(4)], 1)
		case 1:
			r := rng.Intn(R)
			bad.Siblings[r][rng.Intn(4)] = bbAddRef(bad.Siblings[r][rng.Intn(4)], 1)
		case 2:
			r := rng.Intn(R)
			if len(bad.MerkleProofs[r]) > 0 {
				l := rng.Intn(len(bad.MerkleProofs[r]))
				bad.MerkleProofs[r][l][rng.Intn(DigestWidth)] = bbAddRef(bad.MerkleProofs[r][l][rng.Intn(DigestWidth)], 1)
			} else {
				bad.CommitRoots[r][rng.Intn(DigestWidth)] = bbAddRef(bad.CommitRoots[r][rng.Intn(DigestWidth)], 1)
			}
		case 3:
			bad.Betas[R-1][rng.Intn(4)] = bbAddRef(bad.Betas[R-1][rng.Intn(4)], 1)
		case 4:
			bad.FinalEval[rng.Intn(4)] = bbAddRef(bad.FinalEval[rng.Intn(4)], 1)
		}
		agree(bad, "tampered")
	}
}

// RESIDUAL — what this lane does NOT cover, for the next FRI wrap milestone:
//
//   - open_input / reduced openings (fri/src/verifier.rs:271, :523): the seed
//     folded_eval here is provided directly. The full batch-STARK forms it by
//     alpha-batching (f(z)-f(x))/(z-x) across every opened matrix and rolling in
//     lower-height reduced openings at their fold round with a beta^arity factor
//     (verifier.rs:477). That is the per-table degree_bits + multi-height
//     structure.
//   - higher arity: max_log_arity 3 in ir2_leaf_wrap_config. Arity 2^k folds
//     decompose into k sequential arity-2 folds with beta, beta^2, ...
//     (two_adic_pcs.rs:160), the immediate extension of this gadget.
//   - realistic blowup + genuine RS codeword: this fixture uses log_blowup=0 so
//     the final domain is a single point. A production-shaped fixture needs a
//     real coset IDFT so final_poly has length 2^log_final_poly_len and the
//     Horner evaluation at x = g^rev(domain_index) is exercised.
//   - the logup interaction bus and the four non-primitive op tables
//     (Poseidon2-w16/w24, recompose, expose_claim).
//   - challenger wiring: betas/index arrive pre-sampled here; the assembly wires
//     challenger.go (Observe roots -> Sample betas; SampleBits for the index
//     after CheckWitness) around this gadget.
