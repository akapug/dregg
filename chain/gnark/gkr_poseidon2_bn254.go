// GKR-batched Poseidon2Bn254 — prototype of the next verification-preserving
// shrink of the SettlementCircuit after the open_input α-hoist.
//
// WHAT: the SettlementCircuit's remaining R1CS whale is native Poseidon2
// Merkle/leaf hashing (~316 perms/query × 38 queries = 12,008 permutations ≈
// 2.9M R1CS at ~243 R1CS/perm — see TestGkrPoseidon2PermCensus). GKR (the
// proven sum-check protocol, gnark std/gkr) can batch N instances of the SAME
// low-degree layered circuit behind one in-SNARK sum-check verifier whose cost
// is ~O(#wires · log N) instead of N · cost(perm).
//
// HOW: dregg's pinned Poseidon2Bn254<3> (poseidon2_bn254.go — WIDTH=3, d=5,
// R_F=8, R_P=56, HorizenLabs RC3 constants) is expressed as a GKR wire DAG:
//   - every S-box becomes ONE degree-5 gate that fuses the previous round's
//     linear layer and the round constant:  (Σ cᵢ·xᵢ + rc)^5
//     (the same regrouping gnark v0.15's gkr-poseidon2 uses for its t=2
//     instance — but THIS circuit is dregg's t=3 instance with dregg's
//     constants, so the batched hashes are bit-exact with poseidon2_bn254.go
//     and the Rust shrink layer's MMCS).
//   - partial rounds carry the two passive lanes through degree-1 gates.
//   - the compression output is the final external linear layer's lane 0.
//
// Gates are registered under "dregg.p2b.*" names in BOTH registries the v0.11
// GKR stack consults: gnark std/gkr Gates (the in-SNARK sum-check verifier)
// and gnark-crypto fr/gkr Gates (the out-of-circuit prover that runs inside
// the solve/prove hints). The two implementations of each gate are independent
// (frontend.API vs fr.Element) and are cross-checked by the parity test.
//
// Fiat–Shamir: the GKR transcript hash is the native Poseidon2Bn254 sponge
// (direct gadget calls — NOT GKR-batched, so no circularity; MiMC stays
// registered as the measurement baseline). The initial challenge is a
// multicommit commitment binding ALL batch inputs and outputs — without it
// the in-SNARK prover could grind the transcript (this mirrors gnark v0.15's
// gkrapi/compile.go, which seeds the transcript the same way).
//
// SOUNDNESS SHAPE: outputs come from the GKR solve hint (untrusted witness);
// Solution.Verify adds the sum-check verifier constraints that force
// out_i == Poseidon2Bn254Compress(left_i, right_i) for every instance. The
// parity test additionally pins the GKR outputs against the direct
// poseidon2_bn254.go gadget in the same circuit, bit-exact.
package friverifier

import (
	"fmt"
	"hash"
	"math/big"
	"sync"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	frgkr "github.com/consensys/gnark-crypto/ecc/bn254/fr/gkr"
	bn254mimc "github.com/consensys/gnark-crypto/ecc/bn254/fr/mimc"
	"github.com/consensys/gnark/constraint"
	bn254cs "github.com/consensys/gnark/constraint/bn254"
	"github.com/consensys/gnark/frontend"
	stdgkr "github.com/consensys/gnark/std/gkr"
	stdhash "github.com/consensys/gnark/std/hash"
	stdmimc "github.com/consensys/gnark/std/hash/mimc"
	"github.com/consensys/gnark/std/multicommit"
)

// ============================================================================
// The gate: (Σ coeffs[i]·x_i + rc)^d with d ∈ {1, 5}
// ============================================================================

// gkrP2GateSnark is the in-SNARK (sum-check verifier) side of a Poseidon2
// round gate. It is evaluated ONCE per wire, at the final claim check.
type gkrP2GateSnark struct {
	coeffs []int64
	rc     *big.Int // nil for the linear carry/output gates
	pow5   bool
}

func (g gkrP2GateSnark) Evaluate(api frontend.API, in ...frontend.Variable) frontend.Variable {
	if len(in) != len(g.coeffs) {
		panic(fmt.Sprintf("dregg.p2b gate: %d inputs, want %d", len(in), len(g.coeffs)))
	}
	acc := frontend.Variable(0)
	for i, c := range g.coeffs {
		acc = api.Add(acc, api.Mul(c, in[i]))
	}
	if g.rc != nil {
		acc = api.Add(acc, g.rc)
	}
	if !g.pow5 {
		return acc
	}
	x2 := api.Mul(acc, acc)
	x4 := api.Mul(x2, x2)
	return api.Mul(x4, acc)
}

func (g gkrP2GateSnark) Degree() int {
	if g.pow5 {
		return 5
	}
	return 1
}

// gkrP2GateFr is the native (prover hint) side of the same gate.
type gkrP2GateFr struct {
	coeffs []int64
	rc     *fr.Element // nil for linear gates
	pow5   bool
}

func (g gkrP2GateFr) Evaluate(in ...fr.Element) fr.Element {
	if len(in) != len(g.coeffs) {
		panic(fmt.Sprintf("dregg.p2b gate (fr): %d inputs, want %d", len(in), len(g.coeffs)))
	}
	var acc, t fr.Element
	for i, c := range g.coeffs {
		switch c {
		case 1:
			t = in[i]
		case 2:
			t.Double(&in[i])
		case 3:
			t.Double(&in[i])
			t.Add(&t, &in[i])
		default:
			panic("dregg.p2b gate (fr): unsupported coefficient")
		}
		acc.Add(&acc, &t)
	}
	if g.rc != nil {
		acc.Add(&acc, g.rc)
	}
	if !g.pow5 {
		return acc
	}
	var x2, x4 fr.Element
	x2.Mul(&acc, &acc)
	x4.Mul(&x2, &x2)
	acc.Mul(&x4, &acc)
	return acc
}

func (g gkrP2GateFr) Degree() int {
	if g.pow5 {
		return 5
	}
	return 1
}

// ============================================================================
// Gate registration (both registries, once)
// ============================================================================

// gkrP2LinName are the four shared linear-layer row shapes:
//
//	extR1 = M_E row 1 = [1,2,1]   extR2 = M_E row 2 = [1,1,2]
//	intR1 = M_I row 1 = [1,2,1] (== extR1, kept distinct for clarity of use)
//	intR2 = M_I row 2 = [1,1,3]   out   = M_E row 0 = [2,1,1]
const (
	gkrP2LinExtR1 = "dregg.p2b.lin.121"
	gkrP2LinExtR2 = "dregg.p2b.lin.112"
	gkrP2LinIntR2 = "dregg.p2b.lin.113"
	gkrP2LinOut   = "dregg.p2b.lin.211"
)

var gkrP2RegisterOnce sync.Once

func gkrP2Register(name string, coeffs []int64, rc *big.Int, pow5 bool) {
	var rcFr *fr.Element
	if rc != nil {
		var e fr.Element
		e.SetBigInt(rc)
		rcFr = &e
	}
	stdgkr.Gates[name] = gkrP2GateSnark{coeffs: coeffs, rc: rc, pow5: pow5}
	frgkr.Gates[name] = gkrP2GateFr{coeffs: coeffs, rc: rcFr, pow5: pow5}
}

// gkrP2FullGateName / gkrP2PartialGateName name the keyed S-box gates.
// Full rounds r ∈ [0,8) (0..3 initial, 4..7 terminal), lanes j ∈ [0,3);
// partial rounds k ∈ [0,56).
func gkrP2FullGateName(r, j int) string { return fmt.Sprintf("dregg.p2b.f.%d.%d", r, j) }
func gkrP2PartialGateName(k int) string { return fmt.Sprintf("dregg.p2b.p.%d", k) }

// registerGkrPoseidon2Gates registers every gate of the dregg Poseidon2Bn254
// GKR circuit and the MiMC transcript hash builders. Idempotent.
func registerGkrPoseidon2Gates() {
	gkrP2RegisterOnce.Do(func() {
		bn254InitRC() // materialise the RC3 constants (poseidon2_bn254.go)

		// Keyed S-box gates. Coefficient rows follow the wire layout of
		// gkrPoseidon2CompressWires below.
		//
		// Initial round 0 acts on the RAW compress inputs (L, R) with the
		// initial external linear layer folded in: M_E·(L,R,0) =
		// (2L+R, L+2R, L+R).
		rows0 := [3][]int64{{2, 1}, {1, 2}, {1, 1}}
		// Full rounds 1..3 and 5..7 act on the previous round's three S-box
		// outputs with M_E folded in.
		rowsE := [3][]int64{{2, 1, 1}, {1, 2, 1}, {1, 1, 2}}
		// Terminal round 4 (the first terminal full round) acts on the last
		// partial round's (u, b, c) with the INTERNAL matrix folded in.
		rowsI := [3][]int64{{2, 1, 1}, {1, 2, 1}, {1, 1, 3}}
		for j := 0; j < 3; j++ {
			gkrP2Register(gkrP2FullGateName(0, j), rows0[j], bn254RCExtInitial[0][j], true)
			for r := 1; r < 4; r++ {
				gkrP2Register(gkrP2FullGateName(r, j), rowsE[j], bn254RCExtInitial[r][j], true)
			}
			gkrP2Register(gkrP2FullGateName(4, j), rowsI[j], bn254RCExtTerminal[0][j], true)
			for r := 5; r < 8; r++ {
				gkrP2Register(gkrP2FullGateName(r, j), rowsE[j], bn254RCExtTerminal[r-4][j], true)
			}
		}
		// Partial-round S-box gates: row 0 of M_E (k=0, acting on round-3
		// S-box outputs) and of M_I (k≥1, acting on (u,b,c)) are both [2,1,1].
		for k := 0; k < 56; k++ {
			gkrP2Register(gkrP2PartialGateName(k), []int64{2, 1, 1}, bn254RCInternalBig[k], true)
		}
		// Shared linear gates (no round constant).
		gkrP2Register(gkrP2LinExtR1, []int64{1, 2, 1}, nil, false)
		gkrP2Register(gkrP2LinExtR2, []int64{1, 1, 2}, nil, false)
		gkrP2Register(gkrP2LinIntR2, []int64{1, 1, 3}, nil, false)
		gkrP2Register(gkrP2LinOut, []int64{2, 1, 1}, nil, false)

		// Fiat–Shamir transcript hashes, both sides. MiMC is kept registered
		// as the measurement baseline; the Poseidon2 sponge is the production
		// choice (gkrP2TranscriptHashName).
		bn254cs.RegisterHashBuilder("mimc", func() hash.Hash { return bn254mimc.NewMiMC() })
		stdhash.Register("mimc", func(api frontend.API) (stdhash.FieldHasher, error) {
			m, err := stdmimc.NewMiMC(api)
			return &m, err
		})
		bn254cs.RegisterHashBuilder(gkrP2TranscriptHashName, func() hash.Hash { return &gkrP2NativeHasher{} })
		stdhash.Register(gkrP2TranscriptHashName, func(api frontend.API) (stdhash.FieldHasher, error) {
			return &gkrP2FieldHasher{api: api}, nil
		})
	})
}

// ============================================================================
// The wire DAG (one compression = 195 wires, 193 proven)
// ============================================================================

// gkrPoseidon2CompressWires lays down the Poseidon2Bn254Compress DAG on a GKR
// API whose two input wires are (left, right); the capacity lane starts at the
// constant 0 and is folded into round 0's gates. Returns the output wire
// (lane 0 after the final external linear layer).
func gkrPoseidon2CompressWires(gk *stdgkr.API, left, right constraint.GkrVariable) constraint.GkrVariable {
	// Initial full rounds. t holds the current round's three S-box outputs.
	var t [3]constraint.GkrVariable
	for j := 0; j < 3; j++ {
		t[j] = gk.NamedGate(gkrP2FullGateName(0, j), left, right)
	}
	for r := 1; r < 4; r++ {
		var n [3]constraint.GkrVariable
		for j := 0; j < 3; j++ {
			n[j] = gk.NamedGate(gkrP2FullGateName(r, j), t[0], t[1], t[2])
		}
		t = n
	}

	// Partial rounds. State entering partial round k is (a_k, b_k, c_k);
	// a_k is never materialised (folded into the S-box gate), u_k is the
	// S-box output. Entry 0 comes from round 3's external layer (M_E rows);
	// thereafter the internal layer: b_{k+1} = u+2b+c, c_{k+1} = u+b+3c.
	u := gk.NamedGate(gkrP2PartialGateName(0), t[0], t[1], t[2])
	b := gk.NamedGate(gkrP2LinExtR1, t[0], t[1], t[2])
	c := gk.NamedGate(gkrP2LinExtR2, t[0], t[1], t[2])
	for k := 1; k < 56; k++ {
		nu := gk.NamedGate(gkrP2PartialGateName(k), u, b, c)
		nb := gk.NamedGate(gkrP2LinExtR1, u, b, c) // M_I row 1 == [1,2,1]
		nc := gk.NamedGate(gkrP2LinIntR2, u, b, c)
		u, b, c = nu, nb, nc
	}

	// Terminal full rounds. Round 4 folds the LAST internal linear layer
	// (M_I rows over (u,b,c)); rounds 5..7 fold M_E as usual.
	for j := 0; j < 3; j++ {
		t[j] = gk.NamedGate(gkrP2FullGateName(4, j), u, b, c)
	}
	for r := 5; r < 8; r++ {
		var n [3]constraint.GkrVariable
		for j := 0; j < 3; j++ {
			n[j] = gk.NamedGate(gkrP2FullGateName(r, j), t[0], t[1], t[2])
		}
		t = n
	}

	// Final external linear layer, lane 0 = the compression digest.
	return gk.NamedGate(gkrP2LinOut, t[0], t[1], t[2])
}

// ============================================================================
// Poseidon2 as the GKR Fiat–Shamir transcript hash
// ============================================================================
//
// The measured cost of the GKR verifier is dominated by the per-sum-check-round
// transcript hashing (H(name ‖ previous ‖ round-poly evals) per challenge, both
// std/fiat-shamir sides). MiMC absorbs ONE field element per ~330-R1CS block;
// the native Poseidon2Bn254 absorbs TWO per ~243-R1CS permutation — a ~2.7×
// cheaper transcript. These transcript permutations are DIRECT gadget calls
// (poseidon2_bn254.go), not GKR-batched, so there is no circularity — the GKR
// proof's own transcript never depends on the hashes being batched.
//
// Sponge shape (identical on both sides, cross-checked by the parity test):
// rate-2 overwrite sponge over the width-3 permutation, with the absorbed
// element COUNT pre-loaded into the capacity lane (length domain separation):
//
//	state = [0, 0, n]; per pair: state[0..1] = (e_{2i}, e_{2i+1}); permute
//	digest = final state[0]   (odd tail: state[1] = 0)

// gkrP2TranscriptHashName selects the transcript hash for the batch gadget.
const gkrP2TranscriptHashName = "dregg-p2b"

// gkrP2FieldHasher is the in-SNARK transcript hasher (std/hash.FieldHasher).
type gkrP2FieldHasher struct {
	api frontend.API
	buf []frontend.Variable
}

func (h *gkrP2FieldHasher) Write(data ...frontend.Variable) { h.buf = append(h.buf, data...) }
func (h *gkrP2FieldHasher) Reset()                          { h.buf = nil }

func (h *gkrP2FieldHasher) Sum() frontend.Variable {
	state := [bn254P3Width]frontend.Variable{0, 0, len(h.buf)}
	for i := 0; i < len(h.buf); i += 2 {
		state[0] = h.buf[i]
		if i+1 < len(h.buf) {
			state[1] = h.buf[i+1]
		} else {
			state[1] = 0
		}
		Poseidon2Bn254(h.api, &state)
	}
	return state[0]
}

// gkrP2NativeHasher is the prover-hint-side twin (stdlib hash.Hash over
// 32-byte big-endian fr elements, mirroring gnark-crypto mimc's Write
// contract: short single writes are left-padded — that is how the transcript
// feeds challenge NAMES).
type gkrP2NativeHasher struct {
	data []fr.Element
}

func (h *gkrP2NativeHasher) Write(p []byte) (int, error) {
	if len(p) > 0 && len(p) < fr.Bytes {
		pp := make([]byte, fr.Bytes)
		copy(pp[len(pp)-len(p):], p)
		p = pp
	}
	if len(p)%fr.Bytes != 0 {
		return 0, fmt.Errorf("gkr poseidon2 hasher: input is not a multiple of %d bytes", fr.Bytes)
	}
	for start := 0; start < len(p); start += fr.Bytes {
		var e fr.Element
		e.SetBytes(p[start : start+fr.Bytes])
		h.data = append(h.data, e)
	}
	return len(p), nil
}

func (h *gkrP2NativeHasher) Sum(b []byte) []byte {
	var state [bn254P3Width]fr.Element
	state[2].SetUint64(uint64(len(h.data)))
	for i := 0; i < len(h.data); i += 2 {
		state[0] = h.data[i]
		if i+1 < len(h.data) {
			state[1] = h.data[i+1]
		} else {
			state[1].SetZero()
		}
		poseidon2Bn254Ref(&state)
	}
	digest := state[0].Bytes()
	return append(b, digest[:]...)
}

func (h *gkrP2NativeHasher) Reset()         { h.data = nil }
func (h *gkrP2NativeHasher) Size() int      { return fr.Bytes }
func (h *gkrP2NativeHasher) BlockSize() int { return fr.Bytes }

// ============================================================================
// The batch gadget
// ============================================================================

// GkrBatchPoseidon2Bn254Compress computes out_i = Poseidon2Bn254Compress
// (left_i, right_i) for all i through ONE GKR batch: the values come from the
// GKR solve hint and Solution.Verify adds the sum-check verifier constraints
// proving every instance's permutation. len(left) must be a power of two
// (callers pad with duplicate instances).
//
// The transcript's initial challenge is a multicommit commitment over all
// inputs and outputs (the same binding gnark v0.15's gkrapi uses), so the
// in-SNARK Fiat–Shamir transcript is seeded by a value the prover cannot
// choose after the fact.
func GkrBatchPoseidon2Bn254Compress(api frontend.API, left, right []frontend.Variable) ([]frontend.Variable, error) {
	return gkrBatchPoseidon2Bn254CompressWithHash(api, left, right, gkrP2TranscriptHashName)
}

// gkrBatchPoseidon2Bn254CompressWithHash is the hash-parameterised core; the
// measurement test A/Bs the MiMC baseline against the Poseidon2 transcript.
func gkrBatchPoseidon2Bn254CompressWithHash(api frontend.API, left, right []frontend.Variable, hashName string) ([]frontend.Variable, error) {
	if len(left) != len(right) {
		return nil, fmt.Errorf("gkr poseidon2: %d left vs %d right inputs", len(left), len(right))
	}
	registerGkrPoseidon2Gates()

	gk := stdgkr.NewApi()
	l, err := gk.Import(left)
	if err != nil {
		return nil, fmt.Errorf("gkr poseidon2: import left: %w", err)
	}
	r, err := gk.Import(right)
	if err != nil {
		return nil, fmt.Errorf("gkr poseidon2: import right: %w", err)
	}
	outWire := gkrPoseidon2CompressWires(gk, l, r)

	solution, err := gk.Solve(api)
	if err != nil {
		return nil, fmt.Errorf("gkr poseidon2: solve: %w", err)
	}
	outs := solution.Export(outWire)

	bound := make([]frontend.Variable, 0, 3*len(left))
	bound = append(bound, left...)
	bound = append(bound, right...)
	bound = append(bound, outs...)
	multicommit.WithCommitment(api, func(api frontend.API, commitment frontend.Variable) error {
		return solution.Verify(hashName, commitment)
	}, bound...)

	return outs, nil
}
