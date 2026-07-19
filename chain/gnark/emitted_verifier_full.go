// GENERIC interpreter for the COMPACT full-verifier descriptor
// (schema "dregg.gnark.verifier_full.v1", emitted by
// Dregg2/Circuit/Emit/GnarkVerifier/EmitJson.lean `emitVerifierFullJson`,
// byte-pinned by #guard against chain/gnark/emitted/verifier_full.json).
//
// Unlike the flat toy grammar (emitted_interp.go: every constraint is an
// op-DAG node), this descriptor is the SIX-leaf `emitVerifier` composition
// (EmitVerifier.lean, one leaf per `verifyAlgoO` conjunct in disjoint
// `Nat.pair` variable blocks) tagged with the deployed apex-shrink fixture
// MULTIPLICITIES. The heavy constraint content is DEFERRED to interp time:
// this file materializes each gadget record by invoking the SAME hand-Go
// gadget the settlement circuit uses (Poseidon2Bn254 compress, BabyBear
// reduce/mul, the degree-4 extension mul, the Merkle-path walk, 31-bit range
// checks, and — for the batch-STARK block — the emitted symbolic-DAG
// evaluator), replicated `count` times over FRESH witness variables and
// wired per the emitted structure. Compiling the result to an R1CS confirms
// the whole op-set expands and lets us count the materialized constraints.
//
// Faithfulness posture (named, not silent). The Lean side is explicit
// (EmitJson.lean §4): the compact descriptor is NOT covered by
// `emit_faithful`; the interpreter's per-gadget expansion is the obligation,
// and the `derived` block is the parity oracle (fold_rows,
// commit/input_merkle_compressions, segment_lane_asserts). This interpreter
// asserts that parity before building (Plan.checkDerivedParity).
//
// TWO NAMED SEAMS surfaced by this expansion (see the report / block 3 + the
// scope note on ExpandBlock):
//
//  1. The "stark_constraint_dag" / "logup_sum" records (block 3) are NOT
//     self-contained in verifier_full.json — the manifest carries only the
//     per-instance degree_bits, not the constraint DAG. Their faithful
//     expansion requires the COMPANION emitted artifact
//     fixtures/shrink_symbolic_constraints.json (the same file
//     stark_constraint_interp.go loads + validates), supplied as `sym`. With
//     sym==nil block 3 fail-closes with a clear error rather than fabricating
//     a constraint DAG.
//
//  2. The compact descriptor models the composed `emitVerifier` (the six
//     refinement leaves), which is a STRUCTURAL abstraction of the verifier —
//     it does NOT carry the SettlementCircuit's full transcript-replay
//     challenger duplex, the native FRI fold arithmetic beyond the fold-row
//     ext-muls, or the open_input seed binding. So the materialized total is
//     the emitVerifier-leaf budget (dominated by the 8436 Merkle Poseidon2
//     compressions), which is SMALLER than the hand-Go SettlementCircuit's
//     ~12.87M; the delta is exactly those un-modeled settlement phases. The
//     report states the measured number and this gap plainly.
package friverifier

import (
	"encoding/json"
	"fmt"
	"os"

	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/rangecheck"
)

// ---------------------------------------------------------------------------
// §1  The v1 descriptor grammar (Go mirror of emitVerifierFullJson's JSON).
// ---------------------------------------------------------------------------

// VFShape is the fixture-shape block.
type VFShape struct {
	LogBlowup           int `json:"log_blowup"`
	NumQueries          int `json:"num_queries"`
	Rounds              int `json:"rounds"`
	LogFinalPolyLen     int `json:"log_final_poly_len"`
	MaxLogArity         int `json:"max_log_arity"`
	QueryPowBits        int `json:"query_pow_bits"`
	CommitPowBits       int `json:"commit_pow_bits"`
	ExtraQueryIndexBits int `json:"extra_query_index_bits"`
	LogGlobalMaxHeight  int `json:"log_global_max_height"`
	DigestWidth         int `json:"digest_width"`
	NumPublicLanes      int `json:"num_public_lanes"`
	ExtDegree           int `json:"ext_degree"`
	FoldArity           int `json:"fold_arity"`
	NumInstances        int `json:"num_instances"`
	InputRounds         int `json:"input_rounds"`
}

// VFVarBlock is one composition block (its Nat.pair key + verifyAlgoO role).
type VFVarBlock struct {
	Block   int    `json:"block"`
	PairKey int    `json:"pair_key"`
	Role    string `json:"role"`
}

// VFGadget is one compact gadget-invocation record: the composition block, the
// gnark gadget NAME (the leaf's own .gadgets name), the primitive the
// interpreter EXPANDS it through, the fixture-shape MULTIPLICITY, and the
// integer params the expansion needs (flat map key -> int list).
type VFGadget struct {
	Block  int              `json:"block"`
	Gadget string           `json:"gadget"`
	Expand string           `json:"expand"`
	Count  int              `json:"count"`
	Params map[string][]int `json:"params"`
}

// VFDerived is the parity oracle for the interpreter's unroll.
type VFDerived struct {
	FoldRows                 int `json:"fold_rows"`
	CommitMerkleCompressions int `json:"commit_merkle_compressions"`
	InputMerkleCompressions  int `json:"input_merkle_compressions"`
	SegmentLaneAsserts       int `json:"segment_lane_asserts"`
}

// VerifierFull is the parsed compact descriptor.
type VerifierFull struct {
	Schema    string       `json:"schema"`
	Name      string       `json:"name"`
	Fixture   string       `json:"fixture"`
	Source    string       `json:"source"`
	Shape     VFShape      `json:"shape"`
	VarBlocks []VFVarBlock `json:"var_blocks"`
	Gadgets   []VFGadget   `json:"gadgets"`
	Derived   VFDerived    `json:"derived"`
}

const verifierFullSchema = "dregg.gnark.verifier_full.v1"

// knownVFGadgets are the (gadget, expand) pairs this interpreter carries. A
// record naming anything else fail-closes: an unknown pair would mean an
// emitter recording an expansion this replayer does not implement.
var knownVFGadgets = map[[2]string]bool{
	{"AssertIsCanonical", "rangecheck"}:                            true,
	{"FriFoldRowArity2", "babybear_ext_mul"}:                       true,
	{"ExtAssertIsEqual", "babybear_ext_eq"}:                        true,
	{"VerifyMerklePathBn254", "poseidon2_bn254_compress"}:          true,
	{"VerifyMerklePathBn254InputOpen", "poseidon2_bn254_compress"}: true,
	{"BatchTableInstance", "stark_constraint_dag"}:                 true,
	{"LogUpBalance", "logup_sum"}:                                  true,
	{"SampleBitsDecomposed", "rangecheck"}:                         true,
	{"AssertPowBitsZero", "zero_low_bits"}:                         true,
	{"AssertIsEqual", "wire_eq"}:                                   true,
}

// inputBatchTemplatePaths maps a round's per-class row-width signature to the
// committed Lean-emitted multi-height MMCS batch-opening template
// (InputOpenBatchEmit.lean `batchData widths 18 katMask`, §12). The apex-shrink
// fixture's four input rounds (trace / quotient / preprocessed / permutation)
// share the height classes {18,17,12,3} and the {0,5,14} injection schedule but
// differ in per-class row widths; each shape has its own emitted template. Round
// 1 ([16,8,16,8]) is the originally-committed template; the other three shapes
// are emitted from the SAME `batchData` (proven by `inputOpenBatch_refines`,
// parametric over widths) at the deployed round widths.
var inputBatchTemplatePaths = map[string]string{
	"16,8,16,8":    "emitted/inputopen_batch_template.json",
	"80,300,8,132": "emitted/inputopen_batch_r0.json",
	"61,24,4,66":   "emitted/inputopen_batch_r2.json",
	"76,28,8,132":  "emitted/inputopen_batch_r3.json",
}

// widthsSig is the comma-joined per-class width signature used to key the batch
// templates and the descriptor round shapes.
func widthsSig(widths []int) string {
	s := ""
	for i, w := range widths {
		if i > 0 {
			s += ","
		}
		s += fmt.Sprintf("%d", w)
	}
	return s
}

// inputOpenRoundWidths reads the per-round per-class row widths from the
// input-open gadget's descriptor params: `round_widths` is the class widths of
// every input round flattened in round order, `class_heights` gives the shared
// (tallest-first) height classes — so its length is the per-round class count and
// its head is the batch-tree max log-height (maxLh = path depth). Returns
// [round][class] widths and maxLh.
func inputOpenRoundWidths(g VFGadget) ([][]int, int, error) {
	classHeights := g.Params["class_heights"]
	if len(classHeights) == 0 {
		return nil, 0, fmt.Errorf("VerifyMerklePathBn254InputOpen: missing class_heights param " +
			"(descriptor not extended with per-round height-class + row widths)")
	}
	nClasses := len(classHeights)
	maxLh := classHeights[0]
	flat := g.Params["round_widths"]
	if len(flat) == 0 || len(flat)%nClasses != 0 {
		return nil, 0, fmt.Errorf("VerifyMerklePathBn254InputOpen: round_widths length %d "+
			"is not a positive multiple of the class count %d", len(flat), nClasses)
	}
	nr := len(flat) / nClasses
	rw := make([][]int, nr)
	for r := 0; r < nr; r++ {
		rw[r] = flat[r*nClasses : (r+1)*nClasses]
	}
	return rw, maxLh, nil
}

// checkBatchTemplateShape fail-closes if a loaded batch template's own gadget
// provenance / boundary does not match the round it is being used for: the
// template's `VerifyOpenInputBatchBn254 [R, maxLh]` record and its single root
// boundary at var R must agree with the descriptor's round widths sum R and
// maxLh. This ties the emitted artifact to the shape the interpreter replays it
// at (an emitter/interpreter drift would be caught here, not silently wired).
func checkBatchTemplateShape(tpl *Template, R, maxLh int) error {
	if len(tpl.Gadgets) != 1 || tpl.Gadgets[0].Gadget != "VerifyOpenInputBatchBn254" {
		return fmt.Errorf("batch template %q: unexpected gadget provenance %v "+
			"(want a single VerifyOpenInputBatchBn254)", tpl.Name, tpl.Gadgets)
	}
	args := tpl.Gadgets[0].Args
	if len(args) != 2 || args[0] != R || args[1] != maxLh {
		return fmt.Errorf("batch template %q gadget args %v != expected [R=%d, maxLh=%d]",
			tpl.Name, args, R, maxLh)
	}
	if len(tpl.PublicInputs) != 1 || tpl.PublicInputs[0].Var != R {
		return fmt.Errorf("batch template %q: root boundary %v != single root at var %d",
			tpl.Name, tpl.PublicInputs, R)
	}
	return nil
}

// loadInputBatchTemplates loads (once per distinct round-widths shape) the
// Lean-emitted batch templates block 2b replays, cross-checking each against the
// descriptor's round shape.
func loadInputBatchTemplates(vf *VerifierFull) (map[string]*Template, error) {
	g, ok := vf.gadget("VerifyMerklePathBn254InputOpen")
	if !ok {
		return nil, nil
	}
	rw, maxLh, err := inputOpenRoundWidths(g)
	if err != nil {
		return nil, err
	}
	out := map[string]*Template{}
	for _, widths := range rw {
		sig := widthsSig(widths)
		if _, done := out[sig]; done {
			continue
		}
		path, ok := inputBatchTemplatePaths[sig]
		if !ok {
			return nil, fmt.Errorf("no emitted batch template for input-round widths [%s] "+
				"(emit batchData %v 18 katMask from InputOpenBatchEmit.lean)", sig, widths)
		}
		tpl, err := LoadTemplate(path)
		if err != nil {
			return nil, fmt.Errorf("load batch template %s: %w", path, err)
		}
		if err := checkBatchTemplateShape(tpl, sumInts(widths), maxLh); err != nil {
			return nil, err
		}
		out[sig] = tpl
	}
	return out, nil
}

// LoadVerifierFull reads and fail-closed-validates the compact descriptor.
func LoadVerifierFull(path string) (*VerifierFull, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	vf := &VerifierFull{}
	if err := json.Unmarshal(raw, vf); err != nil {
		return nil, err
	}
	if err := vf.Validate(); err != nil {
		return nil, fmt.Errorf("%s: %w", path, err)
	}
	return vf, nil
}

// Validate fail-closes on schema drift, unknown (gadget, expand) pairs,
// negative counts, and derived-parity violations against the gadget records.
func (vf *VerifierFull) Validate() error {
	if vf.Schema != verifierFullSchema {
		return fmt.Errorf("schema %q != %q", vf.Schema, verifierFullSchema)
	}
	for _, g := range vf.Gadgets {
		if !knownVFGadgets[[2]string{g.Gadget, g.Expand}] {
			return fmt.Errorf("unknown gadget/expand %q/%q (fail-closed: this replayer does not carry it)",
				g.Gadget, g.Expand)
		}
		if g.Count < 0 {
			return fmt.Errorf("gadget %q: negative count %d", g.Gadget, g.Count)
		}
	}
	return vf.checkDerivedParity()
}

// commitMerkleDepths reconstructs the per-round commit-phase Merkle depths from
// the VerifyMerklePathBn254 record's `depths` param (the emitter's
// [logGlobalMaxHeight-1-r]).
func (vf *VerifierFull) commitMerkleDepths() ([]int, error) {
	for _, g := range vf.Gadgets {
		if g.Gadget == "VerifyMerklePathBn254" {
			d := g.Params["depths"]
			if len(d) == 0 {
				return nil, fmt.Errorf("VerifyMerklePathBn254: empty depths param")
			}
			return d, nil
		}
	}
	return nil, fmt.Errorf("no VerifyMerklePathBn254 record")
}

func sumInts(xs []int) int {
	s := 0
	for _, x := range xs {
		s += x
	}
	return s
}

// checkDerivedParity asserts the descriptor's `derived` multiplicities equal
// what the interpreter will unroll from the gadget records + shape — the
// contract the Lean `derivedJson` comment names as the parity oracle.
func (vf *VerifierFull) checkDerivedParity() error {
	s := vf.Shape
	if got, want := vf.Derived.FoldRows, s.NumQueries*s.Rounds; got != want {
		return fmt.Errorf("derived fold_rows %d != num_queries*rounds %d", got, want)
	}
	depths, err := vf.commitMerkleDepths()
	if err != nil {
		return err
	}
	if got, want := vf.Derived.CommitMerkleCompressions, s.NumQueries*sumInts(depths); got != want {
		return fmt.Errorf("derived commit_merkle_compressions %d != num_queries*sum(depths) %d", got, want)
	}
	if got, want := vf.Derived.InputMerkleCompressions, s.NumQueries*s.InputRounds*s.LogGlobalMaxHeight; got != want {
		return fmt.Errorf("derived input_merkle_compressions %d != num_queries*input_rounds*log_global_max_height %d", got, want)
	}
	if got, want := vf.Derived.SegmentLaneAsserts, s.NumPublicLanes; got != want {
		return fmt.Errorf("derived segment_lane_asserts %d != num_public_lanes %d", got, want)
	}
	return nil
}

func (vf *VerifierFull) gadget(name string) (VFGadget, bool) {
	for _, g := range vf.Gadgets {
		if g.Gadget == name {
			return g, true
		}
	}
	return VFGadget{}, false
}

// ---------------------------------------------------------------------------
// §2  Witness bank + fresh-variable cursor.
// ---------------------------------------------------------------------------

// varCursor hands out the next fresh frontend variable from the flat witness
// bank the gadget expansion wires against. (For a COMPILE the concrete values
// are irrelevant; only the structure — how the gadgets are wired — determines
// the R1CS.)
type varCursor struct {
	w   []frontend.Variable
	pos int
}

func (c *varCursor) next() frontend.Variable {
	v := c.w[c.pos]
	c.pos++
	return v
}

func (c *varCursor) nextExt() BBExt {
	var e BBExt
	for i := range e {
		e[i] = c.next()
	}
	return e
}

// ---------------------------------------------------------------------------
// §3  Per-gadget witness budgets (kept in exact lock-step with §4's cursor
// consumption — Define asserts pos == len(w) at the end).
// ---------------------------------------------------------------------------

// symInstanceVars is the witness budget of one batch-STARK instance's DAG
// evaluation (all rows opened as fresh witness: TraceLocal/Next, PreLocal/Next,
// PermLocal/Next, Challenges, PermValues, PublicValues, 3 selectors, alpha,
// out).
func symInstanceVars(inst *SymInstance) int {
	ext := 2*inst.Width + 2*inst.PreWidth + inst.NumLookups /*PermLocal*/ +
		inst.NumLookups /*PermNext*/ + 2*inst.NumLookups /*Challenges*/ +
		inst.NumLookups /*PermValues*/ + 3 /*selectors*/ + 1 /*alpha*/ + 1 /*out*/
	return 4*ext + inst.NumPublicValues
}

// WitnessLen is the exact number of fresh variables Define consumes for this
// descriptor (+ the companion sym DAG for block 3).
func (vf *VerifierFull) WitnessLen(sym *SymbolicConstraints) (int, error) {
	n := 0
	for _, g := range vf.Gadgets {
		switch g.Gadget {
		case "AssertIsCanonical":
			n += g.Count * 1
		case "FriFoldRowArity2":
			// chained: one running ext accumulator + one fixed ext operand,
			// reused across all `count` ext-muls (cost identical to fresh
			// var*var muls; keeps the bank small).
			n += 8
		case "ExtAssertIsEqual":
			n += g.Count * 8 // fresh (a,b) ext pair per equality
		case "VerifyMerklePathBn254":
			depths := g.Params["depths"]
			for q := 0; q < g.Count; q++ {
				for _, d := range depths {
					n += 2 + 2*d // leaf + root + d siblings + d bits
				}
			}
		case "VerifyMerklePathBn254InputOpen":
			// Block 2b: one Lean-emitted multi-height MMCS batch opening per
			// (query, input-round). Each binds R = sum(round widths) opened row
			// limbs, the input root, and maxLh (sibling, path-bit) pairs; the
			// Poseidon leaf hashes + path walk are SOLVED by ReplayClosed (not in
			// the bank). Rounds have different widths, so sum per round.
			rw, maxLh, err := inputOpenRoundWidths(g)
			if err != nil {
				return 0, err
			}
			nq := firstParam(g, "num_queries")
			for q := 0; q < nq; q++ {
				for r := range rw {
					n += sumInts(rw[r]) + 1 + 2*maxLh
				}
			}
		case "BatchTableInstance":
			if sym == nil {
				return 0, errBlock3NeedsSym
			}
			for i := range sym.Instances {
				n += symInstanceVars(&sym.Instances[i])
			}
		case "LogUpBalance":
			// global cumulative-sum balance: one fresh ext per instance,
			// summed to zero.
			n += 4 * vf.Shape.NumInstances
		case "SampleBitsDecomposed":
			n += g.Count * 1
		case "AssertPowBitsZero":
			n += g.Count * 1
		case "AssertIsEqual":
			// block 5: one fresh claim-lane witness per public lane, each equated
			// against the exposed public-statement lane (not a fresh pair).
			n += g.Count * 1
		}
	}
	return n, nil
}

func firstParam(g VFGadget, key string) int {
	if v := g.Params[key]; len(v) > 0 {
		return v[0]
	}
	return 0
}

var errBlock3NeedsSym = fmt.Errorf("block 3 (BatchTableInstance/stark_constraint_dag + LogUpBalance) " +
	"is NOT self-contained in verifier_full.json: it carries only degree_bits, not the constraint DAG. " +
	"Supply the companion emitted artifact fixtures/shrink_symbolic_constraints.json as `sym` " +
	"(the same file stark_constraint_interp.go loads)")

// ---------------------------------------------------------------------------
// §4  The circuit — replay each gadget record through the hand-Go gadget.
// ---------------------------------------------------------------------------

// VerifierFullCircuit materializes the compact descriptor. It EXPOSES the same
// 25-lane public settlement statement the hand-Go SettlementCircuit does
// (Publics: genesis_root[8] ++ final_root[8] ++ num_turns ++ chain_digest[8],
// the pinned order shared with DreggSettlement.sol) — so the emit-driven circuit
// carries a public statement and block 5's segment binding equates the
// transcript-absorbed claim lanes against it, exactly as SettlementCircuit.Define
// does. W is the flat witness bank (all secret) the expansion wires against;
// vf/sym are structural (unexported: ignored by the gnark schema walker).
type VerifierFullCircuit struct {
	Publics

	W []frontend.Variable

	vf  *VerifierFull
	sym *SymbolicConstraints

	// batchTpls holds the Lean-emitted multi-height MMCS batch-opening templates
	// (InputOpenBatchEmit.lean `batchData`) keyed by a round's per-class
	// row-width signature. Block 2b replays these through ReplayClosed to bind
	// the real input openings to the committed input roots. Loaded by
	// AllocVerifierFullCircuit from the committed emitted/ artifacts.
	batchTpls map[string]*Template
}

// publicLane returns the i-th lane of the pinned 25-lane public statement in the
// genesis8 ++ final8 ++ numTurns ++ chainDigest8 order (i in [0, NumPublicInputs)).
func (c *VerifierFullCircuit) publicLane(i int) frontend.Variable {
	switch {
	case i < DigestWidth:
		return c.GenesisRoot[i]
	case i < 2*DigestWidth:
		return c.FinalRoot[i-DigestWidth]
	case i == 2*DigestWidth:
		return c.NumTurns
	default:
		return c.ChainDigest[i-2*DigestWidth-1]
	}
}

// AllocVerifierFullCircuit builds a compile-ready template (W sized to the
// exact witness budget). sym is REQUIRED for block 3; pass the loaded
// fixtures/shrink_symbolic_constraints.json.
func AllocVerifierFullCircuit(vf *VerifierFull, sym *SymbolicConstraints) (*VerifierFullCircuit, error) {
	n, err := vf.WitnessLen(sym)
	if err != nil {
		return nil, err
	}
	batchTpls, err := loadInputBatchTemplates(vf)
	if err != nil {
		return nil, err
	}
	return &VerifierFullCircuit{
		W:         make([]frontend.Variable, n),
		vf:        vf,
		sym:       sym,
		batchTpls: batchTpls,
	}, nil
}

func (c *VerifierFullCircuit) Define(api frontend.API) error {
	if c.vf == nil {
		return fmt.Errorf("VerifierFullCircuit: descriptor not attached")
	}
	bb := NewBBApi(api)
	rc := rangecheck.New(api)
	cur := &varCursor{w: c.W}

	for _, g := range c.vf.Gadgets {
		if err := c.expand(api, bb, rc, cur, g); err != nil {
			return err
		}
	}
	if cur.pos != len(c.W) {
		return fmt.Errorf("witness-budget drift: Define consumed %d, bank has %d", cur.pos, len(c.W))
	}
	return nil
}

func (c *VerifierFullCircuit) expand(api frontend.API, bb *BBApi, rc frontend.Rangechecker,
	cur *varCursor, g VFGadget) error {
	switch g.Gadget {

	// block 0 — canonicity / VK-shape pin: the 2×31-bit range check
	// (babybear.go AssertIsCanonical), exactly the canonicityData leaf.
	case "AssertIsCanonical":
		for i := 0; i < g.Count; i++ {
			bb.AssertIsCanonical(cur.next())
		}

	// block 1 — FRI commit-phase fold rows: `count` degree-4 extension
	// multiplies (babybear_ext.go ExtMul), the dominant nonlinear op of
	// friFoldRowArity2. Chained on a running accumulator (var*var cost is
	// operand-independent).
	case "FriFoldRowArity2":
		x := cur.nextExt()
		b := cur.nextExt()
		for i := 0; i < g.Count; i++ {
			x = bb.ExtMul(x, b)
		}
		// pin the accumulator so it is not dead-code-eliminated.
		bb.ExtAssertIsEqual(x, x)

	// block 1 — the fold's claimed==folded equality: `count` extension
	// equalities (babybear_ext.go ExtAssertIsEqual).
	case "ExtAssertIsEqual":
		for i := 0; i < g.Count; i++ {
			a := cur.nextExt()
			b := cur.nextExt()
			bb.ExtAssertIsEqual(a, b)
		}

	// block 2 — commit-phase Merkle openings: for each of `count` queries, a
	// depth-d authentication-path verification per round depth d (merkle_bn254.go
	// VerifyMerklePathBn254 → d Poseidon2Bn254 compressions). Materializes
	// derived.commit_merkle_compressions = count*sum(depths).
	case "VerifyMerklePathBn254":
		depths := g.Params["depths"]
		for q := 0; q < g.Count; q++ {
			for _, d := range depths {
				c.merklePath(api, cur, d)
			}
		}

	// block 2b — input-batch openings, the REAL deployed multi-height MMCS batch
	// tree (verifyOpenInputBatchNative). For each (query, input-round) this
	// replays the Lean-emitted `batchData` template (InputOpenBatchEmit.lean) via
	// ReplayClosed: it binds the class-concatenated opened row limbs, the
	// committed input root, and the (sibling, path-bit) pairs by the template's
	// index layout, and the replay SOLVES the per-class MultiField leaf hashes +
	// the injection-interleaved arity-2 path walk and KEEPS the real
	// recomputed-root == root check. This is the Lean-authored input-open AIR,
	// NOT the placeholder-leaf plain path the skeleton previously carried.
	case "VerifyMerklePathBn254InputOpen":
		return c.expandInputOpenBatch(api, cur, g)

	// block 3 — batch-STARK constraint algebra: for each of the `count`
	// instances, evaluate the emitted symbolic DAG at zeta and bind the folded
	// value (stark_constraint_interp.go evalSymbolicFoldedNative — the SAME
	// evaluator VerifyShrinkStarkAlgebra drives). NEEDS the companion DAG.
	case "BatchTableInstance":
		if c.sym == nil {
			return errBlock3NeedsSym
		}
		if len(c.sym.Instances) != g.Count {
			return fmt.Errorf("BatchTableInstance count %d != companion DAG instances %d",
				g.Count, len(c.sym.Instances))
		}
		for i := range c.sym.Instances {
			c.starkInstance(bb, cur, &c.sym.Instances[i])
		}

	// block 3 — global LogUp balance: all cumulative sums add to zero
	// (stark_verify_native.go global WitnessChecks balance). Modeled as the
	// ext-sum-to-zero over one accumulator per instance — the assignment feeds
	// each instance's PARTIAL cumulative sum, so this NumInstances-wide sum is
	// the true global balance (assignVerifierFull, block 3).
	case "LogUpBalance":
		sum := BBExt{0, 0, 0, 0}
		for i := 0; i < c.vf.Shape.NumInstances; i++ {
			sum = bb.ExtAdd(sum, cur.nextExt())
		}
		bb.ExtAssertIsEqual(sum, BBExt{0, 0, 0, 0})

	// block 4 — grinding-PoW query index sample: a 31-bit range check
	// (challenger SampleBitsDecomposed's canonical-decomposition cost).
	case "SampleBitsDecomposed":
		bits := firstParam(g, "bits")
		for i := 0; i < g.Count; i++ {
			rc.Check(cur.next(), bits)
		}

	// block 4 — the PoW target: the low `pow_bits` bits of the sample are zero
	// (grinding.go CheckWitness's sample_bits(bits)==0). Decompose to 31 bits,
	// assert the low pow_bits are 0.
	case "AssertPowBitsZero":
		powBits := firstParam(g, "pow_bits")
		for i := 0; i < g.Count; i++ {
			decomp := api.ToBinary(cur.next(), 31)
			for k := 0; k < powBits && k < len(decomp); k++ {
				api.AssertIsEqual(decomp[k], 0)
			}
		}

	// block 5 — settlement segment bind: `count` = num_public_lanes wire
	// equalities (segmentData's AssertIsEqual per lane). Each transcript-absorbed
	// claim lane (a fresh witness — the expose_claim public value) is equated
	// against the corresponding EXPOSED public-statement lane, in the pinned
	// genesis8 ++ final8 ++ numTurns ++ chainDigest8 order — the same 25-lane
	// settlement binding SettlementCircuit.Define performs.
	case "AssertIsEqual":
		for i := 0; i < g.Count; i++ {
			api.AssertIsEqual(cur.next(), c.publicLane(i))
		}
	}
	return nil
}

// expandInputOpenBatch replays the Lean-emitted multi-height MMCS batch-opening
// template for every (query, input-round). It consumes the flat witness bank in
// lock-step with WitnessLen and assignVerifierFull: per (query, round), R row
// limbs (class-concatenated, tallest-first), then the root, then maxLh
// (sibling, path-bit) pairs. Each opening is bound into its round's template BY
// INDEX (rows at 0..R-1, root at R, sibling s at R+1+2s, bit s at R+1+2s+1 —
// InputOpenBatchEmit.lean §9) and ReplayClosed solves the Poseidon internals and
// keeps the batch-walk recomputed-root == root check.
func (c *VerifierFullCircuit) expandInputOpenBatch(api frontend.API, cur *varCursor, g VFGadget) error {
	rw, maxLh, err := inputOpenRoundWidths(g)
	if err != nil {
		return err
	}
	nq := firstParam(g, "num_queries")
	for q := 0; q < nq; q++ {
		for r := range rw {
			R := sumInts(rw[r])
			tpl := c.batchTpls[widthsSig(rw[r])]
			if tpl == nil {
				return fmt.Errorf("no batch template loaded for input-round widths [%s]", widthsSig(rw[r]))
			}
			b := make(map[int]frontend.Variable, R+1+2*maxLh)
			for i := 0; i < R; i++ {
				b[i] = cur.next() // opened row limb i (class-concatenated)
			}
			b[R] = cur.next() // committed input root
			for s := 0; s < maxLh; s++ {
				b[R+1+2*s] = cur.next()   // sibling s
				b[R+1+2*s+1] = cur.next() // path bit s
			}
			if err := ReplayClosed(api, *tpl, b); err != nil {
				return fmt.Errorf("query %d input-round %d batch open (Lean template %q): %w",
					q, r, tpl.Name, err)
			}
		}
	}
	return nil
}

// merklePath verifies one depth-d authentication path against a fresh root,
// wiring d fresh siblings + d fresh path bits + a fresh leaf (d Poseidon2Bn254
// compressions). This is exactly VerifyMerklePathBn254 (merkle_bn254.go).
func (c *VerifierFullCircuit) merklePath(api frontend.API, cur *varCursor, d int) {
	leaf := cur.next()
	sibs := make([]frontend.Variable, d)
	bits := make([]frontend.Variable, d)
	for i := 0; i < d; i++ {
		sibs[i] = cur.next()
	}
	for i := 0; i < d; i++ {
		bits[i] = cur.next()
	}
	root := cur.next()
	VerifyMerklePathBn254(api, leaf, sibs, bits, root)
}

// starkInstance materializes one batch-STARK instance's DAG evaluation over
// fresh witness inputs, binding the folded value to a fresh output — the same
// shape as settlement_profile_test.go's symEvalProfileCircuit, driven by the
// emitted symbolic DAG (stark_constraint_interp.go).
func (c *VerifierFullCircuit) starkInstance(bb *BBApi, cur *varCursor, inst *SymInstance) {
	extVec := func(n int) []BBExt {
		out := make([]BBExt, n)
		for i := range out {
			out[i] = cur.nextExt()
		}
		return out
	}
	in := symEvalInputsNative{
		TraceLocal: extVec(inst.Width),
		TraceNext:  extVec(inst.Width),
		PreLocal:   extVec(inst.PreWidth),
		PreNext:    extVec(inst.PreWidth),
		PermLocal:  extVec(inst.NumLookups),
		PermNext:   extVec(inst.NumLookups),
		Challenges: extVec(2 * inst.NumLookups),
		PermValues: extVec(inst.NumLookups),
		Sel: starkSelectorsNative{
			isFirstRow:   cur.nextExt(),
			isLastRow:    cur.nextExt(),
			isTransition: cur.nextExt(),
		},
	}
	if inst.NumPublicValues > 0 {
		pv := make([]BBExt, inst.NumPublicValues)
		for i := range pv {
			pv[i] = BBExt{cur.next(), 0, 0, 0} // base-field public value lifted
		}
		in.PublicValues = pv
	}
	alpha := cur.nextExt()
	out := cur.nextExt()
	folded := evalSymbolicFoldedNative(bb, inst, in, alpha)
	bb.ExtAssertIsEqual(folded, out)
}
