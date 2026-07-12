// GENERIC symbolic-constraint interpreter — the metaprogrammed constraint
// evaluation for the batch-STARK algebra layer (stark_verify_native.go).
//
// The constraints are NOT hand-encoded: they are extracted from the shrink
// tables' AIRs by the verifier's own symbolic path
// (p3_batch_stark::symbolic::get_symbolic_constraints at the pinned rev,
// which runs LogUpGadget::eval_air_and_lookups over an
// InteractionSymbolicBuilder) and emitted as an expression DAG by
// ~/dev/plonky3-recursion/circuit-prover/tests/emit_shrink_symbolic.rs into
// fixtures/shrink_symbolic_constraints.json. One interpreter evaluates ALL
// instances' constraints at zeta over the BBApi extension gadget — the exact
// trees the prover folded, in the exact global order (acc = acc*alpha + C).
//
// Correctness arbiter: on the REAL shrink proof the interpreted folded value
// must satisfy the quotient identity folded == quotient(zeta)·Z_H(zeta) per
// instance (stark_algebra_real_fixture_test.go) — a wrong tree, wrong knob,
// or wrong node semantics cannot pass (the identity is a ~124-bit equation
// per instance over real data). The three simple instances are additionally
// cross-checked against the independent hand-derived LogUp evaluation.
package friverifier

import (
	"encoding/json"
	"fmt"
	"os"
)

// SymNode is one DAG node. Ops:
//
//	var(sp: main|pre|pub, row, col) — opened column value at zeta (row 0)
//	                                  or zeta_next (row 1)
//	sel(k: first|last|trans)        — Lagrange selector at zeta
//	c(v)                            — base-field constant
//	ec(v: [4]u32)                   — extension-field constant
//	permvar(row, col)               — permutation aux column (EF, recomposed)
//	ch(col)                         — permutation challenge
//	pv(col)                         — global lookup cumulative sum
//	add|sub|mul(x, y), neg(x)       — extension arithmetic
type SymNode struct {
	Op  string          `json:"op"`
	Sp  string          `json:"sp,omitempty"`
	Row int             `json:"row,omitempty"`
	Col int             `json:"col,omitempty"`
	V   json.RawMessage `json:"v,omitempty"`
	X   int             `json:"x,omitempty"`
	Y   int             `json:"y,omitempty"`
	K   string          `json:"k,omitempty"`
}

// SymConstraint is one constraint in GLOBAL fold order.
type SymConstraint struct {
	Root   int `json:"root"`
	Degree int `json:"degree"`
}

// SymInstance is one table's emitted constraint set.
type SymInstance struct {
	Name        string          `json:"name"`
	Width       int             `json:"width"`
	PreWidth    int             `json:"pre_width"`
	NumLookups  int             `json:"num_lookups"`
	Nodes       []SymNode       `json:"nodes"`
	Constraints []SymConstraint `json:"constraints"`
}

// SymbolicConstraints is the emitted file: one instance per shrink table, in
// proof instance order.
type SymbolicConstraints struct {
	Version   int           `json:"version"`
	Instances []SymInstance `json:"instances"`
}

// LoadSymbolicConstraints reads + fail-closed-validates the emitted DAG file:
// version, topological node order (children strictly before parents), known
// ops, and per-instance column ranges.
func LoadSymbolicConstraints(path string) (*SymbolicConstraints, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	sc := &SymbolicConstraints{}
	if err := json.Unmarshal(raw, sc); err != nil {
		return nil, err
	}
	if sc.Version != 1 {
		return nil, fmt.Errorf("symbolic constraints version %d (want 1)", sc.Version)
	}
	for ii := range sc.Instances {
		inst := &sc.Instances[ii]
		for i, n := range inst.Nodes {
			switch n.Op {
			case "add", "sub", "mul":
				if n.X >= i || n.Y >= i || n.X < 0 || n.Y < 0 {
					return nil, fmt.Errorf("%s node %d: children not topologically ordered", inst.Name, i)
				}
			case "neg":
				if n.X >= i || n.X < 0 {
					return nil, fmt.Errorf("%s node %d: child not topologically ordered", inst.Name, i)
				}
			case "var":
				lim := map[string]int{"main": inst.Width, "pre": inst.PreWidth, "pub": 0}[n.Sp]
				if n.Col >= lim || n.Row > 1 {
					return nil, fmt.Errorf("%s node %d: var %s[%d][%d] out of range", inst.Name, i, n.Sp, n.Row, n.Col)
				}
			case "permvar":
				if n.Col >= inst.NumLookups || n.Row > 1 {
					return nil, fmt.Errorf("%s node %d: permvar out of range", inst.Name, i)
				}
			case "ch":
				if n.Col >= 2*inst.NumLookups {
					return nil, fmt.Errorf("%s node %d: challenge out of range", inst.Name, i)
				}
			case "pv":
				if n.Col >= inst.NumLookups {
					return nil, fmt.Errorf("%s node %d: perm value out of range", inst.Name, i)
				}
			case "sel":
				if n.K != "first" && n.K != "last" && n.K != "trans" {
					return nil, fmt.Errorf("%s node %d: unknown selector %q", inst.Name, i, n.K)
				}
			case "c", "ec":
				// value parsed at eval
			default:
				return nil, fmt.Errorf("%s node %d: unknown op %q", inst.Name, i, n.Op)
			}
		}
		for ci, c := range inst.Constraints {
			if c.Root < 0 || c.Root >= len(inst.Nodes) {
				return nil, fmt.Errorf("%s constraint %d: root out of range", inst.Name, ci)
			}
		}
	}
	return sc, nil
}

func symNodeBaseConst(n SymNode) (uint32, error) {
	var v uint32
	if err := json.Unmarshal(n.V, &v); err != nil {
		return 0, err
	}
	if uint64(v) >= BabyBearP {
		return 0, fmt.Errorf("constant %d not canonical", v)
	}
	return v, nil
}

func symNodeExtConst(n SymNode) (bbExtRef, error) {
	var v [4]uint32
	if err := json.Unmarshal(n.V, &v); err != nil {
		return bbExtRef{}, err
	}
	for _, c := range v {
		if uint64(c) >= BabyBearP {
			return bbExtRef{}, fmt.Errorf("ext constant coordinate %d not canonical", c)
		}
	}
	return v, nil
}

// symEvalInputsNative are one instance's evaluation inputs (circuit side).
// Missing openings (trace_next / pre_next of instances that do not open
// them) must be ZERO vectors — exactly the verifier's substitution
// (batch-stark verifier/mod.rs:563-581).
type symEvalInputsNative struct {
	TraceLocal, TraceNext []BBExt
	PreLocal, PreNext     []BBExt
	PermLocal, PermNext   []BBExt // recomposed EF, one per aux column
	Challenges            []BBExt // 2 per lookup (bus pair, repeated)
	PermValues            []BBExt // global cumulative sums, lookup order
	Sel                   starkSelectorsNative
}

// evalSymbolicFoldedNative interprets one instance's emitted DAG at zeta and
// returns the alpha-folded constraint value (acc = acc*alpha + C over the
// emitted global order — folder.rs:174-181).
func evalSymbolicFoldedNative(bb *BBApi, inst *SymInstance, in symEvalInputsNative, alphaFold BBExt) BBExt {
	zero := BBExt{0, 0, 0, 0}
	vals := make([]BBExt, len(inst.Nodes))
	for i, n := range inst.Nodes {
		switch n.Op {
		case "var":
			var src []BBExt
			switch n.Sp {
			case "main":
				if n.Row == 0 {
					src = in.TraceLocal
				} else {
					src = in.TraceNext
				}
			case "pre":
				if n.Row == 0 {
					src = in.PreLocal
				} else {
					src = in.PreNext
				}
			default:
				panic("symbolic eval: public values are out of the shrink scope")
			}
			if src == nil {
				vals[i] = zero // verifier's zero substitution for unopened rows
			} else {
				vals[i] = src[n.Col]
			}
		case "permvar":
			if n.Row == 0 {
				vals[i] = in.PermLocal[n.Col]
			} else {
				vals[i] = in.PermNext[n.Col]
			}
		case "ch":
			vals[i] = in.Challenges[n.Col]
		case "pv":
			vals[i] = in.PermValues[n.Col]
		case "sel":
			switch n.K {
			case "first":
				vals[i] = in.Sel.isFirstRow
			case "last":
				vals[i] = in.Sel.isLastRow
			case "trans":
				vals[i] = in.Sel.isTransition
			}
		case "c":
			v, err := symNodeBaseConst(n)
			if err != nil {
				panic(err)
			}
			vals[i] = BBExt{v, 0, 0, 0}
		case "ec":
			v, err := symNodeExtConst(n)
			if err != nil {
				panic(err)
			}
			vals[i] = BBExt{v[0], v[1], v[2], v[3]}
		case "add":
			vals[i] = bb.ExtAdd(vals[n.X], vals[n.Y])
		case "sub":
			vals[i] = bb.ExtSub(vals[n.X], vals[n.Y])
		case "neg":
			vals[i] = bb.ExtSub(zero, vals[n.X])
		case "mul":
			vals[i] = bb.ExtMul(vals[n.X], vals[n.Y])
		}
	}
	folded := zero
	for _, c := range inst.Constraints {
		folded = bb.ExtAdd(bb.ExtMul(folded, alphaFold), vals[c.Root])
	}
	return folded
}

// symEvalInputsRef / evalSymbolicFoldedRef: the host twins.
type symEvalInputsRef struct {
	TraceLocal, TraceNext []bbExtRef
	PreLocal, PreNext     []bbExtRef
	PermLocal, PermNext   []bbExtRef
	Challenges            []bbExtRef
	PermValues            []bbExtRef
	Sel                   starkSelectorsRef
}

func evalSymbolicFoldedRef(inst *SymInstance, in symEvalInputsRef, alphaFold bbExtRef) (bbExtRef, error) {
	zero := bbExtRef{}
	vals := make([]bbExtRef, len(inst.Nodes))
	for i, n := range inst.Nodes {
		switch n.Op {
		case "var":
			var src []bbExtRef
			switch n.Sp {
			case "main":
				if n.Row == 0 {
					src = in.TraceLocal
				} else {
					src = in.TraceNext
				}
			case "pre":
				if n.Row == 0 {
					src = in.PreLocal
				} else {
					src = in.PreNext
				}
			default:
				return zero, fmt.Errorf("public values out of scope")
			}
			if src == nil {
				vals[i] = zero
			} else {
				vals[i] = src[n.Col]
			}
		case "permvar":
			if n.Row == 0 {
				vals[i] = in.PermLocal[n.Col]
			} else {
				vals[i] = in.PermNext[n.Col]
			}
		case "ch":
			vals[i] = in.Challenges[n.Col]
		case "pv":
			vals[i] = in.PermValues[n.Col]
		case "sel":
			switch n.K {
			case "first":
				vals[i] = in.Sel.isFirstRow
			case "last":
				vals[i] = in.Sel.isLastRow
			case "trans":
				vals[i] = in.Sel.isTransition
			}
		case "c":
			v, err := symNodeBaseConst(n)
			if err != nil {
				return zero, err
			}
			vals[i] = bbExtRef{v, 0, 0, 0}
		case "ec":
			v, err := symNodeExtConst(n)
			if err != nil {
				return zero, err
			}
			vals[i] = v
		case "add":
			vals[i] = bbExtAddRef(vals[n.X], vals[n.Y])
		case "sub":
			vals[i] = bbExtSubRef(vals[n.X], vals[n.Y])
		case "neg":
			vals[i] = bbExtSubRef(zero, vals[n.X])
		case "mul":
			vals[i] = bbExtMulRef(vals[n.X], vals[n.Y])
		}
	}
	folded := zero
	for _, c := range inst.Constraints {
		folded = bbExtAddRef(bbExtMulRef(folded, alphaFold), vals[c.Root])
	}
	return folded, nil
}
