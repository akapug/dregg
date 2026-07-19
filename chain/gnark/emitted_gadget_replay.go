// GENERIC replayer for Lean-emitted R1CS constraint TEMPLATES.
//
// A template is a self-contained constraint system authored in Lean and
// emitted as JSON: a wire-indexed gate list over an arithmetic vocabulary
// (var/const/add/sub/neg/mul, plus the field mux `select`) plus a list of
// equality assertions between wires. This file instantiates such a template
// against fresh gnark wires by replaying its gates and asserts through
// frontend.API.
//
// Two entry points, by how the template is boundaried:
//
//   - ReplayTemplate — an I/O-boundaried template: bind a PREFIX of the public
//     inputs, the replay SOLVES the suffix and returns it as outputs (the
//     poseidon2 permutation shape, [in,out]).
//   - ReplayClosed — a CLOSED template with a root-only (non-solving) boundary:
//     the caller binds the named INTERNAL variables (rows/siblings/bits/root of
//     an input-open opening) by index, the replay solves the define-chain
//     internals and keeps the real equality checks (the input-open opening
//     shape, InputOpenEmit.lean).
//
// It knows NOTHING about what any particular template computes. There is no
// Poseidon2 in this file — no round constants, no S-box, no linear layer, no
// width, no round count. Swap in a different emitted template and the same
// code replays it. The precedent is stark_constraint_interp.go, which
// interprets an emitted symbolic-constraint DAG the same way; the difference
// is that this one replays a template with a VARIABLE space and equality
// ASSERTS (an R1CS fragment) rather than an expression DAG evaluated at a
// point.
//
// Grammar (schema of chain/gnark/emitted/*_template.json):
//
//	public_inputs: [{name, var}]   — the template's boundary variables, in
//	                                 order. Replay binds a PREFIX of these to
//	                                 the caller's inputs; the remaining ones
//	                                 are SOLVED by the replay and returned as
//	                                 the outputs. (Which is which is the
//	                                 caller's arity choice, not a property the
//	                                 replayer reads out of names.)
//	gadgets:       [{gadget, args}] — provenance annotation only; ignored here.
//	gates:         [{op, args, out}] — wire `out` is defined by op over args.
//	                                 `out` MUST equal the gate's index.
//	                                   var(v)      — read template variable v
//	                                   const(k)    — field constant (decimal)
//	                                   add(a,b)    — wire a + wire b
//	                                   sub(a,b)    — wire a - wire b
//	                                   neg(a)      — -wire a
//	                                   mul(a,b)    — wire a * wire b
//	                                   select(c,t,f) — api.Select field mux:
//	                                                 c·(t−f)+f (t if c=1, f if c=0)
//	asserts:       [{l, r}]         — wire l == wire r.
//
// SOLVING (why this is a replay and not a hint). The emitted asserts are in a
// SOLVED ORDER: each one has (at most) one side that is a bare `var` gate
// naming a not-yet-determined variable, while the other side reads only
// already-determined variables. Replay therefore walks the asserts in emitted
// order and, for each, either
//
//   - DEFINES the fresh variable as the evaluated other side (binding it to
//     the gnark expression — a `mul` there emits exactly the R1CS constraint
//     the template's fresh-variable-plus-equality form would have emitted, so
//     the constraint count is preserved), or
//   - if both sides are already determined, emits api.AssertIsEqual — a real
//     check, kept.
//
// An assert whose two sides are BOTH undetermined would require a solver hint
// (i.e. knowledge of what the template computes) and is refused: this replayer
// fail-closes rather than fabricate a witness. Same for out-of-range indices,
// unknown ops, non-canonical constants, wires read before their variable is
// determined, and boundary variables the replay never determined.
package friverifier

import (
	"encoding/json"
	"fmt"
	"math/big"
	"os"

	"github.com/consensys/gnark/frontend"
)

// ---------------------------------------------------------------------------
// §1  The template grammar (Go mirror of the emitted JSON).
// ---------------------------------------------------------------------------

// TemplatePublic is one boundary variable of the template.
type TemplatePublic struct {
	Name string `json:"name"`
	Var  int    `json:"var"`
}

// TemplateGadget is the provenance annotation (which Lean gadget produced this
// template, over which boundary variables). The replayer does not interpret it
// — it exists so a template can be traced back to its author.
type TemplateGadget struct {
	Gadget string `json:"gadget"`
	Args   []int  `json:"args"`
}

// TemplateGate is one wire definition. Args are json.Number because `const`
// carries a full-width field element that must not round-trip through float64.
type TemplateGate struct {
	Op   string        `json:"op"`
	Args []json.Number `json:"args"`
	Out  int           `json:"out"`
}

// TemplateAssert is one equality constraint between two wires.
type TemplateAssert struct {
	L int `json:"l"`
	R int `json:"r"`
}

// Template is a parsed Lean-emitted constraint template.
type Template struct {
	Name         string           `json:"name"`
	PublicInputs []TemplatePublic `json:"public_inputs"`
	Gadgets      []TemplateGadget `json:"gadgets"`
	Gates        []TemplateGate   `json:"gates"`
	Asserts      []TemplateAssert `json:"asserts"`

	// numVars is the size of the variable space, derived from the gates.
	numVars int
}

// templateOpArity is the op vocabulary. Anything else fail-closes: an unknown
// op would mean an emitter using semantics this replayer does not carry.
//
// `select(cond, ifTrue, ifFalse)` is the Lean `Wire.select b x y` — gnark's
// `api.Select`, the field mux `cond·(ifTrue−ifFalse)+ifFalse`, which equals
// `ifTrue` when cond=1 and `ifFalse` when cond=0. The arg order is the emitter's
// (`EmitJson.lean`: `["select",[cond,ifTrue,ifFalse]]`) and matches
// `api.Select`'s `(b, i1, i2)` verbatim. It is the mux a boundaried I/O template
// never needs but a CLOSED opening template (the Merkle/input-open path walk)
// spends two of per level.
var templateOpArity = map[string]int{
	"var":    1,
	"const":  1,
	"neg":    1,
	"add":    2,
	"sub":    2,
	"mul":    2,
	"select": 3,
}

// LoadTemplate reads and fail-closed-validates an emitted template file.
func LoadTemplate(path string) (*Template, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	return ParseTemplate(raw)
}

// ParseTemplate parses + validates an emitted template from JSON bytes.
func ParseTemplate(raw []byte) (*Template, error) {
	tpl := &Template{}
	if err := json.Unmarshal(raw, tpl); err != nil {
		return nil, err
	}
	if err := tpl.Validate(); err != nil {
		return nil, fmt.Errorf("template %q: %w", tpl.Name, err)
	}
	return tpl, nil
}

// Validate checks the STRUCTURE of the template independently of any field:
// gate indexing, op arity, topological wire order, variable-index range, and
// assert range. It does not check constants (those need the field modulus and
// are checked at replay).
func (t *Template) Validate() error {
	maxVar := -1
	for i := range t.Gates {
		g := &t.Gates[i]
		if g.Out != i {
			return fmt.Errorf("gate %d: out=%d (gates must be wire-indexed: out==index)", i, g.Out)
		}
		arity, ok := templateOpArity[g.Op]
		if !ok {
			return fmt.Errorf("gate %d: unknown op %q (fail-closed: this replayer does not carry it)", i, g.Op)
		}
		if len(g.Args) != arity {
			return fmt.Errorf("gate %d: op %q takes %d args, got %d", i, g.Op, arity, len(g.Args))
		}
		switch g.Op {
		case "const":
			// value parsed at replay (needs the field modulus).
		case "var":
			v, err := templateArgInt(g.Args[0])
			if err != nil {
				return fmt.Errorf("gate %d: var index: %w", i, err)
			}
			if v < 0 {
				return fmt.Errorf("gate %d: negative var index %d", i, v)
			}
			if v > maxVar {
				maxVar = v
			}
		default:
			for k, a := range g.Args {
				w, err := templateArgInt(a)
				if err != nil {
					return fmt.Errorf("gate %d arg %d: %w", i, k, err)
				}
				if w < 0 || w >= i {
					return fmt.Errorf("gate %d: arg %d references wire %d (children must be strictly earlier)", i, k, w)
				}
			}
		}
	}
	t.numVars = maxVar + 1

	for i, a := range t.Asserts {
		if a.L < 0 || a.L >= len(t.Gates) || a.R < 0 || a.R >= len(t.Gates) {
			return fmt.Errorf("assert %d: wire out of range (%d, %d)", i, a.L, a.R)
		}
	}
	for i, p := range t.PublicInputs {
		if p.Var < 0 || p.Var >= t.numVars {
			return fmt.Errorf("public input %d (%q): var %d out of range", i, p.Name, p.Var)
		}
	}
	return nil
}

// NumVars is the size of the template's variable space.
func (t *Template) NumVars() int { return t.numVars }

// NumMulGates is the count of multiplication gates — the template's R1CS
// constraint budget (add/sub/neg/const are linear combinations and cost
// nothing in R1CS).
func (t *Template) NumMulGates() int {
	n := 0
	for i := range t.Gates {
		if t.Gates[i].Op == "mul" {
			n++
		}
	}
	return n
}

func templateArgInt(a json.Number) (int, error) {
	v, err := a.Int64()
	if err != nil {
		return 0, fmt.Errorf("%q is not an integer index", a.String())
	}
	return int(v), nil
}

// ---------------------------------------------------------------------------
// §2  The replayer.
// ---------------------------------------------------------------------------

// replayState carries the per-instantiation solve: which template variables
// have been determined, and the memoized gnark expression of each wire.
type replayState struct {
	api     frontend.API
	tpl     *Template
	modulus *big.Int

	vars    []frontend.Variable
	varSet  []bool
	wire    []frontend.Variable
	wireSet []bool
}

// ReplayTemplate instantiates a Lean-emitted constraint template against fresh
// wires: it binds `in` to the first len(in) boundary variables, replays every
// gate and assert through the frontend API, and returns the remaining boundary
// variables (which the replay solved) as outputs.
//
// The replayer has no knowledge of what the template computes.
func ReplayTemplate(api frontend.API, tpl Template, in []frontend.Variable) ([]frontend.Variable, error) {
	if tpl.numVars == 0 && len(tpl.Gates) > 0 {
		// Constructed by hand rather than through ParseTemplate/LoadTemplate.
		if err := tpl.Validate(); err != nil {
			return nil, err
		}
	}
	if len(in) > len(tpl.PublicInputs) {
		return nil, fmt.Errorf("template %q: %d inputs supplied but only %d boundary variables",
			tpl.Name, len(in), len(tpl.PublicInputs))
	}

	st := &replayState{
		api:     api,
		tpl:     &tpl,
		modulus: api.Compiler().Field(),
		vars:    make([]frontend.Variable, tpl.numVars),
		varSet:  make([]bool, tpl.numVars),
		wire:    make([]frontend.Variable, len(tpl.Gates)),
		wireSet: make([]bool, len(tpl.Gates)),
	}

	// Bind the supplied inputs to the leading boundary variables.
	for i, v := range in {
		p := tpl.PublicInputs[i]
		if st.varSet[p.Var] {
			return nil, fmt.Errorf("template %q: boundary variable %d (%q) bound twice",
				tpl.Name, p.Var, p.Name)
		}
		st.vars[p.Var] = v
		st.varSet[p.Var] = true
	}

	// Replay the asserts in emitted order, solving as we go.
	for i, a := range tpl.Asserts {
		if err := st.replayAssert(i, a); err != nil {
			return nil, err
		}
	}

	// The trailing boundary variables are the outputs; every one of them must
	// have been determined by the replay.
	out := make([]frontend.Variable, 0, len(tpl.PublicInputs)-len(in))
	for _, p := range tpl.PublicInputs[len(in):] {
		if !st.varSet[p.Var] {
			return nil, fmt.Errorf("template %q: output %q (var %d) was never determined by the replay",
				tpl.Name, p.Name, p.Var)
		}
		out = append(out, st.vars[p.Var])
	}
	return out, nil
}

// ReplayClosed drives a CLOSED emitted template — one that is NOT solvable from
// an I/O boundary. Where ReplayTemplate binds a PREFIX of the public-input
// boundary and returns the SOLVED suffix as outputs, a closed template has a
// root-only (or otherwise non-solving) boundary: its non-derived variables are
// named INTERNAL variables the caller must supply. The input-open opening
// (`inputOpenData`, InputOpenEmit.lean) is the motivating case — its only public
// input is the root, while the opened row limbs, the sibling nodes, and the path
// bits are internal variables at a fixed layout, and the define-chain solves the
// Poseidon internals from them.
//
// ReplayClosed binds each supplied variable BY INDEX, then replays every assert
// in emitted order through the same solve as ReplayTemplate: an assert whose one
// side is a not-yet-determined bare `var` DEFINES that variable (extending the
// witness — the define-chain internals), and an assert whose two sides are both
// already determined emits api.AssertIsEqual (a kept check — booleanity of each
// path bit, and the final recomputed-root == root). It fail-closes, exactly like
// ReplayTemplate, on unknown ops, out-of-range indices, non-canonical constants,
// an assert needing a hint (both sides undetermined vars), a wire read before its
// variable is determined, and — the closed analog of ReplayTemplate's "output
// never determined" — any template variable that ends neither bound nor solved
// (the caller under-bound the circuit).
//
// The replayer has no knowledge of what the template computes; the layout of
// which indices are rows/siblings/bits/root is the caller's, read from the Lean
// spec, not from this file.
func ReplayClosed(api frontend.API, tpl Template, bindings map[int]frontend.Variable) error {
	if tpl.numVars == 0 && len(tpl.Gates) > 0 {
		// Constructed by hand rather than through ParseTemplate/LoadTemplate.
		if err := tpl.Validate(); err != nil {
			return err
		}
	}

	st := &replayState{
		api:     api,
		tpl:     &tpl,
		modulus: api.Compiler().Field(),
		vars:    make([]frontend.Variable, tpl.numVars),
		varSet:  make([]bool, tpl.numVars),
		wire:    make([]frontend.Variable, len(tpl.Gates)),
		wireSet: make([]bool, len(tpl.Gates)),
	}

	// Bind the caller's named internal variables. Order is irrelevant: every
	// binding lands before any assert is replayed.
	for idx, v := range bindings {
		if idx < 0 || idx >= tpl.numVars {
			return fmt.Errorf("template %q: binding for variable %d is out of range [0,%d)",
				tpl.Name, idx, tpl.numVars)
		}
		st.vars[idx] = v
		st.varSet[idx] = true
	}

	// Replay the asserts in emitted order, solving the define-chain as we go.
	for i, a := range tpl.Asserts {
		if err := st.replayAssert(i, a); err != nil {
			return err
		}
	}

	// Fail-closed completeness: every template variable must have been bound or
	// solved. An undetermined variable means the caller under-bound the closed
	// circuit (e.g. omitted a row/sibling/bit), which would have silently left a
	// dangling wire — refuse rather than emit a partial constraint system.
	for v := 0; v < tpl.numVars; v++ {
		if !st.varSet[v] {
			return fmt.Errorf("template %q: variable %d was neither bound nor determined by the "+
				"replay (the closed circuit is under-bound)", tpl.Name, v)
		}
	}
	return nil
}

// freshVarOf reports whether wire w is a bare `var` gate naming a variable
// that the replay has not yet determined (i.e. the definable side).
func (st *replayState) freshVarOf(w int) (int, bool) {
	g := &st.tpl.Gates[w]
	if g.Op != "var" {
		return 0, false
	}
	v, err := templateArgInt(g.Args[0])
	if err != nil {
		return 0, false
	}
	if st.varSet[v] {
		return 0, false
	}
	return v, true
}

func (st *replayState) replayAssert(idx int, a TemplateAssert) error {
	lv, lFresh := st.freshVarOf(a.L)
	rv, rFresh := st.freshVarOf(a.R)

	switch {
	case rFresh && !lFresh:
		val, err := st.eval(a.L)
		if err != nil {
			return fmt.Errorf("assert %d (defines var %d): %w", idx, rv, err)
		}
		st.vars[rv], st.varSet[rv] = val, true

	case lFresh && !rFresh:
		val, err := st.eval(a.R)
		if err != nil {
			return fmt.Errorf("assert %d (defines var %d): %w", idx, lv, err)
		}
		st.vars[lv], st.varSet[lv] = val, true

	case lFresh && rFresh:
		return fmt.Errorf("assert %d: both sides are undetermined variables (%d, %d) — "+
			"solving this template would need a hint, i.e. knowledge of what it computes; "+
			"this replayer is generic and fail-closes", idx, lv, rv)

	default:
		l, err := st.eval(a.L)
		if err != nil {
			return fmt.Errorf("assert %d (lhs): %w", idx, err)
		}
		r, err := st.eval(a.R)
		if err != nil {
			return fmt.Errorf("assert %d (rhs): %w", idx, err)
		}
		st.api.AssertIsEqual(l, r)
	}
	return nil
}

// eval returns the gnark expression for wire w, memoized. Iterative (explicit
// stack) so a long linear chain cannot blow the Go stack.
func (st *replayState) eval(w int) (frontend.Variable, error) {
	if st.wireSet[w] {
		return st.wire[w], nil
	}
	stack := []int{w}
	for len(stack) > 0 {
		cur := stack[len(stack)-1]
		if st.wireSet[cur] {
			stack = stack[:len(stack)-1]
			continue
		}
		g := &st.tpl.Gates[cur]

		// Leaves.
		switch g.Op {
		case "var":
			v, err := templateArgInt(g.Args[0])
			if err != nil {
				return nil, err
			}
			if !st.varSet[v] {
				return nil, fmt.Errorf("wire %d reads var %d before the replay determined it", cur, v)
			}
			st.wire[cur], st.wireSet[cur] = st.vars[v], true
			stack = stack[:len(stack)-1]
			continue
		case "const":
			k, ok := new(big.Int).SetString(g.Args[0].String(), 10)
			if !ok {
				return nil, fmt.Errorf("wire %d: constant %q is not a decimal integer", cur, g.Args[0].String())
			}
			if k.Sign() < 0 || k.Cmp(st.modulus) >= 0 {
				return nil, fmt.Errorf("wire %d: constant %s is not canonical for the compilation field", cur, k.String())
			}
			st.wire[cur], st.wireSet[cur] = k, true
			stack = stack[:len(stack)-1]
			continue
		}

		// Internal nodes: push unevaluated children first.
		args := make([]int, len(g.Args))
		pending := false
		for i, a := range g.Args {
			v, err := templateArgInt(a)
			if err != nil {
				return nil, err
			}
			args[i] = v
			if !st.wireSet[v] {
				stack = append(stack, v)
				pending = true
			}
		}
		if pending {
			continue
		}
		switch g.Op {
		case "add":
			st.wire[cur] = st.api.Add(st.wire[args[0]], st.wire[args[1]])
		case "sub":
			st.wire[cur] = st.api.Sub(st.wire[args[0]], st.wire[args[1]])
		case "neg":
			st.wire[cur] = st.api.Neg(st.wire[args[0]])
		case "mul":
			st.wire[cur] = st.api.Mul(st.wire[args[0]], st.wire[args[1]])
		case "select":
			// Lean `Wire.select b x y` = gnark `api.Select(cond, ifTrue, ifFalse)`:
			// the field mux cond·(ifTrue−ifFalse)+ifFalse. args[0]=cond, args[1]=ifTrue,
			// args[2]=ifFalse (the emitter's [cond,ifTrue,ifFalse] order).
			st.wire[cur] = st.api.Select(st.wire[args[0]], st.wire[args[1]], st.wire[args[2]])
		default:
			return nil, fmt.Errorf("wire %d: unhandled op %q", cur, g.Op)
		}
		st.wireSet[cur] = true
		stack = stack[:len(stack)-1]
	}
	return st.wire[w], nil
}
