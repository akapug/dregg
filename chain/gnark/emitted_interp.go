// GENERIC interpreter for Lean-EMITTED circuit JSON — the gnark side of the
// Emit socket (metatheory/Dregg2/Circuit/Emit/GnarkVerifier/).
//
// The circuit structure is NOT hand-encoded here: it is the op-DAG the Lean
// emitter renders (EmitJson.lean `emitGnarkJson`, byte-pinned by #guard against
// the committed artifact chain/gnark/emitted/canonicity_toy.json). This file
// only REPLAYS that DAG through frontend.API — the JSON is the single source
// of the circuit's constraint content, and the Lean theorems
// (`canonicity_refines_emitted` in CanonicityToy.lean) speak about exactly
// these bytes via `satisfiedEmitted`.
//
// Grammar (EmitJson.lean §2):
//
//	{"name":S,
//	 "public_inputs":[{"name":S,"var":N},…],
//	 "gadgets":[{"gadget":S,"args":[N,…]},…],
//	 "gates":[{"op":"var"|"const"|"add"|"mul"|"select","args":[N,…],"out":N},…],
//	 "asserts":[{"l":N,"r":N},…]}
//
// Gates are the flattened op-DAG in emission order; a gate's `out` is its own
// node id (== its index — the Lean flattener's invariant, validated here).
// `args` are node ids for add/mul/select, the frontend variable index for
// `var`, and the canonical Fr residue (decimal, up to ~2^254 — parsed as
// big.Int) for `const`. Each assert is one api.AssertIsEqual between two node
// ids.
//
// Gadget records are wire METADATA (EmitFaithful.lean `GadgetInvocation`: "the
// constraint content is carried by the circuit's asserts; the record lets the
// Go side name-check the layout") — the rangecheck+canonicity gadget's
// expansion (booleanity + recomposition asserts) is already inline in the
// gates. The interpreter therefore adds NO constraints for a gadget record,
// but FAIL-CLOSES on any gadget name it does not recognize: an unknown name
// would mean an emitter recording semantics this replayer might not be
// carrying.
//
// Precedent: stark_constraint_interp.go (the SymNode interpreter for the
// batch-STARK algebra layer) — same load + fail-closed-validate + replay
// discipline.
package friverifier

import (
	"encoding/json"
	"fmt"
	"math/big"
	"os"

	"github.com/consensys/gnark/frontend"
)

// EmittedPublicInput is one public-input record: frontend variable `Var` is
// public and named `Name`.
type EmittedPublicInput struct {
	Name string `json:"name"`
	Var  int    `json:"var"`
}

// EmittedGadget is one recorded gadget invocation (metadata; see header).
type EmittedGadget struct {
	Gadget string `json:"gadget"`
	Args   []int  `json:"args"`
}

// EmittedGate is one flattened op-DAG node. Args are kept as json.Number
// because `const` args are canonical Fr residues up to ~2^254 (the toy carries
// the residue of -1 mod rBN254) — far beyond int64/float64.
type EmittedGate struct {
	Op   string        `json:"op"`
	Args []json.Number `json:"args"`
	Out  int           `json:"out"`
}

// EmittedAssert is one equality assert between two node ids.
type EmittedAssert struct {
	L int `json:"l"`
	R int `json:"r"`
}

// Emitted is the parsed emitted-circuit file (the Go mirror of the Lean
// `Emitted` structure in its JSON rendering).
type Emitted struct {
	Name         string               `json:"name"`
	PublicInputs []EmittedPublicInput `json:"public_inputs"`
	Gadgets      []EmittedGadget      `json:"gadgets"`
	Gates        []EmittedGate        `json:"gates"`
	Asserts      []EmittedAssert      `json:"asserts"`

	// Vars is the frontend variable bank the `var` gates index into —
	// runtime-only, set by the enclosing circuit's Define before calling
	// BuildFromEmitted (index i = the JSON's frontend variable i).
	Vars []frontend.Variable `json:"-"`
}

// knownEmittedGadgets are the gadget-invocation names this replayer
// recognizes as inline-expanded metadata. Anything else fail-closes.
var knownEmittedGadgets = map[string]bool{
	"AssertIsCanonical": true, // BBApi.AssertIsCanonical (babybear.go): 2×31-bit range check, expansion inline
}

// LoadEmitted reads and fail-closed-validates an emitted circuit file.
func LoadEmitted(path string) (*Emitted, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	e := &Emitted{}
	if err := json.Unmarshal(raw, e); err != nil {
		return nil, err
	}
	if err := e.Validate(); err != nil {
		return nil, fmt.Errorf("%s: %w", path, err)
	}
	return e, nil
}

func gateArgInt(g EmittedGate, k int) (int, error) {
	v, err := g.Args[k].Int64()
	if err != nil {
		return 0, fmt.Errorf("gate %d: arg %d not an int: %w", g.Out, k, err)
	}
	if v < 0 {
		return 0, fmt.Errorf("gate %d: negative arg %d", g.Out, v)
	}
	return int(v), nil
}

// Validate fail-closes on structural violations: unknown ops, gate ids not
// equal to their index (the Lean flattener's invariant), non-topological
// child references, malformed const residues, assert ids out of range,
// unknown gadget names, and out-of-range variable references.
func (e *Emitted) Validate() error {
	for i, g := range e.Gates {
		if g.Out != i {
			return fmt.Errorf("gate %d: out %d != index (flattener invariant)", i, g.Out)
		}
		switch g.Op {
		case "var":
			if len(g.Args) != 1 {
				return fmt.Errorf("gate %d: var wants 1 arg, got %d", i, len(g.Args))
			}
			if _, err := gateArgInt(g, 0); err != nil {
				return err
			}
		case "const":
			if len(g.Args) != 1 {
				return fmt.Errorf("gate %d: const wants 1 arg, got %d", i, len(g.Args))
			}
			c, ok := new(big.Int).SetString(g.Args[0].String(), 10)
			if !ok || c.Sign() < 0 {
				return fmt.Errorf("gate %d: const %q not a nonnegative decimal integer", i, g.Args[0])
			}
		case "add", "mul", "select":
			want := 2
			if g.Op == "select" {
				want = 3
			}
			if len(g.Args) != want {
				return fmt.Errorf("gate %d: %s wants %d args, got %d", i, g.Op, want, len(g.Args))
			}
			for k := range g.Args {
				a, err := gateArgInt(g, k)
				if err != nil {
					return err
				}
				if a >= i {
					return fmt.Errorf("gate %d: child %d not topologically ordered", i, a)
				}
			}
		default:
			return fmt.Errorf("gate %d: unknown op %q", i, g.Op)
		}
	}
	for ai, a := range e.Asserts {
		if a.L < 0 || a.L >= len(e.Gates) || a.R < 0 || a.R >= len(e.Gates) {
			return fmt.Errorf("assert %d: node id out of range (l=%d r=%d, %d gates)", ai, a.L, a.R, len(e.Gates))
		}
	}
	n := e.NumVars()
	for _, p := range e.PublicInputs {
		if p.Var < 0 || p.Var >= n {
			return fmt.Errorf("public input %q: var %d out of range (%d vars)", p.Name, p.Var, n)
		}
	}
	for _, gd := range e.Gadgets {
		if !knownEmittedGadgets[gd.Gadget] {
			return fmt.Errorf("unknown gadget %q (fail-closed: this replayer does not carry its semantics)", gd.Gadget)
		}
		for _, a := range gd.Args {
			if a < 0 || a >= n {
				return fmt.Errorf("gadget %q: var %d out of range (%d vars)", gd.Gadget, a, n)
			}
		}
	}
	return nil
}

// NumVars is the size of the frontend variable bank the gates reference:
// 1 + the maximum var index appearing in any `var` gate (0 if none).
func (e *Emitted) NumVars() int {
	max := -1
	for _, g := range e.Gates {
		if g.Op != "var" || len(g.Args) != 1 {
			continue
		}
		if v, err := g.Args[0].Int64(); err == nil && int(v) > max {
			max = int(v)
		}
	}
	return max + 1
}

// PredictedR1CSConstraints derives, from the DAG alone, the R1CS constraint
// count the gnark r1cs builder produces for the replay — the parity oracle:
//   - add: free (linear-combination merge)
//   - mul: 1 constraint iff BOTH operands are non-constant (a constant
//     operand only scales the LC; two constants fold)
//   - select(b,x,y): 2 constraints iff b is non-constant — gnark's Select
//     asserts the selector boolean (1) then multiplies b·(x−y) (1). The
//     builder marks the selector, so a LATER select on a wire it already
//     marked would cost 1; the model tracks that mark per var index / node.
//   - assert: 1 constraint each (1·l == r)
func (e *Emitted) PredictedR1CSConstraints() int {
	isConst := make([]bool, len(e.Gates))
	// varOf[i] = the frontend var index a pure-var node denotes (else -1);
	// gnark's boolean mark lives on the VARIABLE, so two var nodes of the
	// same index share it.
	varOf := make([]int, len(e.Gates))
	boolMarkedVar := map[int]bool{}
	boolMarkedNode := map[int]bool{}
	n := 0
	for i, g := range e.Gates {
		varOf[i] = -1
		switch g.Op {
		case "const":
			isConst[i] = true
		case "var":
			idx, _ := gateArgInt(g, 0)
			varOf[i] = idx
		case "add":
			x, _ := gateArgInt(g, 0)
			y, _ := gateArgInt(g, 1)
			isConst[i] = isConst[x] && isConst[y]
		case "mul":
			x, _ := gateArgInt(g, 0)
			y, _ := gateArgInt(g, 1)
			isConst[i] = isConst[x] && isConst[y]
			if !isConst[x] && !isConst[y] {
				n++
			}
		case "select":
			b, _ := gateArgInt(g, 0)
			x, _ := gateArgInt(g, 1)
			y, _ := gateArgInt(g, 2)
			isConst[i] = isConst[b] && isConst[x] && isConst[y]
			if !isConst[b] {
				n++ // the b·(x−y) product
				marked := boolMarkedNode[b] || (varOf[b] >= 0 && boolMarkedVar[varOf[b]])
				if !marked {
					n++ // gnark Select's AssertIsBoolean on the selector
					boolMarkedNode[b] = true
					if varOf[b] >= 0 {
						boolMarkedVar[varOf[b]] = true
					}
				}
			}
		}
	}
	return n + len(e.Asserts)
}

// BuildFromEmitted replays the emitted op-DAG through frontend.API: each gate
// becomes its frontend value (var lookup / big.Int constant / api.Add /
// api.Mul / api.Select) and each assert becomes one api.AssertIsEqual. The
// emitted file is the ONLY source of the circuit structure; e.Vars must hold
// the NumVars() frontend variables the `var` gates index.
func BuildFromEmitted(api frontend.API, e Emitted) error {
	if err := e.Validate(); err != nil {
		return err
	}
	if n := e.NumVars(); len(e.Vars) < n {
		return fmt.Errorf("emitted circuit %q references %d frontend vars, got %d", e.Name, n, len(e.Vars))
	}
	field := api.Compiler().Field()
	vals := make([]frontend.Variable, len(e.Gates))
	for i, g := range e.Gates {
		switch g.Op {
		case "var":
			idx, _ := gateArgInt(g, 0)
			vals[i] = e.Vars[idx]
		case "const":
			c, _ := new(big.Int).SetString(g.Args[0].String(), 10)
			if c.Cmp(field) >= 0 {
				return fmt.Errorf("gate %d: const %s not a canonical residue of the compile field", i, c)
			}
			vals[i] = c
		case "add":
			x, _ := gateArgInt(g, 0)
			y, _ := gateArgInt(g, 1)
			vals[i] = api.Add(vals[x], vals[y])
		case "mul":
			x, _ := gateArgInt(g, 0)
			y, _ := gateArgInt(g, 1)
			vals[i] = api.Mul(vals[x], vals[y])
		case "select":
			b, _ := gateArgInt(g, 0)
			x, _ := gateArgInt(g, 1)
			y, _ := gateArgInt(g, 2)
			vals[i] = api.Select(vals[b], vals[x], vals[y])
		}
	}
	for _, a := range e.Asserts {
		api.AssertIsEqual(vals[a.L], vals[a.R])
	}
	return nil
}
