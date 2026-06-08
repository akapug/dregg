/-
# Dregg2.Circuit.Emit.EffectVmEmit — the EffectVM-shaped circuit-emission IR.

`Exec.CircuitEmit` (PARTs I–IV) emits the 6-wire TOY kernel, the abstract-`Digest` Merkle
gadget, and column-indexed algebraic `ConstraintExpr` forms over a single `RowEnv`. None of
those is the shape the RUNNING EffectVM prover (`circuit/src/effect_vm_p3_full_air.rs`'s
`EffectVmP3Air`, a faithful mirror of bespoke `effect_vm/air.rs`'s `EffectVmAir`) needs:

  * a FIXED 186-column layout (46 selectors · 14 state_before · 8 params · 14 state_after ·
    96 aux) read by *named* offsets (`sel`/`state`/`param`/`aux`);
  * per-row gates GATED by the selector column (`s_transfer · (…) = 0`), reading
    `state_before`/`state_after`/`param`;
  * TRANSITION gates over the row window (`next.state_before[i] == this.state_after[i]`);
  * BOUNDARY gates pinning the FIRST / LAST row (row-0 `state_before.nonce == PI[ACTOR_NONCE]`,
    last-row `state_after.state_commit == PI[NEW_COMMIT]`, …);
  * PUBLIC-INPUT bindings (`column == PI[k]`);
  * HASH-SITE forms: a Poseidon2 permutation over named aux columns with a DETERMINISTIC
    SITE ORDER (`hash_sites()` in the Rust is the single source of truth shared by the
    symbolic evaluator and the witness generator — site `i` ↔ aux block `i`).

This module supplies that IR (`VmGate` / `VmConstraint` / `VmHashSite` / `EffectVmDescriptor`)
with a self-contained denotation over an EffectVM `VmRowEnv` (the `local`/`next`/`pi` triple
the Rust `eval` reads), reusing PART-III's algebraic-`Int` field model. The `Transfer` effect's
full concrete descriptor is emitted through it (`transferVmDescriptor`), and its denotation is
proved EQUIVALENT to the transfer intent (debit/credit + nonce-increment + frame-passthrough +
the boundary pins) — the same intent `Spec.CircuitSpecTriangle.transfer_circuit_pins_intent`
pins abstractly. See `EffectVmEmitTransfer.lean` for the transfer emission + faithfulness.
-/
import Dregg2.Circuit
import Dregg2.Exec.CircuitEmit

namespace Dregg2.Circuit.Emit.EffectVmEmit

open Dregg2.Circuit
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §0 — The EffectVM column layout (the Lean mirror of `effect_vm/columns.rs`).

These are the SAME absolute column indices the running prover reads. We keep them as plain
`Nat` so the emitted descriptor's `Var` indices are literally the prover's column indices —
the wire form is the prover's layout, not a re-numbering. -/

/-- Number of effect-type selector columns (`columns.rs::NUM_EFFECTS`). -/
def NUM_EFFECTS : Nat := 54
/-- State-block width (`state::SIZE`). -/
def STATE_SIZE : Nat := 14
/-- Number of parameter columns (`NUM_PARAMS`). -/
def NUM_PARAMS : Nat := 8

/-- Absolute base of the `state_before` block (`STATE_BEFORE_BASE = NUM_EFFECTS`). -/
def STATE_BEFORE_BASE : Nat := NUM_EFFECTS
/-- Absolute base of the parameter block (`PARAM_BASE = STATE_BEFORE_BASE + STATE_SIZE`). -/
def PARAM_BASE : Nat := STATE_BEFORE_BASE + STATE_SIZE
/-- Absolute base of the `state_after` block (`STATE_AFTER_BASE = PARAM_BASE + NUM_PARAMS`). -/
def STATE_AFTER_BASE : Nat := PARAM_BASE + NUM_PARAMS
/-- Absolute base of the auxiliary block (`AUX_BASE = STATE_AFTER_BASE + STATE_SIZE`). -/
def AUX_BASE : Nat := STATE_AFTER_BASE + STATE_SIZE
/-- Total BASE trace width (`EFFECT_VM_WIDTH = 186`). -/
def EFFECT_VM_WIDTH : Nat := 186

/-! State-column offsets within a state block (`state::*`). -/
namespace state
def BALANCE_LO : Nat := 0
def BALANCE_HI : Nat := 1
def NONCE      : Nat := 2
def FIELD_BASE : Nat := 3
def CAP_ROOT   : Nat := 11
def STATE_COMMIT : Nat := 12
def RESERVED   : Nat := 13

/-- **`FIELDS_ROOT` (record-layer STAGE 2).** The committed user-field-MAP root
(`_RECORD-LAYER-UPGRADE.md` §B.5, `Exec.FieldsMap.fieldsRoot`) carried in the EffectVM state block.
It is width-neutral: it reuses the single state column GROUP-4 currently leaves UNABSORBED — the
`RESERVED` cell (col 13) — as the carrier (the transfer-keystone `reserved_not_bound_by_commitment`
finding identified `RESERVED` as the lone un-hashed state cell, so binding it costs no new column).
On a record / map-write row the runtime writes the row's `fields_root` felt here; on every legacy
row the carrier is `0` (the empty-map circuit root), so the legacy `state_commit` is byte-identical
to the pre-STAGE-2 `H4(inter1, inter2, inter3, 0)`. STAGE 2 absorbs THIS cell into `state_commit`
via GROUP-4 site 3's previously-spare 4th input (`_IR-EXTENSION-DESIGN.md:23,158-162`). -/
def FIELDS_ROOT : Nat := 13
end state

/-! Selector-column indices (`sel::*`). -/
namespace sel
def NOOP     : Nat := 0
def TRANSFER : Nat := 1
end sel

/-! Transfer parameter offsets (`param::AMOUNT` / `param::DIRECTION`). -/
namespace param
def AMOUNT    : Nat := 0
def DIRECTION : Nat := 1
end param

/-! Aux offsets used by the state-commitment chain (`aux_off::STATE_INTER*`). -/
namespace aux_off
def STATE_INTER1 : Nat := 8
def STATE_INTER2 : Nat := 9
def STATE_INTER3 : Nat := 10
end aux_off

/-! Public-input slot indices (`pi::*`). -/
namespace pi
def OLD_COMMIT : Nat := 0
def NEW_COMMIT : Nat := 4
def INIT_BAL_LO : Nat := 12
def INIT_BAL_HI : Nat := 13
def FINAL_BAL_LO : Nat := 14
def FINAL_BAL_HI : Nat := 15
def ACTOR_NONCE : Nat := 33
end pi

/-- Absolute column index of `state_before[off]`. -/
def sbCol (off : Nat) : Nat := STATE_BEFORE_BASE + off
/-- Absolute column index of `state_after[off]`. -/
def saCol (off : Nat) : Nat := STATE_AFTER_BASE + off
/-- Absolute column index of `param[i]`. -/
def prmCol (i : Nat) : Nat := PARAM_BASE + i
/-- Absolute column index of `aux[i]`. -/
def auxCol (i : Nat) : Nat := AUX_BASE + i

/-! ## §1 — The row environment (`local`/`next`/`pi`, the Rust `eval` triple).

The running `EffectVmP3Air::eval` reads three slices: `local` (current row), `next` (next row),
and `pi` (public values). We model each as a column→`ℤ` map (PART-III's `Int` field model), so
the EffectVM IR reuses the proven `EmittedExpr.eval` and the algebraic forms. -/

/-- A row environment: the current row `loc`, the next row `nxt`, and the public inputs `pub`. -/
structure VmRowEnv where
  loc : Assignment
  nxt : Assignment
  pub : Assignment

/-! ## §2 — `VmGate`: a per-row arithmetic gate over the EffectVM layout.

A `VmGate` is an `EmittedExpr` over the CURRENT row that the AIR asserts is ZERO — exactly the
shape of the `tb.assert_zero(...)` calls in `EffectVmP3Air::eval`. Because the gate is an
`EmittedExpr`, it composes with PART-I's proven `EmittedExpr.eval`, and "holds" means
`eval = 0` (the Rust `assert_zero` semantics). Reading `state_before`/`state_after`/`param` is
just reading the named absolute columns. -/

/-- A per-row gate: the polynomial `body` must vanish on the row (`body.eval loc = 0`). -/
structure VmGate where
  body : EmittedExpr
  deriving Repr

/-- A per-row gate holds iff its body evaluates to zero on the current row. -/
def VmGate.holds (g : VmGate) (env : VmRowEnv) : Prop :=
  g.body.eval env.loc = 0

/-! ## §3 — `VmConstraint`: the four EffectVM constraint FORMS.

Mirrors the four kinds of `assert` the prover emits:

* `gate`        — a per-row `tb.assert_zero(body)` (selector-gated semantics live in `body`).
* `transition`  — `tb.assert_zero(next[hi] - this.after[lo])`: continuity over the row window.
* `boundaryFirst nzero`/`boundaryLast nzero` — a `when_first_row`/`when_last_row` assert that
  the polynomial `nzero` (over `local`+`pi`) vanishes on that boundary row.
* `piBinding col k` — `local[col] == pi[k]` (a `when_first_row` PI pin or in-row binding). -/

/-- A boundary-row tag. -/
inductive VmRow where
  | first | last
  deriving Repr, DecidableEq

/-- The four EffectVM constraint forms. Each constructor records the SAME columns / PI indices
the Rust AIR carries, so a decoder reconstructs the exact gate. -/
inductive VmConstraint where
  /-- Per-row gate `body = 0` (term-for-term a `tb.assert_zero`). -/
  | gate (body : EmittedExpr)
  /-- Transition gate `next[STATE_BEFORE_BASE+hi] = this[STATE_AFTER_BASE+lo]` (continuity). -/
  | transition (hi lo : Nat)
  /-- Boundary gate on `row`: the polynomial `body` (over `local`/`pi`) vanishes on that row. -/
  | boundary (row : VmRow) (body : EmittedExpr)
  /-- PI binding on `row`: `local[col] = pi[piIndex]`. -/
  | piBinding (row : VmRow) (col piIndex : Nat)
  deriving Repr

/-! ## §4 — `VmHashSite`: a Poseidon2 hash site with a DETERMINISTIC ordering.

The running prover lays one Poseidon2 aux block per hash site, in the FIXED order `hash_sites()`
returns. Site `i`'s digest is bound to a named result column (or consumed by a later site). We
model a site by its result column (`digestCol`), an absorbed-input list (`inputs`, a list of
`HashInput`), and the `arity`. The denotation is parametric in an ABSTRACT permutation
`hash : List ℤ → ℤ` (the Layer-A carrier — NEVER an in-Lean algebraic hash), exactly as PART II
keeps `compress` abstract: a site HOLDS iff `loc digestCol = hash (resolved inputs)`. The ORDER
of the site list is load-bearing (a `Digest k` input reads an earlier site's resolved digest),
so the denotation walks the list left-to-right accumulating resolved digests — the Lean mirror
of the Rust `digests.push(d)` loop. -/

/-- A hash-site input: a trace column, an earlier site's digest (by 0-based index), or zero. -/
inductive HashInput where
  | col   (c : Nat)
  | digest (k : Nat)
  | zero
  deriving Repr, DecidableEq

/-- A Poseidon2 hash site: its result column, the absorbed inputs (in order), and the arity tag. -/
structure VmHashSite where
  digestCol : Nat
  inputs    : List HashInput
  arity     : Nat
  deriving Repr

/-- Resolve a single hash input under `(env, earlier-digests)`. A `digest k` reads the `k`-th
already-resolved digest (`default 0` if out of range — the emitter only ever references earlier
sites, so this never fires on a well-formed descriptor). -/
def HashInput.resolve (env : VmRowEnv) (digs : List ℤ) : HashInput → ℤ
  | .col c   => env.loc c
  | .digest k => digs.getD k 0
  | .zero    => 0

/-- Resolve a site's input list to the `ℤ` values absorbed (in order). -/
def VmHashSite.resolvedInputs (env : VmRowEnv) (digs : List ℤ) (s : VmHashSite) : List ℤ :=
  s.inputs.map (HashInput.resolve env digs)

/-! ### Walking the ordered site list (the Rust `digests` accumulator).

`siteDigestsAcc` produces the list of resolved digests for the sites, in order, each site
reading the digests of the sites BEFORE it. `siteHoldsAll` asserts every site's result column
equals its hash — the EffectVM hash layer's denotation, abstract in `hash`. -/

/-- **`siteDigestsAcc hash env acc sites`** — the head-first accumulator: `acc` holds the digests
of the sites ALREADY processed (sites that come BEFORE `sites` in the global order), so a
`digest k` input in `sites` reads `acc.getD k`. Returns the FULL digest list (acc ++ new). This
is the faithful Lean mirror of the Rust `digests.push(poseidon2(...))` loop, where site `i`
sees `digests[0..i]`. -/
def siteDigestsAcc (hash : List ℤ → ℤ) (env : VmRowEnv) :
    List ℤ → List VmHashSite → List ℤ
  | acc, []      => acc
  | acc, s :: ss =>
    let d := hash (s.resolvedInputs env acc)
    siteDigestsAcc hash env (acc ++ [d]) ss

/-- The resolved digests for the whole ordered site list (starting from an empty accumulator). -/
def VmHashSite.allDigests (hash : List ℤ → ℤ) (env : VmRowEnv) (sites : List VmHashSite) : List ℤ :=
  siteDigestsAcc hash env [] sites

/-- **`siteHoldsAll hash env sites`** — every site's result column carries its genuine digest:
for the `i`-th site `s`, `loc s.digestCol = hash (s.resolvedInputs env digests[0..i])`. This is
the EffectVM GROUP-4 (and per-effect) hash-binding denotation, abstract in `hash`. -/
def siteHoldsAll (hash : List ℤ → ℤ) (env : VmRowEnv) (sites : List VmHashSite) : Prop :=
  go [] sites
where
  go : List ℤ → List VmHashSite → Prop
  | _,   []      => True
  | acc, s :: ss =>
    let d := hash (s.resolvedInputs env acc)
    env.loc s.digestCol = d ∧ go (acc ++ [d]) ss

/-! ## §5 — `EffectVmDescriptor`: the whole emitted circuit.

The descriptor bundles the name, trace width, PI count, the constraint list, the ordered hash
sites, and the range-checked balance wires (the field-soundness teeth, mirroring `RangeSpec`). -/

/-- A range-check tooth: wire `wire` must lie in `[0, 2^bits)`. -/
structure VmRange where
  wire : Nat
  bits : Nat
  deriving Repr, DecidableEq

/-- The emitted EffectVM descriptor. -/
structure EffectVmDescriptor where
  name        : String
  traceWidth  : Nat
  piCount     : Nat
  constraints : List VmConstraint
  hashSites   : List VmHashSite
  ranges      : List VmRange

/-! ## §6 — The denotation: `satisfiedVm`.

A descriptor is satisfied by `(env, isFirst, isLast)` iff:
  * every `gate` body vanishes on `loc`;
  * every `transition` continuity holds (`nxt (sbCol hi) = loc (saCol lo)`);
  * every `boundary first/last` body vanishes WHEN the corresponding flag is set;
  * every `piBinding first/last col k` holds WHEN the corresponding flag is set;
  * every hash site carries its genuine digest (under the abstract `hash`).

The boundary/PI clauses are GUARDED by `isFirst`/`isLast` — matching `when_first_row()` /
`when_last_row()`, which are vacuous off the boundary. This is the faithful denotation of the
running AIR's row-quantified constraint set on a single row window. -/

/-- Meaning of one constraint on a row window with first/last flags. -/
def VmConstraint.holdsVm (env : VmRowEnv) (isFirst isLast : Bool) : VmConstraint → Prop
  | .gate body          => body.eval env.loc = 0
  | .transition hi lo   => env.nxt (sbCol hi) = env.loc (saCol lo)
  | .boundary .first b  => isFirst = true → b.eval env.loc = 0
  | .boundary .last  b  => isLast = true → b.eval env.loc = 0
  | .piBinding .first col k => isFirst = true → env.loc col = env.pub k
  | .piBinding .last  col k => isLast = true → env.loc col = env.pub k

/-- **`satisfiedVm hash d env isFirst isLast`** — the emitted descriptor's denotation: every
constraint holds on the row window AND every hash site carries its genuine digest. -/
def satisfiedVm (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) : Prop :=
  (∀ c ∈ d.constraints, c.holdsVm env isFirst isLast) ∧ siteHoldsAll hash env d.hashSites

/-! ## §7 — Wire rendering (the canonical JSON the Rust decoder ingests).

A deterministic renderer for the EffectVM forms, mirroring the `lean_descriptor_air` grammar
(reusing PART-I's `EmittedExpr.toJson` for gate bodies) extended with `transition` / `boundary`
/ `pi_binding` / `hash_site` tags. The hash-site rendering carries the site ORDER (array order),
the result column, the arity, and the resolved input descriptors. -/

open Dregg2.Exec.CircuitEmit (EmittedExpr.toJson)

/-- Render a hash input as JSON. -/
def HashInput.toJson : HashInput → String
  | .col c   => "{\"t\":\"col\",\"c\":" ++ toString c ++ "}"
  | .digest k => "{\"t\":\"digest\",\"k\":" ++ toString k ++ "}"
  | .zero    => "{\"t\":\"zero\"}"

/-- Render an input list as a JSON array. -/
def inputsToJson : List HashInput → String
  | []      => "[]"
  | [i]     => "[" ++ i.toJson ++ "]"
  | i :: is => "[" ++ i.toJson ++ (is.foldl (fun acc x => acc ++ "," ++ x.toJson) "") ++ "]"

/-- Render one constraint as JSON. -/
def VmConstraint.toJson : VmConstraint → String
  | .gate body          => "{\"t\":\"gate\",\"body\":" ++ body.toJson ++ "}"
  | .transition hi lo   =>
      "{\"t\":\"transition\",\"hi\":" ++ toString hi ++ ",\"lo\":" ++ toString lo ++ "}"
  | .boundary r b       =>
      let rs := match r with | .first => "first" | .last => "last"
      "{\"t\":\"boundary\",\"row\":\"" ++ rs ++ "\",\"body\":" ++ b.toJson ++ "}"
  | .piBinding r col k   =>
      let rs := match r with | .first => "first" | .last => "last"
      "{\"t\":\"pi_binding\",\"row\":\"" ++ rs ++ "\",\"col\":" ++ toString col ++
        ",\"pi_index\":" ++ toString k ++ "}"

/-- Render a list of constraints as a JSON array. -/
def constraintsToJson : List VmConstraint → String
  | []      => "[]"
  | [c]     => "[" ++ c.toJson ++ "]"
  | c :: cs => "[" ++ c.toJson ++ (cs.foldl (fun acc x => acc ++ "," ++ x.toJson) "") ++ "]"

/-- Render one hash site as JSON. -/
def VmHashSite.toJson (s : VmHashSite) : String :=
  "{\"digest_col\":" ++ toString s.digestCol ++ ",\"arity\":" ++ toString s.arity ++
    ",\"inputs\":" ++ inputsToJson s.inputs ++ "}"

/-- Render a list of hash sites as a JSON array. -/
def hashSitesToJson : List VmHashSite → String
  | []      => "[]"
  | [s]     => "[" ++ s.toJson ++ "]"
  | s :: ss => "[" ++ s.toJson ++ (ss.foldl (fun acc x => acc ++ "," ++ x.toJson) "") ++ "]"

/-- Render one range as JSON. -/
def VmRange.toJson (r : VmRange) : String :=
  "{\"wire\":" ++ toString r.wire ++ ",\"bits\":" ++ toString r.bits ++ "}"

/-- Render a list of ranges as a JSON array. -/
def rangesToJson : List VmRange → String
  | []      => "[]"
  | [r]     => "[" ++ r.toJson ++ "]"
  | r :: rs => "[" ++ r.toJson ++ (rs.foldl (fun acc x => acc ++ "," ++ x.toJson) "") ++ "]"

/-- **`emitVmJson`** — the canonical wire string for an EffectVM descriptor. -/
def emitVmJson (d : EffectVmDescriptor) : String :=
  "{\"name\":\"" ++ d.name ++ "\",\"trace_width\":" ++ toString d.traceWidth ++
  ",\"public_input_count\":" ++ toString d.piCount ++
  ",\"constraints\":" ++ constraintsToJson d.constraints ++
  ",\"hash_sites\":" ++ hashSitesToJson d.hashSites ++
  ",\"ranges\":" ++ rangesToJson d.ranges ++ "}"

end Dregg2.Circuit.Emit.EffectVmEmit
