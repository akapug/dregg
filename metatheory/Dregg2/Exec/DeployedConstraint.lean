/-
`Dregg2.Exec.DeployedConstraint` — THE single Lean source for the deployed
constraint evaluator's PURE (context-free, witness-free) subset.

## Why this file exists (the reality-gate collapse)

`docs/audit/GAME-PROOF-LARP-AUDIT.md` + `docs/audit/SEMANTIC-LEAN-BOUNDARY.md`
found that the game correctness proofs prove against a **hand-authored Lean copy**
of `cell/src/program/eval.rs` — a PARALLEL-DISCONNECTED evaluator that Rust never
calls, and that ALREADY DIVERGED from the deployed evaluator in two places:

  (a) `HeapAtom.immutable` — the tug copy `decide (new = old)` refuses the first
      write; the deployed `eval.rs:2382` admits the first write then freezes
      (`None => Ok(()) | Some a => new == Some a`).
  (b) `fieldGe` — the Exec copy `intLe val x` is a **signed unbounded `Int`**;
      the deployed `eval.rs:2842` `a >= b` is an **unsigned 256-bit big-endian**
      `[u8;32]` compare.

This module is the ONE evaluator, authored over the DEPLOYED substrate
(`[FieldElement;16]` registers + the unbounded-key heap, UNSIGNED 256-bit field
arithmetic with a low-64-bit lane for the counter reads), with BOTH divergences
reconciled to the **sound deployed semantics** (see `admits` / `heapAdmits`).
It is `@[export dregg_constraint_admits]`-ed (`admitsFFI`) so Rust CALLS it
instead of carrying its own `match`; `dregg-lean-ffi` links the compiled object
and the deployed admission decision is COMPUTED BY THIS FUNCTION.

## The substrate

A field value is the unsigned 256-bit big-endian integer a `[u8;32]` denotes, so
`DField := Nat` (invariant `< 2^256`, enforced by the 32-byte wire), unsigned
compare = `Nat` compare, and the deployed `field_to_u64` low lane = `n % 2^64`.

## Import discipline

Imports NOTHING beyond core `Init` — no Mathlib. The `@[export]`ed object must
be self-contained so its leanc-emitted `.c` splices into `libdregg_lean.a` without
dragging a Mathlib-tactic initializer closure into the FFI link (same discipline
as `Dregg2.Grain.R3Verify` / the crypto FFI cores; see `lean_init.c`).
-/

namespace Dregg2.Exec.DeployedConstraint

/-- The number of fixed register slots (`STATE_SLOTS` in `cell/src/state.rs`). -/
def stateSlots : Nat := 16

/-- `2^64`, the modulus of the low field lane (`field_to_u64`). -/
def two64 : Nat := 18446744073709551616

/-- A field value: the unsigned 256-bit big-endian integer a `[u8;32]` denotes. -/
abbrev DField := Nat

/-- `cell/src/program/eval.rs::field_to_u64` — the LOW 64-bit lane (bytes `[24..32]`
big-endian) of a field element. On the `Nat` model this is `n % 2^64`. -/
@[inline] def low64 (n : DField) : Nat := n % two64

/-- The pure heap-atom subset (`cell/src/program/types.rs::HeapAtom`,
`eval.rs::evaluate_heap_atom`). `equals`/`gte`/`lte` compare the FULL 256-bit
field; `memberOf`/`inRange`/`deltaBounded`/`deltaEquals` read the `field_to_u64`
low lane, exactly as the deployed evaluator does. -/
inductive DHeapAtom where
  | equals (v : DField)
  | gte (v : DField)
  | lte (v : DField)
  | memberOf (set : List Nat)
  | inRange (lo hi : Nat)
  | immutable
  | writeOnce
  | monotonic
  | strictMonotonic
  | deltaBounded (d : Nat)
  | deltaEquals (d : Int)
  deriving Repr, DecidableEq

/-- The pure `StateConstraint` subset the games are written in
(`cell/src/program/types.rs::StateConstraint`, `eval.rs::evaluate_constraint_full`).
Context-bearing / witnessed variants (`FieldGteHeight`, `SenderAuthorized`,
`PreimageGate`, `RateLimit`, `Custom`, `Witnessed`, …) are NOT in this subset —
they read `EvalContext` / a `WitnessBundle` and remain Rust-evaluated (see the
module note in `eval.rs`). -/
inductive DConstraint where
  | fieldEquals (index : Nat) (value : DField)
  | fieldGte (index : Nat) (value : DField)
  | fieldLte (index : Nat) (value : DField)
  | fieldLteField (left right : Nat)
  | fieldLteOther (index other : Nat) (delta : Int)
  | sumEquals (indices : List Nat) (value : DField)
  | immutable (index : Nat)
  | writeOnce (index : Nat)
  | monotonic (index : Nat)
  | strictMonotonic (index : Nat)
  | heapField (atom : DHeapAtom)
  deriving Repr, DecidableEq

/-- The `(old, new)` state slice one constraint eval sees over the deployed
substrate: 16 registers each side (always present — registers never "absent"),
the new nonce, an old-state presence flag (the executor's `old_state: Option`),
and the one heap key's `get_field_ext` `Option` on each side (the Rust marshaller
resolves the key; the ATOM SEMANTICS live here). -/
structure DInput where
  oldPresent : Bool
  newNonce : Nat
  oldRegs : List DField
  newRegs : List DField
  heapOld : Option DField
  heapNew : Option DField
  deriving Repr

/-- The admission verdict, mirroring `Result<(), ProgramError>`:
`ok` = admit; `violated` = `ConstraintViolated` (incl. the SumEquals u64-overflow
which the deployed evaluator also raises as `ConstraintViolated`);
`needsOld idx` = `TransitionCheckRequiresOldState { index }`;
`badIndex idx` = `InvalidFieldIndex { index }` (the `check_index` failure). -/
inductive DAdmit where
  | ok
  | violated
  | needsOld (index : Nat)
  | badIndex (index : Nat)
  deriving Repr, DecidableEq

/-- Read register `idx`, mirroring `eval.rs::check_index` (`idx >= STATE_SLOTS`
⇒ `InvalidFieldIndex`). The 16-length invariant on `regs` holds by the wire
(the parser fails closed otherwise), so `getD` never hits its default. -/
@[inline] def getReg (regs : List DField) (idx : Nat) : Option DField :=
  if idx ≥ stateSlots then none else some (regs.getD idx 0)

/-- `eval.rs::evaluate_heap_atom` — the deployed heap-atom teeth, EXACT.
`heapOld`/`heapNew` are `get_field_ext key` on each side (`None` = absent).

⚑ RECONCILED DIVERGENCE (a): `immutable` is the SOUND deployed semantics —
`none ⇒ ok` (the first write is free; heap keys start absent, so this is the write
that ESTABLISHES the sentinel) and `some a ⇒ new == some a` (frozen thereafter;
a flip OR an erasure refuses). The tug copy's `decide (new = old)` was the bug
(it refuses the establishing write, making the atom unusable). -/
def heapAdmits (atom : DHeapAtom) (oldV newV : Option DField) : DAdmit :=
  match atom with
  | .equals v =>
      match newV with
      | some x => if x = v then .ok else .violated
      | none => .violated
  | .gte v =>
      match newV with
      | some x => if v ≤ x then .ok else .violated   -- field_gte(x,v) = x >= v = v <= x (UNSIGNED)
      | none => .violated
  | .lte v =>
      match newV with
      | some x => if x ≤ v then .ok else .violated
      | none => .violated
  | .memberOf set =>
      match newV with
      | some x => if set.contains (low64 x) then .ok else .violated
      | none => .violated
  | .inRange lo hi =>
      match newV with
      | some x => let v := low64 x; if lo ≤ v ∧ v ≤ hi then .ok else .violated
      | none => .violated
  | .immutable =>
      match oldV with
      | none => .ok
      | some a => if newV = some a then .ok else .violated
  | .writeOnce =>
      match oldV with
      | none => .ok
      | some a => if a = 0 then .ok else (if newV = some a then .ok else .violated)
  | .monotonic =>
      match oldV, newV with
      | some a, some b => if a ≤ b then .ok else .violated
      | _, _ => .violated
  | .strictMonotonic =>
      match oldV, newV with
      | some a, some b => if a < b then .ok else .violated
      | _, _ => .violated
  | .deltaBounded d =>
      match oldV, newV with
      | some a, some b =>
          let delta : Int := (low64 b : Int) - (low64 a : Int)
          if delta.natAbs ≤ d then .ok else .violated
      | _, _ => .violated
  | .deltaEquals d =>
      match oldV, newV with
      | some a, some b =>
          let delta : Int := (low64 b : Int) - (low64 a : Int)
          if delta = d then .ok else .violated
      | _, _ => .violated

/-- SumEquals with faithful u64-overflow: accumulate the low-64 lanes; a partial
sum reaching `2^64` is the `checked_add` overflow the deployed evaluator raises as
`ConstraintViolated`; an out-of-range index is `InvalidFieldIndex` at the first
offending slot (iteration order, matching the Rust loop). -/
def sumEqualsAdmit (idxs : List Nat) (v : DField) (regs : List DField) : DAdmit :=
  let rec go (l : List Nat) (acc : Nat) : DAdmit :=
    match l with
    | [] => if acc = low64 v then .ok else .violated
    | idx :: rest =>
        if idx ≥ stateSlots then .badIndex idx
        else
          let s := acc + low64 (regs.getD idx 0)
          if s ≥ two64 then .violated else go rest s
  go idxs 0

/-- **THE deployed evaluator** — `eval.rs::evaluate_constraint_full`, EXACT, over
the deployed substrate.

⚑ RECONCILED DIVERGENCE (b): every field compare (`fieldGte`, `fieldLte`,
`fieldLteField`, `monotonic`, `strictMonotonic`) is UNSIGNED `Nat` compare — the
deployed `[u8;32]` `a >= b` — never the signed-`Int` `intLe` of the old Exec copy.
The transition variants (`immutable`/`writeOnce`/`monotonic`/`strictMonotonic`)
carry the deployed genesis escape: with `old` absent and `newNonce = 0` the field
may initialize (`ok`); with `old` absent and `newNonce ≠ 0` the executor raises
`TransitionCheckRequiresOldState` (`needsOld`). -/
def admits (c : DConstraint) (i : DInput) : DAdmit :=
  match c with
  | .fieldEquals idx v =>
      match getReg i.newRegs idx with
      | none => .badIndex idx
      | some x => if x = v then .ok else .violated
  | .fieldGte idx v =>
      match getReg i.newRegs idx with
      | none => .badIndex idx
      | some x => if v ≤ x then .ok else .violated
  | .fieldLte idx v =>
      match getReg i.newRegs idx with
      | none => .badIndex idx
      | some x => if x ≤ v then .ok else .violated
  | .fieldLteField l r =>
      match getReg i.newRegs l with
      | none => .badIndex l
      | some a =>
          match getReg i.newRegs r with
          | none => .badIndex r
          | some b => if a ≤ b then .ok else .violated
  | .fieldLteOther idx other delta =>
      match getReg i.newRegs idx with
      | none => .badIndex idx
      | some a =>
          match getReg i.newRegs other with
          | none => .badIndex other
          | some b =>
              let lhs : Int := (low64 a : Int)
              let rhs : Int := (low64 b : Int) + delta
              if lhs > rhs then .violated else .ok
  | .sumEquals idxs v => sumEqualsAdmit idxs v i.newRegs
  | .immutable idx =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.oldPresent then
        (if i.newRegs.getD idx 0 = i.oldRegs.getD idx 0 then .ok else .violated)
      else (if i.newNonce = 0 then .ok else .needsOld idx)
  | .writeOnce idx =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.oldPresent then
        let o := i.oldRegs.getD idx 0
        let n := i.newRegs.getD idx 0
        (if o = 0 ∨ n = o then .ok else .violated)
      else (if i.newNonce = 0 then .ok else .needsOld idx)
  | .monotonic idx =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.oldPresent then
        (if i.oldRegs.getD idx 0 ≤ i.newRegs.getD idx 0 then .ok else .violated)
      else (if i.newNonce = 0 then .ok else .needsOld idx)
  | .strictMonotonic idx =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.oldPresent then
        (if i.oldRegs.getD idx 0 < i.newRegs.getD idx 0 then .ok else .violated)
      else (if i.newNonce = 0 then .ok else .needsOld idx)
  | .heapField atom => heapAdmits atom i.heapOld i.heapNew

/-! ## The `@[export]` wire codec (Rust → Lean)

Single-line, space-separated token stream; a malformed wire fails CLOSED
(`"1"` = refuse). Token order:

```
oldPresent(0|1)  newNonce(dec)
heapOldPresent(0|1) heapOldVal(hex)  heapNewPresent(0|1) heapNewVal(hex)
R0..R15(hex, 16 tokens)              -- oldRegs
N0..N15(hex, 16 tokens)              -- newRegs
CONSTRAINT: <TAG> <args…>
```

Field values are hex (the 32-byte `FieldElement`, big-endian); indices / nonce /
counts / u64 args are decimal; deltas are signed decimal. Output:
`"0"` ok · `"1"` violated · `"2 <idx>"` needsOld · `"3 <idx>"` badIndex. -/

/-- One hex digit → `Nat`. -/
@[inline] def hexDigit? (c : Char) : Option Nat :=
  let n := c.toNat
  if '0'.toNat ≤ n ∧ n ≤ '9'.toNat then some (n - '0'.toNat)
  else if 'a'.toNat ≤ n ∧ n ≤ 'f'.toNat then some (n - 'a'.toNat + 10)
  else if 'A'.toNat ≤ n ∧ n ≤ 'F'.toNat then some (n - 'A'.toNat + 10)
  else none

/-- Parse a big-endian hex string → `Nat` (fails closed on any non-hex char). -/
def parseHex (s : String) : Option Nat :=
  s.toList.foldl (fun acc c =>
    match acc, hexDigit? c with
    | some a, some d => some (a * 16 + d)
    | _, _ => none) (some 0)

/-- Parse an unsigned decimal token. -/
@[inline] def parseNat (s : String) : Option Nat := s.toNat?

/-- Parse a signed decimal token (`-…` allowed). -/
def parseInt (s : String) : Option Int :=
  if s.startsWith "-" then (s.drop 1).toNat?.map (fun n => -(Int.ofNat n))
  else s.toNat?.map Int.ofNat

/-- Pop `n` tokens. -/
def popN : Nat → List String → Option (List String × List String)
  | 0, rest => some ([], rest)
  | _+1, [] => none
  | k+1, t :: rest =>
      match popN k rest with
      | some (hd, tl) => some (t :: hd, tl)
      | none => none

/-- Parse a heap atom from its remaining tokens. -/
def parseHeapAtom : List String → Option DHeapAtom
  | "HEQ" :: v :: _ => (parseHex v).map .equals
  | "HGE" :: v :: _ => (parseHex v).map .gte
  | "HLE" :: v :: _ => (parseHex v).map .lte
  | "HMEM" :: n :: rest =>
      match parseNat n with
      | none => none
      | some k =>
          match popN k rest with
          | some (vs, _) =>
              (vs.foldr (fun t acc => match acc, parseNat t with
                | some l, some x => some (x :: l)
                | _, _ => none) (some [])).map .memberOf
          | none => none
  | "HRANGE" :: lo :: hi :: _ =>
      match parseNat lo, parseNat hi with
      | some a, some b => some (.inRange a b)
      | _, _ => none
  | "HIM" :: _ => some .immutable
  | "HWO" :: _ => some .writeOnce
  | "HMON" :: _ => some .monotonic
  | "HSMON" :: _ => some .strictMonotonic
  | "HDB" :: d :: _ => (parseNat d).map .deltaBounded
  | "HDE" :: d :: _ => (parseInt d).map .deltaEquals
  | _ => none

/-- Parse the constraint tail. -/
def parseConstraint : List String → Option DConstraint
  | "FE" :: i :: v :: _ =>
      match parseNat i, parseHex v with | some a, some b => some (.fieldEquals a b) | _, _ => none
  | "FG" :: i :: v :: _ =>
      match parseNat i, parseHex v with | some a, some b => some (.fieldGte a b) | _, _ => none
  | "FL" :: i :: v :: _ =>
      match parseNat i, parseHex v with | some a, some b => some (.fieldLte a b) | _, _ => none
  | "FLF" :: l :: r :: _ =>
      match parseNat l, parseNat r with | some a, some b => some (.fieldLteField a b) | _, _ => none
  | "FLO" :: i :: o :: d :: _ =>
      match parseNat i, parseNat o, parseInt d with
      | some a, some b, some dd => some (.fieldLteOther a b dd) | _, _, _ => none
  | "SE" :: v :: n :: rest =>
      match parseHex v, parseNat n with
      | some vv, some k =>
          match popN k rest with
          | some (idxs, _) =>
              (idxs.foldr (fun t acc => match acc, parseNat t with
                | some l, some x => some (x :: l)
                | _, _ => none) (some [])).map (fun is => .sumEquals is vv)
          | none => none
      | _, _ => none
  | "IM" :: i :: _ => (parseNat i).map .immutable
  | "WO" :: i :: _ => (parseNat i).map .writeOnce
  | "MO" :: i :: _ => (parseNat i).map .monotonic
  | "SM" :: i :: _ => (parseNat i).map .strictMonotonic
  | toks => (parseHeapAtom toks).map .heapField

/-- Parse a fixed run of `n` hex field tokens into a `List DField`. -/
def parseHexRun (n : Nat) (toks : List String) : Option (List DField × List String) :=
  match popN n toks with
  | none => none
  | some (hd, tl) =>
      match hd.foldr (fun t acc => match acc, parseHex t with
        | some l, some x => some (x :: l)
        | _, _ => none) (some []) with
      | some fs => some (fs, tl)
      | none => none

/-- Parse the whole wire into `(constraint, input)`. Fails closed. -/
def parse (s : String) : Option (DConstraint × DInput) := do
  let toks := (s.splitOn " ").filter (· ≠ "")
  let (op :: nn :: hop :: hov :: hnp :: hnv :: rest0) := toks | none
  let oldPresent := op == "1"
  let newNonce ← parseNat nn
  let heapOld ← if hop == "1" then (parseHex hov).map some else some none
  let heapNew ← if hnp == "1" then (parseHex hnv).map some else some none
  let (oldRegs, rest1) ← parseHexRun stateSlots rest0
  let (newRegs, rest2) ← parseHexRun stateSlots rest1
  if oldRegs.length ≠ stateSlots ∨ newRegs.length ≠ stateSlots then none
  else
    let c ← parseConstraint rest2
    some (c, { oldPresent, newNonce, oldRegs, newRegs, heapOld, heapNew })

/-- Render a verdict to the wire code. -/
def render : DAdmit → String
  | .ok => "0"
  | .violated => "1"
  | .needsOld idx => "2 " ++ toString idx
  | .badIndex idx => "3 " ++ toString idx

/-- The whole String → String decision. A malformed wire refuses (`"1"`). -/
def admitsWire (s : String) : String :=
  match parse s with
  | none => "1"
  | some (c, i) => render (admits c i)

/-- **`@[export dregg_constraint_admits]`** — the FFI entry Rust calls. Runs the
verified deployed evaluator over the wire slice; the deployed node's admission
decision for the pure-constraint subset is COMPUTED HERE. -/
@[export dregg_constraint_admits]
def admitsFFI (s : String) : String := admitsWire s

/-! ## Self-tests — the evaluator agrees with `eval.rs` on the pinned cases,
including the two reconciled divergence boundaries. `#guard` FAILS the Lean build
on regression, so these are teeth, not comments. -/

-- 16 registers all zero except where noted; helper wire builders.
private def zeros16 : String := String.intercalate " " (List.replicate 16 "0")

/-- Build a wire with an all-zero old/new state (nonce 0, no heap) + a constraint. -/
private def wire0 (c : String) : String :=
  "1 0 0 0 0 0 " ++ zeros16 ++ " " ++ zeros16 ++ " " ++ c

-- fieldEquals 0 == 0  ⇒ ok
#guard admitsWire (wire0 "FE 0 0") = "0"
-- fieldEquals 0 == 5 on a zero reg ⇒ violated
#guard admitsWire (wire0 "FE 0 5") = "1"
-- fieldGte 0 >= 0 ⇒ ok
#guard admitsWire (wire0 "FG 0 0") = "0"
-- badIndex: idx 16 is out of range
#guard admitsWire (wire0 "FE 16 0") = "3 16"

-- ⚑ DIVERGENCE (b), UNSIGNED: a huge value in reg[0] must be >= a small threshold.
-- new reg[0] = 2^255 (hex 8000…00, 64 chars), fieldGte >= 1 ⇒ ok under UNSIGNED
-- (a signed-Int reading would make 2^255 "negative" and REFUSE — the old bug).
private def bigNewWire (c : String) : String :=
  let big := "8000000000000000000000000000000000000000000000000000000000000000"
  "1 0 0 0 0 0 " ++ zeros16 ++ " "
    ++ String.intercalate " " (big :: List.replicate 15 "0") ++ " " ++ c
#guard admitsWire (bigNewWire "FG 0 1") = "0"

-- ⚑ DIVERGENCE (a), heap immutable: absent old ⇒ first write is FREE (ok).
-- wire: old absent(0), heapOld absent(0), heapNew present(1) = 7, constraint HIM.
private def heapImmFirstWrite : String :=
  "0 0 0 0 1 7 " ++ zeros16 ++ " " ++ zeros16 ++ " HIM"
#guard admitsWire heapImmFirstWrite = "0"
-- heap immutable: present old(=7) and new flips to 9 ⇒ violated (frozen).
private def heapImmFlip : String :=
  "1 0 1 7 1 9 " ++ zeros16 ++ " " ++ zeros16 ++ " HIM"
#guard admitsWire heapImmFlip = "1"
-- heap immutable: present old(=7) and new stays 7 ⇒ ok.
private def heapImmSame : String :=
  "1 0 1 7 1 7 " ++ zeros16 ++ " " ++ zeros16 ++ " HIM"
#guard admitsWire heapImmSame = "0"

-- Immutable register with old absent + nonce != 0 ⇒ needsOld.
#guard admitsWire ("0 5 0 0 0 0 " ++ zeros16 ++ " " ++ zeros16 ++ " IM 0") = "2 0"
-- Immutable register with old absent + nonce == 0 ⇒ ok (genesis init).
#guard admitsWire ("0 0 0 0 0 0 " ++ zeros16 ++ " " ++ zeros16 ++ " IM 0") = "0"

-- SumEquals over regs [0,1] = 0 with value 0 ⇒ ok.
#guard admitsWire (wire0 "SE 0 2 0 1") = "0"

end Dregg2.Exec.DeployedConstraint
