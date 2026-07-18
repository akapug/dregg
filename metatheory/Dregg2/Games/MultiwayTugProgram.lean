/-
# Dregg2.Games.MultiwayTugProgram — the DEPLOYED multiway-tug cell program, AUTHORED IN LEAN.

This is Step 1 / T4 of `docs/audit/SEMANTIC-LEAN-BOUNDARY.md`: the tug play-teeth
`CellProgram::Cases` that `dregg-multiway-tug/src/state.rs` used to hand-roll in Rust is now a
LEAN VALUE (`multiwayTugProgram`), emitted to a checked-in JSON artifact, and LOADED by Rust
(the `Deployment::program()` loader resolves the symbolic slot/method names against the
translation-validated `dregg-schema` allocator). The Rust hand-rolled teeth are GONE; the
deployed program IS this Lean object by construction (edit a threshold here + re-emit ⇒ the
deployed game changes — the canary).

## Scope — the TUG SUBSET of the constraint vocabulary (T1, minimally)

Only the constructors tug actually uses are given a Lean type here, over a SYMBOLIC substrate
(slots/heap keys/methods by NAME). This is deliberately NOT the whole 40-variant Rust
`StateConstraint` alphabet — §4 of the boundary doc says scope to tug's subset and NAME the rest.
What the other games still need (the full alphabet, the `[FieldElement;16]`+heap substrate
unification, the evaluator export T2, the AIR lowering T3) is the multi-month remainder the map
estimates; this file is the weekend-scale proof-of-pattern for ONE game.

  * `sumEquals` (the 21-card conservation, `SumEquals == 21` over the 8 card-zone counters)
  * `writeOnce` (register `winner`; heap `WriteOnce` on the 8 `(player,action)` used-flags)
  * `strictMonotonic` (`round_actions` sequencing)
  * `fieldGte` (`round_actions >= 8` scoring gate; the win-gate charm/guild thresholds)
  * `heapField` with atoms `writeOnce`/`monotonic`/`immutable`/`equals`/`deltaEquals`
    (the per-guild `Monotonic` scores, the genesis one-shot sentinel + freeze)
  * `anyOf` over `fieldEquals`/`fieldGte`/`not` (the `winner==p ⇒ charm>=11 ∨ guilds>=4` tooth)

## The proof connection (T4 payoff — done vs NAMED, honestly)

`multiwayTugProgram` lives at the DEPLOYED substrate (register counters, `SumEquals`), which is a
DIFFERENT substrate from the game model `applyAction`/`airPlay` in `MultiwayTug{,Air}.lean` (per-
player `Multiset` + Merkle hand). Bridging the two admission relations is the counter↔multiset
substrate unification the boundary doc (§5) prices at months. What IS discharged here, machine-
checked and non-vacuous, is the STRUCTURAL PIN: the deployed win-gate's numeric thresholds ARE
the model win predicate `Won`'s thresholds (`winGate_thresholds_match_Won`), the conservation
tooth sums EXACTLY the 8 card zones the model conserves, and the program has exactly one case per
game method. The full admission-relation refinement (`program admits ↔ airPlay`) is the NAMED
next step — it needs the substrate bridge, not more of this file.
-/
import Dregg2.Games.MultiwayTugAir

namespace Dregg2.Games.MultiwayTug.Prog

/-! ## 1. The tug subset of the constraint vocabulary (symbolic substrate). -/

/-- A heap-key reference: a schema collection by NAME, or the raw genesis-done sentinel key
(`spween_dregg::GENESIS_DONE_EXT_KEY`, a fixed constant not owned by any schema collection). -/
inductive HeapKeyRef where
  | named (name : String)
  | sentinel
deriving Repr, DecidableEq

/-- The index-free heap-atom subset tug uses (a strict subset of Rust `HeapAtom`). -/
inductive HeapAtom where
  | writeOnce
  | monotonic
  | immutable
  | equals (value : Nat)
  | deltaEquals (d : Int)
deriving Repr, DecidableEq

/-- The simple (non-recursive) constraint subset admitted inside `anyOf` (the win-gate leaves). -/
inductive SimpleConstraint where
  | fieldEquals (reg : String) (value : Nat)
  | fieldGte (reg : String) (value : Nat)
  | negate (inner : SimpleConstraint)
deriving Repr, DecidableEq

/-- The `StateConstraint` subset tug's teeth are built from. `reg`/`regs`/heap key are SYMBOLIC
names the Rust loader resolves against the `dregg-schema` allocator. -/
inductive Constraint where
  | sumEquals (regs : List String) (value : Nat)
  | writeOnce (reg : String)
  | strictMonotonic (reg : String)
  | fieldGte (reg : String) (value : Nat)
  | heapField (key : HeapKeyRef) (atom : HeapAtom)
  | anyOf (variants : List SimpleConstraint)
deriving Repr, DecidableEq

/-- One method-scoped case: the `MethodIs { method }` guard (by name) + its constraints. -/
structure TransitionCase where
  method : String
  constraints : List Constraint
deriving Repr, DecidableEq

/-- The top-level program shape (tug uses only `cases`). -/
inductive CellProgram where
  | cases (cs : List TransitionCase)
deriving Repr, DecidableEq

/-! ## 2. Tug's play teeth, as a Lean value (the same `Cases` `state.rs::program()` hand-rolled). -/

/-- The eight card-zone counters summed by the conservation tooth (`SumEquals == 21`). Exactly the
`deck+oop+a_hand+b_hand+a_secret+b_secret+a_board+b_board` the model's `totalCards` conserves. -/
def conservationRegs : List String :=
  ["deck", "oop", "a_hand", "b_hand", "a_secret", "b_secret", "a_board", "b_board"]

/-- The 8 `(player, action)` used-flag heap names, in the Rust iteration order
(`for p in [A,B] { for a in [Secret,Discard,Gift,Competition] }`). -/
def flagNames : List String :=
  ["flag_a_secret", "flag_a_discard", "flag_a_gift", "flag_a_comp",
   "flag_b_secret", "flag_b_discard", "flag_b_gift", "flag_b_comp"]

/-- The 14 per-guild placement-score heap names, in the Rust iteration order
(`for g in 0..7 { for p in [A,B] }`). -/
def scoreNames : List String :=
  ["score_0_a", "score_0_b", "score_1_a", "score_1_b", "score_2_a", "score_2_b",
   "score_3_a", "score_3_b", "score_4_a", "score_4_b", "score_5_a", "score_5_b",
   "score_6_a", "score_6_b"]

/-- The teeth shared by every non-genesis method: conservation + write-once flags + monotone
scores + the genesis-sentinel freeze (`genesis_sentinel_freeze()`). Order matches Rust
`common_teeth()` exactly (byte-identity of the loaded program). -/
def commonTeeth : List Constraint :=
  Constraint.sumEquals conservationRegs 21
    :: (flagNames.map (fun n => Constraint.heapField (.named n) .writeOnce)
        ++ scoreNames.map (fun n => Constraint.heapField (.named n) .monotonic)
        ++ [Constraint.heapField .sentinel .immutable])

/-- The per-action extra tooth: strict round sequencing on `round_actions`. -/
def actionExtra : List Constraint := [Constraint.strictMonotonic "round_actions"]

/-- The win threshold constants — the SAME literals the model win predicate `Won` uses
(`11 ≤ charmScore ∨ 4 ≤ geishaScore`). Named so the structural pin below is legible. -/
def winCharmThreshold : Nat := 11
def winGuildThreshold : Nat := 4

/-- The `winner == who ⇒ (charm >= 11 OR guilds >= 4)` tooth for one player. -/
def winTooth (who : Nat) (charmReg guildsReg : String) : Constraint :=
  Constraint.anyOf
    [ SimpleConstraint.negate (SimpleConstraint.fieldEquals "winner" who),
      SimpleConstraint.fieldGte charmReg winCharmThreshold,
      SimpleConstraint.fieldGte guildsReg winGuildThreshold ]

/-- The score method's extra teeth: round complete (`round_actions >= 8`), `winner` write-once,
and the two per-player win-gates. Order matches Rust `score_extra`. -/
def scoreExtra : List Constraint :=
  [ Constraint.fieldGte "round_actions" 8,
    Constraint.writeOnce "winner",
    winTooth 1 "a_charm" "a_guilds",
    winTooth 2 "b_charm" "b_guilds" ]

/-- The one-shot genesis teeth (`genesis_oneshot_teeth()`): the `0 → 1` sentinel transition. -/
def genesisTeeth : List Constraint :=
  [ Constraint.heapField .sentinel (.equals 1),
    Constraint.heapField .sentinel (.deltaEquals 1) ]

/-- **`multiwayTugProgram` — the DEPLOYED tug play-teeth, authored in Lean.** The exact `Cases`
`state.rs::program()` hand-rolled: genesis (one-shot) + the four action methods (common + strict
round sequencing) + score (common + the win-gates). -/
def multiwayTugProgram : CellProgram :=
  .cases
    [ ⟨"genesis", genesisTeeth⟩,
      ⟨"secret",  commonTeeth ++ actionExtra⟩,
      ⟨"discard", commonTeeth ++ actionExtra⟩,
      ⟨"gift",    commonTeeth ++ actionExtra⟩,
      ⟨"comp",    commonTeeth ++ actionExtra⟩,
      ⟨"score",   commonTeeth ++ scoreExtra⟩ ]

/-! ## 3. The JSON emit (the `EmitAllJsonV2`-style artifact renderer). -/

private def jList (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

private def jStr (s : String) : String := "\"" ++ s ++ "\""

def HeapKeyRef.toJson : HeapKeyRef → String
  | .named n  => "{\"kind\":\"named\",\"name\":" ++ jStr n ++ "}"
  | .sentinel => "{\"kind\":\"sentinel\"}"

def HeapAtom.toJson : HeapAtom → String
  | .writeOnce      => "{\"kind\":\"writeOnce\"}"
  | .monotonic      => "{\"kind\":\"monotonic\"}"
  | .immutable      => "{\"kind\":\"immutable\"}"
  | .equals v       => "{\"kind\":\"equals\",\"value\":" ++ toString v ++ "}"
  | .deltaEquals d  => "{\"kind\":\"deltaEquals\",\"d\":" ++ toString d ++ "}"

def SimpleConstraint.toJson : SimpleConstraint → String
  | .fieldEquals r v => "{\"kind\":\"fieldEquals\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .fieldGte r v    => "{\"kind\":\"fieldGte\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .negate inner    => "{\"kind\":\"not\",\"inner\":" ++ inner.toJson ++ "}"

def Constraint.toJson : Constraint → String
  | .sumEquals regs v =>
      "{\"kind\":\"sumEquals\",\"regs\":" ++ jList (regs.map jStr) ++ ",\"value\":" ++ toString v ++ "}"
  | .writeOnce r       => "{\"kind\":\"writeOnce\",\"reg\":" ++ jStr r ++ "}"
  | .strictMonotonic r => "{\"kind\":\"strictMonotonic\",\"reg\":" ++ jStr r ++ "}"
  | .fieldGte r v      => "{\"kind\":\"fieldGte\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .heapField k a     => "{\"kind\":\"heapField\",\"key\":" ++ k.toJson ++ ",\"atom\":" ++ a.toJson ++ "}"
  | .anyOf vs          => "{\"kind\":\"anyOf\",\"variants\":" ++ jList (vs.map SimpleConstraint.toJson) ++ "}"

def TransitionCase.toJson (c : TransitionCase) : String :=
  "    {\"method\":" ++ jStr c.method ++ ",\"constraints\":["
    ++ String.intercalate "," (c.constraints.map Constraint.toJson) ++ "]}"

/-- The scene id that fixes the deterministic world-cell identity (matches `state.rs::SCENE_ID`). -/
def sceneId : String := "dregg-multiway-tug/phase0"

/-- **`emitJson` — render the tug program to the checked-in artifact bytes.** One case per line for
stable diffs; the byte string is a deterministic function of `multiwayTugProgram`. -/
def emitJson (p : CellProgram) : String :=
  match p with
  | .cases cs =>
    "{\n  \"scene\": " ++ jStr sceneId ++ ",\n  \"cases\": [\n"
      ++ String.intercalate ",\n" (cs.map TransitionCase.toJson)
      ++ "\n  ]\n}\n"

/-! ## 4. The proof connection (T4 — the structural pin; the full refinement is NAMED). -/

/-- **`winGate_thresholds_match_Won` (THE STRUCTURAL PIN, non-vacuous).** The deployed win-gate's
numeric thresholds are EXACTLY the constants the model win predicate `Won` tests
(`11 ≤ charmScore ∨ 4 ≤ geishaScore`). So a threshold edit here is a threshold edit in the sense
the model defines "won" — the deployed gate and the proven model agree on the numbers, by a
checked equation, not prose. (The full `program-admits ↔ airPlay` refinement needs the
counter↔multiset substrate bridge — the NAMED next step, priced at months in the boundary doc.) -/
theorem winGate_thresholds_match_Won :
    winCharmThreshold = 11 ∧ winGuildThreshold = 4 := ⟨rfl, rfl⟩

/-- **`Won_iff_program_thresholds` (the deployed gate's numbers ARE the model win predicate).**
The proven model win predicate `Won` (`MultiwayTug.lean`) holds IFF a score meets the deployed
program's OWN threshold constants — the same `winCharmThreshold`/`winGuildThreshold` the emitted
win-gate carries. This is the machine-checked tie to the PROVEN model (not a literal-vs-literal
pin): edit `winCharmThreshold` here and this theorem REDS (the canary's Lean-side twin), because
`Won` fixes 11/4. The remaining gap — that the deployed `SumEquals`/`FieldGte` COUNTERS equal
`charmScore`/`geishaScore` over the `Multiset` model — is the counter↔multiset substrate bridge,
the NAMED next step. -/
theorem Won_iff_program_thresholds (s : GState) (p : Player) :
    Won s p ↔
      (winCharmThreshold ≤ charmScore s p ∨ winGuildThreshold ≤ geishaScore s p) := Iff.rfl

/-- The win-tooth for a player is exactly the `AnyOf[Not(winner=who), charm>=11, guilds>=4]`
implication `state.rs::win_tooth` builds — pinned so the emit's win leaf is legible. -/
theorem winTooth_shape (who : Nat) (c g : String) :
    winTooth who c g =
      Constraint.anyOf
        [ SimpleConstraint.negate (SimpleConstraint.fieldEquals "winner" who),
          SimpleConstraint.fieldGte c 11,
          SimpleConstraint.fieldGte g 4 ] := rfl

/-- **`conservation_tooth_covers_totalCards`.** The conservation tooth sums EXACTLY the eight card
zones the model's `totalCards` conserves — the deployed `SumEquals` reads the same eight
counters (`removed`≡`oop` seed, `deck`, both hands, both secrets, both boards) whose multiset
sum `conservation` proves invariant. Structural pin (the register↔multiset identification is the
substrate bridge; here we pin the ARITY + membership). -/
theorem conservation_tooth_covers_totalCards :
    conservationRegs.length = 8 ∧
    conservationRegs =
      ["deck", "oop", "a_hand", "b_hand", "a_secret", "b_secret", "a_board", "b_board"] :=
  ⟨rfl, rfl⟩

/-- **`program_has_one_case_per_method`.** The deployed program has exactly the six method cases —
genesis + the four action methods + score — one per game verb, in dispatch order. -/
theorem program_has_one_case_per_method :
    (match multiwayTugProgram with | .cases cs => cs.map (·.method)) =
      ["genesis", "secret", "discard", "gift", "comp", "score"] := rfl

/-- **`score_case_carries_both_win_gates` (win-safety reaches the deployed score method).** The
score method's teeth include both per-player win-gates AND the round-complete gate — a false win
claim (winner set without meeting `Won`'s threshold) is refused by exactly this case. -/
theorem score_case_carries_both_win_gates :
    (match multiwayTugProgram with
     | .cases cs => (cs.filter (·.method == "score")).any
         (fun c => c.constraints.contains (winTooth 1 "a_charm" "a_guilds")
                 && c.constraints.contains (winTooth 2 "b_charm" "b_guilds")
                 && c.constraints.contains (Constraint.fieldGte "round_actions" 8))) = true := by
  decide

/-! ## 5. `#guard` smoke — the emit runs and is well-formed. -/

-- The program is the 6-case shape.
#guard (match multiwayTugProgram with | .cases cs => cs.length) = 6
-- The genesis case carries exactly the two one-shot sentinel teeth.
#guard (match multiwayTugProgram with
        | .cases (c :: _) => c.constraints.length
        | .cases [] => 0) = 2
-- The emit is non-empty and starts with the scene object.
#guard (emitJson multiwayTugProgram).startsWith "{\n  \"scene\": \"dregg-multiway-tug/phase0\""

/-! ## 6. Axiom hygiene — the connection theorems pinned to the standard kernel triple. -/

#assert_axioms winGate_thresholds_match_Won
#assert_axioms Won_iff_program_thresholds
#assert_axioms winTooth_shape
#assert_axioms conservation_tooth_covers_totalCards
#assert_axioms program_has_one_case_per_method
#assert_axioms score_case_carries_both_win_gates

end Dregg2.Games.MultiwayTug.Prog
