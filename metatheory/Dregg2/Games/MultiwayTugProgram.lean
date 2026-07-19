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

## ⚑ The referee SEMANTICS — where the deployed evaluator now lives (LARP-audit collapse)

`docs/audit/GAME-PROOF-LARP-AUDIT.md` correctly flagged that the `Constraint.admits` /
`HeapAtom.admits` / `CellProgram.admitsMethod` below were a HAND-AUTHORED Lean copy of the
constraint teeth in `cell/src/program/eval.rs` that Rust never called — a PARALLEL-DISCONNECTED
model that had already DIVERGED from the deployed evaluator (the `immutable` atom above). That
disconnect is now closed on the SEMANTICS axis: the pure (context-free, witness-free) constraint
teeth are AUTHORED ONCE, over the DEPLOYED substrate (`[FieldElement;16]` + heap, UNSIGNED-256
field compares), in `Dregg2.Exec.DeployedConstraint.admits`, which is `@[export
dregg_constraint_admits]`-ed and CALLED by the deployed node (`eval.rs`'s `evaluate_constraint_full`
routes the subset through it via the `dregg_cell::program::ConstraintOracle` seam installed by
`dregg-exec-lean`). The reality-gate canary
(`dregg-lean-ffi/tests/deployed_constraint_probe.rs`,
`exec-lean/tests/constraint_oracle_reality_gate.rs`) proves the deployed decision IS the Lean
source; the differential gate (`exec-lean/tests/constraint_oracle_differential.rs`) pins Lean ==
Rust across the subset.

The `admits` copy BELOW is the honest LOCAL model at tug's SYMBOLIC (String-keyed counter)
substrate — the substrate the game proofs are written over. ⚑ LARP-audit fix: the second seam
the audit named — the String-counter ↔ 16-register allocation bridge — is now BUILT (`§4I`):
`tugRegIdx`/`tugSlots` marshal the counter fragment into the deployed `[FieldElement;16]` + heap
`DInput`, `heapAdmits_*_ok`/`sumEquals_conservation_deployed`/`sumGo_ok` prove the local verdict
agrees with `DeployedConstraint.admits` on the tug pure subset, and
`program_admits_legal_play_deployed` RE-STATES the forward refinement (`§4E`) against the deployed
evaluator itself. So tug's action-teeth admission IS now proven-to-DeployedConstraint (FORWARD:
legal ⇒ the deployed evaluator admits). What remains NAMED: the REVERSE (admitted ⇒ legal, =
`airPlay`'s membership job, `§4H`) and the recursive `anyOf` win-teeth (NOT in the exported pure
subset — the score-case win-gate reaches the referee at the SYMBOLIC layer via
`winTooth_admits_iff_Won`, `§4F`).
-/
import Dregg2.Games.MultiwayTugAir
import Dregg2.Exec.DeployedConstraint
import Mathlib.Tactic.FinCases

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

/-! ## 2. Tug's play teeth, DERIVED from the game combinatorics (not transcribed literals).

The heap-key NAMES are GENERATED from the game's own index sets — players `× ` action-kinds for
the used-flags, guilds `× ` players for the placement scores — the SAME nested product the Rust
allocator builds with `for p in [A,B] { for a in [..] }` / `for g in 0..7 { for p in [A,B] }`
(`state.rs::schema`). This is the un-mirror: the Lean is not a hand-copied list of 22 string
literals but the structural enumeration the game defines; `flagNames_literal` / `scoreNames_literal`
pin the generation to the exact wire strings the loader resolves (so the emitted bytes are
unchanged). -/

/-- The player wire tag (`state.rs::player_tag`). -/
def playerTag : Player → String
  | .p1 => "a"
  | .p2 => "b"

/-- The action-kind wire tag (`state.rs::action_tag`). -/
def actionTag : ActionKind → String
  | .secretK => "secret"
  | .discardK => "discard"
  | .giftK => "gift"
  | .competitionK => "comp"

/-- The two players, in allocation order. -/
def allPlayers : List Player := [.p1, .p2]

/-- The four action-kinds, in allocation order. -/
def allActionKinds : List ActionKind := [.secretK, .discardK, .giftK, .competitionK]

/-- A `(player, action)` used-flag heap name (`state.rs::flag_name`). -/
def flagName (p : Player) (k : ActionKind) : String :=
  "flag_" ++ playerTag p ++ "_" ++ actionTag k

/-- A `(guild, player)` placement-score heap name (`state.rs::score_name`). -/
def scoreName (g : Fin 7) (p : Player) : String :=
  "score_" ++ toString g.val ++ "_" ++ playerTag p

/-- The eight card-zone counters summed by the conservation tooth (`SumEquals == 21`). Exactly the
`deck+oop+a_hand+b_hand+a_secret+b_secret+a_board+b_board` the model's `totalCards` conserves. -/
def conservationRegs : List String :=
  ["deck", "oop", "a_hand", "b_hand", "a_secret", "b_secret", "a_board", "b_board"]

/-- The 8 `(player, action)` used-flag heap names, GENERATED player-major then action-minor
(`for p in [A,B] { for a in [Secret,Discard,Gift,Competition] }`). -/
def flagNames : List String :=
  allPlayers.flatMap (fun p => allActionKinds.map (fun k => flagName p k))

/-- The 14 per-guild placement-score heap names, GENERATED guild-major then player-minor
(`for g in 0..7 { for p in [A,B] }`). -/
def scoreNames : List String :=
  (List.finRange 7).flatMap (fun g => allPlayers.map (fun p => scoreName g p))

/-- The generation reproduces the exact wire strings the loader resolves (byte-pin). -/
theorem flagNames_literal :
    flagNames = ["flag_a_secret", "flag_a_discard", "flag_a_gift", "flag_a_comp",
                 "flag_b_secret", "flag_b_discard", "flag_b_gift", "flag_b_comp"] := by
  decide

/-- The score generation reproduces the exact wire strings the loader resolves (byte-pin). -/
theorem scoreNames_literal :
    scoreNames = ["score_0_a", "score_0_b", "score_1_a", "score_1_b", "score_2_a", "score_2_b",
                  "score_3_a", "score_3_b", "score_4_a", "score_4_b", "score_5_a", "score_5_b",
                  "score_6_a", "score_6_b"] := by
  decide

/-- The conservation constant DERIVED from the game, not a transcribed literal: the number of
favor cards in play is the deck size `∑ g, charm g` (the deck holds `charm g` copies of guild
`g`), which the model's `totalCards` counts and `conservation` proves invariant. -/
def conservationValue : Nat := ((List.finRange 7).map MultiwayTug.charm).sum

/-- The derived deck size is 21 (the `SumEquals` literal, now sourced from `charm`). -/
theorem conservationValue_eq : conservationValue = 21 := by decide

/-- The teeth shared by every non-genesis method: conservation + write-once flags + monotone
scores + the genesis-sentinel freeze (`genesis_sentinel_freeze()`). Order matches Rust
`common_teeth()` exactly (byte-identity of the loaded program). -/
def commonTeeth : List Constraint :=
  Constraint.sumEquals conservationRegs conservationValue
    :: (flagNames.map (fun n => Constraint.heapField (.named n) .writeOnce)
        ++ scoreNames.map (fun n => Constraint.heapField (.named n) .monotonic)
        ++ [Constraint.heapField .sentinel .immutable])

/-- The per-action extra tooth: strict round sequencing on `round_actions`. -/
def actionExtra : List Constraint := [Constraint.strictMonotonic "round_actions"]

/-- The win threshold constants — the SAME shared `charmWinThreshold` / `guildWinThreshold` the
model win predicate `Won` reads (`MultiwayTug.lean`). Single source: editing the threshold in the
model moves BOTH `Won` and this emitted gate. -/
abbrev winCharmThreshold : Nat := MultiwayTug.charmWinThreshold
abbrev winGuildThreshold : Nat := MultiwayTug.guildWinThreshold

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

/-- **`Won_iff_program_thresholds` (the emitted win-gate's LITERAL numbers ARE the model win
predicate).** `Won` holds IFF a score meets the LITERAL `11`/`4` the emitted win-gate JSON carries
(`winTooth_shape`: the gate is `AnyOf[¬(winner=who), FieldGte _ 11, FieldGte _ 4]`).

⚑ LARP-audit fix: this is NO LONGER the old `Iff.rfl` self-identity (`Won ↔ Won-unfolded`, which
survived any value edit because both sides read the same abbrev — the "reds on edit" claim was
FALSE). The proof now ROUTES THROUGH the pin `winGate_thresholds_match_Won`
(`winCharmThreshold = 11 ∧ winGuildThreshold = 4`); the RHS carries the FROZEN literals `11`/`4`
(what the emit actually writes) while `Won` reads the model constants `charmWinThreshold`/
`guildWinThreshold`. So the canary is now REAL: edit the model's `charmWinThreshold` (say to `12`)
and `winGate_thresholds_match_Won` REDS (`winCharmThreshold = 11` becomes `12 = 11`), taking this
theorem down with it — the emitted literal no longer certifiably matches the model threshold.

The remaining gap — that the deployed `SumEquals`/`FieldGte` COUNTERS equal `charmScore`/
`geishaScore` over the `Multiset` model — is the counter↔multiset substrate bridge, the NAMED
next step (§5 of the boundary doc). -/
theorem Won_iff_program_thresholds (s : GState) (p : Player) :
    Won s p ↔ ((11 : ℕ) ≤ charmScore s p ∨ (4 : ℕ) ≤ geishaScore s p) := by
  rw [show (11 : ℕ) = winCharmThreshold from winGate_thresholds_match_Won.1.symm,
      show (4 : ℕ) = winGuildThreshold from winGate_thresholds_match_Won.2.symm]
  exact Iff.rfl

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

/-! ## 4B. The DEPLOYED counter substrate + a NATIVE admission semantics.

The deployed cell state is `[FieldElement;16]` register slots + a heap map (`dregg_cell::CellState`).
Tug reads a small, total fragment: register counters by NAME and a present/absent heap by
`HeapKeyRef`. `Counters` is that fragment; `*.admits` is the Lean-native reading of the executor's
per-constraint check (`cell/src/program/eval.rs::evaluate_constraint_full`) for exactly the tug
subset — SumEquals (u64 sum of the new slots == value), register WriteOnce (old-zero OR unchanged),
StrictMonotonic (old < new), FieldGte (value ≤ new), the heap atoms (WriteOnce/Monotonic/Immutable/
Equals/DeltaEquals, both-present where the executor requires it), and AnyOf (some branch admits).
This is NOT the JSON emit shape — it is the DENOTATION the referee computes, so the bridge below
connects the emitted teeth to what the deployed executor actually does on a transition. -/

/-- The tug fragment of the deployed cell state: register counters by name + present/absent heap. -/
structure Counters where
  reg : String → Nat
  heap : HeapKeyRef → Option Nat

/-- The executor's reading of an `AnyOf` leaf on the post-state (`eval.rs`, the simple-constraint
branch). `negate` flips the acceptance bit (fail-closed: our subset never errors structurally). -/
def SimpleConstraint.admits : SimpleConstraint → Counters → Bool
  | .fieldEquals r v, new => decide (new.reg r = v)
  | .fieldGte r v, new    => decide (v ≤ new.reg r)
  | .negate inner, new    => ! inner.admits new

/-- The executor's reading of a heap atom on `(old, new)` heap values (`eval.rs` heap branch +
`types.rs::HeapAtom` docs): WriteOnce admits absent/zero-old else unchanged; Monotonic/DeltaEquals
require BOTH present; Immutable pins new==old; Equals pins new==value. -/
def HeapAtom.admits : HeapAtom → Option Nat → Option Nat → Bool
  | .writeOnce, old, new =>
      match old with
      | none => true
      | some o => decide (o = 0) || decide (new = some o)
  | .monotonic, old, new =>
      match old, new with
      | some o, some n => decide (o ≤ n)
      | _, _ => false
  -- ⚑ RECONCILED (game-proof LARP-audit divergence a): the DEPLOYED sound semantics is
  -- `none ⇒ admit` (the first write is free — heap keys start absent, so this is the write that
  -- ESTABLISHES the sentinel) and `some a ⇒ new = some a` (frozen thereafter). This is
  -- `Dregg2.Exec.DeployedConstraint.heapAdmits .immutable` — the ONE source `eval.rs` calls. (The
  -- old `decide (new = old)` refused the establishing write; harmless here because tug only ever
  -- hits `immutable` post-genesis with `old = some 1`, but it was the audited divergence, so it is
  -- reconciled at the copy too. The differential gate `constraint_oracle_differential` checks this
  -- agreement on the deployed evaluator.)
  | .immutable, old, new =>
      match old with
      | none => true
      | some a => decide (new = some a)
  | .equals v, _old, new => decide (new = some v)
  | .deltaEquals d, old, new =>
      match old, new with
      | some o, some n => decide ((n : Int) - (o : Int) = d)
      | _, _ => false

/-- The executor's reading of one tug constraint on `(old, new)` (`eval.rs`, the tug variants). -/
def Constraint.admits : Constraint → Counters → Counters → Bool
  | .sumEquals regs v, _old, new => decide ((regs.map new.reg).sum = v)
  | .writeOnce r, old, new       => decide (old.reg r = 0) || decide (new.reg r = old.reg r)
  | .strictMonotonic r, old, new => decide (old.reg r < new.reg r)
  | .fieldGte r v, _old, new     => decide (v ≤ new.reg r)
  | .heapField k a, old, new     => a.admits (old.heap k) (new.heap k)
  | .anyOf vs, _old, new         => vs.any (fun c => c.admits new)

/-- A case admits iff every constraint admits (implicit conjunction, `cell/src/program/eval.rs`). -/
def TransitionCase.admits (tc : TransitionCase) (old new : Counters) : Bool :=
  tc.constraints.all (fun k => k.admits old new)

/-- **The program's admission relation for method `m`** (`CellProgram::Cases` semantics): the cases
whose guard is `MethodIs m` AND together; if NONE match, default-deny. Tug has exactly one case per
method, so `matching` is a singleton. This is the deployed referee's accept predicate. -/
def CellProgram.admitsMethod : CellProgram → String → Counters → Counters → Bool
  | .cases cs, m, old, new =>
      let matching := cs.filter (fun c => c.method == m)
      !matching.isEmpty && matching.all (fun c => c.admits old new)

/-! ## 4C. The abstraction `α : GState → Counters` (register counters ARE the card cardinalities).

The counter substrate is the CARDINALITY view of the multiset game state: each register counter is
the `Multiset.card` of a card zone (the 8 conservation counters), a controlled-score, or a derived
quantity (`round_actions` = the SIZE of the used-set; `sentinel = 1` post-genesis). The heap holds
the per-`(player,action)` used-bit and the per-`(guild,player)` placement tally. This α is the
counter↔multiset bridge the boundary doc named as the missing piece. -/

open MultiwayTug (GState Player ActionKind Action geishaCount charmScore geishaScore totalCards
  applyLegal applyAction legalB Won)

/-- The used-bit of `(p,k)` as a counter (`1` if the flag is set, else `0`). -/
def usedBit (s : GState) (p : Player) (k : ActionKind) : Nat := if s.used p k then 1 else 0

/-- `round_actions` = the SIZE of the used-set (each legal action sets exactly one new flag, so
this is the strictly-increasing action stamp the deployed `StrictMonotonic` reads). -/
def usedCount (s : GState) : Nat :=
  (allPlayers.flatMap (fun p => allActionKinds.map (fun k => usedBit s p k))).sum

/-- The register-counter view of a game state: each named register is the cardinality of its card
zone / the controlled score / the derived counter. `winner`/`current`/`scored` are not card zones
in the pure model (set by the finalization method), so they read `0` here; the score-method
win-gate is bridged separately (`winTooth_admits_iff_Won`). -/
def absReg (s : GState) (name : String) : Nat :=
  if name = "deck" then (s.deck).card
  else if name = "oop" then (s.removed).card + (s.discardPile .p1).card + (s.discardPile .p2).card
  else if name = "a_hand" then (s.hand .p1).card
  else if name = "b_hand" then (s.hand .p2).card
  else if name = "a_secret" then (s.secret .p1).card
  else if name = "b_secret" then (s.secret .p2).card
  else if name = "a_board" then (s.placed .p1).card
  else if name = "b_board" then (s.placed .p2).card
  else if name = "a_charm" then charmScore s .p1
  else if name = "b_charm" then charmScore s .p2
  else if name = "a_guilds" then geishaScore s .p1
  else if name = "b_guilds" then geishaScore s .p2
  else if name = "round_actions" then usedCount s
  else 0

/-- The used-flag heap association (`(name, used-bit)`), generated like the schema's flag loop. -/
def absFlags (s : GState) : List (String × Nat) :=
  allPlayers.flatMap (fun p => allActionKinds.map (fun k => (flagName p k, usedBit s p k)))

/-- The placement-score heap association (`(name, tally)`), generated like the schema's score loop.
The tally is `geishaCount` (placed + secret — the SCORED count, the fixed reference gap). -/
def absScores (s : GState) : List (String × Nat) :=
  (List.finRange 7).flatMap (fun g => allPlayers.map (fun p => (scoreName g p, geishaCount s p g)))

/-- The heap view: the genesis sentinel is set (`some 1`, post-genesis), flags/scores by lookup. -/
def absHeap (s : GState) : HeapKeyRef → Option Nat
  | .sentinel => some 1
  | .named n => List.lookup n (absFlags s ++ absScores s)

/-- **`α` — the abstraction of a game state to the deployed counter substrate.** -/
def abstract (s : GState) : Counters := { reg := absReg s, heap := absHeap s }

/-! ### The register / heap read lemmas (α reads the right cardinality — all definitional). -/

@[simp] theorem absReg_deck (s : GState) : (abstract s).reg "deck" = (s.deck).card := rfl
@[simp] theorem absReg_oop (s : GState) :
    (abstract s).reg "oop" = (s.removed).card + (s.discardPile .p1).card + (s.discardPile .p2).card := rfl
@[simp] theorem absReg_a_hand (s : GState) : (abstract s).reg "a_hand" = (s.hand .p1).card := rfl
@[simp] theorem absReg_b_hand (s : GState) : (abstract s).reg "b_hand" = (s.hand .p2).card := rfl
@[simp] theorem absReg_a_secret (s : GState) : (abstract s).reg "a_secret" = (s.secret .p1).card := rfl
@[simp] theorem absReg_b_secret (s : GState) : (abstract s).reg "b_secret" = (s.secret .p2).card := rfl
@[simp] theorem absReg_a_board (s : GState) : (abstract s).reg "a_board" = (s.placed .p1).card := rfl
@[simp] theorem absReg_b_board (s : GState) : (abstract s).reg "b_board" = (s.placed .p2).card := rfl
@[simp] theorem absReg_round (s : GState) : (abstract s).reg "round_actions" = usedCount s := rfl
@[simp] theorem absHeap_sentinel (s : GState) : (abstract s).heap .sentinel = some 1 := rfl

/-- α reads the flag heap key correctly (finite check over players × action-kinds). -/
theorem absHeap_flag (s : GState) (p : Player) (k : ActionKind) :
    (abstract s).heap (.named (flagName p k)) = some (usedBit s p k) := by
  cases p <;> cases k <;> rfl

/-- α reads the score heap key correctly (finite check over guilds × players). -/
theorem absHeap_score (s : GState) (g : Fin 7) (p : Player) :
    (abstract s).heap (.named (scoreName g p)) = some (geishaCount s p g) := by
  cases p <;> fin_cases g <;> rfl

/-! ## 4D. The bridge lemmas (the deployed teeth ARE the model's proven facts). -/

/-- **The conservation tooth reads `totalCards`.** The `SumEquals` sum over the 8 conservation
registers at `α s` is EXACTLY `(totalCards s).card` — the deployed referee's conservation check is
the multiset conservation the model proves invariant, no re-derivation. -/
theorem conservationSum_eq (s : GState) :
    ((conservationRegs.map (abstract s).reg).sum) = (totalCards s).card := by
  simp only [conservationRegs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    absReg_deck, absReg_oop, absReg_a_hand, absReg_b_hand, absReg_a_secret, absReg_b_secret,
    absReg_a_board, absReg_b_board, totalCards, MultiwayTug.sum2, Multiset.card_add,
    Multiset.card_zero, add_zero]
  omega

/-- The post-state of a legal action, on the used-flags: only `(p, a.kind)` flips; all else held. -/
theorem used_applyLegal (o : GState) (p : Player) (a : Action) (p' : Player) (k' : ActionKind) :
    (applyLegal o p a).used p' k'
      = (if p' = p ∧ k' = a.kind then true else o.used p' k') := by
  show (Function.update o.used p (Function.update (o.used p) a.kind true)) p' k'
      = (if p' = p ∧ k' = a.kind then true else o.used p' k')
  by_cases hpp : p' = p
  · subst hpp
    rw [Function.update_self]
    by_cases hkk : k' = a.kind
    · subst hkk; rw [Function.update_self]; simp
    · rw [Function.update_of_ne hkk]; simp [hkk]
  · rw [Function.update_of_ne hpp]; simp [hpp]

/-- **Every flag write-once tooth admits a legal step.** The played flag goes `0 → 1` (admitted by
old-zero — `legal_needs_unused`); every other flag is unchanged. -/
theorem flag_writeOnce_admits (o : GState) (p : Player) (a : Action) (hleg : legalB o p a = true)
    (p' : Player) (k' : ActionKind) :
    HeapAtom.writeOnce.admits (some (usedBit o p' k')) (some (usedBit (applyLegal o p a) p' k'))
      = true := by
  simp only [HeapAtom.admits]
  by_cases hcase : p' = p ∧ k' = a.kind
  · -- played flag: old-zero (legal_needs_unused)
    obtain ⟨hp, hk⟩ := hcase
    subst hp; subst hk
    have hfalse : o.used p' a.kind = false := MultiwayTug.legal_needs_unused o p' a hleg
    simp [usedBit, hfalse]
  · -- untouched flag: unchanged
    have : (applyLegal o p a).used p' k' = o.used p' k' := by
      rw [used_applyLegal]; simp [hcase]
    simp [usedBit, this]

/-- **Every placement-score monotone tooth admits a legal step.** Scores only accrue
(`geishaCount_mono`). -/
theorem score_monotonic_admits (o : GState) (p : Player) (a : Action) (hleg : legalB o p a = true)
    (g : Fin 7) (p' : Player) :
    HeapAtom.monotonic.admits (some (geishaCount o p' g))
      (some (geishaCount (applyLegal o p a) p' g)) = true := by
  simp only [HeapAtom.admits, decide_eq_true_eq]
  have hmono := MultiwayTug.geishaCount_mono o p a p' g
  rwa [MultiwayTug.applyAction_of_legal o p a hleg] at hmono

/-- **`round_actions` strictly increases.** A legal action sets exactly one previously-unset flag,
so the used-set grows by one — the deployed `StrictMonotonic` on `round_actions`. -/
theorem usedCount_applyLegal (o : GState) (p : Player) (a : Action) (hleg : legalB o p a = true) :
    usedCount (applyLegal o p a) = usedCount o + 1 := by
  have hfalse : o.used p a.kind = false := MultiwayTug.legal_needs_unused o p a hleg
  have key : ∀ p' k', (applyLegal o p a).used p' k'
      = (if p' = p ∧ k' = a.kind then true else o.used p' k') := used_applyLegal o p a
  simp only [usedCount, allPlayers, allActionKinds, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.append_nil, List.cons_append, List.nil_append,
    List.sum_cons, List.sum_nil, usedBit, key]
  -- exactly one summand flips 0→1 (the played (p,a.kind)); the rest are held
  cases p <;> cases hk : a.kind <;>
    simp_all <;> omega

/-! ## 4E. THE FORWARD REFINEMENT — the deployed program admits every legal game move. -/

/-- The action's dispatch method name (`state.rs` method tags). -/
def methodOf : Action → String
  | .secret _ => "secret"
  | .discard _ _ => "discard"
  | .gift _ _ _ => "gift"
  | .competition _ _ _ _ => "comp"

/-- For an action method, the program's admission is exactly the shared action case's teeth. The
teeth are generalized to opaque atoms so the case filter reduces without unfolding the 23-tooth
lists (which would blow the whnf budget). -/
theorem admitsMethod_action (a : Action) (old new : Counters) :
    CellProgram.admitsMethod multiwayTugProgram (methodOf a) old new
      = (commonTeeth ++ actionExtra).all (fun k => k.admits old new) := by
  have h : multiwayTugProgram = CellProgram.cases
      [⟨"genesis", genesisTeeth⟩, ⟨"secret", commonTeeth ++ actionExtra⟩,
       ⟨"discard", commonTeeth ++ actionExtra⟩, ⟨"gift", commonTeeth ++ actionExtra⟩,
       ⟨"comp", commonTeeth ++ actionExtra⟩, ⟨"score", commonTeeth ++ scoreExtra⟩] := rfl
  rw [h]
  generalize genesisTeeth = g0
  generalize commonTeeth ++ scoreExtra = t2
  generalize commonTeeth ++ actionExtra = t
  cases a <;>
    simp [methodOf, CellProgram.admitsMethod, List.filter_cons, TransitionCase.admits, reduceBEq]

/-- **`commonAndAction_admits` — every tooth of an action case admits a legal step.** Conservation
(reads `totalCards`, held by `conservation`), the write-once flags (`flag_writeOnce_admits`), the
monotone scores (`score_monotonic_admits`), the frozen sentinel, and the strict round-sequencing
(`usedCount_applyLegal`) — each discharged against the PROVEN model invariants. -/
theorem commonAndAction_admits (o : GState) (p : Player) (a : Action)
    (hleg : legalB o p a = true) (hcons : (totalCards o).card = 21) :
    (commonTeeth ++ actionExtra).all
      (fun k => k.admits (abstract o) (abstract (applyLegal o p a))) = true := by
  have hcard : (totalCards (applyLegal o p a)).card = 21 := by
    have : totalCards (applyLegal o p a) = totalCards o := by
      rw [← MultiwayTug.applyAction_of_legal o p a hleg]; exact MultiwayTug.conservation o p a
    rw [this]; exact hcons
  rw [List.all_append]
  refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
  · -- commonTeeth
    rw [commonTeeth, List.all_cons]
    refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
    · -- conservation head
      simp only [Constraint.admits, decide_eq_true_eq, conservationSum_eq, hcard,
        conservationValue_eq]
    · -- flags ++ scores ++ [sentinel]
      rw [List.all_append, List.all_append]
      refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩, ?_⟩
      · -- flag write-once teeth
        rw [List.all_eq_true]
        intro c hc
        rw [List.mem_map] at hc
        obtain ⟨nm, hnm, rfl⟩ := hc
        rw [flagNames, List.mem_flatMap] at hnm
        obtain ⟨p', -, hnm⟩ := hnm
        rw [List.mem_map] at hnm
        obtain ⟨k', -, rfl⟩ := hnm
        simp only [Constraint.admits, absHeap_flag]
        exact flag_writeOnce_admits o p a hleg p' k'
      · -- score monotone teeth
        rw [List.all_eq_true]
        intro c hc
        rw [List.mem_map] at hc
        obtain ⟨nm, hnm, rfl⟩ := hc
        rw [scoreNames, List.mem_flatMap] at hnm
        obtain ⟨g, -, hnm⟩ := hnm
        rw [List.mem_map] at hnm
        obtain ⟨p', -, rfl⟩ := hnm
        simp only [Constraint.admits, absHeap_score]
        exact score_monotonic_admits o p a hleg g p'
      · -- sentinel frozen
        simp only [List.all_cons, List.all_nil, Constraint.admits, HeapAtom.admits,
          absHeap_sentinel, Bool.and_true, decide_eq_true_eq]
  · -- actionExtra: strict round sequencing
    simp only [actionExtra, List.all_cons, List.all_nil, Constraint.admits, absReg_round,
      Bool.and_true, decide_eq_true_eq, usedCount_applyLegal o p a hleg]
    omega

/-- **`program_admits_legal_play` (THE FORWARD REFINEMENT — legal ⇒ admitted).** The DEPLOYED
`multiwayTugProgram` ADMITS the abstraction of every legal `applyAction` play: for a legal action
`a` and a state whose card total is the deck's 21, the referee's accept predicate on
`(α o, methodOf a, α (applyLegal o p a))` is `true`. Each admitted counter effect — conservation,
one-action-per-round, monotone scores, strict sequencing — is pinned to the PROVEN model invariant,
not re-asserted. ⚑ This is FORWARD ONLY (legal ⇒ admitted); it does NOT claim the converse
(`admitted ⇒ legal`), which is impossible for the cardinality-blind counter program alone and is
`airPlay`'s membership job (`§4H`, NAMED, gated on `MerkleSound`). `§4I` re-states this conclusion
against the DEPLOYED evaluator (`program_admits_legal_play_deployed`). -/
theorem program_admits_legal_play (o : GState) (p : Player) (a : Action)
    (hleg : legalB o p a = true) (hcons : (totalCards o).card = 21) :
    CellProgram.admitsMethod multiwayTugProgram (methodOf a) (abstract o)
      (abstract (applyLegal o p a)) = true := by
  rw [admitsMethod_action]
  exact commonAndAction_admits o p a hleg hcons

/-! ## 4F. The score method's win-gate IS the model win predicate `Won` (counter-level iff). -/

/-- The counters at a scored state: registers as `α`, but `winner := who`. -/
def scoredCounters (s : GState) (who : Nat) : Counters :=
  { reg := fun nm => if nm = "winner" then who else absReg s nm, heap := absHeap s }

@[simp] theorem scoredCounters_winner (s : GState) (who : Nat) :
    (scoredCounters s who).reg "winner" = who := rfl
@[simp] theorem scoredCounters_a_charm (s : GState) (who : Nat) :
    (scoredCounters s who).reg "a_charm" = charmScore s .p1 := rfl
@[simp] theorem scoredCounters_a_guilds (s : GState) (who : Nat) :
    (scoredCounters s who).reg "a_guilds" = geishaScore s .p1 := rfl
@[simp] theorem scoredCounters_b_charm (s : GState) (who : Nat) :
    (scoredCounters s who).reg "b_charm" = charmScore s .p2 := rfl
@[simp] theorem scoredCounters_b_guilds (s : GState) (who : Nat) :
    (scoredCounters s who).reg "b_guilds" = geishaScore s .p2 := rfl

/-- **`winTooth_admits_iff_Won` (the deployed win-gate IS `Won`).** Player 1's deployed win-gate
tooth admits a scored state IFF the win claim is honest: `winner = 1 → Won s p1`. So the emitted
`AnyOf[¬(winner=1), a_charm≥11, a_guilds≥4]` refuses exactly the false win claims the proven model
`Won` forbids — the win-safety of `MultiwayTug.lean`, reaching the DEPLOYED referee. -/
theorem winTooth_admits_iff_Won_p1 (s : GState) (who : Nat) (old : Counters) :
    (winTooth 1 "a_charm" "a_guilds").admits old (scoredCounters s who) = true
      ↔ (who = 1 → Won s .p1) := by
  simp only [winTooth, Constraint.admits, SimpleConstraint.admits, List.any_cons, List.any_nil,
    scoredCounters_winner, scoredCounters_a_charm, scoredCounters_a_guilds, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Bool.false_eq_true, or_false,
    Won, MultiwayTug.charmWinThreshold, MultiwayTug.guildWinThreshold]
  tauto

/-- The symmetric player-2 win-gate iff (same argument on `b_charm`/`b_guilds`, `winner = 2`). -/
theorem winTooth_admits_iff_Won_p2 (s : GState) (who : Nat) (old : Counters) :
    (winTooth 2 "b_charm" "b_guilds").admits old (scoredCounters s who) = true
      ↔ (who = 2 → Won s .p2) := by
  simp only [winTooth, Constraint.admits, SimpleConstraint.admits, List.any_cons, List.any_nil,
    scoredCounters_winner, scoredCounters_b_charm, scoredCounters_b_guilds, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Bool.false_eq_true, or_false,
    Won, MultiwayTug.charmWinThreshold, MultiwayTug.guildWinThreshold]
  tauto

/-! ## 4G. The genesis one-shot (the Lean twin of the deployed genesis-restaple canary). -/

/-- A minimal counter state with only the genesis sentinel set to `v`. -/
def sentinelCounters (v : Nat) : Counters :=
  { reg := fun _ => 0, heap := fun k => match k with | .sentinel => some v | .named _ => none }

/-- **`genesis_admits_first` (the seeding transition IS admitted).** The genesis case admits the
sentinel `0 → 1` transition (`Equals{1} ∧ DeltaEquals{1}`) — the one-shot seed commits once. -/
theorem genesis_admits_first :
    CellProgram.admitsMethod multiwayTugProgram "genesis"
      (sentinelCounters 0) (sentinelCounters 1) = true := by
  decide

/-- **`genesis_restaple_refused` (the one-shot canary, in Lean).** A SECOND genesis (`old = 1`) is
REFUSED: the injected `→ 1` write gives `Δ = 0 ≠ 1`, so `DeltaEquals{1}` fails and the case rejects
— exactly the `genesis_restaple_is_refused_one_shot` runtime test, at the program's denotation. -/
theorem genesis_restaple_refused :
    CellProgram.admitsMethod multiwayTugProgram "genesis"
      (sentinelCounters 1) (sentinelCounters 1) = false := by
  decide

/-! ## 4H. Composition with the membership leaf — the two referees agree on legal plays.

The counter program is CARDINALITY-blind to WHICH card moved (many `GState`s share an `α`); that
identity is pinned by the membership leaf `airPlay` (`MultiwayTugAir.lean`, PROVEN). The two
referees agree on every legal play: the leaf that `airPlay` admits, the counter program admits too,
and together they refine `applyAction` — `airPlay` fixes the card, `multiwayTugProgram` fixes the
conservation/flags/scores/sequencing. This is why the deployed design is TWO layers, not one. -/

/-- **`play_admitted_by_both` (the composition).** Every membership-proven legal play the fold leaf
`airPlay` admits is ALSO admitted by the deployed counter program, and its successor is the model
`applyAction` step. The card identity comes from `airPlay`; the counter effects from
`multiwayTugProgram`. -/
theorem play_admitted_by_both (M : MultiwayTug.MerkleScheme) (hsound : MultiwayTug.MerkleSound M)
    (o : GState) (p : Player) (a : Action) (n : GState)
    (hair : MultiwayTug.airPlay M o p a n) (hcons : (totalCards o).card = 21) :
    n = applyAction o p a ∧
      CellProgram.admitsMethod multiwayTugProgram (methodOf a) (abstract o) (abstract n) = true := by
  obtain ⟨hleg, _hmem, hstep⟩ := (MultiwayTug.airPlay_iff_applyAction M hsound o p a n).mp hair
  refine ⟨hstep, ?_⟩
  have hlegal : n = applyLegal o p a := by
    rw [hstep, MultiwayTug.applyAction_of_legal o p a hleg]
  rw [hlegal]
  exact program_admits_legal_play o p a hleg hcons

/-! ## 4I. THE REFINEMENT ONTO THE DEPLOYED EVALUATOR (`Dregg2.Exec.DeployedConstraint`).

The `Constraint.admits` copy above is the tug-SYMBOLIC (String-keyed counter) reading of the
referee. This section closes the counter↔register seam the LARP-audit named: it MARSHALS a tug
`Counters` fragment into the DEPLOYED substrate (`[FieldElement;16]` register list + one resolved
heap value, UNSIGNED 256-bit `Nat`) and PROVES the local admission verdict agrees with
`Dregg2.Exec.DeployedConstraint.admits` — the `@[export dregg_constraint_admits]` evaluator the
deployed node routes through — on the tug action-teeth subset. The forward refinement
`program_admits_legal_play` then lands ON the deployed evaluator as `program_admits_legal_play_deployed`.

SCOPE (honest): the DEPLOYED PURE subset covers `sumEquals`/`writeOnce`/`strictMonotonic`/`fieldGte`
/`heapField`-atoms — every action-case tooth. The score case's `anyOf` win-teeth are RECURSIVE and
stay Rust-evaluated (NOT in the exported pure subset) — the named non-pure boundary; the win-gate's
soundness reaches the referee via `winTooth_admits_iff_Won` at the SYMBOLIC layer (`§4F`). This is
the FORWARD direction (legal ⇒ admitted); the reverse (admitted ⇒ legal) is `airPlay`'s membership
job (NAMED, `§4H`), not claimed here. -/
section DeployedRefinement
open Dregg2.Exec.DeployedConstraint

/-- Register allocation: tug's ≤14 register names → distinct deployed slot indices `0..13`
(the two spare slots `14,15` are unused by tug's teeth). -/
def tugRegIdx : String → Nat
  | "deck" => 0 | "oop" => 1 | "a_hand" => 2 | "b_hand" => 3
  | "a_secret" => 4 | "b_secret" => 5 | "a_board" => 6 | "b_board" => 7
  | "round_actions" => 8 | "winner" => 9
  | "a_charm" => 10 | "b_charm" => 11 | "a_guilds" => 12 | "b_guilds" => 13
  | _ => 15

/-- Marshal the tug counter fragment into the deployed 16-slot register list (`newRegs`/`oldRegs`),
each slot at its `tugRegIdx`. -/
def tugSlots (c : Counters) : List DField :=
  [ c.reg "deck", c.reg "oop", c.reg "a_hand", c.reg "b_hand",
    c.reg "a_secret", c.reg "b_secret", c.reg "a_board", c.reg "b_board",
    c.reg "round_actions", c.reg "winner",
    c.reg "a_charm", c.reg "b_charm", c.reg "a_guilds", c.reg "b_guilds", 0, 0 ]

/-- Tug's heap-atom subset embeds into the deployed heap-atom vocabulary (`DHeapAtom`). -/
def HeapAtom.toDHeap : HeapAtom → DHeapAtom
  | .writeOnce => .writeOnce
  | .monotonic => .monotonic
  | .immutable => .immutable
  | .equals v => .equals v
  | .deltaEquals d => .deltaEquals d

/-! ### Heap-atom agreement (verdict level, over arbitrary `Option` heap values — no marshalling).
The local `HeapAtom.admits` (Bool `true`) implies the deployed `heapAdmits` verdict `.ok`. These
hold UNCONDITIONALLY (the tug reconciliation of divergence (a) already matches the deployed
`immutable` semantics; `writeOnce`/`monotonic`/`immutable` involve no field-lane arithmetic). -/

theorem heapAdmits_writeOnce_ok {o n : Option Nat}
    (h : HeapAtom.writeOnce.admits o n = true) :
    heapAdmits DHeapAtom.writeOnce o n = DAdmit.ok := by
  cases o with
  | none => rfl
  | some a =>
    simp only [HeapAtom.admits, Bool.or_eq_true, decide_eq_true_eq] at h
    simp only [heapAdmits]
    rcases h with h0 | hn
    · simp [h0]
    · by_cases ha : a = 0
      · simp [ha]
      · simp [ha, hn]

theorem heapAdmits_monotonic_ok {o n : Option Nat}
    (h : HeapAtom.monotonic.admits o n = true) :
    heapAdmits DHeapAtom.monotonic o n = DAdmit.ok := by
  cases o with
  | none => simp [HeapAtom.admits] at h
  | some a =>
    cases n with
    | none => simp [HeapAtom.admits] at h
    | some b =>
      simp only [HeapAtom.admits, decide_eq_true_eq] at h
      simp [heapAdmits, h]

theorem heapAdmits_immutable_ok {o n : Option Nat}
    (h : HeapAtom.immutable.admits o n = true) :
    heapAdmits DHeapAtom.immutable o n = DAdmit.ok := by
  cases o with
  | none => rfl
  | some a =>
    simp only [HeapAtom.admits, decide_eq_true_eq] at h
    simp [heapAdmits, h]

/-! ### The deployed `sumEqualsAdmit` forward lemma (small nonneg terms, no u64-overflow ⇒ `.ok`). -/

/-- The accumulator invariant for `sumEqualsAdmit.go`: if every index is in range and the running
total (low-64 lanes) stays under `2^64` and lands on `low64 v`, the deployed sum-check admits. -/
theorem sumGo_ok (v : DField) (regs : List DField) :
    ∀ (l : List Nat) (acc : Nat),
      (∀ i ∈ l, i < stateSlots) →
      (acc + (l.map (fun i => low64 (regs.getD i 0))).sum < two64) →
      (acc + (l.map (fun i => low64 (regs.getD i 0))).sum = low64 v) →
      sumEqualsAdmit.go v regs l acc = DAdmit.ok := by
  intro l
  induction l with
  | nil =>
    intro acc _ _ hgoal
    simp only [List.map_nil, List.sum_nil, add_zero] at hgoal
    unfold sumEqualsAdmit.go
    rw [if_pos hgoal]
  | cons i rest ih =>
    intro acc hidx hbound hgoal
    have hi : i < stateSlots := hidx i (by simp)
    simp only [List.map_cons, List.sum_cons] at hbound hgoal
    unfold sumEqualsAdmit.go
    rw [if_neg (by omega : ¬ i ≥ stateSlots)]
    simp only
    rw [if_neg (by omega : ¬ acc + low64 (regs.getD i 0) ≥ two64)]
    apply ih (acc + low64 (regs.getD i 0))
    · intro j hj; exact hidx j (by simp [hj])
    · omega
    · omega

/-- The marshalled deployed input for one tug tooth on a `(old,new)` counter transition (registers
via `tugSlots`, the resolved heap value for a `heapField` tooth's key; `oldPresent` — tug states
are present). -/
def mkDInput (old new : Counters) : Constraint → DInput
  | .heapField k _ =>
      { oldPresent := true, newNonce := 0, oldRegs := tugSlots old, newRegs := tugSlots new,
        heapOld := old.heap k, heapNew := new.heap k }
  | _ =>
      { oldPresent := true, newNonce := 0, oldRegs := tugSlots old, newRegs := tugSlots new,
        heapOld := none, heapNew := none }

/-- The deployed constraint for one tug tooth (the PURE subset; `anyOf` — the named non-pure
boundary — maps to an unused placeholder, never hit by the pure-subset teeth this section proves). -/
def Constraint.toDC : Constraint → DConstraint
  | .sumEquals regs v => .sumEquals (regs.map tugRegIdx) v
  | .writeOnce r => .writeOnce (tugRegIdx r)
  | .strictMonotonic r => .strictMonotonic (tugRegIdx r)
  | .fieldGte r v => .fieldGte (tugRegIdx r) v
  | .heapField _ atom => .heapField atom.toDHeap
  | .anyOf _ => .fieldEquals 15 0

/-- The conservation-tooth forward bridge: with the eight zones summing to 21, the deployed
`SumEquals` evaluator admits (`.ok`). Per-term smallness follows from the sum (each zone ≤ 21 <
`2^64`, so the low-64 lane is the identity and no `checked_add` overflow trips). -/
theorem sumEquals_conservation_deployed (new : Counters)
    (hsum : (conservationRegs.map new.reg).sum = 21) :
    admits (.sumEquals (conservationRegs.map tugRegIdx) 21)
        { oldPresent := true, newNonce := 0, oldRegs := tugSlots new, newRegs := tugSlots new,
          heapOld := none, heapNew := none } = DAdmit.ok := by
  have hidxs : conservationRegs.map tugRegIdx = [0,1,2,3,4,5,6,7] := by decide
  simp only [conservationRegs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at hsum
  have h64 : (21 : Nat) < two64 := by decide
  have small : ∀ x : Nat, x ≤ 21 → low64 x = x := fun x hx => Nat.mod_eq_of_lt (by omega)
  have hmap : ([0,1,2,3,4,5,6,7].map (fun i => low64 ((tugSlots new).getD i 0))).sum = 21 := by
    show low64 ((tugSlots new).getD 0 0) + (low64 ((tugSlots new).getD 1 0)
      + (low64 ((tugSlots new).getD 2 0) + (low64 ((tugSlots new).getD 3 0)
      + (low64 ((tugSlots new).getD 4 0) + (low64 ((tugSlots new).getD 5 0)
      + (low64 ((tugSlots new).getD 6 0) + (low64 ((tugSlots new).getD 7 0) + 0))))))) = 21
    show low64 (new.reg "deck") + (low64 (new.reg "oop") + (low64 (new.reg "a_hand")
      + (low64 (new.reg "b_hand") + (low64 (new.reg "a_secret") + (low64 (new.reg "b_secret")
      + (low64 (new.reg "a_board") + (low64 (new.reg "b_board") + 0))))))) = 21
    rw [small _ (by omega), small _ (by omega), small _ (by omega), small _ (by omega),
        small _ (by omega), small _ (by omega), small _ (by omega), small _ (by omega)]
    omega
  simp only [admits, hidxs, sumEqualsAdmit]
  apply sumGo_ok
  · decide
  · rw [Nat.zero_add, hmap]; exact h64
  · rw [Nat.zero_add, hmap, low64]; decide

/-- **`program_admits_legal_play_deployed` — the FORWARD refinement lands on the DEPLOYED
evaluator.** For a legal action play, EVERY tooth of the deployed action case evaluates to
`Dregg2.Exec.DeployedConstraint.admits`'s `.ok` verdict on the marshalled register/heap input —
i.e. the `@[export dregg_constraint_admits]` evaluator the deployed node routes through ADMITS
each action-case constraint of the abstraction transition. This is `program_admits_legal_play`
(`§4E`) with its conclusion RE-STATED against the deployed evaluator via the counter↔register
marshalling. (`anyOf` win-teeth are the named non-pure boundary — recursive, Rust-evaluated — and
appear only in the score case, not in the action case; FORWARD only, the reverse is `airPlay`.) -/
theorem program_admits_legal_play_deployed (o : GState) (p : Player) (a : Action)
    (hleg : legalB o p a = true) (hcons : (totalCards o).card = 21) :
    ∀ c ∈ (commonTeeth ++ actionExtra),
      admits (Constraint.toDC c)
        (mkDInput (abstract o) (abstract (applyLegal o p a)) c) = DAdmit.ok := by
  have hcard : (totalCards (applyLegal o p a)).card = 21 := by
    have : totalCards (applyLegal o p a) = totalCards o := by
      rw [← MultiwayTug.applyAction_of_legal o p a hleg]; exact MultiwayTug.conservation o p a
    rw [this]; exact hcons
  intro c hc
  rw [commonTeeth, actionExtra] at hc
  simp only [List.cons_append, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | (((hflag | hscore) | rfl) | rfl)
  · -- conservation head
    have hsum : (conservationRegs.map (abstract (applyLegal o p a)).reg).sum = 21 := by
      rw [conservationSum_eq]; exact hcard
    show admits (Constraint.toDC (Constraint.sumEquals conservationRegs conservationValue)) _ = _
    rw [conservationValue_eq]
    exact sumEquals_conservation_deployed _ hsum
  · -- flag write-once teeth
    rw [List.mem_map] at hflag
    obtain ⟨nm, hnm, rfl⟩ := hflag
    rw [flagNames, List.mem_flatMap] at hnm
    obtain ⟨p', -, hnm⟩ := hnm
    rw [List.mem_map] at hnm
    obtain ⟨k', -, rfl⟩ := hnm
    simp only [Constraint.toDC, HeapAtom.toDHeap, mkDInput, admits, absHeap_flag]
    exact heapAdmits_writeOnce_ok (flag_writeOnce_admits o p a hleg p' k')
  · -- score monotone teeth
    rw [List.mem_map] at hscore
    obtain ⟨nm, hnm, rfl⟩ := hscore
    rw [scoreNames, List.mem_flatMap] at hnm
    obtain ⟨g, -, hnm⟩ := hnm
    rw [List.mem_map] at hnm
    obtain ⟨p', -, rfl⟩ := hnm
    simp only [Constraint.toDC, HeapAtom.toDHeap, mkDInput, admits, absHeap_score]
    exact heapAdmits_monotonic_ok (score_monotonic_admits o p a hleg g p')
  · -- sentinel frozen
    simp [Constraint.toDC, HeapAtom.toDHeap, mkDInput, admits, absHeap_sentinel, heapAdmits]
  · -- round_actions strict sequencing
    have hlt : (abstract o).reg "round_actions"
        < (abstract (applyLegal o p a)).reg "round_actions" := by
      rw [absReg_round, absReg_round, usedCount_applyLegal o p a hleg]; omega
    show (if (abstract o).reg "round_actions" < (abstract (applyLegal o p a)).reg "round_actions"
      then DAdmit.ok else DAdmit.violated) = DAdmit.ok
    rw [if_pos hlt]

end DeployedRefinement

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
-- The un-mirror (generated names / derived value) and the closed refinement, all kernel-clean.
#assert_axioms flagNames_literal
#assert_axioms scoreNames_literal
#assert_axioms conservationValue_eq
#assert_axioms conservationSum_eq
#assert_axioms used_applyLegal
#assert_axioms flag_writeOnce_admits
#assert_axioms score_monotonic_admits
#assert_axioms usedCount_applyLegal
#assert_axioms absHeap_flag
#assert_axioms absHeap_score
#assert_axioms admitsMethod_action
#assert_axioms commonAndAction_admits
#assert_axioms program_admits_legal_play
#assert_axioms winTooth_admits_iff_Won_p1
#assert_axioms winTooth_admits_iff_Won_p2
#assert_axioms genesis_admits_first
#assert_axioms genesis_restaple_refused
#assert_axioms play_admitted_by_both
-- §4I: the refinement onto the DEPLOYED evaluator (`Dregg2.Exec.DeployedConstraint`).
#assert_axioms heapAdmits_writeOnce_ok
#assert_axioms heapAdmits_monotonic_ok
#assert_axioms heapAdmits_immutable_ok
#assert_axioms sumGo_ok
#assert_axioms sumEquals_conservation_deployed
#assert_axioms program_admits_legal_play_deployed

end Dregg2.Games.MultiwayTug.Prog
