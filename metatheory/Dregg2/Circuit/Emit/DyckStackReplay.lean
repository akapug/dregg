/-
# Dregg2.Circuit.Emit.DyckStackReplay — SLICE 4 of *parse as derivation*: the CAPSTONE that
closes the SAT⇒Replay loop.

`docs/DESIGN-parse-as-derivation.md` §3/§5.1 names the hard part deferred through slices 1–3: the
whole-descriptor bridge

    parse_sat_imp_replay :
      Satisfied2 dyckDesc … t  →  ReplayAccepts dyck (rulesOf t) (inputOf t)

— "a satisfying trace IS an accepting leftmost pushdown replay of the Dyck grammar." §3 calls this a
"genuine transition-relation induction across all active rows, with the STACK as the inductive
invariant" and flags it as the multi-month-*risk* item.

## What slice 3 already landed (verified at HEAD, `DyckStackRefine.lean`)

Two proven halves stand there, joined by ONE honestly-named residual (its §7):

* **(§4.1) the per-row bridge** `dyck_sat_imp_row_valid` — a trace `Satisfied2 dyckDesc`, canonical
  (`DyckCanon`), witnesses the genuine per-row relation `DyckRowValid` on EVERY transition row.
* **(§6) the multi-row assembly** `mrun_imp_replay` — a FORWARD `MRun` of per-row-valid steps ending
  in an accepting `done` IS a backward `CfgCompact.Replay`, with the rule sequence RECONSTRUCTED by
  `rulesOf` and the stack threaded as the induction invariant. This is the design's named hard part,
  and it is proven, not assumed.
* **(§7) the seam between them** — the DECODE GLUE: a function `decode : VmTrace → List MRow` reading
  each row's `STACK[0..D−1]` + `STACK_DEPTH` back into a `List (Symbol Brk NTs)`, its `Act` from the
  selectors, its remaining input from `INPUT_POS`; plus the per-row lemma `DyckRowValid (envAt t i) →
  MStep (decode t)[i] (decode t)[i+1]`. Its general form needs the **depth↔occupancy invariant**
  `dyck_stack.rs` still owes ("nothing yet ties `STACK_DEPTH` to which cells are nonzero").

## What THIS file (slice 4) adds

1. **`replay_of_run_initial`** (§1) — the stack-invariant fold's payoff stated at the `ReplayAccepts`
   level: an `MRun` whose head stack is the grammar's initial nonterminal IS an accepting replay.
   This is `mrun_imp_replay` lifted to the acceptance predicate; it is the "assemble per-row validity
   into a whole pushdown replay" of the prompt, PROVEN.
2. **The decode (§2)** — `symOfId` / `decodeStack` / `decodeAct` / `decodeRow` / `decodeRun`: the §7
   decode function, written concretely. It reads the same `STACK[i]` / `STACK_DEPTH` / selector /
   `INPUT_POS` columns the per-row teeth constrain.
3. **`decode_witTrace`** (§3) — the §7 decode seam CLOSED for the shipped bracket-pair trace: the
   satisfying `witTrace` (proven `Satisfied2` in slice 3, `DyckStackRefine.witTrace_satisfies`)
   decodes to the accepting forward run `bRow0 :: bracketsRest`. For this concrete trace the
   depth↔occupancy invariant holds by COMPUTATION, so the seam needs no circuit tooth here.
4. **`witTrace_replays`** (§3) — the concrete `parse_sat_imp_replay`: the decoded run assembles,
   through `mrun_imp_replay`, into `ReplayAccepts dyck [rBracket, rEmpty] [op, cl]` — EXACTLY the
   statement of the hand proof `CfgCompact.Reference.brackets_replays`, reached here from the actual
   circuit trace via decode.
5. **`witTrace_steps_valid`** (§3) — the satisfaction is load-bearing: the circuit's acceptance of
   `witTrace` CERTIFIES (via the per-row bridge) that every decoded transition row is a genuine
   pushdown step. Acceptance ⇒ valid steps; decode ⇒ the run; the two compose into the replay.
6. **`witTrace_in_language`** (§3) — the consistency check the prompt asks for: `compact_sound` on the
   produced `ReplayAccepts` recovers `[op, cl] ∈ dyck.language`.
7. **`witTrace_satisfies_and_replays`** (§4) — the closed loop for the shipped word, stated as the
   honest conjunction: the concrete trace is BOTH accepted by the circuit AND decodes to an accepting
   grammar replay.

## SCOPE (honest, per the iterative method)

**Concrete-witnesses, not fully general.** The general length-induction `parse_sat_imp_replay` (all
satisfying traces, arbitrary length) is STATED as the §5 residual with its exact invariant and its
exact missing tooth — NOT proven, NOT `sorry`ed, NOT faked. What is proven here is the loop closed
for the shipped bracket-pair witness (`witTrace`, the `"[]"` parse `build_brackets_witness` lays),
plus the general RUN⇒REPLAY reduction (`replay_of_run_initial`, fully general in the length of the
run). The only thing standing between the concrete case and the general theorem is the general decode
glue — the §7 residual, which needs the depth↔occupancy circuit tooth, not more proof cleverness.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only; not
reachable from `Dregg2.lean`. Verified with `lake env lean` on this file.
-/
import Dregg2.Circuit.Emit.DyckStackRefine
import Dregg2.Crypto.CfgCompact
import Dregg2.Tactics

namespace Dregg2.Circuit.Emit.DyckStackReplay

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.DyckStackRefine
open Dregg2.Crypto.Cfg.Reference (Brk NTs dyck rBracket rEmpty)
open Dregg2.Crypto.Cfg.Reference.Brk (op cl)
open Dregg2.Crypto.CfgCompact (Replay ReplayAccepts)

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## §1 — THE ASSEMBLY, at the acceptance predicate: an `MRun` from the initial stack IS an
accepting replay.

`mrun_imp_replay` (slice 3, §6) is the transition-relation induction with the stack as invariant:
it turns a forward `MRun a rest` into `Replay dyck (rulesOf (a :: rest)) a.inp a.stk`. Here we pin the
head stack to the grammar's initial nonterminal, which is exactly the initial stack `ReplayAccepts`
opens on — so the run becomes an ACCEPTING replay. This is the "fold per-row validity forward,
maintaining `Replay g rs_so_far input_remaining stack_of_row` as the invariant" step, delivered. It is
general in the run length: no concreteness is used. -/
theorem replay_of_run_initial {a : MRow} {rest : List MRow}
    (hrun : MRun a rest) (hinit : a.stk = [Symbol.nonterminal dyck.initial]) :
    ReplayAccepts dyck (rulesOf (a :: rest)) a.inp := by
  have h := mrun_imp_replay hrun
  rw [hinit] at h
  exact h

/-! ## §2 — THE DECODE (the §7 seam, written concretely).

`decode` reads a trace row back into the `MRow` the abstract machine carries: the stack cells
`STACK[0..STACK_DEPTH)` under the symbol-id map, the action from the selectors + `RULE_ID`, and the
remaining input as the suffix of the word from `INPUT_POS`. These are the SAME columns
`DyckRowValid`'s per-action teeth constrain (`ruleTopIsS`, `bracketPush`, `termTopIsToken`,
`termAdvances`, …). -/

/-- The symbol-id map (`dyck_stack.rs`'s `SYM_*`): `1 ↦ S`, `2 ↦ op`, `3 ↦ cl`, everything else
(the `0 = EMPTY` marker, out-of-range) is absent. -/
def symOfId (z : ℤ) : Option (Symbol Brk NTs) :=
  if z = SYM_S then some (Symbol.nonterminal NTs.S)
  else if z = SYM_OP then some (Symbol.terminal op)
  else if z = SYM_CL then some (Symbol.terminal cl)
  else none

/-- Read the working stack: the first `STACK_DEPTH` cells (top at index `0`), symbol-decoded. The
`EMPTY` marker maps to nothing, so a well-formed occupancy yields exactly the live prefix. -/
def decodeStack (a : Assignment) : List (Symbol Brk NTs) :=
  (List.range (a STACK_DEPTH).toNat).filterMap (fun i => symOfId (a (stk i)))

/-- Read the action from the selectors + `RULE_ID` + `INPUT_TOKEN` (`dyck_stack.rs::Action`). -/
def decodeAct (a : Assignment) : Act :=
  if a IS_RULE = 1 then
    (if a RULE_ID = RULE_BRACKET then Act.rule rBracket else Act.rule rEmpty)
  else if a IS_TERM = 1 then
    (if a INPUT_TOKEN = SYM_OP then Act.term op else Act.term cl)
  else Act.done

/-- Decode one row against the input `word`: the remaining input is `word` dropped by `INPUT_POS`. -/
def decodeRow (word : List Brk) (a : Assignment) : MRow :=
  ⟨decodeAct a, decodeStack a, word.drop (a INPUT_POS).toNat⟩

/-- Decode the first `n` rows of a trace into a forward run. (The general `decode` truncates at the
first `done`; the concrete run length is supplied here — the truncation lemma is part of the §5
residual, not needed for the shipped fixed-length witness.) -/
def decodeRun (word : List Brk) (t : VmTrace) (n : Nat) : List MRow :=
  (List.range n).map (fun i => decodeRow word (t.rows.getD i zeroAsg))

/-! ## §3 — THE LOOP CLOSED FOR THE SHIPPED WORD.

`witTrace` (slice 3, §5) is the honest `"[]"` parse `build_brackets_witness` lays, PROVEN in the
deployed accept-set by `DyckStackRefine.witTrace_satisfies`. Its 8 rows are `rule rBracket · term
'[' · rule rEmpty · term ']' · done`, padded with `done` self-loops; the run is the first 5. -/

/-- **`decode_witTrace` — the §7 decode seam, CLOSED for the concrete trace.** The satisfying
`witTrace` decodes (STACK cells + depth + selectors + `INPUT_POS`, read directly) to the accepting
forward run `bRow0 :: bracketsRest` — the SAME abstract machine slice 3's `abs_brackets_accepts`
hand-built, now recovered FROM the circuit trace's columns. For this fixed trace the depth↔occupancy
invariant the general seam needs holds by computation, so no circuit tooth is required here. -/
theorem decode_witTrace : decodeRun [op, cl] witTrace 5 = bRow0 :: bracketsRest := by
  rfl

/-- **`witTrace_replays` — the concrete `parse_sat_imp_replay`.** The decoded run assembles, through
the stack-invariant fold `mrun_imp_replay` (via `replay_of_run_initial`), into an accepting Dyck
replay whose reconstructed certificate is `[rBracket, rEmpty]` and whose word is `[op, cl]` — EXACTLY
`CfgCompact.Reference.brackets_replays`'s statement, reached here from the actual circuit trace. -/
theorem witTrace_replays :
    ReplayAccepts dyck (rulesOf (decodeRun [op, cl] witTrace 5)) [op, cl] := by
  rw [decode_witTrace]
  exact replay_of_run_initial bracketsRows_run rfl

/-- **`witTrace_steps_valid` — the satisfaction is load-bearing.** The circuit's ACCEPTANCE of
`witTrace` certifies, through the slice-3 per-row bridge `dyck_sat_imp_row_valid`, that every one of
the four transition rows the run decodes is a genuine pushdown step (`DyckRowValid`). Acceptance ⇒
valid steps (this lemma) and acceptance's trace decodes to the run (`decode_witTrace`); the two
compose into `witTrace_replays`. Nothing here rests on a vacuous hypothesis: `witTrace_satisfies`
inhabits the `Satisfied2` antecedent. -/
theorem witTrace_steps_valid (i : Nat) (hi : i + 1 < 5) : DyckRowValid (envAt witTrace i) :=
  dyck_sat_imp_row_valid witTrace_satisfies witTrace_canon i (by
    have h : witTrace.rows.length = 8 := rfl
    omega)

/-- **`witTrace_in_language` — the consistency check.** `compact_sound` on the produced
`ReplayAccepts` recovers language membership: the parse certificate the circuit trace decodes to
proves `[op, cl] ∈ dyck.language`, the SAME fact slice 3 reaches by hand. -/
theorem witTrace_in_language : [op, cl] ∈ dyck.language :=
  Dregg2.Crypto.CfgCompact.compact_sound dyck
    (rulesOf (decodeRun [op, cl] witTrace 5)) [op, cl] witTrace_replays

/-! ## §4 — THE CLOSED LOOP, stated honestly.

The concrete capstone is the CONJUNCTION: the shipped trace is BOTH accepted by the deployed circuit
predicate AND decodes to an accepting grammar replay. This is "a satisfying trace IS an accepting
leftmost pushdown replay" — for the shipped word, with the satisfaction genuinely established
(`witTrace_satisfies`), not assumed. -/

/-- **THE CAPSTONE (concrete):** `witTrace` satisfies the deployed Dyck descriptor AND decodes to an
accepting Dyck replay. The SAT⇒Replay loop `docs/DESIGN-parse-as-derivation.md` §3 names, closed for
the bracket-pair witness. -/
theorem witTrace_satisfies_and_replays :
    Satisfied2 (fun _ => (0 : ℤ)) dyckDesc (fun _ => 0) (fun _ => (0, 0)) [] witTrace
      ∧ ReplayAccepts dyck (rulesOf (decodeRun [op, cl] witTrace 5)) [op, cl] :=
  ⟨witTrace_satisfies, witTrace_replays⟩

/-! ## §5 — THE GENERAL RESIDUAL (stated precisely, NOT proven, NOT `sorry`ed).

The fully-general bridge is:

    theorem parse_sat_imp_replay
        {hash minit mfin maddrs} {t : VmTrace} {word : List Brk} {n : Nat}
        (hsat   : Satisfied2 hash dyckDesc minit mfin maddrs t)
        (hcanon : DyckCanon t)
        (hword  : «the input columns of t spell `word`»)
        (hlen   : «row n is the first `done`; rows 0..n are the live run») :
      ReplayAccepts dyck (rulesOf (decodeRun word t (n + 1))) word

The PROOF SKELETON is already assembled — only ONE arrow is missing:

  * (§1 here)              `replay_of_run_initial`  : MRun a rest → a.stk = [initial] → ReplayAccepts
                            — PROVEN, general in run length.
  * (slice 3 §4.1)         `dyck_sat_imp_row_valid` : Satisfied2 → ∀ transition row, DyckRowValid
                            — PROVEN.
  * (slice 3 §6)           `mrun_imp_replay`        : MRun → Replay (folded under `replay_of_run_initial`)
                            — PROVEN.

  * (THE RESIDUAL)         `decode_step` :
        DyckRowValid (envAt t i) → i < n → MStep (decodeRow word (t.rows.getD i _))
                                                 (decodeRow word (t.rows.getD (i+1) _))
      plus `MFinal (decodeRow word (t.rows.getD n _))` from the `done` boundary, assembled into
      `MRun (decodeRow word row₀) (decodeRun word t n |>.tail)` — the general form of `decode_witTrace`.

**The exact invariant** is the one `mrun_imp_replay` already carries: *the decoded stack of row `i`
equals the `Replay` working stack after the first `i` steps.* Threading it forward across `decode_step`
is the whole general induction; it is discharged HERE for the concrete `witTrace` by
`decode_witTrace` + `bracketsRows_run`.

**The exact missing tooth** is the DEPTH↔OCCUPANCY invariant: `decode_step` needs `STACK_DEPTH` to
count exactly the non-`EMPTY` prefix of the `STACK[·]` cells, so that the per-row shift equations
(`bracketPush`, `emptyPop`, `termPop`) compose into `b.stk = r.output ++ rest`. `dyck_stack.rs` states
plainly this does not exist yet ("nothing yet ties `STACK_DEPTH` to which cells are nonzero; the
boundaries and per-action deltas pin the endpoints, not every intermediate cell"). So the honest
ordering — unchanged from slice 3's §7 — is: land the depth↔occupancy constraint in the CIRCUIT
first (a real missing tooth, not a proof inconvenience), then `decode_step` closes the general
`parse_sat_imp_replay` by composing the four PROVEN facts above. Until then, the loop is closed for
the shipped witness (§3/§4) and the general theorem is this named residual. -/

/-! ## §6 — Non-vacuity guards + axiom hygiene. -/

-- The decoded run has all five rows (nothing collapsed).
#guard (decodeRun [op, cl] witTrace 5).length = 5
-- The reconstructed compact certificate has exactly two rules (`rBracket`, `rEmpty`) — the
-- O(tokens) wire form, non-empty, recovered from the circuit trace.
#guard (rulesOf (decodeRun [op, cl] witTrace 5)).length = 2
-- The decoded word is the length-2 bracket pair — the replay is not over the empty input.
#guard (decodeRow [op, cl] witTrace.rows.head!).inp.length = 2

#assert_axioms replay_of_run_initial
#assert_axioms decode_witTrace
#assert_axioms witTrace_replays
#assert_axioms witTrace_steps_valid
#assert_axioms witTrace_in_language
#assert_axioms witTrace_satisfies_and_replays

end Dregg2.Circuit.Emit.DyckStackReplay
