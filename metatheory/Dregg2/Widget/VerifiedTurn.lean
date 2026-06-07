/-
# Dregg2.Widget.VerifiedTurn — the EXECUTE → PROVE → VERIFY path, with the ANTI-GHOST tooth, visualized.

The other leaf widgets each render one facet of a real value: `DreggForest` the call-tree, `CapabilityGraph`
the Granovetter slot-table, `ConservationLedger` the per-asset books. This widget renders the *verifiable-
execution pipeline itself* — the beachhead `Dregg2/Circuit/TransferWitness.lean` closes — as one inspector
panel, so the explorer can SHOW "this turn was executed, a satisfying witness was generated, the circuit
verifies it, and a forged variant is rejected" with every number read off the real Lean derivation.

THE THREE STAGES, each a REAL computation (no placeholder, no hand-typed digest):

  ① EXECUTE.  `transferWitnessVec kS0 goodTurnS` RUNS the record-kernel executor `recKExec` on the concrete
     reference triple (actor 0 transfers 30 of asset 0, cell 0 → cell 1; cell 2 is a live bystander) and lays
     the post-state out as the flat 20-wire satisfying assignment. This is `honestWitness` — the EXACT bytes
     the Rust `lean_executor_derived_transfer` test feeds the real Plonky3 prover. We render all 20 wires with
     their genuine meanings (`vSrcPre`…`vMovedDigExpected`) from `Transfer.lean`/`StateCommit.lean`.

  ② PROVE/VERIFY.  `satisfiedC (encodeSC kS0 goodTurnS goodPostS)` DECIDES whether the executor-derived witness
     satisfies the full-state circuit `stateCircuit` (the 9 transfer gates + 3 frame-forcing EQ gates). It does
     — `decide` returns `true`, kernel-checked — so the verify column shows a green "VERIFIES". The three
     frame-EQ gates' wire pairs (13/14 rest, 15/16 frame-reuse, 18/19 moved-bind) are surfaced as equalities,
     each a tick.

  ③ ANTI-GHOST.  `forgedWitness` is the SAME pre-state + turn but the REAL `forgedThirdCell` post-state — the
     bystander cell 2 minted 50 → 999, value forged into a third cell. `transferCircuit` (the old projection)
     would ACCEPT it: the two moved balances still conserve (wire 2 + wire 3 = wire 0 + wire 1). The full-state
     `stateCircuit` REJECTS it: `satisfiedC (encodeSC … forgedThirdCell) = false`, and specifically the
     FRAME-REUSE gate breaks (wire 15 ≠ wire 16). We render that as a red "REJECTED · frame-reuse" row — the
     pale-ghost forgery the soundness theorem `stateCircuit_rejects_third_cell` forbids by construction.

THE GUARANTEES, BADGED.  Three `#dregg_badge`s anchor the path on its real theorems (colour = the proof term's
`collectAxioms` verdict, kernel-clean = green): `execute_produces_satisfying_witness` (execute ⟹ a satisfying
witness exists), `satisfying_witness_proves_full_state` (verify ⟹ the WHOLE 18-field post-state is certified,
not a projection — soundness), and `stateCircuit_rejects_third_cell` (the anti-ghost tooth). The panel SHOWS
the pipeline; the badges PROVE it sound.

Discipline: NO `sorry`/`admit`/`native_decide`/SMT, NO new `axiom`s. Every wire value, every gate verdict, and
the forged-rejection are READ off the real `TransferWitness`/`StateCommit` derivation; the pure helpers are
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`. The `#html`/`#guard`s at the bottom force
the render path AND exhibit the non-vacuity (honest verifies, forged rejected, and they differ on wire 16).
-/
import Dregg2.Widget.Basic
import Dregg2.Circuit.TransferWitness
import ProofWidgets.Component.HtmlDisplay

open Lean
open ProofWidgets
open scoped ProofWidgets.Jsx
open Dregg2.Circuit
open Dregg2.Circuit.TransferWitness
open Dregg2.Circuit.StateCommit

namespace Dregg2.Widget

/-! ## §1 — The 20 wire meanings, read off the real circuit's `Var` layout.

`stateTraceWidth = 20`. Wires `0..10` are `Transfer.lean`'s transfer columns; `11..19` are
`StateCommit.lean`'s digest columns. This table is the human gloss for each wire index — it does NOT
produce any value; the VALUES are read from the executor-derived `honestWitness`/`forgedWitness`. -/

/-- The human name of wire `v` in the 20-wide full-state trace (`Transfer` wires 0..10, `StateCommit`
digest wires 11..19). A total function over the real layout — `"?"` only past the declared width. -/
def wireName : Nat → String
  | 0  => "srcPre"           | 1  => "dstPre"
  | 2  => "srcPost"          | 3  => "dstPost"
  | 4  => "amt"              | 5  => "tAuth"
  | 6  => "tNonneg"          | 7  => "tAvail"
  | 8  => "tDistinct"        | 9  => "tSrcLive"
  | 10 => "tDstLive"         | 11 => "preRoot"
  | 12 => "postRoot"         | 13 => "restDigPre"
  | 14 => "restDigPost"      | 15 => "frameDigPre"
  | 16 => "frameDigPost"     | 17 => "movedDigPre"
  | 18 => "movedDigPost"     | 19 => "movedDigExpected"
  | _  => "?"

/-- Which "lane" a wire belongs to (for colour grouping): the moved balances, the boolean gate flags,
the root commits, or the frame/moved digest pairs. Pure presentation. -/
def wireLane : Nat → String
  | 0 | 1 | 2 | 3 | 4 => "moved"
  | 5 | 6 | 7 | 8 | 9 | 10 => "guard"
  | 11 | 12 => "root"
  | _ => "digest"

/-- The accent colour for a wire's lane. -/
def laneColor (lane : String) : String :=
  if lane == "moved" then "#56c8ff"
  else if lane == "guard" then "#8b949e"
  else if lane == "root" then "#b794f6"
  else "#f0a429"

/-! ## §2 — The wire-value rows, read off the REAL executor-derived witness vectors.

`honestWitness`/`forgedWitness` are `List Int` of length 20 (the executor-derived satisfying assignment
and the real forged variant). `wireRows` reads each wire's value from BOTH and flags the ones that
differ — the forgery touches exactly the frame-reuse digest (wire 16). Everything is `getD` over the
genuine vectors. -/

/-- A wire's value in a witness vector (`getD … 0`, total). -/
def wireVal (xs : List Int) (v : Nat) : Int := xs.getD v 0

/-- One inspector row for wire `v`: its name, lane-tinted index, the honest value, and the forged value
(highlighted when it differs from the honest one — the forgery's footprint). -/
def wireRow (v : Nat) : Html :=
  let lane := wireLane v
  let hv := wireVal honestWitness v
  let fv := wireVal forgedWitness v
  let differs := hv ≠ fv
  kvRow s!"w{v} · {wireName v}"
    (.element "span" #[]
      #[ badge (toString hv) valColor (laneColor lane),
         Html.text "  ",
         badge (if differs then s!"⚠ {fv}" else toString fv)
           (if differs then "#ffffff" else keyColor)
           (if differs then "#da3633" else panelBg) ])

/-! ## §3 — The stage verdicts, DECIDED off the real circuit-satisfaction predicate.

`satisfiedC a` is `satisfied stateCircuit a`, decidable (re-exported in `TransferWitness`). We decide it
on the honest assignment (`true` — VERIFIES) and the forged one (`false` — REJECTED), and we surface the
SPECIFIC gate that bites on the forgery (the frame-reuse gate, wire 15 ≠ wire 16). These are the literal
proof-relevant facts, not captions. -/

/-- `true` iff the executor-derived HONEST witness satisfies the full-state circuit (it does). -/
def honestVerifies : Bool := decide (satisfiedC (encodeSC kS0 goodTurnS goodPostS))

/-- `true` iff the FORGED (bystander-mint) witness satisfies the circuit (it does NOT — anti-ghost). -/
def forgedVerifies : Bool := decide (satisfiedC (encodeSC kS0 goodTurnS forgedThirdCell))

/-- The frame-reuse digest equality on the honest witness (wire 15 = wire 16) — holds. -/
def honestFrameOk : Bool := wireVal honestWitness 15 == wireVal honestWitness 16

/-- The frame-reuse digest equality on the FORGED witness (wire 15 = wire 16) — BROKEN (the tooth). -/
def forgedFrameOk : Bool := wireVal forgedWitness 15 == wireVal forgedWitness 16

/-- The moved-balance conservation on the forged witness (w2 + w3 = w0 + w1) — STILL holds, which is
exactly WHY the old projection circuit accepted the forgery: the pale ghost conserves the moved pair. -/
def forgedMovedConserves : Bool :=
  wireVal forgedWitness 2 + wireVal forgedWitness 3 == wireVal forgedWitness 0 + wireVal forgedWitness 1

/-- A stage verdict pill — green "ok"/red "no" with a label. -/
def verdictPill (ok : Bool) (okLabel noLabel : String) : Html :=
  if ok then badge okLabel "#0d1117" "#3fb950" else badge noLabel "#ffffff" "#da3633"

/-! ## §4 — The pipeline panel: ① execute · ② verify · ③ anti-ghost, all from the real derivation. -/

/-- A stage header strip (the circled-number band the explorer's pipeline reads as one step). -/
def stageHeader (tag title : String) : Html :=
  <div style={json% {
      display: "flex", alignItems: "baseline", gap: "8px",
      marginTop: "12px", marginBottom: "4px"
    }}>
    <span style={json% {color: "#f0a429", fontFamily: "ui-monospace, Menlo, monospace",
        fontSize: "12px", fontWeight: "700"}}>{.text tag}</span>
    <span style={json% {color: $valColor, fontSize: "13px", fontWeight: "700"}}>{.text title}</span>
  </div>

/-- **The verified-turn inspector panel.** One dark card showing the full execute→prove→verify→anti-ghost
pipeline over the REAL reference transfer, every value read off `honestWitness`/`forgedWitness`/`satisfiedC`:

  * ① the 20-wire executor-derived satisfying assignment (honest vs forged, the diff highlighted);
  * ② the verify verdict (honest VERIFIES) + the three frame-EQ gate ticks;
  * ③ the anti-ghost verdict (forged REJECTED at the frame-reuse gate, though it conserves the moved pair).

Nothing is hand-set: change the turn or the forgery and every cell moves. -/
def verifiedTurnPanel : Html :=
  <div style={json% {
      background: $panelBg,
      border: $("1px solid " ++ panelBorder),
      borderRadius: "8px",
      padding: "12px 14px",
      maxWidth: "620px",
      fontFamily: "ui-sans-serif, system-ui, sans-serif",
      color: $valColor
    }}>
    <div style={json% {fontSize: "13px", fontWeight: "700", marginBottom: "2px"}}>
      {.text "dregg verified turn · execute → prove → verify → anti-ghost"}
    </div>
    <div style={json% {fontSize: "11px", color: $keyColor, marginBottom: "6px"}}>
      {.text "reference transfer: actor 0 moves 30 of asset 0, cell 0 → cell 1 (cell 2 is a live bystander) · 20-wire full-state witness, executor-derived"}
    </div>

    {stageHeader "①" "EXECUTE — recKExec → satisfying assignment (honest | forged)"}
    {.element "div" #[] ((List.range stateTraceWidth).map wireRow).toArray}

    {stageHeader "②" "VERIFY — does the executor-derived witness satisfy stateCircuit?"}
    {kvRow "honest witness" (verdictPill honestVerifies "VERIFIES (all 12 gates)" "FAILS")}
    {kvRow "frame-reuse gate (w15 = w16)" (verdictPill honestFrameOk "w15 = w16 ✓" "w15 ≠ w16")}

    {stageHeader "③" "ANTI-GHOST — the forged bystander-mint (cell 2: 50 → 999)"}
    {kvRow "moved pair conserves (w2+w3 = w0+w1)"
      (verdictPill forgedMovedConserves "conserves — old projection PASSED it" "fails")}
    {kvRow "full-state circuit accepts forgery?"
      (verdictPill (!forgedVerifies) "REJECTED — anti-ghost tooth bites" "accepted (BUG)")}
    {kvRow "frame-reuse gate on forgery (w15 = w16)"
      (verdictPill forgedFrameOk "passes (unexpected)" "w15 ≠ w16 — the bystander mint is caught")}

    <div style={json% {marginTop: "10px", fontSize: "11px", color: $keyColor}}>
      {.text "the pale ghost conserves the moved pair (so transferCircuit passed it) but the frame-reuse digest binds every untouched cell — minting a third cell is forbidden by construction"}
    </div>
  </div>

/-! ## §5 — Force the render over the REAL value, then BADGE the three guarantees. -/

-- THE RENDER DRIVER — elaborates the whole pipeline over the executor-derived witnesses.
#html verifiedTurnPanel

-- ① EXECUTE ⟹ a satisfying witness exists (the execute→prove direction).
#dregg_badge Dregg2.Circuit.TransferWitness.execute_produces_satisfying_witness
-- ② VERIFY ⟹ the WHOLE 18-field post-state is certified (soundness, not a projection).
#dregg_badge Dregg2.Circuit.TransferWitness.satisfying_witness_proves_full_state
-- ③ ANTI-GHOST — a forged third-cell post-state is REJECTED by construction.
#dregg_badge Dregg2.Circuit.StateCommit.stateCircuit_rejects_third_cell

/-! ## §6 — NON-VACUITY (`#guard`): the pipeline tracks the real derivation.

If the widget were placeholder, these would not move with the executor. They do: the honest witness
verifies, the forged one is rejected at the frame-reuse gate alone (while still conserving the moved
pair), and the two vectors differ on EXACTLY the frame-reuse digest wire (16). -/

-- ① the executor-derived honest witness is the 20-wire vector (length pinned).
#guard honestWitness.length == 20
#guard forgedWitness.length == 20
-- ② the honest witness VERIFIES; the frame-reuse gate holds (w15 = w16).
#guard honestVerifies == true
#guard honestFrameOk == true
-- ③ the forged witness is REJECTED, yet it CONSERVES the moved pair (the pale ghost) and breaks
--    specifically the frame-reuse gate (w15 ≠ w16) — the anti-ghost tooth, end-to-end.
#guard forgedVerifies == false
#guard forgedMovedConserves == true
#guard forgedFrameOk == false
-- The honest and forged vectors differ on EXACTLY wire 16 (frameDigPost) among the constrained EQ wires:
#guard wireVal honestWitness 16 ≠ wireVal forgedWitness 16
#guard wireVal honestWitness 15 == wireVal forgedWitness 15      -- frameDigPre unchanged (pre-state shared)
#guard wireVal honestWitness 0  == wireVal forgedWitness 0       -- moved srcPost identical (real transfer same)
-- The wire glosses cover the whole declared width (no `?` inside `[0, 20)`):
#guard (List.range stateTraceWidth).all (fun v => wireName v ≠ "?")
-- The lane partition is non-trivial (the widget colour-groups wires; ≥ 3 distinct lanes appear):
#guard ((List.range stateTraceWidth).map wireLane).dedup.length ≥ 3

/-! ## §7 — Axiom hygiene. The pure pipeline derivations are pinned kernel-clean.

The verdict bits (`honestVerifies`/`forgedVerifies`/the frame-gate reads) and the wire glosses must rest
on nothing but `{propext, Classical.choice, Quot.sound}` — they carry the widget's "computed, not faked"
credibility. (The `Html` builders inherit ProofWidgets' own clean axioms; we pin the dregg-specific
derivations. The badged guarantees are pinned at their definition sites in `TransferWitness`/`StateCommit`.) -/

#assert_axioms wireName
#assert_axioms wireLane
#assert_axioms wireVal
#assert_axioms honestVerifies
#assert_axioms forgedVerifies
#assert_axioms forgedFrameOk
#assert_axioms forgedMovedConserves

end Dregg2.Widget
