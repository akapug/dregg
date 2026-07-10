import Reactor.Pipeline

/-!
# Reactor.Stage.ConnLimit — the per-source concurrent-connection cap GATE

A byte-driving `Stage` for the extensible serve fold: on the request phase it
consults the number of connections currently active from this request's source
(its client IP) and, when that count has reached the configured per-source cap,
short-circuits the whole pipeline with a `503 Service Unavailable` — the handler
and every later stage are skipped. Under the cap the request passes through
untouched.

## The decision core — a real bounded admission test

`admits cap active` is the exact admission rule of a per-source concurrent cap: a
new connection is admitted iff the cap is disabled (`cap = 0`, unlimited) OR the
source's active-connection count is strictly below the cap. This is the total,
saturation-free form of the reference accept test (reject once `active ≥ cap`;
always accept when the cap is `0`).

Because the sans-IO serve is one stateless call per request, the source's standing
active-connection count rides in the extensible attribute bag under `activeKey`:
the accept path (which owns the per-IP counter) stashes that many bytes, and the
gate reads its length. A source at or over the cap therefore reconstructs an
over-limit `active`, and the REAL `admits` decision rejects it with a `503`.

The effect is a genuine change to the emitted bytes:

* `connStage_gate_build` — at/over the cap, the built pipeline response IS the `503`;
* `connStage_pass` — under the cap, the stage is transparent (the handler's bytes);
* `connStage_changes_bytes` — same handler, an over-cap and an under-cap source emit
  *different* status bytes: the gate really drives the wire.

`admits` truth-table lemmas (`admits_unlimited`, `admits_under`, `admits_at_cap`,
`admits_over`) and the concrete over/under contexts (`overCtx_over`,
`underCtx_under`, closed by `decide`) keep all of the above non-vacuous.
-/

namespace Reactor.Stage.ConnLimit

open Reactor.Pipeline
open Proto (Bytes)

/-! ## The 503 rejection response -/

/-- Reason phrase for the rejection. -/
def reason503 : Bytes := "Service Unavailable".toUTF8.toList

/-- Body prose for the rejection. -/
def busyBody : Bytes := "per-source connection limit reached\n".toUTF8.toList

/-- The `503 Service Unavailable` response the gate answers with when the source is
at or over its concurrent-connection cap — a real `Response` whose status is `503`. -/
def resp503 : Response := error4xx 503 reason503 busyBody

/-! ## The decision core -/

/-- The configured per-source cap. A REAL low limit (`4`) so a burst of concurrent
connections from one source trips the gate; `0` would disable the cap entirely. -/
def connCap : Nat := 4

/-- **The admission decision.** A new connection from a source with `active`
currently-open connections is admitted iff the cap is disabled (`cap = 0`) or the
source is strictly below the cap. This is the reference accept rule, total. -/
def admits (cap active : Nat) : Bool := cap == 0 || active < cap

/-! ### Truth table (non-vacuity of the decision) -/

/-- A disabled cap (`0`) admits any load — the unlimited path. -/
theorem admits_unlimited (active : Nat) : admits 0 active = true := by
  simp [admits]

/-- Strictly under the cap ⇒ admitted. -/
theorem admits_under {cap active : Nat} (hpos : 0 < cap) (h : active < cap) :
    admits cap active = true := by
  simp only [admits, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr h

/-- Exactly at the cap ⇒ rejected (the boundary is closed against admission). -/
theorem admits_at_cap {cap : Nat} (hpos : 0 < cap) : admits cap cap = false := by
  simp only [admits, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  simp [Nat.ne_of_gt hpos, Nat.lt_irrefl]

/-- At or over the cap (with a live cap) ⇒ rejected. -/
theorem admits_over {cap active : Nat} (hpos : 0 < cap) (h : cap ≤ active) :
    admits cap active = false := by
  have h0 : (cap == 0) = false := by simp [Nat.ne_of_gt hpos]
  have h1 : decide (active < cap) = false := by simp [Nat.not_lt.mpr h]
  simp only [admits, h0, h1, Bool.or_false]

/-! ## Reading the source's active-connection count off the context -/

/-- Attribute key holding the source's standing active-connection count (its
byte-length = the number of connections currently open from this source). Written
by the accept path that owns the per-source counter. -/
def activeKey : String := "conn-active"

/-- Look the value bytes up for a key in the attribute bag (`[]` if absent). -/
def lookupBytes (c : Ctx) (k : String) : Bytes :=
  match c.attrs.find? (fun p => p.1 == k) with
  | some p => p.2
  | none   => []

/-- The source's active-connection count = the length of the `activeKey` attr
(`0` when absent — a fresh source with no standing connections). -/
def activeOf (c : Ctx) : Nat := (lookupBytes c activeKey).length

/-- **The real gate decision on the context.** Admit iff the source's reconstructed
active count is under the configured cap. -/
def ctxAdmits (c : Ctx) : Bool := admits connCap (activeOf c)

/-! ## The stage -/

/-- **The connection-limit gate stage.** Request phase: consult the real admission
rule on the source's active-connection count — admit → `.continue`, reject →
`.respond resp503` (short-circuit with the `503`, skipping the handler and every
later stage). Response phase: transparent — a pure gate. -/
def connStage : Stage where
  name := "conn-limit"
  onRequest  := fun c => cond (ctxAdmits c) (.continue c) (.respond resp503)
  onResponse := fun _ b => b

/-! ## The gate's request-phase decision -/

/-- At/over the cap, the gate short-circuits with the `503`. -/
theorem connStage_onReq_respond (c : Ctx) (hover : ctxAdmits c = false) :
    connStage.onRequest c = .respond resp503 := by
  simp only [connStage, hover, cond]

/-- Under the cap, the gate passes the context through. -/
theorem connStage_onReq_continue (c : Ctx) (hunder : ctxAdmits c = true) :
    connStage.onRequest c = .continue c := by
  simp only [connStage, hunder, cond]

/-! ## The byte effect -/

/-- **Gate byte-effect.** At/over the cap, the BUILT pipeline response — for ANY
tail and handler — is the `503`: the handler and every later stage are skipped. -/
theorem connStage_gate_build (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : ctxAdmits c = false) :
    runPipeline (connStage :: rest) h c = runResp rest c (ResponseBuilder.ofResponse resp503) :=
  pipeline_gate_short_circuits connStage rest h c resp503 (connStage_onReq_respond c hover)

/-- The `503`'s status field is `503`. -/
theorem resp503_status : resp503.status = 503 := rfl

/-- The over-cap response's status byte is `503` — preserved through a
status-stable inner onion. -/
theorem connStage_over_status (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : ctxAdmits c = false) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (connStage :: rest) h c).build).status = 503 :=
  pipeline_gate_status connStage rest h c resp503 (connStage_onReq_respond c hover) hst

/-- **Pass-through byte-effect.** Under the cap, the stage is transparent: the
pipeline output is exactly the tail's. -/
theorem connStage_pass (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hunder : ctxAdmits c = true) :
    runPipeline (connStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect connStage rest h c c (connStage_onReq_continue c hunder)]
  rfl

/-! ## Concrete over- and under-cap contexts (non-vacuity) -/

/-- A source whose standing active-connection count has reached the cap — over the
limit, so this connection is rejected. -/
def overCtx : Ctx :=
  { input := [], req := {}, attrs := [(activeKey, List.replicate connCap (0 : UInt8))] }

/-- A fresh source (no standing connections) — under the limit, admitted. -/
def underCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- `overCtx` is over the cap — the real rule rejects it. -/
theorem overCtx_over : ctxAdmits overCtx = false := by decide

/-- `underCtx` is under the cap — the real rule admits it. -/
theorem underCtx_under : ctxAdmits underCtx = true := by decide

/-- An over-cap connection emits a `503` (through a status-stable inner onion). -/
theorem overCtx_emits_503 (rest : List Stage) (h : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (connStage :: rest) h overCtx).build).status = 503 :=
  connStage_over_status rest h overCtx overCtx_over hst

/-- An under-cap connection passes through to the tail unchanged. -/
theorem underCtx_passes (rest : List Stage) (h : Ctx → Response) :
    runPipeline (connStage :: rest) h underCtx = runPipeline rest h underCtx :=
  connStage_pass rest h underCtx underCtx_under

/-- **The gate genuinely drives the wire.** With the SAME handler and tail, an
over-cap source and an under-cap source emit different status bytes: the over-cap
one is forced to `503`, the under-cap one keeps the handler's status. So the stage
really changes the bytes the serve emits — a byte-driver, not a proof attachment. -/
theorem connStage_changes_bytes (h : Ctx → Response)
    (hstatus : (h underCtx).status ≠ 503) :
    ((runPipeline [connStage] h overCtx).build).status
      ≠ ((runPipeline [connStage] h underCtx).build).status := by
  rw [overCtx_emits_503 [] h (by intro t ht; exact absurd ht (List.not_mem_nil t)),
      underCtx_passes [] h, pipeline_empty, build_ofResponse]
  exact fun heq => hstatus heq.symm

/-! ## Axiom audit -/

#print axioms admits_unlimited
#print axioms admits_at_cap
#print axioms overCtx_over
#print axioms underCtx_under
#print axioms connStage_gate_build
#print axioms connStage_over_status
#print axioms connStage_pass
#print axioms connStage_changes_bytes

end Reactor.Stage.ConnLimit
