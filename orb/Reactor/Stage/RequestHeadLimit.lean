import Reactor.Stage.FramingValidation

/-!
# Reactor.Stage.RequestHeadLimit — the request-head length gate (Z1 DoS)

The wave-5 EXTENDED probe (`docs/engine/review/CONFORMANCE-EXT.md`, finding **Z1** —
the TOP finding of the whole conformance effort) showed a single unauthenticated
request whose **head** (request-line + header block) is ≳ 30 KiB aborts the entire
`dataplane` process with a stack overflow:

```
thread 'drorb-serve' has overflowed its stack
fatal runtime error: stack overflow, aborting
```

Root class: a non-tail-recursive fold over the request head grows one stack frame
per input unit until the ~8 MiB thread stack is exhausted. Any shape of oversized
head triggers it — a long URI, one large header value, or ~900 small headers — and
they all inflate the same quantity: the **total head byte length**. A 28 KiB head
survives (`200`); 32 KiB crashes. Body size is safe.

**The fix (RFC 7230 §3.2.5 / §6.5 practice).** Bound the head length BEFORE the
recursive parse and answer `431 Request Header Fields Too Large`. This file provides:

* `headBytesTooLarge` — the single decision (`limit < size`) the fix keys on, over a
  Nat byte-count. `maxHeadBytes` (16 KiB) sits well below the 28–32 KiB crash band and
  well above any legitimate head.
* `requestHeaderFieldsTooLargeResp` — the `431` refusal.
* `headLimitStage` — a request-phase GATE that rejects an oversized head with the
  `431`. In the `runPipeline` model this is an in-pipeline BACKSTOP (defense in
  depth). The DEFINITIVE Z1 fix is the SAME decision applied at the BYTE boundary —
  on `input.size` (an O(1) `ByteArray.size`) **before** `Proto.RequestSerialize.parse`
  is ever called — so the recursive parse never runs on an oversized head and cannot
  overflow. See the ServeConformant wire fragment in the lane report. (A gate that
  runs AFTER the parse cannot un-overflow it; hence the primary gate is pre-parse.
  This stage's Lean content is the shared, proven decision + the `431` response the
  pre-parse gate emits, plus a post-parse backstop for any head the byte gate lets
  through.)

## What is proven (non-vacuous on concrete witnesses)

* `headLimitStage_rejects` — an oversized head ⇒ `.respond` the `431`.
* `headLimitStage_passes` — a within-limit head ⇒ `.continue` unchanged.
* `requestHeaderFieldsTooLargeResp_status` — the refusal is a `431`.
* Concrete witnesses: a 40000-byte head (`bigCtx`) ⇒ `431`; a small head (`smallCtx`)
  ⇒ pass — each guard `by decide` (no `native_decide`).
-/

namespace Reactor.Stage.RequestHeadLimit

open Reactor.Pipeline
open Proto (Bytes Request)
open Reactor.Stage.RequestValidation (strBytes)

/-- The maximum accepted request-head byte length. 16 KiB: comfortably above any
legitimate request-line + header block, comfortably below the 28–32 KiB stack-crash
band the Z1 bisection found. -/
def maxHeadBytes : Nat := 16384

/-- **The decision.** A head of `size` bytes is too large when it exceeds the limit.
Applied at the byte boundary to `input.size` (the definitive Z1 gate, pre-parse) and,
as a backstop, to `c.input.length` inside the pipeline — the SAME function both. -/
def headBytesTooLarge (size : Nat) : Bool := decide (maxHeadBytes < size)

/-- `431 Request Header Fields Too Large` — the oversized-head refusal (Z1). -/
def requestHeaderFieldsTooLargeResp : Response :=
  { status := 431, reason := strBytes "Request Header Fields Too Large", headers := []
    body := strBytes "request header fields too large\n" }

theorem requestHeaderFieldsTooLargeResp_status :
    requestHeaderFieldsTooLargeResp.status = 431 := rfl

/-! ## The stage (in-pipeline backstop over `c.input.length`) -/

/-- **The head-length gate.** Request phase: if the raw head is over `maxHeadBytes`,
short-circuit with the `431`; otherwise pass unchanged. Response phase transparent.
The DEFINITIVE gate is this same decision on `input.size` before parse (see the wire
fragment); this in-pipeline form is a backstop. -/
def headLimitStage : Stage where
  name := "request-head-limit"
  onRequest := fun c =>
    if headBytesTooLarge c.input.length then .respond requestHeaderFieldsTooLargeResp
    else .continue c
  onResponse := fun _ b => b

theorem headLimitStage_statusStable : Stage.statusStable headLimitStage := fun _ _ => rfl

/-- **Reject.** An oversized head ⇒ the gate answers `431`. -/
theorem headLimitStage_rejects (c : Ctx) (h : headBytesTooLarge c.input.length = true) :
    headLimitStage.onRequest c = .respond requestHeaderFieldsTooLargeResp := by
  show (if headBytesTooLarge c.input.length then _ else _) = _
  rw [h]; simp only [if_true]

/-- **Pass.** A within-limit head ⇒ `.continue` unchanged. -/
theorem headLimitStage_passes (c : Ctx) (h : headBytesTooLarge c.input.length = false) :
    headLimitStage.onRequest c = .continue c := by
  show (if headBytesTooLarge c.input.length then _ else StageStep.continue c) = _
  rw [h]; simp only [Bool.false_eq_true, if_false]

/-- The `431` survives a status-stable inner onion (gate composition). -/
theorem headLimitStage_status (c : Ctx) (rest : List Stage) (handler : Ctx → Response)
    (h : headBytesTooLarge c.input.length = true)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (headLimitStage :: rest) handler c).build).status = 431 := by
  have := pipeline_gate_status headLimitStage rest handler c requestHeaderFieldsTooLargeResp
    (headLimitStage_rejects c h) hst
  rw [this]; rfl

/-- A rejected (oversized) request never reaches the handler. -/
theorem headLimitStage_skips_handler (c : Ctx) (rest : List Stage)
    (handler handler' : Ctx → Response) (h : headBytesTooLarge c.input.length = true) :
    runPipeline (headLimitStage :: rest) handler c
      = runPipeline (headLimitStage :: rest) handler' c :=
  pipeline_gate_ignores_handler headLimitStage rest handler handler' c
    requestHeaderFieldsTooLargeResp (headLimitStage_rejects c h)

/-! ## Concrete non-vacuity witnesses -/

/-- A request whose raw head is 40000 bytes (over the 16 KiB limit — a Z1-class
oversized head; `List.replicate` of a filler byte stands in for the real bytes). -/
def bigCtx : Ctx :=
  { input := List.replicate 40000 65, req := { } }

/-- A small, normal request head (100 bytes). -/
def smallCtx : Ctx :=
  { input := List.replicate 100 65, req := { } }

theorem bigCtx_too_large : headBytesTooLarge bigCtx.input.length = true := by
  simp only [bigCtx, List.length_replicate]; decide
theorem smallCtx_ok : headBytesTooLarge smallCtx.input.length = false := by
  simp only [smallCtx, List.length_replicate]; decide

/-- **Z1.** The oversized head ⇒ the gate answers `431`. -/
theorem bigCtx_rejected :
    headLimitStage.onRequest bigCtx = .respond requestHeaderFieldsTooLargeResp :=
  headLimitStage_rejects bigCtx bigCtx_too_large

/-- The small head passes through unchanged. -/
theorem smallCtx_passes : headLimitStage.onRequest smallCtx = .continue smallCtx :=
  headLimitStage_passes smallCtx smallCtx_ok

/-- **Non-vacuity contrast.** The gate rejects the oversized head with `431` but
passes the small one — it genuinely discriminates on size. -/
theorem gate_discriminates :
    (headLimitStage.onRequest bigCtx = .respond requestHeaderFieldsTooLargeResp)
    ∧ (headLimitStage.onRequest smallCtx = .continue smallCtx) :=
  ⟨bigCtx_rejected, smallCtx_passes⟩

/-! ### Executable sanity checks -/

def decideStatus : StageStep → Nat
  | .respond r => r.status
  | .continue _ => 200

#guard decideStatus (headLimitStage.onRequest bigCtx) == 431
#guard decideStatus (headLimitStage.onRequest smallCtx) == 200
#guard headBytesTooLarge 40000 == true
#guard headBytesTooLarge 100 == false
#guard headBytesTooLarge 16384 == false
#guard headBytesTooLarge 16385 == true

/-! ## Axiom audit -/

#print axioms headLimitStage_rejects
#print axioms headLimitStage_passes
#print axioms headLimitStage_status
#print axioms headLimitStage_skips_handler
#print axioms bigCtx_rejected
#print axioms smallCtx_passes
#print axioms gate_discriminates

end Reactor.Stage.RequestHeadLimit
