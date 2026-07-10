import Reactor.Pipeline

/-!
# Reactor.Stage.BodyLimit — the declared-body-size gate (RFC 9110 §15.5.14 `413`)

A request whose declared `Content-Length` is wider than the configured digit budget
(so ≥ `10 ^ maxCLDigits` bytes) is refused `413 Content Too Large` before the body is
read; a request within budget (or with no declared length) passes. This is the nginx
`client_max_body_size` / Apache `LimitRequestBody` behaviour: a client that announces an
oversized upload is rejected up front rather than the server buffering it.

The guard is on the WIDTH of the `Content-Length` field (its digit count), a monotone
proxy for the announced size that needs no decimal parser: a decimal `Content-Length`
with more than `maxCLDigits` digits announces at least `10 ^ maxCLDigits` bytes. With
`maxCLDigits = 7` the cap is 10 MB.

## What is proven (headline)

* `body_denies` — an over-budget declared length makes the stage `.respond` the `413`,
  and `body_denies_status` carries that `413` through a status-stable inner onion.
* `body_allows` — a within-budget (or absent) declared length `.continue`s.
* `body_denies_skips_handler` — the handler never runs on a refused request.
* `body_changes_bytes` — same handler: an over-budget request is forced to `413`, a
  within-budget one runs the handler (`200`).

Non-vacuity: `witnessCtx` (an 8-digit `Content-Length`, over the 7-digit budget) takes
the deny branch (`witness_oversized`), `okCtx` (a 3-digit length) takes the allow branch.
-/

namespace Reactor.Stage.BodyLimit

open Reactor.Pipeline
open Proto (Bytes Request)

def strBytes (s : String) : Bytes := s.toUTF8.toList

/-! ## The declared-size decision -/

/-- `Content-Length` header name (explicit ASCII bytes so the header match reduces in
the kernel). -/
def contentLengthName : Bytes := [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104]

/-- Digit budget for the declared `Content-Length`. A wider field announces ≥
`10 ^ maxCLDigits` bytes and is refused. `7` ⇒ a 10 MB cap. -/
def maxCLDigits : Nat := 7

/-- **The declared-size decision.** `true` when the request carries a `Content-Length`
whose decimal field is wider than the digit budget (announces an over-cap body); a
within-budget or absent length is `false`. -/
def oversized (req : Request) : Bool :=
  match req.headers.find? (fun nv => nv.1 == contentLengthName) with
  | some nv => decide (maxCLDigits < nv.2.length)
  | none    => false

/-! ## The refusal response -/

def tooLargeBody : Bytes := strBytes "content too large\n"

/-- The genuine `413` the gate answers with — status `413`, reason phrase, empty body-cap
notice. -/
def contentTooLarge : Response :=
  { status  := 413
    reason  := strBytes "Content Too Large"
    headers := []
    body    := tooLargeBody }

theorem contentTooLarge_status : contentTooLarge.status = 413 := rfl

/-! ## The stage -/

/-- **The declared-body-size gate stage.** Request phase: an over-budget declared length
is refused `413` (short-circuit, handler skipped); a within-budget or absent length
passes. Response phase transparent. -/
def bodyLimitStage : Stage where
  name := "body-limit"
  onRequest := fun c =>
    if oversized c.req then .respond contentTooLarge else .continue c
  onResponse := fun _ b => b

theorem bodyLimitStage_statusStable : Stage.statusStable bodyLimitStage := fun _ _ => rfl

/-! ## Deny: an over-budget declared length is refused 413, handler skipped -/

/-- **`body_denies`.** An over-budget declared length makes the stage `.respond` the
`413`. -/
theorem body_denies (c : Ctx) (h : oversized c.req = true) :
    bodyLimitStage.onRequest c = .respond contentTooLarge := by
  show (if oversized c.req then StageStep.respond contentTooLarge else StageStep.continue c) = _
  rw [h]; rfl

/-- **`body_allows`.** A within-budget (or absent) declared length passes (`.continue`). -/
theorem body_allows (c : Ctx) (h : oversized c.req = false) :
    bodyLimitStage.onRequest c = .continue c := by
  show (if oversized c.req then StageStep.respond contentTooLarge else StageStep.continue c) = _
  rw [h]
  simp only [Bool.false_eq_true, if_false]

/-- **`body_denies_status`.** The refusal keeps its `413` through a status-stable inner
onion — a `413` stays a `413` on the wire. -/
theorem body_denies_status (c : Ctx) (rest : List Stage) (handler : Ctx → Response)
    (h : oversized c.req = true) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (bodyLimitStage :: rest) handler c).build).status = 413 := by
  have := pipeline_gate_status bodyLimitStage rest handler c contentTooLarge
    (body_denies c h) hst
  rw [this]; rfl

/-- **`body_denies_skips_handler`.** The request is NOT forwarded on a refused body. -/
theorem body_denies_skips_handler (c : Ctx) (rest : List Stage) (handler handler' : Ctx → Response)
    (h : oversized c.req = true) :
    runPipeline (bodyLimitStage :: rest) handler c
      = runPipeline (bodyLimitStage :: rest) handler' c :=
  pipeline_gate_ignores_handler bodyLimitStage rest handler handler' c
    contentTooLarge (body_denies c h)

/-! ## Concrete non-vacuity -/

/-- A request declaring an 8-digit `Content-Length` (over the 7-digit budget). -/
def witnessCtx : Ctx :=
  { input := [], req := { headers := [(contentLengthName, [49, 50, 51, 52, 53, 54, 55, 56])] } }

/-- The witness declares an over-budget body. -/
theorem witness_oversized : oversized witnessCtx.req = true := by decide

/-- **`witness_responds`.** On the over-budget witness the real stage `.respond`s the
`413` — the decision the braid gate delegates to. -/
theorem witness_responds : bodyLimitStage.onRequest witnessCtx = .respond contentTooLarge :=
  body_denies witnessCtx witness_oversized

/-- A request declaring a 3-digit `Content-Length` (within budget). -/
def okCtx : Ctx :=
  { input := [], req := { headers := [(contentLengthName, [49, 50, 51])] } }

theorem okCtx_within : oversized okCtx.req = false := by decide

/-- **`body_changes_bytes`.** Same handler: an over-budget request is forced to `413`, a
within-budget one runs the handler (`200`). The gate genuinely drives the response. -/
theorem body_changes_bytes (body : Bytes) :
    ((runPipeline [bodyLimitStage] (fun _ => Reactor.ok200 body) witnessCtx).build).status = 413
    ∧ ((runPipeline [bodyLimitStage] (fun _ => Reactor.ok200 body) okCtx).build).status = 200 := by
  refine ⟨?_, ?_⟩
  · have := body_denies_status witnessCtx [] (fun _ => Reactor.ok200 body) witness_oversized
      (by intro t ht; exact absurd ht (List.not_mem_nil t))
    simpa using this
  · rw [pipeline_stage_effect bodyLimitStage [] (fun _ => Reactor.ok200 body) okCtx okCtx
        (body_allows okCtx okCtx_within)]
    rfl

/-! ## Axiom audit -/

#print axioms body_denies
#print axioms body_allows
#print axioms body_denies_status
#print axioms body_denies_skips_handler
#print axioms witness_responds
#print axioms body_changes_bytes

end Reactor.Stage.BodyLimit
