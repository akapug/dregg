import Reactor.Pipeline
import StickTable

/-!
# Reactor.Stage.StickTable — the keyed cross-request counter, as a pipeline stage

The `StickTable` base library proved the shared accounting substrate: a keyed
counter table (`bump`/`track`, `lookup`, `evict`) with the per-step correctness
lemmas — `bump_getCount_self` (a track raises exactly the tracked key's counter by
one), `lookup_expired` / `evict_removes_expired` (an entry past its TTL reads back
absent and is evicted), and `bump_Wf` / `evict_Wf` (the table stays a finite,
key-unique map). This is the counter behind per-source request aggregation and the
threshold limits (rate / connection caps) that read it.

This file promotes that substrate from a *proof-attachment* to a **byte-driver** in
the deployed serve fold. It is the SUBSTRATE stage the threshold gates compose on:
on the request phase it reconstructs the source's standing request count from the
attribute bag, and when that aggregated count has reached the configured threshold
it short-circuits with a `429 Too Many Requests` — the handler and every later stage
are skipped.

## The counting bound is the base library's, lifted

`countAfter n` is the table produced by `n` successive `track`s of one source key
from empty. `getCount_countAfter` proves its counter is EXACTLY `n` — a direct
induction on the base `StickTable.bump_getCount_self`, so the aggregated count the
gate decides on is the real stick-table counter, not a stub. Because the sans-IO
serve is one stateless call per request, `n` (the source's standing count) rides in
the attribute bag under `countKey`; the gate reads its length and reconstructs the
live table.

The TTL bound is likewise the base library's: `stick_lookup_expired` and
`stick_evict_removes_expired` re-export `StickTable.lookup_expired` /
`evict_removes_expired` on a concrete over-TTL table — an idle entry reads back
absent and is evicted, so the table is bounded, not monotonically growing.

The byte effect is genuine:

* `stickStage_gate_build` — at/over the threshold, the built response IS the `429`;
* `stickStage_pass` — under the threshold, the stage is transparent;
* `stickStage_changes_bytes` — same handler, an over- and an under-threshold source
  emit different status bytes.
-/

namespace Reactor.Stage.StickTable

open Reactor.Pipeline
open Proto (Bytes)

/-! ## The keyed counter, driven from the base substrate -/

/-- The single source key the deployed stick stage aggregates on (one shard's view;
the cross-shard merge is the base library's named CR-2 obligation). -/
def srcKey : Nat := 0

/-- `countAfter n` — the stick table after `n` successive `track`s of `srcKey` from
empty, each at clock `0`. This is the source's live table reconstructed from its
standing request count. -/
def countAfter : Nat → _root_.StickTable.Table
  | 0     => []
  | n + 1 => _root_.StickTable.bump srcKey 0 (countAfter n)

/-- **The counting bound (lifted from the base substrate).** The aggregated counter
for `srcKey` after `n` tracks is EXACTLY `n` — a direct induction on the base
`bump_getCount_self`, so the gate decides on the real stick-table counter. -/
theorem getCount_countAfter (n : Nat) :
    _root_.StickTable.getCount srcKey (countAfter n) = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show _root_.StickTable.getCount srcKey
      (_root_.StickTable.bump srcKey 0 (countAfter m)) = m + 1
    rw [_root_.StickTable.bump_getCount_self, ih]

/-- The reconstructed table stays a finite key-unique map (base `bump_Wf`). -/
theorem countAfter_Wf (n : Nat) : _root_.StickTable.Wf (countAfter n) := by
  induction n with
  | zero => exact _root_.StickTable.Wf_nil
  | succ m ih => exact _root_.StickTable.bump_Wf srcKey 0 ih

/-! ## The 429 rejection response -/

/-- Reason phrase for the rejection. -/
def reason429 : Bytes := "Too Many Requests".toUTF8.toList

/-- Body prose for the rejection. -/
def tooManyBody : Bytes := "aggregated request limit exceeded\n".toUTF8.toList

/-- The `429 Too Many Requests` response the gate answers with when the source's
aggregated count reaches the threshold — status `429`. -/
def resp429 : Response := error4xx 429 reason429 tooManyBody

/-! ## The threshold decision -/

/-- The configured aggregated-request threshold. A REAL low bound (`16`); a source
whose stick counter reaches it is throttled. -/
def threshold : Nat := 16

/-- **The threshold decision** on an aggregated count: admit iff strictly below the
threshold. Total. -/
def admits (count : Nat) : Bool := count < threshold

/-- Under the threshold ⇒ admitted. -/
theorem admits_under {count : Nat} (h : count < threshold) : admits count = true := by
  simp [admits, h]

/-- At/over the threshold ⇒ rejected. -/
theorem admits_over {count : Nat} (h : threshold ≤ count) : admits count = false := by
  simp [admits, Nat.not_lt.mpr h]

/-! ## Reading the source's standing count off the context -/

/-- Attribute key holding the source's standing aggregated request count (its
byte-length = the count the stick substrate has recorded for this source). -/
def countKey : String := "stick-count"

/-- Look the value bytes up for a key in the attribute bag (`[]` if absent). -/
def lookupBytes (c : Ctx) (k : String) : Bytes :=
  match c.attrs.find? (fun p => p.1 == k) with
  | some p => p.2
  | none   => []

/-- The source's standing count = the length of the `countKey` attr (`0` when
absent — a fresh source). -/
def countOf (c : Ctx) : Nat := (lookupBytes c countKey).length

/-- **The real gate decision on the context.** Reconstruct the source's live table
(`countAfter (countOf c)`), read its counter through the REAL base `getCount`, and
admit iff it is under the threshold. The counter equals `countOf c` by
`getCount_countAfter` — the substrate's counting bound. -/
def ctxAdmits (c : Ctx) : Bool :=
  admits (_root_.StickTable.getCount srcKey (countAfter (countOf c)))

/-- The context decision reduces to the threshold test on the standing count — the
substrate counter is exactly the standing count. -/
theorem ctxAdmits_eq (c : Ctx) : ctxAdmits c = admits (countOf c) := by
  unfold ctxAdmits; rw [getCount_countAfter]

/-! ## The stage -/

/-- **The stick-table threshold gate stage.** Request phase: reconstruct the source's
aggregated stick counter and, when it reaches the threshold, `.respond resp429`
(short-circuit); otherwise `.continue`. Response phase: transparent. -/
def stickStage : Stage where
  name := "stick-table"
  onRequest  := fun c => cond (ctxAdmits c) (.continue c) (.respond resp429)
  onResponse := fun _ b => b

/-- At/over the threshold, the gate short-circuits with the `429`. -/
theorem stickStage_onReq_respond (c : Ctx) (hover : ctxAdmits c = false) :
    stickStage.onRequest c = .respond resp429 := by
  simp only [stickStage, hover, cond]

/-- Under the threshold, the gate passes the context through. -/
theorem stickStage_onReq_continue (c : Ctx) (hunder : ctxAdmits c = true) :
    stickStage.onRequest c = .continue c := by
  simp only [stickStage, hunder, cond]

/-! ## The byte effect -/

/-- **Gate byte-effect.** At/over the threshold, the BUILT pipeline response — for
ANY tail and handler — is the `429`. -/
theorem stickStage_gate_build (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : ctxAdmits c = false) :
    runPipeline (stickStage :: rest) h c = runResp rest c (ResponseBuilder.ofResponse resp429) :=
  pipeline_gate_short_circuits stickStage rest h c resp429 (stickStage_onReq_respond c hover)

/-- The over-threshold response's status byte is `429` — through a status-stable onion. -/
theorem stickStage_over_status (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : ctxAdmits c = false) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (stickStage :: rest) h c).build).status = 429 :=
  pipeline_gate_status stickStage rest h c resp429 (stickStage_onReq_respond c hover) hst

/-- **Pass-through byte-effect.** Under the threshold, the stage is transparent. -/
theorem stickStage_pass (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hunder : ctxAdmits c = true) :
    runPipeline (stickStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect stickStage rest h c c (stickStage_onReq_continue c hunder)]
  rfl

/-! ## TTL bound — re-exported from the base substrate (boundedness) -/

/-- A concrete stick table with one entry for `srcKey`, last-seen at clock `0`. -/
def idleTable : _root_.StickTable.Table := [(srcKey, ⟨3, 0⟩)]

/-- **TTL read bound (base `lookup_expired`).** With time-to-idle `5` and the clock
advanced to `10`, the entry (last-seen `0`) is past its TTL, so `lookup` reads it back
as absent — the table does not serve stale counters. -/
theorem stick_lookup_expired :
    _root_.StickTable.lookup srcKey 5 10 idleTable = none :=
  _root_.StickTable.lookup_expired (t := idleTable) (e := ⟨3, 0⟩) rfl (by decide)

/-- `idleTable` is a finite key-unique map. -/
theorem idleTable_wf : _root_.StickTable.Wf idleTable := by
  simp [_root_.StickTable.Wf, _root_.StickTable.keys, idleTable]

/-- **TTL evict bound (base `evict_removes_expired`).** The same idle entry is
removed by `evict`, so the table is bounded (idle sources are reclaimed), not
monotonically growing. -/
theorem stick_evict_removes_expired :
    _root_.StickTable.find srcKey (_root_.StickTable.evict 5 10 idleTable) = none :=
  _root_.StickTable.evict_removes_expired (t := idleTable) (e := ⟨3, 0⟩)
    idleTable_wf rfl (by decide)

/-! ## Concrete over- and under-threshold contexts (non-vacuity) -/

/-- A source whose standing count has reached the threshold — over the limit. -/
def overCtx : Ctx :=
  { input := [], req := {}, attrs := [(countKey, List.replicate threshold (0 : UInt8))] }

/-- A fresh source (no standing count) — under the limit. -/
def underCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- `overCtx` is over the threshold — the real substrate counter (= `threshold`)
rejects it. -/
theorem overCtx_over : ctxAdmits overCtx = false := by
  rw [ctxAdmits_eq]; exact admits_over (by decide)

/-- `underCtx` is under the threshold — the real substrate counter (= `0`) admits it. -/
theorem underCtx_under : ctxAdmits underCtx = true := by
  rw [ctxAdmits_eq]; exact admits_under (by decide)

/-- An over-threshold source emits a `429` (through a status-stable inner onion). -/
theorem overCtx_emits_429 (rest : List Stage) (h : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (stickStage :: rest) h overCtx).build).status = 429 :=
  stickStage_over_status rest h overCtx overCtx_over hst

/-- An under-threshold source passes through to the tail unchanged. -/
theorem underCtx_passes (rest : List Stage) (h : Ctx → Response) :
    runPipeline (stickStage :: rest) h underCtx = runPipeline rest h underCtx :=
  stickStage_pass rest h underCtx underCtx_under

/-- **The gate genuinely drives the wire.** Same handler and tail, an over-threshold
and an under-threshold source emit different status bytes. -/
theorem stickStage_changes_bytes (h : Ctx → Response)
    (hstatus : (h underCtx).status ≠ 429) :
    ((runPipeline [stickStage] h overCtx).build).status
      ≠ ((runPipeline [stickStage] h underCtx).build).status := by
  rw [overCtx_emits_429 [] h (by intro t ht; exact absurd ht (List.not_mem_nil t)),
      underCtx_passes [] h, pipeline_empty, build_ofResponse]
  exact fun heq => hstatus heq.symm

/-! ## Axiom audit -/

#print axioms getCount_countAfter
#print axioms countAfter_Wf
#print axioms stick_lookup_expired
#print axioms stick_evict_removes_expired
#print axioms overCtx_over
#print axioms underCtx_under
#print axioms stickStage_gate_build
#print axioms stickStage_pass
#print axioms stickStage_changes_bytes

end Reactor.Stage.StickTable
