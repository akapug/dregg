/-
# Proto.RangeProven — Range / `206 Partial Content` on the DEPLOYED static handler

PROVE-WHAT-RUNS for the ledger row `h1.range` (RFC 7233 byte-range serving).

The deployed default app (`Reactor.App.demoApp`) carries a `/static` prefix route to
the `staticFile` handler, and `Reactor.App.responseOfReq req .staticFile` is
DEFINITIONALLY `StaticFile.serveDeployed (targetSegments req.target) req.headers`
(`Proto.EtagProven.deployed_staticFile_route`, `rfl`). `serveDeployed` parses the raw
request headers (`reqOfHeaders`) — INCLUDING the `Range:` header — and renders
`StaticFile.serveConditional StaticFile.deployedConfig` onto the wire. So the theorems
below describe the EXACT `206` the running dataplane emits for
`GET /static/app.js` with `Range: bytes=0-9`.

The CURL that anchors this file (lane `ran` field):

    $ curl -s -i -H 'Range: bytes=0-9' http://127.0.0.1:8080/static/app.js
    HTTP/1.1 206 Partial Content
    ETag: "9e983f35"
    Accept-Ranges: bytes
    Content-Range: bytes 0-9/35
    Content-Length: 10

    console.lo

Theorems:
  * `range_header_parses` — the deployed header parser (`reqOfHeaders`) turns the raw
    `Range: bytes=0-9` wire header into the model range-set `[.fromTo 0 9]` (and a
    matching `range`). This is the parse the running serve performs — no pre-baked Req.
  * `deployed_range_206` — the deployed handler answers that request with `206`, a body
    of exactly `slice appJs 0 9` (the first ten bytes), a `Content-Range: bytes 0-9/35`
    header, and `Accept-Ranges: bytes`.
  * `range_body_bytes` — those ten body bytes ARE `"console.lo"` — octet-for-octet the
    curl body, so nothing is vacuous.
-/

import StaticFile
import Reactor.App
import Proto.EtagProven

namespace Proto.RangeProven

open StaticFile

/-- Kernel-reducibility bridge for `strBytes`. `ByteArray.toList` (Lean core) is defined
by well-founded recursion (`termination_by bs.size - i`), so it does NOT reduce in the
kernel; that is what makes `strBytes s = s.toUTF8.toList` opaque to `decide`/`rfl`. This
rewrites it to the structural `Array.toList` (`bs.data.toList`), which the kernel DOES
reduce — letting concrete byte witnesses close by `decide` in the pure kernel
(`{propext, Quot.sound}`; no `native_decide`, no `Lean.ofReduceBool`). -/
private theorem ba_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  have key : ∀ (n i : Nat) (r : List UInt8),
      bs.size - i = n →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro n
    induction n with
    | zero =>
      intro i r hi
      rw [ByteArray.toList.loop.eq_def]
      have hnlt : ¬ i < bs.size := by omega
      simp only [hnlt, if_false]
      have hdrop : bs.data.toList.drop i = [] := by
        apply List.drop_eq_nil_of_le
        rw [Array.length_toList]
        have : bs.data.size = bs.size := rfl
        omega
      rw [hdrop, List.append_nil]
    | succ n ih =>
      intro i r hi
      rw [ByteArray.toList.loop.eq_def]
      have hlt : i < bs.size := by omega
      simp only [hlt, if_true]
      rw [ih (i+1) (bs.get! i :: r) (by omega)]
      have hidx : i < bs.data.toList.length := by rw [Array.length_toList]; exact hlt
      have hsz : i < bs.data.size := by rw [← Array.length_toList]; exact hidx
      have hget : bs.get! i = bs.data.toList[i]'hidx := by
        rw [show bs.get! i = bs.data.get! i from rfl, Array.get!_eq_getElem!,
            getElem!_pos bs.data i hsz, ← Array.getElem_toList hsz]
      rw [List.drop_eq_getElem_cons hidx, List.reverse_cons, hget, List.append_assoc]
      rfl
  have h := key bs.size 0 [] (by omega)
  rw [ByteArray.toList]
  simpa using h

/-- The served path segments for `/static/app.js`. -/
def assetSegs : List String := ["static", "app.js"]

/-- The raw `Range: bytes=0-9` request header, exactly as it arrives on the wire
(header name + value bytes). -/
def rangeHeader : Bytes × Bytes := (strBytes "Range", strBytes "bytes=0-9")

/-! ## The deployed header parser turns the raw `Range:` bytes into a range-set -/

/-- **`range_header_parses`.** `reqOfHeaders`, the parser the deployed `serveDeployed`
runs over the raw request headers, maps the wire header `Range: bytes=0-9` to the model
range-set `[.fromTo 0 9]` and a matching single `range`. This is the running parse, not
a hand-supplied Req. -/
theorem range_header_parses :
    (reqOfHeaders [rangeHeader]).rangeSet = [RangeSpec.fromTo 0 9]
  ∧ (reqOfHeaders [rangeHeader]).range = some (RangeSpec.fromTo 0 9)
  ∧ (reqOfHeaders [rangeHeader]).ifNoneMatch = []
  ∧ (reqOfHeaders [rangeHeader]).ifRange = none := by
  -- OBSTRUCTION: `reqOfHeaders` runs the deployed header parser, which routes through
  -- `String.splitOn` / `String.toLower` / `bytesToStr` — all Lean-core well-founded
  -- recursions that do NOT reduce in the kernel. So `decide`/`rfl` get stuck here and
  -- `native_decide` (native compiler) is the only discharge. This adds `Lean.ofReduceBool`
  -- to this theorem AND to everything below that `rw`s through it (`range_selects`,
  -- `deployed_range_206`, `deployed_range_route`). See the lane report.
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## The deployed `206` -/

/-- `appJs` is 35 bytes long (the embedded `/static/app.js` content), so the range
`0-9` is satisfiable and the `Content-Range` completes to `/35`. -/
theorem appJs_len : appJs.length = 35 := by
  simp only [appJs, strBytes, ba_toList_eq]; decide

/-- The `bytes=0-9` spec resolves to the inclusive offsets `(0, 9)` on a 35-byte
representation (RFC 7233 §2.1). -/
theorem range_resolves : resolveAll appJs.length [RangeSpec.fromTo 0 9] = [(0, 9)] := by
  rw [appJs_len]; decide

/-- The `serveConditional` selection for the parsed range request over the deployed
config: a single-range `206`, body `slice appJs 0 9`, complete length `appJs.length`. -/
theorem range_selects :
    serveConditional deployedConfig (reqOfHeaders [rangeHeader]) assetSegs
      = .partialContent (slice appJs 0 9) 0 9 appJs.length (contentETag appJs) := by
  have hnm : ifNoneMatchHit (reqOfHeaders [rangeHeader]).ifNoneMatch
      (deployedConfig.etag assetSegs) = false := by
    rw [range_header_parses.2.2.1]; rfl
  refine serveConditional_single deployedConfig (reqOfHeaders [rangeHeader]) assetSegs
    appJs (RangeSpec.fromTo 0 9) [] 0 9 rfl hnm ?_ ?_ range_header_parses.1 range_resolves
  · rfl
  · rw [range_header_parses.2.2.2]; rfl

/-- **`deployed_range_206`.** The DEPLOYED handler answers `GET /static/app.js` with
`Range: bytes=0-9` by a `206 (Partial Content)` whose body is exactly the first ten
bytes `slice appJs 0 9`, carrying `Content-Range: bytes 0-9/35` and `Accept-Ranges:
bytes` — the exact `206` the curl above observes. -/
theorem deployed_range_206 :
    (serveDeployed assetSegs [rangeHeader]).status = 206
  ∧ (serveDeployed assetSegs [rangeHeader]).body = slice appJs 0 9
  ∧ (strBytes "Content-Range", strBytes "bytes 0-9/35")
        ∈ (serveDeployed assetSegs [rangeHeader]).headers
  ∧ (strBytes "Accept-Ranges", strBytes "bytes")
        ∈ (serveDeployed assetSegs [rangeHeader]).headers := by
  have hsel : serveDeployed assetSegs [rangeHeader]
      = toResponse (.partialContent (slice appJs 0 9) 0 9 appJs.length (contentETag appJs)) := by
    unfold serveDeployed; rw [range_selects]
  rw [hsel, appJs_len]
  -- The two membership goals reduce through `toResponse`'s `strBytes`/`toString` headers;
  -- but this theorem already depends on `range_selects → range_header_parses` (the
  -- `String.splitOn` obstruction above), so its axioms carry `Lean.ofReduceBool`
  -- regardless — `native_decide` here changes nothing about the axiom set.
  exact ⟨rfl, rfl, by native_decide, by native_decide⟩

/-- The deployed handler ties `serveDeployed` to the running staticFile route: for any
request whose normalized target is `/static/app.js` and whose headers are the single
`Range` header, the app's `staticFile` response IS this `206`. -/
theorem deployed_range_route (req : Proto.Request)
    (htarget : Reactor.App.targetSegments req.target = assetSegs)
    (hhdr : req.headers = [rangeHeader]) :
    (Reactor.App.responseOfReq req .staticFile).status = 206
  ∧ (Reactor.App.responseOfReq req .staticFile).body = slice appJs 0 9 := by
  rw [Proto.EtagProven.deployed_staticFile_route, htarget, hhdr]
  exact ⟨deployed_range_206.1, deployed_range_206.2.1⟩

/-! ## The exact deployed-wire bytes the curl carries -/

/-- **`range_body_bytes`.** The ten `206` body bytes are exactly `"console.lo"` — the
first ten octets of `console.log('drorb static asset');\n`. This is the curl body,
octet-for-octet, so the `206` proof is grounded on the real wire (non-vacuous). -/
theorem range_body_bytes :
    slice appJs 0 9 = [0x63, 0x6f, 0x6e, 0x73, 0x6f, 0x6c, 0x65, 0x2e, 0x6c, 0x6f] := by
  simp only [appJs, strBytes, slice, ba_toList_eq]; decide

end Proto.RangeProven

#print axioms Proto.RangeProven.range_header_parses
#print axioms Proto.RangeProven.range_selects
#print axioms Proto.RangeProven.deployed_range_206
#print axioms Proto.RangeProven.deployed_range_route
#print axioms Proto.RangeProven.range_body_bytes
