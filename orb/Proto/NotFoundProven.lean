/-
# Proto.NotFoundProven — the DEPLOYED default-route `404 Not Found`

PROVE-WHAT-RUNS for the routing **fall-through 404** the running dataplane returns for any
well-formed target that matches no author route. The deployed default serve routes every
request through `Reactor.App.handle Reactor.App.demoApp`: the author routes
(`/health`, `/static`, `/cgi-bin`) are tried by the real `Route.Match.bestMatch`, and an
unmatched-but-safe path falls to the host/glob default handler (`.hostGlob demoVhBlocks`),
whose `anyHost` block ends in a catch-all route `VHandler.respond 404 "not found"`. So a
`GET /nope` under a non-vhost authority is answered by that catch-all — a genuine
router decision, not a hardcoded status.

Curl-confirmed against the deployed `dataplane` binary (io_uring):

    $ printf 'GET / HTTP/1.1\r\nHost: x\r\n\r\n' | nc 127.0.0.1 8080 | head
    HTTP/1.1 404 Not Found          ← proven here (status line + reason)
    Connection: keep-alive
    Date: Mon, 01 Jan 2024 00:00:00 GMT
    …
    $ curl -s http://127.0.0.1:8080/nope        # body
    not found                       ← proven here (9 bytes → Content-Length: 9)

This maps ledger row **rt.1** (route table default `404` fall-through): the deployed status
line, reason phrase, and body of the default 404 were DEPLOYED-UNPROVEN — no theorem pinned
the router's own miss response to the wire bytes. This file pins them.

Theorems (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound} — no `native_decide`,
no `Lean.ofReduceBool`):

  * `deployed_default_404` — the whole deployed routing decision: for ANY request whose
    target normalizes to a single unmatched segment `["nope"]` under an authority that is
    neither exact vhost (any method / headers / query), `App.handle demoApp` returns the
    404 response `{status := 404, reason := reasonFor 404, headers := [], body := "not found"}`.
    Non-vacuous: it drives `bestMatch` → the host/glob default → `RouteAdvanced.dispatch`
    (`selectBlock` picks `anyHost`, then first-match routing falls past the glob and `/bulk`
    routes to the catch-all).
  * `nope_dispatches` — a concrete `GET /nope` routed request whose REAL `dispatch` reaches
    the catch-all 404 route, so the 404 branch is genuinely reachable (non-vacuity).
  * `reasonFor_404_wire_bytes` — the deployed reason phrase is exactly the 9 bytes of
    `"Not Found"` (pinned via `ba_toList_eq`), matching the curl `404 Not Found`.
  * `notfound_body_wire_bytes` — the deployed 404 body is exactly the 9 bytes of
    `"not found"` (⇒ `Content-Length: 9`, curl-confirmed).
  * `deployed_404_status_line` — the full serialized status LINE of the 404 response is
    exactly the bytes of `"HTTP/1.1 404 Not Found"`.
-/

import Reactor.App
import Reactor.Serialize

namespace Proto.NotFoundProven

open Proto (Bytes)
open Reactor.App
open RouteAdvanced (dispatch catchAllRoute)

/-- Kernel-reducibility bridge for `toUTF8`-derived byte lists (see `Proto.GzipProven`):
`bs.toList = bs.data.toList`, letting `toUTF8` byte constants close by pure-kernel
`decide` (`{propext, Quot.sound}`; no `native_decide`, no `Lean.ofReduceBool`). -/
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

/-! ## The deployed routing decision: an unmatched safe path 404s -/

/-- **`deployed_default_404`.** The whole deployed routing decision for a well-formed target
that matches no author route: `bestMatch` falls through the author routes to the host/glob
default, `RouteAdvanced.selectBlock` picks the `anyHost` block
(`demoVhBlocks_selectBlock_anyHost` — NOT pinned to `localhost`), and its first-matching
route is the catch-all (the glob `/health/assets/**` and `/bulk` routes both miss a single
`["nope"]` segment), so `vhandlerResponse` builds the `404`. Mirrors the deployed `/bulk`
result (`bulk_serves_large_body_any`) on the 404 branch. -/
theorem deployed_default_404 (req : Proto.Request)
    (htarget : targetSegments req.target = ["nope"])
    (hna : hostLabelsOf req ≠ ["a", "example"])
    (hnb : hostLabelsOf req ≠ ["b", "example"]) :
    handle demoApp req
      = { status := 404, reason := reasonFor 404, headers := [],
          body := "not found".toUTF8.toList } := by
  have hseg : (hostReqOf req).segs = ["nope"] := by unfold hostReqOf; exact htarget
  have hb : dispatch demoVhBlocks (hostReqOf req)
      = some (catchAllRoute (VHandler.respond 404 "not found".toUTF8.toList)) := by
    unfold RouteAdvanced.dispatch RouteAdvanced.routeMatches
    rw [demoVhBlocks_selectBlock_anyHost req hna hnb, hseg]
    rfl
  unfold handle
  rw [htarget]
  show (match dispatch demoVhBlocks (hostReqOf req) with
        | some rt => vhandlerResponse req rt.handler
        | none => vhandlerResponse req (VHandler.respond 404 "not found".toUTF8.toList)) = _
  rw [hb]
  show vhandlerResponse req (VHandler.respond 404 "not found".toUTF8.toList) = _
  rfl

/-! ## A concrete witness — the catch-all is genuinely reached (non-vacuity) -/

/-- A concrete routed `GET /nope` request under the plaintext listener's `localhost`
authority — the `RouteAdvanced.Req` shape `hostReqOf` builds for the curl above (a single
unmatched path segment). Built directly, mirroring `Reactor.App.bulkReq`. -/
def nopeReq : RouteAdvanced.Req :=
  { host := ["localhost"], method := "GET", segs := ["nope"], headers := [], query := [] }

/-- **`nope_dispatches`.** The REAL `RouteAdvanced.dispatch` over the deployed `demoVhBlocks`
— the exact matcher the deployed default handler runs — selects the CATCH-ALL route for a
`GET /nope` under a non-vhost authority: `selectBlock` picks `anyHost`, then first-match
routing falls past the `/health/assets/**` glob and the `/bulk` route to the catch-all. This
discharges the non-vacuity of `deployed_default_404` — the 404 branch is genuinely reachable
by concrete dispatch (mirrors `Reactor.App.bulk_dispatches`). -/
theorem nope_dispatches :
    dispatch demoVhBlocks nopeReq
      = some (catchAllRoute (VHandler.respond 404 "not found".toUTF8.toList)) := rfl

/-! ## The exact wire bytes -/

/-- **`reasonFor_404_wire_bytes`.** The deployed reason phrase for `404` is exactly the 9
bytes of `"Not Found"` — pinned through the `ba_toList_eq` bridge (pure-kernel `decide`, no
`native_decide`), matching the curl `HTTP/1.1 404 Not Found`. -/
theorem reasonFor_404_wire_bytes :
    reasonFor 404 = [78, 111, 116, 32, 70, 111, 117, 110, 100] := by
  simp only [reasonFor, ba_toList_eq]; decide

/-- **`notfound_body_wire_bytes`.** The deployed 404 body is exactly the 9 bytes of
`"not found"` — so the serializer frames `Content-Length: 9` (curl-confirmed). -/
theorem notfound_body_wire_bytes :
    ("not found".toUTF8.toList : Bytes) = [110, 111, 116, 32, 102, 111, 117, 110, 100] := by
  simp only [ba_toList_eq]; decide

/-- **`deployed_404_status_line`.** The full serialized status LINE of the deployed 404
response (`Reactor.statusLine` over the built wire record) is exactly the bytes of
`"HTTP/1.1 404 Not Found"`: the fixed `HTTP/1.1` version token, the `404` status rendered by
`natToDec`, and the `"Not Found"` reason. -/
theorem deployed_404_status_line :
    Reactor.statusLineOf
        { status := 404, reason := reasonFor 404, headers := [],
          body := "not found".toUTF8.toList }
      = [72, 84, 84, 80, 47, 49, 46, 49, 32, 52, 48, 52, 32,
         78, 111, 116, 32, 70, 111, 117, 110, 100] := by
  simp only [Reactor.statusLineOf, Reactor.statusLine, Reactor.build, Reactor.http11,
             Reactor.natToDec, reasonFor, ba_toList_eq]
  decide

end Proto.NotFoundProven

#print axioms Proto.NotFoundProven.deployed_default_404
#print axioms Proto.NotFoundProven.nope_dispatches
#print axioms Proto.NotFoundProven.reasonFor_404_wire_bytes
#print axioms Proto.NotFoundProven.notfound_body_wire_bytes
#print axioms Proto.NotFoundProven.deployed_404_status_line
