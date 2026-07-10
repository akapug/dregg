/-
# Proto.XFrameOptionsProven — `X-Frame-Options: DENY` on the DEPLOYED serve

PROVE-WHAT-RUNS for the clickjacking-protection header the running dataplane stamps on
every response. Curl-confirmed against the deployed `dataplane` binary (the wire dump
recorded in `Proto.OptionsProven`, re-run by the verifier):

    $ curl -sS -i http://127.0.0.1:9147/
    HTTP/1.1 404 Not Found
    …
    Strict-Transport-Security: max-age=31536000; includeSubDomains; preload
    X-Frame-Options: DENY                         ← proven here
    X-Content-Type-Options: nosniff
    Referrer-Policy: no-referrer
    …

The deployed pipeline's `Reactor.Stage.SecurityHeaders.securityheadersStage` folds the
REAL `SecurityHeaders.render` output for the deployed policy onto the response builder.
The deployed policy sets `xfo := some .deny`, so `render` emits
`("X-Frame-Options", "DENY")` — the RFC-defined directive (WHATWG / RFC 7034) that
forbids the response from being rendered inside a frame, defeating clickjacking.

The existing `securityheadersStage_hsts_present` proves the `Strict-Transport-Security`
member reaches the BUILT output, and `Proto.NoSniffProven` the `X-Content-Type-Options`
member; this file proves the same byte-effect for the `X-Frame-Options: DENY` member.

Theorems:

  * `xfo_in_render` / `xfo_in_wireHeaders` — `(X-Frame-Options, DENY)` is a member of the
    rendered / wire header set the deployed policy produces.
  * `securityheaders_xfo_present` — for ANY pipeline tail and handler, the
    `X-Frame-Options: DENY` header genuinely appears in the BUILT pipeline output of
    `securityheadersStage :: rest` (rides `securityheadersStage_effect` +
    `build_addHeaders`, exactly as the deployed HSTS / nosniff byte-effects do).
  * `xfo_wire_bytes` — the name/value are exactly the bytes of `"X-Frame-Options"` /
    `"DENY"` (pinned via the `ba_toList_eq` bridge — pure-kernel `decide`, no
    `native_decide`).
-/

import Reactor.Stage.SecurityHeaders
import SecurityHeaders

namespace Proto.XFrameOptionsProven

open Reactor.Pipeline
open Reactor.Stage.SecurityHeaders
open Proto (Bytes)

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

/-- The `X-Frame-Options` header name on the wire. -/
def xfoName : Bytes := "X-Frame-Options".toUTF8.toList

/-- The `DENY` header value on the wire. -/
def xfoVal : Bytes := "DENY".toUTF8.toList

/-! ## The `X-Frame-Options` member is in the rendered wire header set -/

/-- The deployed policy's rendered `SecurityHeaders` set contains the
`("X-Frame-Options", "DENY")` pair — the policy sets `xfo := some .deny`, so the
`render` disjunct fires and `xfoValue .deny` reduces to `"DENY"`. -/
theorem xfo_in_render :
    ("X-Frame-Options", "DENY") ∈ _root_.SecurityHeaders.render policy := by
  simp only [_root_.SecurityHeaders.render, policy, _root_.SecurityHeaders.xfoValue]
  simp

/-- **`xfo_in_wireHeaders`.** The wire header set the deployed policy renders contains
the `X-Frame-Options: DENY` pair (the `toWireHeader` image of the rendered member). -/
theorem xfo_in_wireHeaders :
    (xfoName, xfoVal) ∈ wireHeaders policy := by
  show (xfoName, xfoVal)
    ∈ (_root_.SecurityHeaders.render policy).map toWireHeader
  have : (xfoName, xfoVal) = toWireHeader ("X-Frame-Options", "DENY") := rfl
  rw [this]
  exact List.mem_map_of_mem _ xfo_in_render

/-! ## The deployed byte-effect: `X-Frame-Options` reaches the BUILT pipeline output -/

/-- **`securityheaders_xfo_present`.** The real `X-Frame-Options: DENY` header genuinely
appears in the BUILT pipeline output, for ANY tail and handler — a true byte-driver:
`build_addHeaders` carries the affine security-header fold into the finalized `Response`
the serializer renders. Mirrors the deployed HSTS / nosniff byte-effects; with
`rest = [Reactor.Stage.Header.headerStage]` this is exactly the deployed
`deployStagesFull2` tail (the terminal header rewrite strips only hop-by-hop fields, so
`X-Frame-Options` survives to the wire — curl-confirmed). -/
theorem securityheaders_xfo_present (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) :
    (xfoName, xfoVal)
      ∈ ((runPipeline (securityheadersStage :: rest) h c).build).headers := by
  rw [securityheadersStage_effect, build_addHeaders]
  exact List.mem_append.mpr (Or.inr xfo_in_wireHeaders)

/-! ## The exact wire bytes -/

/-- **`xfo_wire_bytes`.** The header name/value the deployed stage emits are exactly the
bytes of `"X-Frame-Options"` / `"DENY"` — pinned to explicit literals through the
`ba_toList_eq` bridge (pure-kernel `decide`, no `native_decide`), matching the curl
`X-Frame-Options: DENY`. -/
theorem xfo_wire_bytes :
    xfoName = [88, 45, 70, 114, 97, 109, 101, 45, 79, 112, 116, 105, 111, 110, 115]
  ∧ xfoVal = [68, 69, 78, 89] := by
  refine ⟨?_, ?_⟩ <;> simp only [xfoName, xfoVal, ba_toList_eq] <;> decide

end Proto.XFrameOptionsProven

#print axioms Proto.XFrameOptionsProven.xfo_in_render
#print axioms Proto.XFrameOptionsProven.xfo_in_wireHeaders
#print axioms Proto.XFrameOptionsProven.securityheaders_xfo_present
#print axioms Proto.XFrameOptionsProven.xfo_wire_bytes
