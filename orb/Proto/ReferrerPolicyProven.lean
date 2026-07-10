/-
# Proto.ReferrerPolicyProven — `Referrer-Policy: no-referrer` on the DEPLOYED serve

PROVE-WHAT-RUNS for the referrer-leak-protection header the running dataplane stamps on
every response. Curl-confirmed against the deployed `dataplane` binary (the wire dump
recorded in `Proto.OptionsProven`, re-run by the verifier):

    $ curl -sS -i http://127.0.0.1:9147/
    HTTP/1.1 404 Not Found
    …
    X-Frame-Options: DENY
    X-Content-Type-Options: nosniff
    Referrer-Policy: no-referrer                  ← proven here
    …

The deployed pipeline's `Reactor.Stage.SecurityHeaders.securityheadersStage` folds the
REAL `SecurityHeaders.render` output for the deployed policy onto the response builder.
The deployed policy sets `referrerPolicy := some "no-referrer"`, so `render` emits
`("Referrer-Policy", "no-referrer")` — the WHATWG Referrer-Policy directive that
suppresses the `Referer` request header on outbound navigations, so no URL of this
origin leaks to third parties.

The existing `securityheadersStage_hsts_present` proves the `Strict-Transport-Security`
member reaches the BUILT output, `Proto.NoSniffProven` the `X-Content-Type-Options`
member, and `Proto.XFrameOptionsProven` the `X-Frame-Options` member; this file proves
the same byte-effect for the `Referrer-Policy: no-referrer` member.

Theorems:

  * `referrer_in_render` / `referrer_in_wireHeaders` — `(Referrer-Policy, no-referrer)` is
    a member of the rendered / wire header set the deployed policy produces.
  * `securityheaders_referrer_present` — for ANY pipeline tail and handler, the
    `Referrer-Policy: no-referrer` header genuinely appears in the BUILT pipeline output
    of `securityheadersStage :: rest` (rides `securityheadersStage_effect` +
    `build_addHeaders`, exactly as the deployed HSTS / nosniff / X-Frame byte-effects do).
  * `referrer_wire_bytes` — the name/value are exactly the bytes of `"Referrer-Policy"` /
    `"no-referrer"` (pinned via the `ba_toList_eq` bridge — pure-kernel `decide`, no
    `native_decide`).
-/

import Reactor.Stage.SecurityHeaders
import SecurityHeaders

namespace Proto.ReferrerPolicyProven

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

/-- The `Referrer-Policy` header name on the wire. -/
def referrerName : Bytes := "Referrer-Policy".toUTF8.toList

/-- The `no-referrer` header value on the wire. -/
def referrerVal : Bytes := "no-referrer".toUTF8.toList

/-! ## The `Referrer-Policy` member is in the rendered wire header set -/

/-- The deployed policy's rendered `SecurityHeaders` set contains the
`("Referrer-Policy", "no-referrer")` pair — the policy sets
`referrerPolicy := some "no-referrer"`, so the `render` disjunct fires. -/
theorem referrer_in_render :
    ("Referrer-Policy", "no-referrer") ∈ _root_.SecurityHeaders.render policy := by
  simp only [_root_.SecurityHeaders.render, policy]
  simp

/-- **`referrer_in_wireHeaders`.** The wire header set the deployed policy renders
contains the `Referrer-Policy: no-referrer` pair (the `toWireHeader` image of the
rendered member). -/
theorem referrer_in_wireHeaders :
    (referrerName, referrerVal) ∈ wireHeaders policy := by
  show (referrerName, referrerVal)
    ∈ (_root_.SecurityHeaders.render policy).map toWireHeader
  have : (referrerName, referrerVal) = toWireHeader ("Referrer-Policy", "no-referrer") := rfl
  rw [this]
  exact List.mem_map_of_mem _ referrer_in_render

/-! ## The deployed byte-effect: `Referrer-Policy` reaches the BUILT pipeline output -/

/-- **`securityheaders_referrer_present`.** The real `Referrer-Policy: no-referrer` header
genuinely appears in the BUILT pipeline output, for ANY tail and handler — a true
byte-driver: `build_addHeaders` carries the affine security-header fold into the
finalized `Response` the serializer renders. Mirrors the deployed HSTS / nosniff /
X-Frame byte-effects; with `rest = [Reactor.Stage.Header.headerStage]` this is exactly
the deployed `deployStagesFull2` tail (the terminal header rewrite strips only
hop-by-hop fields, so `Referrer-Policy` survives to the wire — curl-confirmed). -/
theorem securityheaders_referrer_present (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) :
    (referrerName, referrerVal)
      ∈ ((runPipeline (securityheadersStage :: rest) h c).build).headers := by
  rw [securityheadersStage_effect, build_addHeaders]
  exact List.mem_append.mpr (Or.inr referrer_in_wireHeaders)

/-! ## The exact wire bytes -/

/-- **`referrer_wire_bytes`.** The header name/value the deployed stage emits are exactly
the bytes of `"Referrer-Policy"` / `"no-referrer"` — pinned to explicit literals through
the `ba_toList_eq` bridge (pure-kernel `decide`, no `native_decide`), matching the curl
`Referrer-Policy: no-referrer`. -/
theorem referrer_wire_bytes :
    referrerName = [82, 101, 102, 101, 114, 114, 101, 114, 45, 80, 111, 108, 105, 99, 121]
  ∧ referrerVal = [110, 111, 45, 114, 101, 102, 101, 114, 114, 101, 114] := by
  refine ⟨?_, ?_⟩ <;> simp only [referrerName, referrerVal, ba_toList_eq] <;> decide

end Proto.ReferrerPolicyProven

#print axioms Proto.ReferrerPolicyProven.referrer_in_render
#print axioms Proto.ReferrerPolicyProven.referrer_in_wireHeaders
#print axioms Proto.ReferrerPolicyProven.securityheaders_referrer_present
#print axioms Proto.ReferrerPolicyProven.referrer_wire_bytes
