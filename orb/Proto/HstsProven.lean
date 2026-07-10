/-
# Proto.HstsProven — `Strict-Transport-Security` (HSTS, RFC 6797) on the DEPLOYED serve

PROVE-WHAT-RUNS for the deployed `Strict-Transport-Security` response header. The
deployed `Reactor.Stage.SecurityHeaders.securityheadersStage` runs in the deployed
pipeline (`Reactor.Deploy.deployStagesFull2`, stage 13) and folds the REAL
`SecurityHeaders.render` set onto every response. Its lead member is HSTS: the
`Strict-Transport-Security` header whose value is produced by the real RFC-6797
`SecurityHeaders.hstsRender` for the deployed one-year/subdomains/preload policy.

The CURL that anchors this file (against the running `dataplane` serve):

    $ curl -s -D - -o /dev/null http://127.0.0.1:8099/static/app.js
    HTTP/1.1 200 OK
    …
    Strict-Transport-Security: max-age=31536000; includeSubDomains; preload
    …

Theorems (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound} — no `native_decide`,
no `Lean.ofReduceBool`):
  * `hsts_value_is_rfc6797` — the deployed wire value IS `SecurityHeaders.hstsRender`
    of the deployed policy (the real RFC-6797 renderer, NOT a hardcoded literal), and
    that render equals the exact directive string `max-age=31536000;
    includeSubDomains; preload`. Non-vacuity: the value flows from the real function.
  * `hsts_value_bytes` — that wire value, as the explicit 44 octets the curl carries
    (via the `ba_toList_eq` bridge — pure-kernel `decide`, no `native_decide`).
  * `deployed_hsts_present` — whenever the deployed security-header stage runs in the
    pipeline, the built response carries `(Strict-Transport-Security, <those bytes>)`
    for ANY tail/handler/ctx — the header the curl reads, lifted onto the real
    `runPipeline` output.
-/

import Reactor.Stage.SecurityHeaders

namespace Proto.HstsProven

open Reactor.Pipeline (Ctx Stage runPipeline)
open Reactor (Response)
open Reactor.Stage.SecurityHeaders
  (securityheadersStage hstsHeaderName hstsHeaderVal hstsPolicy securityheadersStage_hsts_present)

/-- Kernel-reducibility bridge for `toUTF8`-derived byte lists. `ByteArray.toList`
(Lean core) is defined by well-founded recursion (`termination_by bs.size - i`), so it
does NOT reduce in the kernel — which is what makes `"…".toUTF8.toList` opaque to
`decide`/`rfl`. This rewrites it to the structural `Array.toList` (`bs.data.toList`),
which the kernel DOES reduce, so the concrete byte witness closes by `decide` in the
pure kernel (`{propext, Quot.sound}`; no `native_decide`, no `Lean.ofReduceBool`). -/
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

/-- The exact 44 octets of `max-age=31536000; includeSubDomains; preload`. -/
def hstsValueBytes : Proto.Bytes :=
  [109,97,120,45,97,103,101,61,51,49,53,51,54,48,48,48,59,32,105,110,99,108,117,100,101,
   83,117,98,68,111,109,97,105,110,115,59,32,112,114,101,108,111,97,100]

/-- **`hsts_value_is_rfc6797`.** The deployed HSTS wire value is the byte encoding of
the REAL `SecurityHeaders.hstsRender` applied to the deployed policy — not a baked-in
literal — and that render is exactly `max-age=31536000; includeSubDomains; preload`
(one-year `max-age`, `includeSubDomains`, `preload`; RFC 6797 §6.1). -/
theorem hsts_value_is_rfc6797 :
    hstsHeaderVal = (SecurityHeaders.hstsRender hstsPolicy).toUTF8.toList
  ∧ SecurityHeaders.hstsRender hstsPolicy = "max-age=31536000; includeSubDomains; preload" :=
  ⟨rfl, rfl⟩

/-- **`hsts_value_bytes`.** The deployed `Strict-Transport-Security` value is exactly
the 44 octets the curl carries. `hstsHeaderVal` is `(hstsRender hstsPolicy).toUTF8.toList`;
the `ba_toList_eq` bridge makes the `toUTF8.toList` kernel-reduce, so this closes by pure
`decide` — no `native_decide`, no `Lean.ofReduceBool`. -/
theorem hsts_value_bytes : hstsHeaderVal = hstsValueBytes := by
  have h : hstsHeaderVal = "max-age=31536000; includeSubDomains; preload".toUTF8.toList := rfl
  rw [h, ba_toList_eq]; decide

/-- **`deployed_hsts_present`.** When the deployed security-header stage runs in the
pipeline, the BUILT response genuinely carries the `Strict-Transport-Security` header —
name AND the exact RFC-6797 value bytes — for ANY tail, handler and ctx. This lifts the
stage byte-effect `securityheadersStage_hsts_present` onto the real `runPipeline` output
and pins the value to the explicit curl octets. -/
theorem deployed_hsts_present (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (hstsHeaderName, hstsValueBytes)
      ∈ ((runPipeline (securityheadersStage :: rest) h c).build).headers := by
  rw [← hsts_value_bytes]
  exact securityheadersStage_hsts_present rest h c

end Proto.HstsProven

#print axioms Proto.HstsProven.hsts_value_is_rfc6797
#print axioms Proto.HstsProven.hsts_value_bytes
#print axioms Proto.HstsProven.deployed_hsts_present
