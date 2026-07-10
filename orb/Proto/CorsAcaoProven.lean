/-
# Proto.CorsAcaoProven — `Access-Control-Allow-Origin` on the DEPLOYED serve

PROVE-WHAT-RUNS for the CORS grant the running dataplane stamps when a request carries a
permitted `Origin`. The deployed `Reactor.Deploy.deployCorsStage` runs the REAL
`Cors.acaoValue` decision over the deployed `Reactor.Stage.Cors.corsPolicy` (one allowed
origin `https://app.example.com`, no wildcard, no credentials) on the request's canonical
lowercase `origin`, and — iff the origin is permitted — pushes `Access-Control-Allow-Origin`
onto the affine builder. Curl-confirmed against the deployed `dataplane` binary:

    $ curl -sS -i -H 'Origin: https://app.example.com' http://127.0.0.1:9147/
    HTTP/1.1 404 Not Found
    …
    Access-Control-Allow-Origin: https://app.example.com     ← proven here

    $ curl -sS -i -H 'Origin: https://evil.example.com' http://127.0.0.1:9147/
    HTTP/1.1 404 Not Found
    …
    (no Access-Control-Allow-Origin — the no-leak boundary)

The existing `Reactor.Deploy.full2_cors_acao_inner` proves the ACAO value lands in the
BUILT inner fold (`full2InnerStages` — the five deployed response transforms) whenever the
REAL `Cors.acaoValue` admits the request's origin. This file specializes it to the deployed
policy's concrete allowed origin, decides the real policy branch, and pins the wire name.

Theorems:

  * `cors_acao_value_deployed` — the REAL `Cors.acaoValue` on the deployed policy admits
    `https://app.example.com` and echoes it (no wildcard, no credentials) — pure-kernel
    `decide` over the genuine policy, NOT a stub.
  * `acao_name_wire_bytes` — the header name is exactly the 27 bytes of
    `"Access-Control-Allow-Origin"` (pure-kernel `decide` via the `ba_toList_eq` bridge,
    no `native_decide`, no `Lean.ofReduceBool`).
  * `deployed_cors_acao_present` — for ANY deployed ctx whose canonical `origin` is the
    permitted `https://app.example.com`, the `(Access-Control-Allow-Origin,
    https://app.example.com)` pair genuinely appears in the BUILT deployed inner fold
    (rides `full2_cors_acao_inner` + `cors_acao_value_deployed`).
-/

import Reactor.Deploy
import Reactor.Stage.Cors
import Cors

namespace Proto.CorsAcaoProven

open Proto (Bytes)
open Reactor.Pipeline (Ctx)

/-- Kernel-reducibility bridge for `toUTF8`-derived byte lists (see `Proto.GzipProven`):
`bs.toList = bs.data.toList`, letting `toUTF8` byte constants close by pure-kernel `decide`
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

/-- The deployed policy's single permitted origin. -/
def deployedOrigin : String := "https://app.example.com"

/-! ## The REAL policy admits the deployed origin -/

/-- **`cors_acao_value_deployed`.** The REAL `Cors.acaoValue` over the deployed
`Reactor.Stage.Cors.corsPolicy` admits the origin `https://app.example.com` and echoes it
back (the policy has no wildcard and no credentials, so the specific origin is emitted).
Pure-kernel `decide` over the genuine policy — a stub would not agree with the real
allowlist. -/
theorem cors_acao_value_deployed :
    Cors.acaoValue Reactor.Stage.Cors.corsPolicy deployedOrigin = some deployedOrigin := by
  decide

/-! ## The exact wire name -/

/-- **`acao_name_wire_bytes`.** The deployed CORS header name is exactly the 27 bytes of
`"Access-Control-Allow-Origin"` — pinned to an explicit literal through the `ba_toList_eq`
bridge (pure-kernel `decide`, no `native_decide`), matching the curl. -/
theorem acao_name_wire_bytes :
    Reactor.Stage.Cors.acaoName
      = [65, 99, 99, 101, 115, 115, 45, 67, 111, 110, 116, 114, 111, 108, 45,
         65, 108, 108, 111, 119, 45, 79, 114, 105, 103, 105, 110] := by
  simp only [Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes, ba_toList_eq]; decide

/-! ## The deployed byte-effect: ACAO reaches the BUILT deployed inner fold -/

/-- **`deployed_cors_acao_present`.** For any deployed ctx whose canonical lowercase
`origin` is the permitted `https://app.example.com`, the CORS grant fires and the
`(Access-Control-Allow-Origin, https://app.example.com)` pair genuinely appears in the
BUILT deployed inner fold (`full2InnerStages` — the five deployed response transforms the
outer header rewrite wraps). Rides `Reactor.Deploy.full2_cors_acao_inner` (the composed
deployed CORS byte-effect) fed by `cors_acao_value_deployed` (the real policy branch). The
outer deploy rewrite's only header drop is the hop-by-hop strip, which keeps this non-hop
field — curl-confirmed on the wire. -/
theorem deployed_cors_acao_present (c : Ctx)
    (horigin : Reactor.Deploy.corsOriginOf c = deployedOrigin) :
    (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes deployedOrigin)
      ∈ ((Reactor.Pipeline.runPipeline Reactor.Deploy.full2InnerStages
            Reactor.Deploy.appHandler c).build).headers := by
  apply Reactor.Deploy.full2_cors_acao_inner c deployedOrigin
  rw [horigin]
  exact cors_acao_value_deployed

end Proto.CorsAcaoProven

#print axioms Proto.CorsAcaoProven.cors_acao_value_deployed
#print axioms Proto.CorsAcaoProven.acao_name_wire_bytes
#print axioms Proto.CorsAcaoProven.deployed_cors_acao_present
