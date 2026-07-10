/-
# Proto.ServerHeaderProven — `Server: drorb` on the DEPLOYED serve, AND a real finding

PROVE-WHAT-RUNS for the `Server` header the running dataplane stamps on every response.
Curl-confirmed against the deployed `dataplane` binary:

    $ curl -s -D - -o /dev/null http://127.0.0.1:8097/static/app.js
    HTTP/1.1 200 OK
    …
    Server: drorb                                 ← proven here
    x-upstream: 1572395042
    x-corr: …

The deployed pipeline's `Reactor.Deploy.headerRewriteStage` applies the REAL `Header.run`
program `Reactor.Deploy.deployProg` (= `Reactor.Lifecycle.stdRewrite ++ [set upstream,
set corr]`) to the response headers: it strips the RFC 9110 §7.6.1 hop-by-hop set and
installs `Server: Reactor.Lifecycle.serverVal`, then sets `x-upstream` and `x-corr`. The
existing `Reactor.Deploy.deploy_keeps_server` proves the `Server` install SURVIVES those
two later sets. This file pins the emitted value to the wire bytes and records a finding.

Theorems:

  * `deployed_server_present` — for ANY plan/input/base-headers, a `Header.get Server` on
    the deployed rewrite's output is `some serverVal` (re-states `deploy_keeps_server`).
  * `server_name_wire_bytes` / `server_val_wire_bytes` — the header name is `"Server"` and
    the emitted value is exactly the 5 bytes of `"drorb"` (pinned via the `ba_toList_eq`
    bridge — pure-kernel `decide`, no `native_decide`), matching the curl `Server: drorb`.

## The finding: the terminal `headerStage` `Server: reactor` never reaches the wire

`Reactor.Stage.Header.headerStage` (the LAST entry of `deployStagesFull2`) ALSO sets a
`Server` header — but to a DIFFERENT value, `"reactor"`
(`Reactor.Stage.Header.serverVal`). By the pipeline's stage order, `headerRewriteStage`
(earlier in the list ⇒ its `onResponse` runs OUTERMOST, last) overwrites that with
`"drorb"`. So the `headerStage` `"reactor"` value is dead on the wire — the curl shows
`Server: drorb`, never `Server: reactor`.

  * `deployed_server_not_reactor` — `Reactor.Lifecycle.serverVal ≠
    Reactor.Stage.Header.serverVal`: the two deployed `Server`-setting stages disagree,
    and (per `deploy_keeps_server` + the wire) the `drorb` one wins.
-/

import Reactor.Deploy
import Reactor.Lifecycle
import Reactor.Stage.Header

namespace Proto.ServerHeaderProven

open Proto (Bytes)
open Reactor (RingSubmission)

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

/-! ## The deployed `Server` install survives the later stamps -/

/-- **`deployed_server_present`.** On the deployed header rewrite (`deployProg` =
`stdRewrite ++ [set upstream, set corr]`), a `Header.get Server` returns
`Reactor.Lifecycle.serverVal` for ANY DNS/proxy plan, any input bytes, any base headers —
the `Server` install is not clobbered by the two later sets. Re-states the deployed
`Reactor.Deploy.deploy_keeps_server`; this is the header the wire carries. -/
theorem deployed_server_present (plan : List RingSubmission) (input : Bytes)
    (h : Header.Headers) :
    Header.get Reactor.Lifecycle.serverName
        (Header.run (Reactor.Deploy.deployProg plan input) h)
      = some Reactor.Lifecycle.serverVal :=
  Reactor.Deploy.deploy_keeps_server plan input h

/-! ## The exact wire bytes -/

/-- **`server_name_wire_bytes`.** The deployed `Server` header name is the ASCII bytes of
`"Server"`. -/
theorem server_name_wire_bytes :
    Reactor.Lifecycle.serverName = [83, 101, 114, 118, 101, 114] := rfl

/-- **`server_val_wire_bytes`.** The value the deployed rewrite installs for `Server` is
exactly the 5 bytes of `"drorb"` — pinned to an explicit literal through the
`ba_toList_eq` bridge (pure-kernel `decide`, no `native_decide`), matching the curl
`Server: drorb`. -/
theorem server_val_wire_bytes :
    Reactor.Lifecycle.serverVal = [100, 114, 111, 114, 98] := by
  simp only [Reactor.Lifecycle.serverVal, ba_toList_eq]; decide

/-! ## THE FINDING — the terminal `headerStage` `Server: reactor` is dead on the wire -/

/-- **`deployed_server_not_reactor`.** The two `Server`-setting stages in
`deployStagesFull2` install DIFFERENT values: `Reactor.Lifecycle.serverVal` (`"drorb"`,
used by `headerRewriteStage`) versus `Reactor.Stage.Header.serverVal` (`"reactor"`, used
by the terminal `headerStage`). By the stage order `headerRewriteStage` runs outermost
and overwrites, so the wire carries `"drorb"` (`deployed_server_present` + curl) and the
`headerStage` `"reactor"` value never appears. Non-vacuous: the values are provably
distinct. -/
theorem deployed_server_not_reactor :
    Reactor.Lifecycle.serverVal ≠ Reactor.Stage.Header.serverVal := by
  rw [server_val_wire_bytes]
  simp only [Reactor.Stage.Header.serverVal]
  decide

end Proto.ServerHeaderProven

#print axioms Proto.ServerHeaderProven.deployed_server_present
#print axioms Proto.ServerHeaderProven.server_name_wire_bytes
#print axioms Proto.ServerHeaderProven.server_val_wire_bytes
#print axioms Proto.ServerHeaderProven.deployed_server_not_reactor
