import Reactor.Deploy

/-!
# Reactor.ObserveFast — a flat, linear-time runtime for the correlation-id
render on the deployed serve path (`@[csimp]`, spec untouched).

## The super-linear site

The deployed serve stamps an `x-corr` response header carrying the request's
correlation id (`Reactor.Deploy.corrVal`, run inside `deployProg` on every
served request — stage 8 of `deployStagesFull2`, hence on `servePipelineFull2`
and the exported `drorb_serve`). Under the deployed generator/trust
(`demoGen = id`, `demoTrust = false`) the assigned id is exactly the request's
seed — `Reactor.Observe.seedOf input = input.map UInt8.toNat` — so the id has
one entry **per request byte**. The id is rendered to bytes by

    corrBytes c = (String.intercalate "." (c.map toString)).toUTF8.toList

`seedOf` (`input.map UInt8.toNat`) and `c.map toString` are each a single `O(N)`
pass — linear, not the cliff. The cliff is `String.intercalate`: its accumulator
loop is `go (acc ++ sep ++ a)`, and each `String.append` copies the whole growing
`acc` (`lean_string_append` reallocates when the left string has no spare
capacity, which an exactly-sized intercalation accumulator never does). Over an
id of length `N` that is `O(N²)` in the request size — the measured
43→308→1076-byte serve-bench slope grows quadratically, on both the 200 and the
refused (404) arm (both run `deployProg`).

## The flat runtime

`corrStringFast` builds the identical dotted-decimal string in a single linear
construction: the digit char-lists of the parts, joined by `'.'` via one
right-associated `flatten` (each part's chars copied once ⇒ `O(N)`), packed to a
`String` once (`String.mk`). `corrBytesFast` is its `toUTF8.toList` — the SAME
tail as the spec, so the proof reuses it verbatim and never reasons about the
UTF-8 encoder or `ByteArray.toList`.

`corrBytes_eq_fast` proves `corrStringFast` produces the same `String` (`String`
equality via `.data`, established by the `String.intercalate.go` invariant
`interc_go_data`) and hence `corrBytesFast = corrBytes`; `@[csimp]` installs the
linear pass as the compiled implementation of `Reactor.Deploy.corrBytes`. Every
theorem about `corrBytes` / `corrVal` / `servePipelineFull2` keeps referring to
the unchanged spec — only the runtime changes, and the emitted `x-corr` bytes are
byte-identical (so the deterministic, observable corr-id value is preserved).

Axioms of the agreement theorem: `⊆ {propext, Quot.sound}`.
-/

namespace Reactor.ObserveFast

open Reactor.Deploy (corrBytes)

/-! ## String-level facts -/

/-- `String.append` is `List.append` on the underlying char lists. -/
private theorem append_data (a b : String) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

/-- **The `String.intercalate.go` invariant.** Threading accumulator `acc` and
separator `sep` over `parts`, the resulting string's char list is `acc`'s chars
followed by the flattened `sep ++ part` blocks — the exact shape the accumulator
loop `go (acc ++ sep ++ a)` produces. Proved by induction on `parts`; this is the
one lemma that opens the accumulator, so the quadratic `++` never appears in the
fast function. -/
private theorem interc_go_data (sep : String) :
    ∀ (parts : List String) (acc : String),
      (String.intercalate.go acc sep parts).data
        = acc.data ++ (parts.map (fun p => sep.data ++ p.data)).flatten := by
  intro parts
  induction parts with
  | nil => intro acc; simp [String.intercalate.go]
  | cons x xs ih =>
    intro acc
    rw [show String.intercalate.go acc sep (x :: xs)
          = String.intercalate.go (acc ++ sep ++ x) sep xs from rfl]
    rw [ih (acc ++ sep ++ x)]
    simp only [append_data, List.map_cons, List.flatten_cons, List.append_assoc]

/-! ## The flat correlation-id render -/

/-- **The linear dotted-decimal render, as a `String`.** The first part opens the
string; every subsequent part contributes a `'.'`-prefixed digit block, joined by
a single right-associated `flatten` (each block's chars copied once ⇒ `O(N)`),
then packed once by `String.mk`. No `String.append` accumulator — so no `O(N²)`
copy of a growing buffer. -/
def corrStringFast : List Nat → String
  | [] => ""
  | x :: xs =>
      String.mk ((toString x).data
        ++ (xs.map (fun n => ".".data ++ (toString n).data)).flatten)

/-- `corrStringFast` builds the SAME `String` as the spec's `String.intercalate`.
`String` equality via `.data` (structure eta on `String.mk`), closed by
`interc_go_data`. -/
theorem interc_eq_fast (c : List Nat) :
    String.intercalate "." (c.map toString) = corrStringFast c := by
  cases c with
  | nil => rfl
  | cons x xs =>
    have hgo : String.intercalate "." ((x :: xs).map toString)
        = String.intercalate.go (toString x) "." (xs.map toString) := rfl
    apply String.ext
    rw [hgo, interc_go_data, corrStringFast]
    simp only [List.map_map]
    rfl

/-- **The flat correlation-id render, as bytes.** The SAME `toUTF8.toList` tail as
`corrBytes`, over the linear `corrStringFast` — so the emitted `x-corr` bytes are
byte-identical while the runtime is `O(N)`. -/
def corrBytesFast (c : Trace.CorrId) : Proto.Bytes := (corrStringFast c).toUTF8.toList

/-- **The linear/spec agreement.** `corrBytesFast` computes exactly `corrBytes`,
in `O(N)` — installed as the compiled implementation of `Reactor.Deploy.corrBytes`
(`@[csimp]`). Every theorem about `corrBytes` / `corrVal` / the deployed serve
keeps referring to the unchanged spec; the `x-corr` header value on the wire is
unchanged. -/
@[csimp] theorem corrBytes_eq_fast : @corrBytes = @corrBytesFast := by
  funext c
  show Reactor.Deploy.corrBytes c = corrBytesFast c
  unfold Reactor.Deploy.corrBytes corrBytesFast
  rw [interc_eq_fast]

end Reactor.ObserveFast
