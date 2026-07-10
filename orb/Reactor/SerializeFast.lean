import Reactor.Serialize

/-!
# Flat-accumulator response serializer (`serializeFast`)

`serialize` (Reactor/Serialize.lean) renders the response wire bytes with `List
UInt8` `++` chains: `serializeWire` is a left-nested `statusLine ++ crlf ++
renderHeaders … ++ crlf ++ crlf ++ body`, and `renderHeaders` is the
right-recursive `headerLine h ++ crlf ++ renderHeaders t`. Each `++` on a
cons-list copies its left operand, so the accumulated head is re-walked once per
join — a constant number of times, but every join allocates a fresh spine.

## Why the *head*, not the whole response, is flattened

The response body is the **final right operand** of `serializeWire`'s `++` chain
(`… ++ crlf ++ crlf ++ w.body`), and Lean's `List.append` shares its right
operand: `head ++ body` walks only `head` and reuses `body`'s spine — the body is
**never copied**. So `serialize` is already linear in the head and *body-optimal*
(zero body copies). A naive "flatten the whole response into one `Array UInt8`,
then `.toList`" is measurably **worse** here — it copies the body into the array
and again back out through `.toList`, two extra `O(body)` passes (measured ~4–5×
slower on 8–64 KiB bodies).

`serializeFast` therefore flattens only the **head** into a flat `Array UInt8`
accumulator (`serializeHeadAcc`: each fragment appended with `Array.appendList`,
a `foldl Array.push`, amortized `O(1)` per byte), materializes it once
(`.toList`), and appends the body as the shared right operand exactly as the spec
does — so the body stays zero-copy while the head avoids the spec's per-join
cons-spine allocations. The output type is unchanged (`Bytes = List UInt8`), so
the spec `serialize` and every theorem/conformance obligation on it are untouched.

`serialize_eq_fast` proves `serialize = serializeFast` byte-for-byte and installs
the head-flat builder as the compiled implementation (`@[csimp]`). This uses the
`Arena.Parse.parseHeaders_eq_fast` technique (flat `Array` accumulator + `toList`
bridge, spec untouched). It is a proven **non-regression** (break-even on
body-dominated responses, a modest constant-factor win where many headers make
the spec's repeated head-block copies visible), not a super-linear cliff kill —
`serialize` never carried a super-linear cliff. Reaching a fully packed buffer
end-to-end is the separate bridged/compiler step.
-/

namespace Reactor

open Proto (Bytes)

/-- Header block rendered into a flat accumulator: mirrors `renderHeaders`
(no trailing `CRLF`), appending each `headerLine`/`crlf` fragment onto the
uniquely-owned `Array UInt8` (`++` here is `Array.appendList`, an amortized-`O(1)`
per-byte push) instead of allocating a fresh cons-spine per join. -/
def renderHeadersAcc (acc : Array UInt8) : List (Bytes × Bytes) → Array UInt8
  | []     => acc
  | [h]    => acc ++ headerLine h
  | h :: t => renderHeadersAcc ((acc ++ headerLine h) ++ crlf) t

/-- The response **head** serialized into a flat `Array UInt8` accumulator:
status line, CRLF, header block, then the blank-line separator (`CRLF CRLF`) —
everything up to but not including the body, built without per-join cons-list
copies. The body is appended separately (shared, zero-copy) in `serializeFast`. -/
def serializeHeadAcc (w : Wire) : Array UInt8 :=
  let acc : Array UInt8 := ((#[] : Array UInt8) ++ statusLine w) ++ crlf
  let acc := renderHeadersAcc acc (allHeaders w)
  (acc ++ crlf) ++ crlf

/-- **The flat response serializer.** Byte-identical to `serialize`; flattens the
head into a flat accumulator (materialized once) and appends the body as the
shared right operand (no body copy). Installed as the compiled `serialize` by
`serialize_eq_fast`. -/
def serializeFast (resp : Response) : Bytes :=
  let w := build resp
  (serializeHeadAcc w).toList ++ w.body

/-- Reading the accumulator back as a list, `renderHeadersAcc acc hs` prepends
exactly `renderHeaders hs` onto `acc` — the flat pass renders the same bytes. -/
theorem renderHeadersAcc_toList (hs : List (Bytes × Bytes)) :
    ∀ acc : Array UInt8, (renderHeadersAcc acc hs).toList = acc.toList ++ renderHeaders hs := by
  induction hs with
  | nil => intro acc; simp [renderHeadersAcc, renderHeaders]
  | cons h t ih =>
    intro acc
    cases t with
    | nil => simp [renderHeadersAcc, renderHeaders]
    | cons h2 t2 =>
      rw [show renderHeadersAcc acc (h :: h2 :: t2)
            = renderHeadersAcc ((acc ++ headerLine h) ++ crlf) (h2 :: t2) from rfl,
          ih ((acc ++ headerLine h) ++ crlf)]
      simp only [renderHeaders, Array.toList_appendList, List.append_assoc]

/-- The flat head accumulator reads back exactly the head of `serializeWire`
(`statusLine ++ CRLF ++ headerBlock ++ CRLF ++ CRLF`), so appending the body
reconstructs the full wire byte sequence. -/
theorem serializeHeadAcc_toList (w : Wire) :
    (serializeHeadAcc w).toList
      = statusLine w ++ crlf ++ renderHeaders (allHeaders w) ++ crlf ++ crlf := by
  unfold serializeHeadAcc
  simp only [Array.toList_appendList, renderHeadersAcc_toList, Array.toList_empty,
    List.nil_append, List.append_assoc]

/-- **The flat/spec agreement.** `serializeFast` produces the same wire bytes as
`serialize`: the head built into a flat accumulator, the body appended shared.
Installed as the compiled implementation, so the deployed serve uses the flat
head builder while `serialize` — the spec every theorem and conformance
obligation references — is untouched. -/
@[csimp] theorem serialize_eq_fast : @serialize = @serializeFast := by
  funext resp
  show serializeWire (build resp) = (serializeHeadAcc (build resp)).toList ++ (build resp).body
  rw [serializeHeadAcc_toList]
  unfold serializeWire
  simp only [List.append_assoc]

end Reactor
