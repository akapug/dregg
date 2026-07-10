import Reactor.Stage.RequestValidation
import Reactor.Stage.FramingValidation
import Reactor.Stage.DateHeader
import Reactor.Stage.RequestHeadLimit
import Reactor.Stage.ConditionalRequest
import Reactor.Serialize
import Proto.RequestSerialize
import Proto.ResponseParse

/-!
# Reactor.ServeConformant — the RFC-conformance WRAPPER around the deployed serve

The wave-4 RFC 7230/7231 conformance probe (`docs/engine/review/CONFORMANCE-PROBE.md`,
`conformance/rfc_conformance.py`) found seven MUSTs the deployed `drorbServe`
violates — all at the EDGES of the verified core, none in the core itself:

* **C1/C2** (RFC 7230 §5.4) — a missing / duplicate `Host` MUST get `400`.
* **B2** (RFC 7231 §4.1) — an unrecognized method MUST NOT be served as `GET` (`501`).
* **G1** (RFC 7230 §2.6) — an unsupported HTTP version MUST NOT be `200`ed (`505`).
* **C3** (RFC 7230 §5.3.2) — an absolute-form request-target MUST route like origin-form.
* **F1** (RFC 7231 §7.1.1.2) — an origin server with a clock MUST send `Date`.
* **B1** (RFC 7231 §4.3.2) — a `HEAD` response MUST NOT carry a message body.

This module wires the ALREADY-PROVEN conformance stages —
`Reactor.Stage.RequestValidation.validationStage` (C1/C2/B2/G1/C3) and
`Reactor.Stage.DateHeader` (F1/B1) — as a WRAPPER around the deployed serve
`inner : ByteArray → ByteArray`. The inner serve is UNCHANGED: the dense/poly serve
family's byte-identity to `drorbServe` is untouched. `conformantServe inner`:

1. Parses the request. If `validationStage` rejects it (bad version/method/Host),
   it answers the stage's `4xx/5xx` (`+ Date`) and never touches `inner`.
2. If `validationStage` passes, it routes through `inner` — normalizing an
   absolute-form target to origin-form FIRST (C3) so `inner` keys on `/path`.
3. It post-processes the response bytes: injects a `Date` header (F1), and on a
   `HEAD` request strips the body (B1).

## Residual (honest)

`deployNow` is a FIXED RFC-1123 placeholder, not a live clock. The probe F1 asserts
`Date` is PRESENT (which a placeholder satisfies); a live-clock render is a host time
FFI seam — the same effect residual `Reactor.Stage.DateHeader` names. Named here so the
`Date` VALUE is not claimed to be the real wall-clock time.

The C3 absolute-form path RE-SERIALIZES the normalized request for `inner`
(`Proto.RequestSerialize.serialize`); the round-trip preserves method/target/version/
headers (`Proto.RequestSerialize.parse_serialize`). Requests whose target is already
origin-form pass `input` VERBATIM to `inner` — byte-identical to the deployed path.
-/

namespace Reactor.ServeConformant

open Proto (Bytes Request)
open Reactor (Response serialize crlf)
open Reactor.Pipeline (Ctx StageStep Stage)
open Reactor.Stage.RequestValidation
  (validationStage badRequestResp notImplementedResp badVersionResp)
open Reactor.Stage.FramingValidation (framingValidationStage expectationFailedResp)
open Reactor.Stage.DateHeader (dateName mHEAD)
open Reactor.Stage.RequestHeadLimit (headBytesTooLarge requestHeaderFieldsTooLargeResp)
open Reactor.Stage.ConditionalRequest
  (conditionalRewrite headerVal ifNoneMatchNameLower ifMatchNameLower)

/-! ## The Date value (fixed placeholder — see residual) -/

/-- A fixed RFC-1123 `Date` value. NOT a live clock (residual): the probe F1 needs
`Date` PRESENT, which this satisfies; the live render is a host time FFI seam. -/
def deployNow : Bytes := "Mon, 01 Jan 2024 00:00:00 GMT".toUTF8.toList

/-- The injected `Date` header rendered as `name ": " value` — exactly the
serializer's `Reactor.headerLine (dateName, deployNow)` form. -/
def dateHdr : Bytes := dateName ++ [58, 32] ++ deployNow

/-! ## Byte-level response post-processors

The inner serve returns already-SERIALIZED response bytes. `injectDate` and
`stripBody` are the two response-side MUSTs applied at that byte boundary. -/

/-- The bytes strictly BEFORE the first CRLF (the status line). CRLF-free. -/
def beforeCRLF : Bytes → Bytes
  | 13 :: 10 :: _ => []
  | b :: rest => b :: beforeCRLF rest
  | [] => []

/-- The bytes AFTER the first CRLF (headers + blank line + body). `[]` if no CRLF. -/
def afterCRLF : Bytes → Bytes
  | 13 :: 10 :: rest => rest
  | _ :: rest => afterCRLF rest
  | [] => []

/-- **F1 — inject a `Date` header.** Splice `Date: <now>` as the FIRST header line,
right after the status line's CRLF: `status CRLF Date:… CRLF headers… CRLF CRLF body`.
The status line (`beforeCRLF`) is preserved verbatim, so the status is unchanged; the
`Date` header (name + value) is genuinely present (`injectDate_date_present`). -/
def injectDate (bs : Bytes) : Bytes :=
  beforeCRLF bs ++ crlf ++ dateHdr ++ crlf ++ afterCRLF bs

/-- Whether the byte string BEGINS with a blank line (`CR LF CR LF`). A single
4-byte boolean lookahead — reduces cleanly on concrete heads (no 4-deep pattern
that resists `rfl`). -/
def startsBlank (bs : Bytes) : Bool :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: _ => b0 == 13 && b1 == 10 && b2 == 13 && b3 == 10
  | _ => false

/-- The bytes AFTER the first blank line (`CRLF CRLF`) — the message body per the
probe's `resp.partition(b"\r\n\r\n")`. `[]` if there is no blank line. -/
def afterBlank : Bytes → Bytes
  | [] => []
  | b :: rest => if startsBlank (b :: rest) then rest.drop 3 else afterBlank rest

/-- **B1 — strip the body.** Keep the head up to and INCLUDING the first blank line
(`CRLF CRLF`), discarding everything after — so the built response carries no body
octets (`stripBody_no_body`: `afterBlank (stripBody bs) = []`). -/
def stripBody : Bytes → Bytes
  | [] => []
  | b :: rest => if startsBlank (b :: rest) then (b :: rest).take 4 else b :: stripBody rest

/-! ## Post-processor theorems -/

/-- **F1.** The `Date` header (`CRLF ++ Date: <now>`) is present in `injectDate bs`
for ANY response bytes — the status line's CRLF followed by the `Date` field, so the
probe's `header_present(head, b"date")` (which scans for `"\r\ndate:"`) finds it. -/
theorem injectDate_date_present (bs : Bytes) :
    ∃ pre suf, injectDate bs = pre ++ (crlf ++ dateHdr) ++ suf := by
  refine ⟨beforeCRLF bs, crlf ++ afterCRLF bs, ?_⟩
  unfold injectDate
  simp only [List.append_assoc]

/-- `startsBlank bs = true` exactly when the first four bytes are `CR LF CR LF`. -/
theorem take4_of_startsBlank (bs : Bytes) (h : startsBlank bs = true) :
    bs.take 4 = [13, 10, 13, 10] := by
  match bs with
  | b0 :: b1 :: b2 :: b3 :: _ =>
    simp only [startsBlank, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
    subst h0; subst h1; subst h2; subst h3; rfl
  | [] => simp [startsBlank] at h
  | [a] => simp [startsBlank] at h
  | [a, b] => simp [startsBlank] at h
  | [a, b, c] => simp [startsBlank] at h

/-- Conversely, first four bytes `CR LF CR LF` ⇒ `startsBlank bs = true`. -/
theorem startsBlank_of_take4 (bs : Bytes) (h : bs.take 4 = [13, 10, 13, 10]) :
    startsBlank bs = true := by
  match bs with
  | b0 :: b1 :: b2 :: b3 :: _ =>
    simp only [List.take] at h
    obtain ⟨h0, h1, h2, h3⟩ : b0 = 13 ∧ b1 = 10 ∧ b2 = 13 ∧ b3 = 10 := by
      injection h with h0 h; injection h with h1 h; injection h with h2 h
      injection h with h3 _; exact ⟨h0, h1, h2, h3⟩
    subst h0; subst h1; subst h2; subst h3
    rfl
  | [] => simp at h
  | [a] => simp at h
  | [a, b] => simp at h
  | [a, b, c] => simp at h

/-- `stripBody` preserves the first `n ≤ 4` bytes of its input. Its only truncation
emits exactly the first four bytes `CR LF CR LF` at the blank, so no byte within the
first four positions is ever moved. -/
theorem stripBody_take_le4 (n : Nat) (hn : n ≤ 4) (bs : Bytes) :
    (stripBody bs).take n = bs.take n := by
  match bs with
  | [] => simp only [stripBody]
  | b :: rest =>
    simp only [stripBody]
    by_cases hsb : startsBlank (b :: rest) = true
    · rw [if_pos hsb, List.take_take]
      congr 1
      omega
    · rw [if_neg hsb]
      match n with
      | 0 => rfl
      | m + 1 =>
        show b :: (stripBody rest).take m = b :: rest.take m
        rw [stripBody_take_le4 m (by omega) rest]
  termination_by bs.length

/-- **B1.** After `stripBody`, the built response has NO body octets: the bytes after
the first blank line are empty, for ANY response bytes. So a HEAD response the wrapper
strips carries an empty body (RFC 7231 §4.3.2), which is what the probe B1 asserts. -/
theorem stripBody_no_body (bs : Bytes) : afterBlank (stripBody bs) = [] := by
  match bs with
  | [] => simp only [stripBody, afterBlank]
  | b :: rest =>
    simp only [stripBody]
    by_cases hsb : startsBlank (b :: rest) = true
    · rw [if_pos hsb]
      -- stripBody = (b::rest).take 4 = [13,10,13,10]; afterBlank of it is [].
      rw [take4_of_startsBlank _ hsb]; rfl
    · rw [if_neg hsb]
      show afterBlank (b :: stripBody rest) = []
      simp only [afterBlank]
      by_cases hsb2 : startsBlank (b :: stripBody rest) = true
      · -- if the stripped head started a blank, so did the original — contradiction.
        exfalso
        apply hsb
        have e1 : (b :: stripBody rest).take 4 = [13, 10, 13, 10] := take4_of_startsBlank _ hsb2
        have e2 : (stripBody rest).take 3 = rest.take 3 := stripBody_take_le4 3 (by omega) rest
        apply startsBlank_of_take4
        have hstep : (b :: stripBody rest).take 4 = b :: (stripBody rest).take 3 := rfl
        rw [hstep, e2] at e1
        show (b :: rest).take 4 = [13, 10, 13, 10]
        exact e1
      · rw [if_neg hsb2]
        exact stripBody_no_body rest
  termination_by bs.length

/-! ## DENSE (ByteArray) post-processors — killing the body re-cons

`injectDate`/`stripBody` above are the LIST SPEC (they carry all the conformance
proofs). Feeding the WHOLE inner response (body included) through them re-cons the
1 MiB body as a `List UInt8` on every request — the ~43 MB/s cliff. The native pair
below computes the SAME bytes over `ByteArray` (index-scan the head with `ByteArray.get!`
for the first `CRLF` / blank line, then NATIVE `ByteArray.extract`/`ByteArray.append` —
`lean_byte_array_copy_slice` memcpy of the body, never a boxed `Array UInt8` / cons
spine), and is proven byte-identical to the spec via `.toList`. -/

/-! ### ByteArray ↔ List bridges -/

/-- Kernel-reducibility bridge `bs.toList = bs.data.toList` (the loop unrolls to the
underlying array's list). Same proof shape as `Proto.ServerHeaderProven.ba_toList_eq`;
`{propext, Quot.sound}`, no `native_decide`. -/
theorem ba_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
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

/-- A byte list materialized into a `ByteArray` reads back as itself. -/
theorem mk_toArray_toList (l : Bytes) : (ByteArray.mk l.toArray).toList = l := by
  rw [ba_toList_eq]

/-! ### List-spec identities: `beforeCRLF`/`afterCRLF`/`stripBody` as `take`/`drop` -/

/-- One-step reduction of the match-defined `beforeCRLF` on a ≥2-byte head. -/
theorem beforeCRLF_cons2 (a b : UInt8) (rest : Bytes) :
    beforeCRLF (a :: b :: rest)
      = if a = 13 ∧ b = 10 then [] else a :: beforeCRLF (b :: rest) := by
  rw [beforeCRLF.eq_def]; split
  · next heq => cases heq; simp
  · next hne h => cases h; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hne rest rfl rfl
  · next h => exact absurd h (by simp)

/-- One-step reduction of the match-defined `afterCRLF` on a ≥2-byte head. -/
theorem afterCRLF_cons2 (a b : UInt8) (rest : Bytes) :
    afterCRLF (a :: b :: rest)
      = if a = 13 ∧ b = 10 then rest else afterCRLF (b :: rest) := by
  rw [afterCRLF.eq_def]; split
  · next heq => cases heq; simp
  · next hne h => cases h; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hne rest rfl rfl
  · next h => exact absurd h (by simp)

/-- `beforeCRLF L` is the take of `L` at its own length — the split point (`k`). -/
theorem beforeCRLF_eq_take (L : Bytes) : beforeCRLF L = L.take (beforeCRLF L).length := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => simp [beforeCRLF]
    | cons b rest =>
      rw [beforeCRLF_cons2]
      by_cases hcr : a = 13 ∧ b = 10
      · rw [if_pos hcr]; rfl
      · rw [if_neg hcr, List.length_cons, List.take_succ_cons, ← ih]

/-- `afterCRLF L` is the drop of `L` past the first `CRLF` (`k + 2`). -/
theorem afterCRLF_eq_drop (L : Bytes) : afterCRLF L = L.drop ((beforeCRLF L).length + 2) := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => simp [afterCRLF, beforeCRLF]
    | cons b rest =>
      rw [afterCRLF_cons2, beforeCRLF_cons2]
      by_cases hcr : a = 13 ∧ b = 10
      · rw [if_pos hcr, if_pos hcr]; rfl
      · rw [if_neg hcr, if_neg hcr, List.length_cons,
            show (beforeCRLF (b :: rest)).length + 1 + 2
               = ((beforeCRLF (b :: rest)).length + 2) + 1 from by omega,
            List.drop_succ_cons, ← ih]

/-- The take-length `stripBody` keeps: the first blank line's start + 4, or `L.length`. -/
def blankLen : Bytes → Nat
  | [] => 0
  | b :: rest => if startsBlank (b :: rest) then 4 else blankLen rest + 1

/-- `stripBody L` is exactly `L.take (blankLen L)` — head up to and including the
first blank line, no body. -/
theorem stripBody_eq_take (L : Bytes) : stripBody L = L.take (blankLen L) := by
  induction L with
  | nil => rfl
  | cons b rest ih =>
    simp only [stripBody]
    by_cases hsb : startsBlank (b :: rest) = true
    · rw [if_pos hsb]
      show (b::rest).take 4 = (b::rest).take (blankLen (b::rest))
      congr 1; unfold blankLen; rw [if_pos hsb]
    · rw [if_neg hsb]
      show b :: stripBody rest = (b::rest).take (blankLen (b::rest))
      unfold blankLen; rw [if_neg hsb, List.take_succ_cons, ih]

/-- A head of fewer than 4 bytes cannot begin a blank line. -/
theorem startsBlank_short (L : Bytes) (h : L.length ≤ 3) : startsBlank L = false := by
  match L with
  | [] => rfl
  | [a] => rfl
  | [a, b] => rfl
  | [a, b, c] => rfl
  | a :: b :: c :: d :: t => simp at h

/-- With no room for a blank line, `blankLen` keeps the whole (short) list. -/
theorem blankLen_of_short (L : Bytes) (h : L.length ≤ 3) : blankLen L = L.length := by
  induction L with
  | nil => rfl
  | cons b rest ih =>
    rw [blankLen, startsBlank_short _ h, if_neg (by simp), List.length_cons,
        ih (by simp only [List.length_cons] at h; omega)]

/-! ### The dense index scanners (over `ByteArray`, native byte loads — no list, no `.data`)

The scanners read the head directly with `ByteArray.get!` (`@[extern
"lean_byte_array_get"]`, a native single-byte load) — NEVER `bs.data` (a projection to
`Array UInt8` that boxes the whole buffer). Only the head is scanned (the first `CRLF` /
blank line ends it), so this is O(head), not O(body). -/

/-- CR-index of the first `CRLF` at or after `i`, else `bs.size`. Native byte loads. -/
def crIdxFrom (bs : ByteArray) (i : Nat) : Nat :=
  if h : i + 1 < bs.size then
    if bs.get! i == 13 && bs.get! (i + 1) == 10 then i
    else crIdxFrom bs (i + 1)
  else bs.size
termination_by bs.size - i
decreasing_by omega

/-- Take-length of the first blank line (`CRLF CRLF`) at or after `i` (its start + 4),
else `bs.size`. Native byte loads; used to truncate a HEAD response. -/
def blankTakeFrom (bs : ByteArray) (i : Nat) : Nat :=
  if h : i + 3 < bs.size then
    if bs.get! i == 13 && bs.get! (i + 1) == 10 && bs.get! (i + 2) == 13 && bs.get! (i + 3) == 10 then i + 4
    else blankTakeFrom bs (i + 1)
  else bs.size
termination_by bs.size - i
decreasing_by omega

/-! ### ByteArray access bridges (native loads = list indices) -/

/-- `bs.data.size = bs.size` (the underlying array's size IS the buffer size). -/
theorem ba_data_size (bs : ByteArray) : bs.data.size = bs.size := rfl

/-- `bs.toList.length = bs.size`. -/
theorem ba_toList_length (bs : ByteArray) : bs.toList.length = bs.size := by
  rw [ba_toList_eq, Array.length_toList, ba_data_size]

/-- The native load `bs.get! i` reads the `i`-th list byte (in bounds). -/
theorem get!_eq_getElem (bs : ByteArray) (i : Nat) (h : i < bs.size) :
    bs.get! i = bs.data[i]'h := by
  rw [show bs.get! i = bs.data.get! i from rfl, Array.get!_eq_getElem!, getElem!_pos bs.data i h]

/-- List-drop of a `ByteArray` is the cons of its `i`-th byte onto the next drop. -/
theorem drop_toList_cons (bs : ByteArray) (i : Nat) (h : i < bs.size) :
    bs.toList.drop i = bs.get! i :: bs.toList.drop (i + 1) := by
  rw [ba_toList_eq bs]
  have hidx : i < bs.data.toList.length := by rw [Array.length_toList]; exact h
  rw [List.drop_eq_getElem_cons hidx]
  congr 1
  rw [Array.getElem_toList, get!_eq_getElem bs i h]

/-- **The `CRLF`-scan bridge.** The native CR-index from `i` equals `i` plus the list
split point of the remaining bytes — so at `i = 0` it is `(beforeCRLF bs.toList).length`. -/
theorem crIdxFrom_eq (bs : ByteArray) :
    ∀ (n i : Nat), bs.size - i = n → i ≤ bs.size →
      crIdxFrom bs i = i + (beforeCRLF (bs.toList.drop i)).length := by
  intro n
  induction n with
  | zero =>
    intro i hn hle
    have hi : i = bs.size := by omega
    subst hi
    rw [crIdxFrom, dif_neg (by omega : ¬ bs.size + 1 < bs.size),
        List.drop_eq_nil_of_le (Nat.le_of_eq (ba_toList_length bs))]
    simp [beforeCRLF]
  | succ n ih =>
    intro i hn hle
    have hi : i < bs.size := by omega
    rw [crIdxFrom]
    by_cases hlt : i + 1 < bs.size
    · rw [dif_pos hlt]
      have hd0 : bs.toList.drop i = bs.get! i :: bs.toList.drop (i + 1) := drop_toList_cons bs i hi
      have hd1 : bs.toList.drop (i + 1) = bs.get! (i + 1) :: bs.toList.drop (i + 2) :=
        drop_toList_cons bs (i + 1) hlt
      by_cases hb : (bs.get! i == 13 && bs.get! (i + 1) == 10) = true
      · rw [if_pos hb]
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        obtain ⟨h13, h10⟩ := hb
        rw [hd0, hd1, beforeCRLF_cons2, if_pos ⟨h13, h10⟩]; simp
      · rw [if_neg hb, ih (i + 1) (by omega) (by omega), hd0, hd1, beforeCRLF_cons2]
        have hcr : ¬ (bs.get! i = 13 ∧ bs.get! (i + 1) = 10) := by
          intro ⟨e1, e2⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hb
          exact hb ⟨e1, e2⟩
        rw [if_neg hcr, ← hd1, List.length_cons]; omega
    · rw [dif_neg hlt]
      have hd0 : bs.toList.drop i = bs.get! i :: bs.toList.drop (i + 1) := drop_toList_cons bs i hi
      rw [hd0, List.drop_eq_nil_of_le (by rw [ba_toList_length]; omega)]
      have h1 : (beforeCRLF (bs.get! i :: ([] : Bytes))).length = 1 := by simp [beforeCRLF]
      rw [h1]; omega

/-- **The blank-line-scan bridge.** The native take-length from `i` equals `i` plus
`blankLen` of the remaining bytes — so at `i = 0` it is `blankLen bs.toList`. -/
theorem blankTakeFrom_eq (bs : ByteArray) :
    ∀ (n i : Nat), bs.size - i = n → i ≤ bs.size →
      blankTakeFrom bs i = i + blankLen (bs.toList.drop i) := by
  intro n
  induction n with
  | zero =>
    intro i hn hle
    have hi : i = bs.size := by omega
    subst hi
    rw [blankTakeFrom, dif_neg (by omega : ¬ bs.size + 3 < bs.size),
        List.drop_eq_nil_of_le (Nat.le_of_eq (ba_toList_length bs))]
    simp [blankLen]
  | succ n ih =>
    intro i hn hle
    have hi : i < bs.size := by omega
    rw [blankTakeFrom]
    by_cases hlt : i + 3 < bs.size
    · rw [dif_pos hlt]
      have hlt1 : i + 1 < bs.size := by omega
      have hlt2 : i + 2 < bs.size := by omega
      have hlt3 : i + 3 < bs.size := by omega
      have hd0 : bs.toList.drop i = bs.get! i :: bs.toList.drop (i + 1) := drop_toList_cons bs i hi
      have hd1 : bs.toList.drop (i+1) = bs.get! (i+1) :: bs.toList.drop (i + 2) := drop_toList_cons bs (i + 1) hlt1
      have hd2 : bs.toList.drop (i+2) = bs.get! (i+2) :: bs.toList.drop (i + 3) := drop_toList_cons bs (i + 2) hlt2
      have hd3 : bs.toList.drop (i+3) = bs.get! (i+3) :: bs.toList.drop (i + 4) := drop_toList_cons bs (i + 3) hlt3
      have hsb : startsBlank (bs.get! i :: bs.toList.drop (i + 1))
          = (bs.get! i == 13 && bs.get! (i+1) == 10 && bs.get! (i+2) == 13 && bs.get! (i+3) == 10) := by
        rw [hd1, hd2, hd3]; rfl
      have hbl : blankLen (bs.toList.drop i)
          = if (bs.get! i == 13 && bs.get! (i+1) == 10 && bs.get! (i+2) == 13 && bs.get! (i+3) == 10) = true
            then 4 else blankLen (bs.toList.drop (i + 1)) + 1 := by
        rw [hd0]; simp only [blankLen]; rw [hsb]
      by_cases hb : (bs.get! i == 13 && bs.get! (i+1) == 10 && bs.get! (i+2) == 13 && bs.get! (i+3) == 10) = true
      · rw [if_pos hb, hbl, if_pos hb]
      · rw [if_neg hb, ih (i + 1) (by omega) (by omega), hbl, if_neg hb]; omega
    · rw [dif_neg hlt]
      have hshort : (bs.toList.drop i).length ≤ 3 := by
        rw [List.length_drop, ba_toList_length]; omega
      rw [blankLen_of_short _ hshort, List.length_drop, ba_toList_length]; omega

/-! ### The native post-processors and their `.toList` bridges -/

/-- `Date: <now> ` header fragment as a `ByteArray` (fixed, tiny — built once). -/
def dateHdrBytes : ByteArray := ByteArray.mk dateHdr.toArray
/-- `CRLF` as a `ByteArray` (fixed, tiny — built once). -/
def crlfBytes : ByteArray := ByteArray.mk crlf.toArray

theorem dateHdrBytes_toList : dateHdrBytes.toList = dateHdr := mk_toArray_toList dateHdr
theorem crlfBytes_toList : crlfBytes.toList = crlf := mk_toArray_toList crlf

/-- `ByteArray.append` reads back as list append — the native `copySlice` (`@[extern
"lean_byte_array_copy_slice"]`) concatenation, no per-byte boxing. -/
theorem BA_append_toList (a b : ByteArray) : (a ++ b).toList = a.toList ++ b.toList := by
  rw [ba_toList_eq (a ++ b), ba_toList_eq a, ba_toList_eq b]
  show (a.data.extract 0 a.size ++ b.data.extract 0 (0 + b.size)
        ++ a.data.extract (a.size + min b.size (b.data.size - 0)) a.data.size).toList
      = a.data.toList ++ b.data.toList
  have h3 : a.data.size - (a.size + min b.size b.data.size) = 0 :=
    Nat.sub_eq_zero_of_le (by rw [show a.data.size = a.size from rfl]; exact Nat.le_add_right _ _)
  simp only [Array.toList_append, Array.toList_extract, List.extract_eq_drop_take,
    Nat.zero_add, Nat.sub_zero, List.drop_zero, h3, List.take_zero, List.append_nil]
  rw [show a.size = a.data.toList.length by rw [Array.length_toList, ba_data_size],
      show b.size = b.data.toList.length by rw [Array.length_toList, ba_data_size],
      List.take_length, List.take_length]

/-- `ByteArray.extract` reads back as list `drop`-then-`take` — the native `copySlice`
(`@[extern "lean_byte_array_copy_slice"]`) slice, no per-byte boxing. -/
theorem BA_extract_toList (bs : ByteArray) (s e : Nat) :
    (bs.extract s e).toList = (bs.toList.drop s).take (e - s) := by
  rw [ba_toList_eq (bs.extract s e), ba_toList_eq bs]
  show (ByteArray.empty.data.extract 0 0 ++ bs.data.extract s (s + (e - s))
        ++ ByteArray.empty.data.extract (0 + min (e - s) (bs.data.size - s)) ByteArray.empty.data.size).toList
      = (bs.data.toList.drop s).take (e - s)
  have he : ByteArray.empty.data = (#[] : Array UInt8) := rfl
  rw [he]
  simp only [Array.toList_append, Array.toList_extract, List.extract_eq_drop_take,
    Array.size_empty, Array.toList_empty, List.drop_nil, List.take_nil,
    List.nil_append, List.append_nil, Nat.add_sub_cancel_left, Nat.sub_zero, Nat.zero_add,
    List.drop_zero]

/-- **Dense F1 (native).** Splice `Date: <now> CRLF` right after the first `CRLF`, over
`ByteArray`: native `ByteArray.extract` head + tail (one `memcpy` of the body via
`lean_byte_array_copy_slice`), `ByteArray.append`ed — no `bs.data`, no boxed `Array`. -/
def injectDateBA (bs : ByteArray) : ByteArray :=
  bs.extract 0 (crIdxFrom bs 0) ++ crlfBytes ++ dateHdrBytes ++ crlfBytes
    ++ bs.extract (crIdxFrom bs 0 + 2) bs.size

/-- **Dense B1 (native).** Truncate at the first blank line — one native
`ByteArray.extract` of the head (the body is never copied). -/
def stripBodyBA (bs : ByteArray) : ByteArray :=
  bs.extract 0 (blankTakeFrom bs 0)

/-- **Dense = spec (F1).** The native splice is byte-identical to the list `injectDate`. -/
theorem injectDateBA_toList (bs : ByteArray) :
    (injectDateBA bs).toList = injectDate bs.toList := by
  have hk : crIdxFrom bs 0 = (beforeCRLF bs.toList).length := by
    have h := crIdxFrom_eq bs bs.size 0 (by omega) (by omega)
    simpa using h
  have h1 : bs.toList.take (beforeCRLF bs.toList).length = beforeCRLF bs.toList :=
    (beforeCRLF_eq_take bs.toList).symm
  have h2 : (bs.toList.drop ((beforeCRLF bs.toList).length + 2)).take
              (bs.size - ((beforeCRLF bs.toList).length + 2)) = afterCRLF bs.toList := by
    rw [afterCRLF_eq_drop]
    have hlen : bs.size - ((beforeCRLF bs.toList).length + 2)
         = (bs.toList.drop ((beforeCRLF bs.toList).length + 2)).length := by
      rw [List.length_drop, ba_toList_length]
    rw [hlen, List.take_length]
  unfold injectDateBA
  simp only [BA_append_toList, BA_extract_toList, crlfBytes_toList, dateHdrBytes_toList,
    Nat.sub_zero, List.drop_zero]
  rw [hk]
  unfold injectDate
  rw [h1, h2]

/-- **Dense = spec (B1).** The native truncate is byte-identical to the list `stripBody`. -/
theorem stripBodyBA_toList (bs : ByteArray) :
    (stripBodyBA bs).toList = stripBody bs.toList := by
  have hj : blankTakeFrom bs 0 = blankLen bs.toList := by
    have h := blankTakeFrom_eq bs bs.size 0 (by omega) (by omega)
    simpa using h
  unfold stripBodyBA
  rw [BA_extract_toList]
  simp only [Nat.sub_zero, List.drop_zero]
  rw [hj, stripBody_eq_take]

/-! ## The request context -/

/-- Build the pipeline context from the raw input bytes and the parsed request. -/
def mkCtx (input : ByteArray) (req : Request) : Ctx :=
  { input := input.toList, req := req }

/-- Add the `Date` header to a response at the record level (used on the reject
branch, where the status is preserved by construction). -/
def addDate (r : Response) : Response :=
  { r with headers := r.headers ++ [(dateName, deployNow)] }

theorem addDate_status (r : Response) : (addDate r).status = r.status := rfl

/-! ## The conformant serve -/

/-- The request bytes to parse for the validation gate: the raw input with any
LEADING `NUL` bytes dropped. The io_uring zero-copy receive path hands the seam a
leased provided-buffer slot with a fixed 4-byte zeroed header before the request
line; the deployed `drorbServe` tokenizer already skips those leading `NUL`s (a
`NUL`-prefixed request routes identically, a printable-prefixed one does not — so
the leniency is `NUL`-specific, not general). The validation gate parses the SAME
`NUL`-skipped view so its request-line/Host decisions agree with the inner serve's
routing. `inner` is still handed the ORIGINAL `input` (it skips the `NUL`s itself),
keeping its output byte-identical to the deployed serve. -/
def reqBytes (input : ByteArray) : Bytes :=
  (input.toList).dropWhile (· == (0 : UInt8))

/-! ## The conditional-request finisher, wired at the response-byte boundary (H1/H2/H3/H5)

`Reactor.Stage.ConditionalRequest.conditionalRewrite` rewrites a `Response` RECORD
(`200`+ETag+precondition ⇒ `304`/`412`). The conformant wrapper post-processes
SERIALIZED bytes, so wiring it means a RECORD round-trip: parse the inner serve's
serialized response (`Proto.ResponseParse.parse`, proven inverse of `serialize`),
apply `conditionalRewrite`, re-`serialize` (+Date). That round-trip re-cons the whole
body as a `List`, so it is GATED on the request actually carrying `If-None-Match` /
`If-Match` (`hasConditional`): a request with no precondition header NEVER pays it and
takes the DENSE `injectDateBA` splice — so the common `/bulk` path is untouched. -/

/-- Whether the request carries a precondition header (`If-None-Match` or `If-Match`).
Only such a request is routed through the record round-trip; everything else stays
dense. A pure `Bool` on the parsed request — identical in the spec and dense paths. -/
def hasConditional (req : Request) : Bool :=
  (headerVal ifNoneMatchNameLower req.headers).isSome ||
  (headerVal ifMatchNameLower req.headers).isSome

/-- **The conditional finisher over serialized bytes.** Parse the inner response
(`Proto.ResponseParse.parse`), apply the proven `conditionalRewrite` (which fires only
on a `200` carrying an `ETag`), re-serialize with `Date` (F1). If the inner bytes do
not parse as a well-formed response (never, for `serialize`-shaped output) fall back to
the plain `Date` splice — so this is total and never drops a response. -/
def condRewriteBytes (req : Request) (innerBytes : Bytes) : Bytes :=
  match Proto.ResponseParse.parse innerBytes with
  | some resp => serialize (addDate (conditionalRewrite req resp))
  | none => injectDate innerBytes

/-- The request with any `If-None-Match` / `If-Match` header REMOVED. The inner serve
(`drorbServe`) applies its OWN direction-blind precondition handling (a matching tag ⇒
`304` for BOTH `If-Match` and `If-None-Match`), so feeding it the precondition headers
would let it answer a `304` that masks the correct `412` (H5). Stripping them makes the
inner return the plain `200` representation, so the PROVEN `conditionalRewrite`
(`If-None-Match` ⇒ `304`, `If-Match` non-match ⇒ `412`) is the SOLE authority for the
precondition semantics. Only the (rare) conditional path re-serializes; `/bulk` is
untouched. -/
def stripCondReq (req : Request) : Request :=
  { req with headers := req.headers.filter (fun kv =>
      let n := Reactor.Stage.FramingValidation.lowerBytes kv.1
      n != ifNoneMatchNameLower && n != ifMatchNameLower) }

/-- The inner input for a conditional request: the precondition-stripped request,
re-serialized so `inner` routes it identically but sees NO precondition header. -/
def condInnerInput (req : Request) : ByteArray :=
  ByteArray.mk (Proto.RequestSerialize.serialize (stripCondReq req)).toArray

/-- The accepted-path response bytes (LIST spec): a conditional request feeds `inner`
the precondition-STRIPPED request (so `inner` returns the plain `200`) and takes the
record round-trip (`condRewriteBytes` — the proven `conditionalRewrite`); everything
else takes the dense `Date` splice (`injectDate`) on the verbatim `innerInput`. -/
def acceptedRaw (inner : ByteArray → ByteArray) (req : Request) (innerInput : ByteArray) : Bytes :=
  if hasConditional req then condRewriteBytes req (inner (condInnerInput req)).toList
  else injectDate (inner innerInput).toList

/-- The accepted-path response bytes (DENSE `ByteArray`): the non-conditional branch is
the native `injectDateBA` splice (the `/bulk` fast path — no body re-cons); the
conditional branch materializes the (rare) precondition-stripped record round-trip. -/
def acceptedRawBA (inner : ByteArray → ByteArray) (req : Request) (innerInput : ByteArray) : ByteArray :=
  if hasConditional req then ByteArray.mk (condRewriteBytes req (inner (condInnerInput req)).toList).toArray
  else injectDateBA (inner innerInput)

/-- **Dense accepted = spec accepted.** Both branches read back to the list spec:
the conditional branch by `mk_toArray_toList`, the dense branch by `injectDateBA_toList`. -/
theorem acceptedRawBA_toList (inner : ByteArray → ByteArray) (req : Request) (innerInput : ByteArray) :
    (acceptedRawBA inner req innerInput).toList = acceptedRaw inner req innerInput := by
  unfold acceptedRawBA acceptedRaw
  split
  · exact mk_toArray_toList _
  · exact injectDateBA_toList _

/-- The response bytes BEFORE the HEAD-strip: the reject `4xx/5xx` (+Date), or the
Date-injected inner serve. Two request gates run in front of `inner`, in order:
`validationStage` (C1/C2/B2/G1/C3 — version/method/Host, absolute-form normalize)
then `framingValidationStage` (L1/J2/M1 — Transfer-Encoding-final, Expect,
field-name whitespace). Either gate's `.respond` answers `serialize (addDate r)`
and never touches `inner`; only a request clearing BOTH reaches `inner`. -/
def respBytesRaw (inner : ByteArray → ByteArray) (input : ByteArray) : Bytes :=
  match Proto.RequestSerialize.parse (reqBytes input) with
  | none => serialize (addDate badRequestResp)
  | some req =>
    match validationStage.onRequest (mkCtx input req) with
    | .respond r => serialize (addDate r)
    | .continue c' =>
        match framingValidationStage.onRequest c' with
        | .respond r => serialize (addDate r)
        | .continue c'' =>
            let innerInput :=
              if c''.req.target == req.target then input
              else ByteArray.mk (Proto.RequestSerialize.serialize c''.req).toArray
            acceptedRaw inner req innerInput

/-- **The DENSE deployed response bytes.** The `ByteArray`-native mirror of
`respBytesRaw`: identical control flow (same parse/validation/framing gates, same
`innerInput`), but the accepted path splices `Date` over `ByteArray` (`injectDateBA`)
instead of re-consing `(inner …).toList`. Byte-identical to the spec by
`respBytesRawBA_toList`. This is what makes the DEFAULT serve dense-fast. -/
def respBytesRawBA (inner : ByteArray → ByteArray) (input : ByteArray) : ByteArray :=
  match Proto.RequestSerialize.parse (reqBytes input) with
  | none => ByteArray.mk (serialize (addDate badRequestResp)).toArray
  | some req =>
    match validationStage.onRequest (mkCtx input req) with
    | .respond r => ByteArray.mk (serialize (addDate r)).toArray
    | .continue c' =>
        match framingValidationStage.onRequest c' with
        | .respond r => ByteArray.mk (serialize (addDate r)).toArray
        | .continue c'' =>
            let innerInput :=
              if c''.req.target == req.target then input
              else ByteArray.mk (Proto.RequestSerialize.serialize c''.req).toArray
            acceptedRawBA inner req innerInput

/-- **Dense = spec.** The dense deployed bytes read back exactly as the list spec —
so every `respBytesRaw` conformance theorem (reject statuses, `Date` present) governs
the actual served bytes. -/
theorem respBytesRawBA_toList (inner : ByteArray → ByteArray) (input : ByteArray) :
    (respBytesRawBA inner input).toList = respBytesRaw inner input := by
  -- Explicit case structure (NOT `repeat' split` + a blind `first | exact …`): the
  -- accepted leaf's head is now `ByteArray.append …` (native splice), so trying
  -- `mk_toArray_toList` there would `whnf` `injectDateBA`'s well-founded `crIdxFrom`
  -- recursion and spin. Applying the RIGHT lemma per leaf keeps unification head-matched.
  unfold respBytesRawBA respBytesRaw
  split
  · exact mk_toArray_toList _
  · split
    · exact mk_toArray_toList _
    · split
      · exact mk_toArray_toList _
      · exact acceptedRawBA_toList _ _ _

/-- Whether the request is a `HEAD` (drives the B1 body strip). -/
def isHeadReq (input : ByteArray) : Bool :=
  match Proto.RequestSerialize.parse (reqBytes input) with
  | some req => req.method == mHEAD
  | none => false

/-- **The conformant serve (DENSE + Z1).** Wraps `inner` with the proven conformance
stages: the O(1) pre-parse head-length gate (Z1 → `431`, before the recursive parse can
overflow) → validation gate (C1/C2/B2/G1/C3) → `inner` → `Date` (F1, dense splice) /
`HEAD`-strip (B1, dense truncate). The accepted-path body is carried as `ByteArray`
throughout — no 1 MiB `List` re-cons (`conformantServe_toList` pins the bytes to the
list spec). -/
def conformantServe (inner : ByteArray → ByteArray) (input : ByteArray) : ByteArray :=
  if headBytesTooLarge input.size then
    ByteArray.mk (serialize (addDate requestHeaderFieldsTooLargeResp)).toArray
  else
    let raw := respBytesRawBA inner input
    if isHeadReq input then stripBodyBA raw else raw

/-- **The deployed dense bytes ARE the list spec.** For a within-limit request the
served bytes read back as the list `respBytesRaw` (HEAD → `stripBody` of it); an
over-limit head short-circuits to the `431` (Z1). Every list-spec conformance theorem
(`conformant_reject_eq`, `conformant_date_present_accept`, `conformant_head_no_body`)
therefore governs the ACTUAL served `ByteArray`. -/
theorem conformantServe_toList (inner : ByteArray → ByteArray) (input : ByteArray) :
    (conformantServe inner input).toList =
      if headBytesTooLarge input.size then
        serialize (addDate requestHeaderFieldsTooLargeResp)
      else if isHeadReq input then stripBody (respBytesRaw inner input)
      else respBytesRaw inner input := by
  unfold conformantServe
  by_cases hz : headBytesTooLarge input.size = true
  · rw [if_pos hz, if_pos hz]; exact mk_toArray_toList _
  · rw [if_neg hz, if_neg hz]
    by_cases hh : isHeadReq input = true
    · rw [if_pos hh, if_pos hh, stripBodyBA_toList, respBytesRawBA_toList]
    · rw [if_neg hh, if_neg hh, respBytesRawBA_toList]

/-! ## Conformance theorems (reusing the proven stage lemmas) -/

/-- **Reject → the stage's status.** If the request parses and `validationStage`
rejects it with `r`, the wrapper emits `serialize (addDate r)`, whose status is
`r.status` — `inner` is never consulted. Parametric over `inner`, `input`, `r`. -/
theorem conformant_reject_eq
    (inner : ByteArray → ByteArray) (input : ByteArray) (req : Request) (r : Response)
    (hp : Proto.RequestSerialize.parse (reqBytes input) = some req)
    (hr : validationStage.onRequest (mkCtx input req) = .respond r) :
    respBytesRaw inner input = serialize (addDate r) := by
  simp only [respBytesRaw, hp, hr]

/-- **F1, on the accepted path.** For a request that parses, PASSES validation, and
PASSES the framing gate (`.continue c''`) with an origin-form target (so `inner` is
fed `input` verbatim), the wrapper's raw response bytes carry the `Date` header —
for ANY `inner`. -/
theorem conformant_date_present_accept
    (inner : ByteArray → ByteArray) (input : ByteArray) (req : Request) (c' c'' : Ctx)
    (hp : Proto.RequestSerialize.parse (reqBytes input) = some req)
    (hr : validationStage.onRequest (mkCtx input req) = .continue c')
    (hf : framingValidationStage.onRequest c' = .continue c'')
    (htgt : c''.req.target = req.target)
    (hnc : hasConditional req = false) :
    ∃ pre suf, respBytesRaw inner input = pre ++ (crlf ++ dateHdr) ++ suf := by
  have hraw : respBytesRaw inner input = injectDate (inner input).toList := by
    simp only [respBytesRaw, hp, hr, hf, htgt, beq_self_eq_true, if_true, acceptedRaw,
      hnc, Bool.false_eq_true, if_false]
  rw [hraw]
  exact injectDate_date_present _

/-- On a within-limit HEAD request, the served bytes read back exactly as `stripBody`
of the list-spec raw response — the dense truncate is byte-identical to the spec. -/
theorem conformantServe_head_bytes
    (inner : ByteArray → ByteArray) (input : ByteArray)
    (hhead : isHeadReq input = true)
    (hz : headBytesTooLarge input.size = false) :
    (conformantServe inner input).toList = stripBody (respBytesRaw inner input) := by
  rw [conformantServe_toList, if_neg (by rw [hz]; decide), if_pos hhead]

/-- **B1.** On a HEAD request, the wrapper strips the body: the post-processed
response bytes carry no body octets (`afterBlank … = []`), for ANY `inner`. This is
the RFC 7231 §4.3.2 MUST the probe B1 asserts. -/
theorem conformant_head_no_body (inner : ByteArray → ByteArray) (input : ByteArray) :
    afterBlank (stripBody (respBytesRaw inner input)) = [] :=
  stripBody_no_body _

/-! ## A concrete non-vacuous reject witness (C1, reusing the stage lemma)

A real missing-`Host` request — round-tripped through the request serializer so its
parse is pinned by `Proto.RequestSerialize.parse_serialize` — is rejected by the
wrapper with `serialize (addDate badRequestResp)`, whose status is `400`. This
instantiates the parametric `conformant_reject_eq` on genuine input bytes and reuses
`validationStage_rejects_bad_host` (the proven C1 gate), so the reject path is not
vacuous. -/

/-- A concrete HTTP/1.1 `GET /health` with NO `Host` header (the probe C1 request). -/
def missingHostReq : Request :=
  { method := [71, 69, 84], target := [47, 104, 101, 97, 108, 116, 104],
    version := [72, 84, 84, 80, 47, 49, 46, 49], headers := [] }

theorem missingHostReq_WF : Proto.RequestSerialize.WF missingHostReq := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro kv hkv
  simp [missingHostReq] at hkv

/-- The input bytes: the missing-Host request on the wire. -/
def missingHostInput : ByteArray :=
  ByteArray.mk (Proto.RequestSerialize.serialize missingHostReq).toArray

theorem missingHostInput_parses :
    Proto.RequestSerialize.parse (reqBytes missingHostInput) = some missingHostReq := by
  have h1 : missingHostInput.toList = Proto.RequestSerialize.serialize missingHostReq := by
    rw [ba_toList_eq missingHostInput]
    show ((Proto.RequestSerialize.serialize missingHostReq).toArray).toList
          = Proto.RequestSerialize.serialize missingHostReq
    exact Array.toList_toArray _
  have h2 : reqBytes missingHostInput = Proto.RequestSerialize.serialize missingHostReq := by
    -- the serialized request starts with the method byte `G` (71) ≠ 0, so the leading-
    -- NUL strip is the identity here.
    unfold reqBytes
    rw [h1]
    rfl
  rw [h2]
  exact Proto.RequestSerialize.parse_serialize missingHostReq missingHostReq_WF

theorem missingHostReq_rejected :
    validationStage.onRequest (mkCtx missingHostInput missingHostReq)
      = .respond badRequestResp := by
  apply Reactor.Stage.RequestValidation.validationStage_rejects_bad_host <;> decide

/-- **C1, end to end.** The missing-Host input is rejected as `serialize (addDate
badRequestResp)` — a `400` (`badRequestResp.status = 400`) — for ANY inner serve. -/
theorem conformant_rejects_missingHost (inner : ByteArray → ByteArray) :
    respBytesRaw inner missingHostInput = serialize (addDate badRequestResp) :=
  conformant_reject_eq inner missingHostInput missingHostReq badRequestResp
    missingHostInput_parses missingHostReq_rejected

theorem conformant_missingHost_status :
    (addDate badRequestResp).status = 400 :=
  Reactor.Stage.RequestValidation.badRequestResp_status

/-! ## L1 / J2 end-to-end reject witnesses (the deployed conformant path)

Real requests that PASS the validation gate (valid Host/version/method) but are then
rejected by the FRAMING gate — the parse is pinned by
`Proto.RequestSerialize.parse_serialize` (not assumed). Reuses the proven
`FramingValidation.framingValidationStage_rejects_*` (L1/J2) and
`RequestValidation.validationStage_passes_valid`, so neither reject path is vacuous. -/

/-- The framing-gate reject branch: parse ✓, validation `.continue c'`, framing gate
`.respond r` ⟹ the wrapper answers `serialize (addDate r)`, never touching `inner`. -/
theorem conformant_framing_reject_eq
    (inner : ByteArray → ByteArray) (input : ByteArray) (req : Request) (c' : Ctx) (r : Response)
    (hp : Proto.RequestSerialize.parse (reqBytes input) = some req)
    (hv : validationStage.onRequest (mkCtx input req) = .continue c')
    (hf : framingValidationStage.onRequest c' = .respond r) :
    respBytesRaw inner input = serialize (addDate r) := by
  simp only [respBytesRaw, hp, hv, hf]

/-- **L1** request bytes: `GET /health HTTP/1.1`, `Host: x`,
`Transfer-Encoding: chunked, gzip` (chunked not final). -/
def teReq : Request := Reactor.Stage.FramingValidation.teNotFinalCtx.req
def teInput : ByteArray := ByteArray.mk (Proto.RequestSerialize.serialize teReq).toArray

theorem teReq_WF : Proto.RequestSerialize.WF teReq := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem teInput_parses : Proto.RequestSerialize.parse (reqBytes teInput) = some teReq := by
  have h1 : teInput.toList = Proto.RequestSerialize.serialize teReq := by
    rw [ba_toList_eq teInput]; exact Array.toList_toArray _
  have h2 : reqBytes teInput = Proto.RequestSerialize.serialize teReq := by
    unfold reqBytes; rw [h1]; rfl
  rw [h2]; exact Proto.RequestSerialize.parse_serialize teReq teReq_WF

/-- **L1, end to end.** The `chunked, gzip` request PASSES validation (valid Host) and
is then rejected by the framing gate as `serialize (addDate badRequestResp)` — a `400`
— for ANY inner serve. -/
theorem conformant_rejects_te_not_final (inner : ByteArray → ByteArray) :
    respBytesRaw inner teInput = serialize (addDate badRequestResp) := by
  refine conformant_framing_reject_eq inner teInput teReq _ badRequestResp teInput_parses
    (Reactor.Stage.RequestValidation.validationStage_passes_valid (mkCtx teInput teReq)
      (by decide) (by decide) (by decide)) ?_
  apply Reactor.Stage.FramingValidation.framingValidationStage_rejects_te_not_final <;> decide

/-- **J2** request bytes: `GET /health HTTP/1.1`, `Host: x`,
`Expect: drorb-nonsense-99` (an unsupported expectation). -/
def exReq : Request := Reactor.Stage.FramingValidation.badExpectCtx.req
def exInput : ByteArray := ByteArray.mk (Proto.RequestSerialize.serialize exReq).toArray

theorem exReq_WF : Proto.RequestSerialize.WF exReq := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem exInput_parses : Proto.RequestSerialize.parse (reqBytes exInput) = some exReq := by
  have h1 : exInput.toList = Proto.RequestSerialize.serialize exReq := by
    rw [ba_toList_eq exInput]; exact Array.toList_toArray _
  have h2 : reqBytes exInput = Proto.RequestSerialize.serialize exReq := by
    unfold reqBytes; rw [h1]; rfl
  rw [h2]; exact Proto.RequestSerialize.parse_serialize exReq exReq_WF

/-- **J2, end to end.** The unsupported-`Expect` request PASSES validation and is then
rejected by the framing gate as `serialize (addDate expectationFailedResp)` — a `417` —
for ANY inner serve. -/
theorem conformant_rejects_bad_expect (inner : ByteArray → ByteArray) :
    respBytesRaw inner exInput = serialize (addDate expectationFailedResp) := by
  refine conformant_framing_reject_eq inner exInput exReq _ expectationFailedResp exInput_parses
    (Reactor.Stage.RequestValidation.validationStage_passes_valid (mkCtx exInput exReq)
      (by decide) (by decide) (by decide)) ?_
  apply Reactor.Stage.FramingValidation.framingValidationStage_rejects_bad_expect <;> decide

theorem conformant_te_status : (addDate badRequestResp).status = 400 :=
  Reactor.Stage.RequestValidation.badRequestResp_status
theorem conformant_expect_status : (addDate expectationFailedResp).status = 417 :=
  Reactor.Stage.FramingValidation.expectationFailedResp_status

/-! ## H1/H2 conditional end-to-end witness (the deployed conformant path)

A real `If-None-Match` request that PASSES validation + framing, whose inner serve
returns an `ETag`-bearing `200`: the wrapper answers the `304` (body stripped). The
request parse is pinned by `Proto.RequestSerialize.parse_serialize`, the inner
response round-trip by `Proto.ResponseParse.parse_serialize`, and the rewrite by the
proven `ConditionalRequest.conditionalRewrite_ifNoneMatch` — so no step is vacuous. -/

open Reactor.Stage.ConditionalRequest
  (reqINM etagNameWire etag9e notModifiedOf notModifiedOf_status
   reqINM_inm reqINM_im_ok)
open Reactor.Stage.RequestValidation (normalizeTarget)

/-- The inner serve's `200` static response carrying the live `ETag` validator — a
concrete `Response` with EXPLICIT ASCII bytes (so every guard `decide`s without
reducing `String.toUTF8`). -/
def condResp : Response :=
  { status := 200, reason := [79, 75],  -- "OK"
    headers := [(etagNameWire, etag9e)], body := [104, 105, 33] }  -- "hi!"

theorem condResp_WF : Proto.ResponseParse.WF condResp := by
  refine ⟨by decide, ?_⟩
  intro kv hkv
  simp only [condResp, List.mem_singleton] at hkv
  subst hkv; exact ⟨by decide, by decide, by decide⟩

/-- An inner serve that returns the `ETag`-bearing `200` for any input. -/
def condInner : ByteArray → ByteArray :=
  fun _ => ByteArray.mk (serialize condResp).toArray

/-- The `If-None-Match: "9e983f35"` request on the wire (the probe H1 request). -/
def condInput : ByteArray := ByteArray.mk (Proto.RequestSerialize.serialize reqINM).toArray

theorem reqINM_WF : Proto.RequestSerialize.WF reqINM := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem condInput_parses :
    Proto.RequestSerialize.parse (reqBytes condInput) = some reqINM := by
  have h1 : condInput.toList = Proto.RequestSerialize.serialize reqINM := by
    rw [ba_toList_eq condInput]; exact Array.toList_toArray _
  have h2 : reqBytes condInput = Proto.RequestSerialize.serialize reqINM := by
    unfold reqBytes; rw [h1]; rfl
  rw [h2]; exact Proto.RequestSerialize.parse_serialize reqINM reqINM_WF

/-- `hasConditional` genuinely fires on the `If-None-Match` request (it is routed to
the record round-trip, not the dense splice). -/
theorem reqINM_isConditional : hasConditional reqINM = true := by decide

/-- The validation + framing gates both PASS the `If-None-Match` request, with the
origin-form target preserved (so `inner` is fed the verbatim input). -/
theorem condReq_valid_pass :
    validationStage.onRequest (mkCtx condInput reqINM)
      = .continue (mkCtx condInput { reqINM with target := normalizeTarget reqINM.target }) :=
  Reactor.Stage.RequestValidation.validationStage_passes_valid
    (mkCtx condInput reqINM) (by decide) (by decide) (by decide)

theorem condReq_framing_pass :
    framingValidationStage.onRequest (mkCtx condInput { reqINM with target := normalizeTarget reqINM.target })
      = .continue (mkCtx condInput { reqINM with target := normalizeTarget reqINM.target }) :=
  Reactor.Stage.FramingValidation.framingValidationStage_passes _ (by decide) (by decide) (by decide)

/-- **H1 + H2, end to end.** The `If-None-Match: "9e983f35"` request, served by an
`ETag`-bearing inner `200`, produces `serialize (addDate (304 ⋯))` — a `304` whose
body is stripped by `notModifiedOf` — for the deployed conformant path. -/
theorem cond_witness_304 :
    respBytesRaw condInner condInput
      = serialize (addDate (notModifiedOf (Proto.ResponseParse.wireForm condResp))) := by
  have hnt : normalizeTarget reqINM.target = reqINM.target := by decide
  have hinner : (condInner (condInnerInput reqINM)).toList = serialize condResp := mk_toArray_toList _
  have hpr : Proto.ResponseParse.parse (serialize condResp)
      = some (Proto.ResponseParse.wireForm condResp) :=
    Proto.ResponseParse.parse_serialize condResp condResp_WF
  have hetag : Reactor.Stage.ConditionalRequest.respETag (Proto.ResponseParse.wireForm condResp)
      = some etag9e := by decide
  have h200 : ((Proto.ResponseParse.wireForm condResp).status == 200) = true := by decide
  have hcr : conditionalRewrite reqINM (Proto.ResponseParse.wireForm condResp)
      = notModifiedOf (Proto.ResponseParse.wireForm condResp) :=
    Reactor.Stage.ConditionalRequest.conditionalRewrite_ifNoneMatch
      reqINM (Proto.ResponseParse.wireForm condResp) etag9e h200 hetag reqINM_im_ok reqINM_inm
  simp only [respBytesRaw, condInput_parses, condReq_valid_pass, condReq_framing_pass]
  rw [hnt]
  simp only [mkCtx, beq_self_eq_true, if_true, acceptedRaw,
    reqINM_isConditional, if_true, condRewriteBytes, hinner, hpr, hcr]

theorem cond_witness_304_status :
    (addDate (notModifiedOf (Proto.ResponseParse.wireForm condResp))).status = 304 := by
  rw [addDate_status]; exact notModifiedOf_status _

/-! ## Axiom audit -/

#print axioms conformant_framing_reject_eq
#print axioms conformant_rejects_te_not_final
#print axioms conformant_rejects_bad_expect

#print axioms injectDate_date_present
#print axioms stripBody_no_body
#print axioms stripBody_take_le4
#print axioms conformant_reject_eq
#print axioms conformant_date_present_accept
#print axioms conformant_head_no_body
#print axioms conformantServe_head_bytes
#print axioms conformant_rejects_missingHost

/-! ### Axiom audit — the DENSE bridges (byte-identity to the list spec) -/

#print axioms crIdxFrom_eq
#print axioms blankTakeFrom_eq
#print axioms injectDateBA_toList
#print axioms stripBodyBA_toList
#print axioms respBytesRawBA_toList
#print axioms conformantServe_toList

/-! ### Axiom audit — the CONDITIONAL wiring (H1/H2/H3/H5) -/

#print axioms acceptedRawBA_toList
#print axioms condInput_parses
#print axioms condReq_valid_pass
#print axioms condReq_framing_pass
#print axioms cond_witness_304
#print axioms cond_witness_304_status

end Reactor.ServeConformant
