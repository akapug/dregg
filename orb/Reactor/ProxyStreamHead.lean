import Reactor.ServeStep

/-!
# Reactor.ProxyStreamHead — the CL-trust head-independence lemma (native passthrough streaming)

The whole-reply proxy resume (`Reactor.ServeStep.proxyRespTransform`) feeds the ENTIRE
upstream reply into one continuation, so a native path must buffer the whole body before
it can emit the transformed head — the head carries the derived `Content-Length`, and the
head/body split (`proxyRespTransform_split`) proves head-FIRST delivery is faithful but not
head-BEFORE-body emission.

This file closes that residual for the **non-gzip passthrough** case. It proves the head is
computable from `(input, upstream-head-bytes, body-LENGTH)` alone — never from the body
BYTES — so a native io_uring proxy can compute+emit the transformed head the moment the
upstream head completes and then forward the body straight through, RSS-bounded, without
ever buffering it whole.

The genuine mathematical content is **body-content-independence of the non-gzip transform
stages** (`proxyTransform_body_subst`): for `acceptsGzip (ctxOf input).req = false`, the
four response-transform stages (`deployCorsStage` / `gzipStage` / `securityheadersStage` /
`headerStage`) touch only request-keyed headers + the status/reason — none reads the body
bytes, and none rewrites the body (the gzip re-encode is gated OFF). Combined with the
serializer deriving `Content-Length = body.length`, the transformed head factors through
`body.length`.

`proxyStreamHead` is the exported head computation; `proxyRespHead_factors` is the head-
independence lemma; `proxyStream_bytes_faithful` proves the streamed output
(`head ++ body`) is byte-identical to the buffered `proxyRespTransform`.

**gzip stays honestly open.** When `acceptsGzip` is true, `gzipStage` re-encodes the body,
so the transformed head genuinely depends on the body bytes (its length changes). That case
needs chunked transfer-encoding — a different, deeper residual — and is NOT closed here; the
native path keeps buffering it (`drive_proxy_refines`).
-/

namespace Reactor.ServeStep

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Stage runPipeline ResponseBuilder build_addHeader build_addHeaders
  build_mapResp build_ofResponse)

/-! ## splitHeadBody append-stability

Once `splitHeadBody` has found the first CRLF-CRLF inside a delimiter-terminated head,
appending more bytes only extends the already-decided body tail — the head split point
never moves. This lets a shell that has received the upstream head (through `\r\n\r\n`)
reason about the full reply it has NOT yet received. -/

/-- One-step reduction of `splitHeadBody` once four leading bytes are exposed: it takes the
delimiter branch iff the four bytes are `13,10,13,10`, otherwise peels one byte. -/
theorem splitHeadBody_four (b r0 r1 r2 : UInt8) (tail : Bytes) :
    splitHeadBody (b :: r0 :: r1 :: r2 :: tail)
      = if b = 13 ∧ r0 = 10 ∧ r1 = 13 ∧ r2 = 10 then ([], tail)
        else (b :: (splitHeadBody (r0 :: r1 :: r2 :: tail)).1,
              (splitHeadBody (r0 :: r1 :: r2 :: tail)).2) := by
  by_cases h : b = 13 ∧ r0 = 10 ∧ r1 = 13 ∧ r2 = 10
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rw [splitHeadBody.eq_1]; simp
  · rw [if_neg h, splitHeadBody.eq_def]
    split
    · rename_i he; simp only [List.cons.injEq] at he
      exact absurd ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1⟩ h
    · rename_i b' rest' he; rw [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he; rfl
    · rename_i he; simp at he

/-- **Split-append stability.** For a head of the form `pre ++ CRLFCRLF`, appending a body
distributes: the head component is unchanged and the body component gains the appended
bytes. (Holds unconditionally — a straddling early delimiter is accounted for identically
on both sides.) -/
theorem splitHeadBody_append (pre body : Bytes) :
    splitHeadBody (pre ++ [13,10,13,10] ++ body)
      = ((splitHeadBody (pre ++ [13,10,13,10])).1,
         (splitHeadBody (pre ++ [13,10,13,10])).2 ++ body) := by
  induction pre using splitHeadBody.induct with
  | case1 rest => simp only [List.cons_append, splitHeadBody, List.append_assoc]
  | case2 b rest _ _ _ _ ihr =>
      rcases rest with _|⟨r0,_|⟨r1,_|⟨r2,rr⟩⟩⟩
      · simp [splitHeadBody_four]
      · simp only [List.nil_append, List.cons_append, splitHeadBody_four]
        by_cases h : b = 13 ∧ r0 = 10 <;> simp [h]
      · simp only [List.nil_append, List.cons_append, splitHeadBody_four]
        by_cases h : r0 = 13 ∧ r1 = 10 <;> simp [h]
      · have e1 : (b::r0::r1::r2::rr) ++ [13,10,13,10] ++ body
                = b::r0::r1::r2::(rr ++ [13,10,13,10] ++ body) := by simp
        have e2 : (b::r0::r1::r2::rr) ++ [13,10,13,10]
                = b::r0::r1::r2::(rr ++ [13,10,13,10]) := by simp
        rw [e1, e2, splitHeadBody_four b r0 r1 r2 (rr ++ [13,10,13,10] ++ body),
            splitHeadBody_four b r0 r1 r2 (rr ++ [13,10,13,10])]
        by_cases hc : b = 13 ∧ r0 = 10 ∧ r1 = 13 ∧ r2 = 10
        · simp only [if_pos hc, List.append_assoc]
        · rw [if_neg hc, if_neg hc]
          have e3 : r0::r1::r2::(rr ++ [13,10,13,10] ++ body)
                  = (r0::r1::r2::rr) ++ [13,10,13,10] ++ body := by simp
          have e4 : r0::r1::r2::(rr ++ [13,10,13,10])
                  = (r0::r1::r2::rr) ++ [13,10,13,10] := by simp
          rw [e3, e4, ihr]
  | case3 => simp only [List.nil_append, List.cons_append, splitHeadBody]

/-! ## parseUpstream factors through the head bytes -/

/-- `splitCRLFLines` is never empty (its base case is `[[]]`). Kills the dead `[]`
branch of `parseUpstream`. -/
theorem splitCRLFLines_ne_nil (h : Bytes) : splitCRLFLines h ≠ [] := by
  rw [splitCRLFLines.eq_def]
  split
  · simp
  · simp
  · split <;> simp

/-- **`parseUpstream` factors through the head bytes.** For a delimiter-terminated head
`pre ++ CRLFCRLF` (whose first CRLF-CRLF is the terminal one, `hclean`), parsing the full
reply `pre ++ CRLFCRLF ++ body` yields exactly the parse of the head bytes with the body
field swapped in. The status/reason/headers depend ONLY on the head bytes. -/
theorem parseUpstream_split (pre body : Bytes)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, [])) :
    parseUpstream (pre ++ [13,10,13,10] ++ body)
      = { parseUpstream (pre ++ [13,10,13,10]) with body := body } := by
  have hfull : splitHeadBody (pre ++ [13,10,13,10] ++ body) = (pre, body) := by
    rw [splitHeadBody_append, hclean]; rfl
  unfold parseUpstream
  rw [hfull, hclean]
  dsimp only
  rcases hc : splitCRLFLines pre with _ | ⟨sl, hl⟩
  · exact absurd hc (splitCRLFLines_ne_nil pre)
  · rfl

/-! ## The non-gzip transform is body-content-independent (the REAL lemma) -/

/-- The proxy response transform as a `Response → Response`: run the four response-transform
stages over `r` keyed on the original request context. `proxyBuiltResp input upstream`
is exactly `proxyTransform input (parseUpstream upstream)`. -/
def proxyTransform (input : Bytes) (r : Response) : Response :=
  (runPipeline proxyRespStages (fun _ => r) (Reactor.Deploy.ctxOf input)).build

theorem proxyTransform_of_parse (input upstream : Bytes) :
    proxyBuiltResp input upstream = proxyTransform input (parseUpstream upstream) := rfl

/-- **Body-content-independence of the non-gzip transform.** When the request does NOT
accept gzip, running the response-transform stages over `{ r with body := b }` produces the
SAME status/reason/headers as running them over `r`, with the body simply threaded through.
No stage reads the body bytes, and no stage rewrites the body (the gzip re-encode is gated
OFF). This is the load-bearing fact: the transformed HEAD is a function of the request +
the parsed upstream head, not of the body content. -/
theorem proxyTransform_body_subst (input : Bytes) (r : Response) (body : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false) :
    proxyTransform input { r with body := body }
      = { proxyTransform input r with body := body } := by
  unfold proxyTransform proxyRespStages
  simp only [runPipeline, Reactor.Deploy.deployCorsStage, Reactor.Stage.Gzip.gzipStage,
    Reactor.Stage.SecurityHeaders.securityheadersStage, Reactor.Stage.Header.headerStage, hgz]
  split <;>
    simp only [build_addHeader, build_addHeaders, build_mapResp, build_ofResponse,
      Reactor.Stage.Header.rewriteResp, List.append_assoc]

/-- **The transformed proxy response over the full reply splits off its body.** For a clean,
non-gzip reply `pre ++ CRLFCRLF ++ body`, the built transformed response is exactly the one
built over the head-only bytes with the real body swapped in — so its status/reason/headers
are body-content-independent and its body is exactly `body`. -/
theorem proxyBuiltResp_split (input pre body : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, [])) :
    proxyBuiltResp input (pre ++ [13,10,13,10] ++ body)
      = { proxyBuiltResp input (pre ++ [13,10,13,10]) with body := body } := by
  rw [proxyTransform_of_parse, proxyTransform_of_parse,
      parseUpstream_split pre body hclean, proxyTransform_body_subst input _ body hgz]

/-! ## The exported streaming head + the head-independence lemma -/

/-- **The transformed proxy response HEAD, computed from `(input, upstream-head, body-len)`
WITHOUT the body bytes.** Parse the head-only bytes (the body parses empty), run the
non-gzip transform (which keeps the body empty), then render the head — status line, the
transformed header block, and the derived `Content-Length` set to the KNOWN `bodyLen` (from
the upstream `Content-Length`), followed by the blank-line separator. This is the head the
native streaming proxy emits the moment the upstream head completes; the body then streams
through. -/
def proxyStreamHead (input upHead : Bytes) (bodyLen : Nat) : Bytes :=
  let R := proxyBuiltResp input upHead
  Reactor.statusLineOf R ++ Reactor.crlf
    ++ Reactor.renderHeaders (R.headers ++ [(Reactor.clName, Reactor.natToDec bodyLen)])
    ++ Reactor.crlf ++ Reactor.crlf

/-- **THE CL-TRUST HEAD-INDEPENDENCE LEMMA.** For a request that does NOT accept gzip and a
clean upstream head `pre ++ CRLFCRLF`, the transformed proxy response HEAD over the full
reply `pre ++ CRLFCRLF ++ body` equals `proxyStreamHead input (pre ++ CRLFCRLF) body.length`
— a function of `(input, upstream-head-bytes, body.length)` that NEVER inspects the body
BYTES. The head factors through the body's LENGTH. -/
theorem proxyRespHead_factors (input pre body : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, [])) :
    proxyRespHead input (pre ++ [13,10,13,10] ++ body)
      = proxyStreamHead input (pre ++ [13,10,13,10]) body.length := by
  unfold proxyRespHead proxyStreamHead
  rw [proxyBuiltResp_split input pre body hgz hclean]
  simp only [Reactor.statusLineOf, Reactor.headerBlockOf, Reactor.allHeaders, Reactor.build,
    Reactor.statusLine]

/-- **Body-content-independence (the two-body witness that the head factors through
length).** Two non-gzip replies with the SAME head and EQUAL body lengths produce the SAME
transformed head — regardless of body content. Non-vacuous corollary of
`proxyRespHead_factors`. -/
theorem proxyRespHead_body_content_indep (input pre b1 b2 : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, []))
    (hlen : b1.length = b2.length) :
    proxyRespHead input (pre ++ [13,10,13,10] ++ b1)
      = proxyRespHead input (pre ++ [13,10,13,10] ++ b2) := by
  rw [proxyRespHead_factors input pre b1 hgz hclean,
      proxyRespHead_factors input pre b2 hgz hclean, hlen]

/-- **Byte-identity of the streamed output to the buffered transform.** The streamed
non-gzip output — the body-free head `proxyStreamHead` followed by the raw body streamed
through — is byte-for-byte the buffered `proxyRespTransform input (full reply)`. So the
native streaming path (compute head on head-complete, forward body chunks) produces exactly
the bytes the buffered oracle produces, while never holding the body whole. -/
theorem proxyStream_bytes_faithful (input pre body : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, [])) :
    proxyStreamHead input (pre ++ [13,10,13,10]) body.length ++ body
      = proxyRespTransform input (pre ++ [13,10,13,10] ++ body) := by
  rw [proxyRespTransform_split, ← proxyRespHead_factors input pre body hgz hclean,
      proxyBuiltResp_split input pre body hgz hclean]

#print axioms splitHeadBody_append
#print axioms proxyTransform_body_subst
#print axioms proxyRespHead_factors
#print axioms proxyStream_bytes_faithful

end Reactor.ServeStep
