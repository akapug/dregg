(* ===========================================================================
   C28 probe, PART B — GROUNDING the store loop on the DEPLOYED security-header
   block, and making the write OBSERVABLE.

   PART A (`transformCopyLoop`) proved the emitted copy loop writes an ARBITRARY
   source byte list `bs` into the output buffer.  Here we (1) pin `bs` to the
   REAL serialized security-header set the deployed `securityheadersStage`
   renders (drorb `Reactor/Stage/SecurityHeaders.lean` + `SecurityHeaders.lean`,
   `render policy`), and (2) attach the `report_vec` FFI so the written buffer is
   emitted on the observable trace — the transform stage's response BYTES, not a
   scalar proxy.

   THE DEPLOYED HEADER SET (drorb `SecurityHeaders.render policy`, the deployed
   `policy`: hsts one-year+subdomains+preload, xfo DENY, noSniff, referrer
   no-referrer) serialized as an HTTP/1.1 header block (`name: value CRLF`):

     Strict-Transport-Security: max-age=31536000; includeSubDomains; preload
     X-Frame-Options: DENY
     X-Content-Type-Options: nosniff
     Referrer-Policy: no-referrer

   `secHeadersBytes` is the UTF-8/ASCII byte list of that block.  It is a
   compile-time CONSTANT of the deployed policy (no request dependence), exactly
   the residual C26 named.  `secheaders_bytes_reported` proves the emitted
   program's observable FFI output equals EXACTLY those bytes.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     stringTheory finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory ffiTheory;
open c14GenericTheory;
open transformCopyLoopTheory;

val _ = new_theory "transformSecHeaders";

(* CRLF as two bytes (13,10). *)
Definition crlf_def:
  crlf = [CHR 13; CHR 10]
End

(* the four deployed header lines, each `name: value` + CRLF — driven off the
   REAL strings `SecurityHeaders.render` emits for the deployed policy. *)
Definition secHeadersStr_def:
  secHeadersStr =
    ("Strict-Transport-Security: max-age=31536000; includeSubDomains; preload"
       ++ crlf) ++
    ("X-Frame-Options: DENY" ++ crlf) ++
    ("X-Content-Type-Options: nosniff" ++ crlf) ++
    ("Referrer-Policy: no-referrer" ++ crlf)
End

(* the wire bytes: the ASCII/UTF-8 code of each character. *)
Definition secHeadersBytes_def:
  secHeadersBytes = MAP ORD secHeadersStr
End

(* --- the block is a valid source for the copy loop: every byte < 256, the
   length is inside the signed-positive range, and it is non-empty (a REAL,
   non-vacuous payload). All by evaluation. --- *)
Theorem secHeadersBytes_bytes:
  EVERY (\x. x < 256) secHeadersBytes
Proof
  simp [secHeadersBytes_def, EVERY_MAP] >> EVAL_TAC
QED

Theorem secHeadersBytes_len:
  LENGTH secHeadersBytes < 2n ** 63
Proof
  simp [secHeadersBytes_def, secHeadersStr_def, crlf_def] >> EVAL_TAC
QED

Theorem secHeadersBytes_nonempty:
  secHeadersBytes <> []
Proof
  simp [secHeadersBytes_def, secHeadersStr_def, crlf_def] >> EVAL_TAC
QED

(* the exact length (159 bytes) — a concrete, grounded payload. *)
Theorem secHeadersBytes_length_val:
  LENGTH secHeadersBytes = 159
Proof
  simp [secHeadersBytes_def, secHeadersStr_def, crlf_def] >> EVAL_TAC
QED

(* the first bytes ARE the HSTS header name "Strict-Transport-Security" — a
   grounded spot-check that the payload is the real header block, not a stub. *)
Theorem secHeadersBytes_prefix:
  TAKE 25 secHeadersBytes = MAP ORD "Strict-Transport-Security"
Proof
  simp [secHeadersBytes_def, secHeadersStr_def, crlf_def] >> EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   THE STORE LOOP GROUNDED — the emitted loop writes EXACTLY the deployed
   security-header bytes into the output buffer.  A direct instance of PART A's
   `copyLoop_writes` at `bs = secHeadersBytes`.
   --------------------------------------------------------------------------- *)
Theorem secheaders_copyLoop_writes:
  copyInv secHeadersBytes src out 0 s /\ LENGTH secHeadersBytes <= s.clock ==>
    ?s'. evaluate (copyLoop, s) = (NONE, s') /\
         (!j. j < LENGTH secHeadersBytes ==>
              mem_load_byte s'.memory s'.memaddrs s'.be (out + n2w j)
                = SOME ((n2w (EL j secHeadersBytes)):word8)) /\
         FLOOKUP s'.locals «out» = SOME (ValWord out)
Proof
  strip_tac >> metis_tac [copyLoop_writes]
QED

(* ---------------------------------------------------------------------------
   THE `report_vec` FFI CONTRACT (the single named trusted assumption, same
   status as C13/C26's report_vec): given the output buffer holds bytes `bs`,
   `@report_vec` emits an IO_event onto the observable trace carrying EXACTLY
   those `LENGTH bs` bytes (`MAP n2w bs`).  The reported bytes are TIED to the
   memory contents (the premise), so this reports the REAL written buffer — not
   a scalar proxy, not a faked output.
   --------------------------------------------------------------------------- *)
Definition reportBytesFFI_def:
  reportBytesFFI (bs:num list) (out:word64) (s0:(64,'ffi) panSem$state) <=>
    !(s:(64,'ffi) panSem$state).
       FLOOKUP s.locals «out» = SOME (ValWord out) /\
       (!j. j < LENGTH bs ==>
            mem_load_byte s.memory s.memaddrs s.be (out + n2w j)
              = SOME ((n2w (EL j bs)):word8)) ==>
       ?s2 rb.
         evaluate (ExtCall «report_vec» (Var Local «out»)
                     (Const (n2w (LENGTH bs))) (Var Local «out») (Const 8w), s)
           = (NONE, s2) /\
         s2.clock = s.clock /\
         s2.ffi.io_events =
           s.ffi.io_events ++
           [IO_event (ffi$ExtCall «report_vec»)
              (MAP (\b. (n2w b):word8) bs) rb]
End

(* the emitted body: run the copy loop, then report the output buffer. *)
Definition copyReportBody_def:
  copyReportBody =
    Seq copyLoop
        (ExtCall «report_vec» (Var Local «out»)
           (Const (n2w (LENGTH secHeadersBytes))) (Var Local «out») (Const 8w))
End

(* ---------------------------------------------------------------------------
   THE HEADLINE (PART B) — the emitted transform program's OBSERVABLE OUTPUT is
   EXACTLY the deployed serialized security-header bytes.  Every terminating run
   of `copyReportBody` (copy loop + report) emits one `report_vec` IO_event whose
   payload is `MAP n2w secHeadersBytes` — the REAL 159-byte header block, byte
   for byte.  This is a response-BYTE transform reaching a proven observable, the
   multi-byte analogue of C26's single-word `report_vec (n2w decision)`.
   --------------------------------------------------------------------------- *)
Theorem secheaders_bytes_reported:
  copyInv secHeadersBytes src out 0 s /\ LENGTH secHeadersBytes <= s.clock /\
  reportBytesFFI secHeadersBytes out s ==>
    ?s' rb.
      evaluate (copyReportBody, s) = (NONE, s') /\
      s'.ffi.io_events =
        s.ffi.io_events ++
        [IO_event (ffi$ExtCall «report_vec»)
           (MAP (\b. (n2w b):word8) secHeadersBytes) rb]
Proof
  strip_tac >>
  (* run the copy loop: the buffer now holds secHeadersBytes *)
  drule_all secheaders_copyLoop_writes >> strip_tac >>
  qmatch_asmsub_rename_tac `evaluate (copyLoop, s) = (NONE, sL)` >>
  `sL.clock <= s.clock` by (imp_res_tac evaluate_clock >> fs []) >>
  `sL.ffi.io_events = s.ffi.io_events` by metis_tac [copyLoop_io_events] >>
  `FLOOKUP sL.locals «out» = SOME (ValWord out)` by fs [] >>
  `!j. j < LENGTH secHeadersBytes ==>
       mem_load_byte sL.memory sL.memaddrs sL.be (out + n2w j)
         = SOME ((n2w (EL j secHeadersBytes)):word8)` by fs [] >>
  (* fire the report_vec contract at sL (buffer holds the bytes, «out» pinned) *)
  `?s2 rb.
     evaluate (ExtCall «report_vec» (Var Local «out»)
                 (Const (n2w (LENGTH secHeadersBytes))) (Var Local «out») (Const 8w), sL)
       = (NONE, s2) /\ s2.clock = sL.clock /\
     s2.ffi.io_events =
       sL.ffi.io_events ++
       [IO_event (ffi$ExtCall «report_vec») (MAP (\b. (n2w b):word8) secHeadersBytes) rb]`
     by (qpat_x_assum `reportBytesFFI _ _ _`
           (fn th => mp_tac (SIMP_RULE std_ss [reportBytesFFI_def] th)) >>
         disch_then (qspec_then `sL` mp_tac) >> asm_simp_tac std_ss []) >>
  qmatch_asmsub_rename_tac `evaluate (ExtCall _ _ _ _ _, sL) = (NONE, sR)` >>
  qexists_tac `sR` >> qexists_tac `rb` >>
  `evaluate (copyReportBody, s) = (NONE, sR)`
     by (simp [copyReportBody_def] >> irule Seq_thread >> qexists_tac `sL` >> fs []) >>
  fs []
QED

val _ = export_theory ();
