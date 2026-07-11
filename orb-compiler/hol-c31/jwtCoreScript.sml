(* ===========================================================================
   C31 — the HS256 JWT admin gate's decision CORE (drorb Reactor/Deploy.jwtAdminStage
   -> Reactor.Stage.Jwt.jwtStage -> Jwt.authenticate / afterKey over the HS256
   verify, stage 1 of Reactor.Deploy.deployStagesFull2).  The security-relevant
   admit decision, after the crypto/decode boundaries, is the sig-equality gate
   (verifyHmac's own compare) conjoined with the alg-confusion gate of afterKey:

     admit  iff  verifyHmac(key, header.payload) == signature      (RFC 7518 HS256)
              AND jws.header.alg = key.alg  AND  jws.header.alg <> none

   i.e. admit iff (a) the presented signature equals the HMAC-SHA256 digest the
   trust boundary computed over the signing input, AND (b) the token's declared
   algorithm is exactly the key's HS256 (rejecting alg=none and any cross-algorithm
   confusion - Jwt.jwt_alg_confusion_safe).  Modeled on the SAME 2-fold + scalar-gate
   spine C22/C23/C25/C27 close: fold #1 hashes the HMAC DIGEST arena, fold #2 hashes
   the (decoded) SIGNATURE arena, and the ONE staged scalar @+16 carries the token's
   declared alg tag (1 = HS256, 0 = none, 2 = RS256/other - the alg-confusion case).
   The gate reports the admit bit

     jwtAdmit digest sig alg =
       if hash(digest) = hash(sig)  (verifyHmac T)
          /\ alg = 1 (HS256)        (alg = key.alg /\ alg <> none)
       then 1  (admit, request reaches /admin handler)
       else 0  (reject -> 401 : bad signature, alg=none, or alg confusion)

   The two hashBytes folds are REUSED verbatim from C22 (cacheBodyA1/A2, cacheLoop1/2
   + their generic framed cores).  UNLIKE C27 (where the scalar was staged-but-unused)
   the scalar IS read by the gate here: the gate is a two-condition cascade
   (sig-equality AND alg-tag), the alg check reading the staged scalar.

   TRUST BOUNDARY (named, NOT compiled): the HMAC-SHA256 digest itself - a verified
   crypto primitive behind an FFI, exactly like the TLS crypto.  This gate takes its
   OUTPUT (the digest bytes) as the machine input arena and compares it (the equality
   that IS verifyHmac's decision) - it does NOT recompute the HMAC.

   RESIDUAL (named, NOT closed): base64url-decode of the header/payload/signature
   segments + the JSON claim parse are the UPSTREAM general loops (C27's base64
   residual class - stateful emit-buffer / parse `While`s, not hashBytes folds).  The
   `/admin*` path guard (Deploy.isAdminPath / isPrefixB) is upstream routing (a prefix
   scan, C29's cidr-matcher class), the same role C27's isProtectedPath played -
   it selects WHETHER this gate runs, and is not part of the compiled admit decision.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     finite_mapTheory optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory foldWrapCommonTheory c14GenericTheory
     panAutoTheory;

val _ = new_theory "jwtCore";

(* ---------- the composed Lean SPEC: admit iff sig-equal AND alg = HS256 -------- *)
(* digest = the HMAC-SHA256(signing input, key) output (the crypto trust boundary's
   result, taken as input); sig = the base64url-decoded signature segment; alg = the
   token's declared algorithm tag (HS256 = 1).  hash-equality of the digest/sig
   arenas models verifyHmac's constant-time compare (as C22/C25/C27 model the
   key/origin/credential match); alg = 1 is the afterKey alg gate (alg = key.alg,
   key.alg = HS256, so alg <> none is subsumed). *)
Definition jwtAdmit_def:
  jwtAdmit (digest:num list) (sig:num list) (alg:num) : num =
    if (n2w (hashBytesN digest) = (n2w (hashBytesN sig):word64)) /\
       ((n2w alg):word64 = 1w) then 1n else 0n
End

(* ---------- the scalar GATE (verbatim emitted nested If; sig-equal AND alg) ----- *)
(* the exact parser subterm on jwt.pnk lines 43-47 (copied from the verified parser
   output - see the C31 report; leanc OUT of the TCB). *)
Definition jwtGate_def:
  jwtGate =
    If (Cmp Equal (Var Local «km») (Var Local «ku»))
       (Seq (Annot «location» «(44:7 UNKNOWN)»)
          (If (Cmp Equal (Var Local «alg») (Const 1w))
             (Seq (Annot «location» «(45:6 45:12)»)
                (Assign Local «dec» (Const 1w)))
             (Seq (Annot «location» «(UNKNOWN UNKNOWN)») Skip)))
       (Seq (Annot «location» «(UNKNOWN UNKNOWN)») Skip)
End

Theorem jwtGate_noFFI:
  noFFI jwtGate
Proof
  REWRITE_TAC [jwtGate_def] >> EVAL_TAC
QED

(* the gate leaves «dec» = n2w (jwtAdmit ...) and touches only «dec»; it reads the
   two fold accumulators «km»/«ku» AND the staged alg scalar. *)
Theorem evaluate_jwtGate:
  FLOOKUP (s:(64,'ffi) panSem$state).locals «km» = SOME (ValWord (n2w (hashBytesN digest))) /\
  FLOOKUP s.locals «ku» = SOME (ValWord (n2w (hashBytesN sig))) /\
  FLOOKUP s.locals «alg» = SOME (ValWord (n2w alg)) /\
  FLOOKUP s.locals «dec» = SOME (ValWord 0w) ==>
  ?s'. evaluate (jwtGate, s) = (NONE, s') /\
       FLOOKUP s'.locals «dec» = SOME (ValWord (n2w (jwtAdmit digest sig alg))) /\
       (!v. v <> «dec» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v) /\
       s'.ffi = s.ffi /\ s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\
       s'.clock = s.clock /\ s'.base_addr = s.base_addr
Proof
  strip_tac >>
  `eval s (Cmp Equal (Var Local «km») (Var Local «ku»)) =
     SOME (ValWord (if (n2w (hashBytesN digest) = (n2w (hashBytesN sig):word64))
                    then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval s (Cmp Equal (Var Local «alg») (Const 1w)) =
     SOME (ValWord (if ((n2w alg):word64 = 1w) then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  Cases_on `n2w (hashBytesN digest) = (n2w (hashBytesN sig):word64)` >>
  Cases_on `(n2w alg):word64 = 1w` >>
  full_simp_tac (srw_ss()) [] >>
  simp [jwtGate_def] >>
  asm_simp_tac (srw_ss()) [evaluate_If_reduce, Annot_Seq_eval, evaluate_Assign_const,
     evaluate_def, cond1w_ne0, set_var_def, jwtAdmit_def] >>
  gvs [FLOOKUP_UPDATE, set_var_def] >> rw [] >> gvs [FLOOKUP_UPDATE]
QED

val _ = export_theory ();
