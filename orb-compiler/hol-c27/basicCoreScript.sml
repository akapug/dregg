(* ===========================================================================
   C27 — the HTTP Basic-auth credential COMPARE gate (drorb
   Reactor/Stage/BasicAuth.basicStage / BasicAuth.authenticate over stageConfig,
   stage 2 of Reactor.Deploy.deployStagesFull2).  The REAL Lean decision, after
   the base64/scheme decode boundaries, is the ONE trust boundary `verify`:

     verify user pass = (user == "admin" && pass == "secret")

   i.e. admit iff the decoded credential equals the configured "admin:secret".
   Modeled on the SAME 2-fold + scalar-gate spine C22/C23/C25 close: fold #1
   hashes the PRESENTED (decoded) credential arena, fold #2 hashes the CONFIGURED
   credential arena, and the gate reports the admit bit

     basicAdmit cred configured =
       if hash(cred) = hash(configured) then 1  (verify -> admit -> .ok)
       else                                  0  (verify fails -> challenge -> 401)

   which is `verify` exactly (hash-equality of the two arenas models the byte-
   string credential equality, as C22/C23/C25 model key/route/origin match).  The
   two hashBytes folds are REUSED verbatim from C22 (cacheBodyA1/A2, cacheLoop1/2
   + their generic framed cores); ONLY the gate + spec are new here - a SINGLE
   hash-equality gate (an If over the two fold accumulators; no scalar read, no
   wildcard - structurally the plainest gate in the family).

   RESIDUAL (named, not closed): base64-decode (BasicAuth.b64Decode / emitStep)
   and the `Basic` scheme match (parseBasic/decodeUserPass) are the UPSTREAM
   decode boundaries.  emitStep is a stateful bit-buffer transducer emitting a
   variable-length byte list with a carry - a general loop, NOT a hashBytes
   scalar fold - so it is out of this gate's scope (see C27 report).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     finite_mapTheory optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory foldWrapCommonTheory c14GenericTheory
     panAutoTheory;

val _ = new_theory "basicCore";

(* ---------- the composed Lean SPEC: admit iff credential = configured -------- *)
(* cred = the presented (decoded) credential arena; configured = the deployed
   "admin:secret" arena.  hash-equality of the arenas models the credential
   equality `verify` decides (as C22/C23/C25 model key/route/origin match). *)
Definition basicAdmit_def:
  basicAdmit (cred:num list) (configured:num list) : num =
    if (n2w (hashBytesN cred) = (n2w (hashBytesN configured):word64)) then 1n else 0n
End

(* ---------- the scalar GATE (verbatim emitted If; single hash-equality) ------- *)
Definition basicGate_def:
  basicGate =
    If (Cmp Equal (Var Local «km») (Var Local «ku»))
       (Seq (Annot «location» «(44:4 44:10)»)
          (Assign Local «dec» (Const 1w)))
       (Seq (Annot «location» «(UNKNOWN UNKNOWN)») Skip)
End

Theorem basicGate_noFFI:
  noFFI basicGate
Proof
  REWRITE_TAC [basicGate_def] >> EVAL_TAC
QED

(* the gate leaves «dec» = n2w (basicAdmit ...) and touches only «dec» *)
Theorem evaluate_basicGate:
  FLOOKUP (s:(64,'ffi) panSem$state).locals «km» = SOME (ValWord (n2w (hashBytesN cred))) /\
  FLOOKUP s.locals «ku» = SOME (ValWord (n2w (hashBytesN configured))) /\
  FLOOKUP s.locals «dec» = SOME (ValWord 0w) ==>
  ?s'. evaluate (basicGate, s) = (NONE, s') /\
       FLOOKUP s'.locals «dec» = SOME (ValWord (n2w (basicAdmit cred configured))) /\
       (!v. v <> «dec» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v) /\
       s'.ffi = s.ffi /\ s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\
       s'.clock = s.clock /\ s'.base_addr = s.base_addr
Proof
  strip_tac >>
  `eval s (Cmp Equal (Var Local «km») (Var Local «ku»)) =
     SOME (ValWord (if (n2w (hashBytesN cred) = (n2w (hashBytesN configured):word64))
                    then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  Cases_on `n2w (hashBytesN cred) = (n2w (hashBytesN configured):word64)` >>
  full_simp_tac (srw_ss()) [] >>
  simp [basicGate_def] >>
  asm_simp_tac (srw_ss()) [evaluate_If_reduce, Annot_Seq_eval, evaluate_Assign_const,
     evaluate_def, cond1w_ne0, set_var_def, basicAdmit_def] >>
  gvs [FLOOKUP_UPDATE, set_var_def] >> rw [] >> gvs [FLOOKUP_UPDATE]
QED

val _ = export_theory ();
