(* ===========================================================================
   C25 — the THIRD composed stage's core: the CORS Access-Control-Allow-Origin
   decision (drorb Reactor/Deploy.lean deployCorsStage / Cors.acaoValue over
   Reactor.Stage.Cors.corsPolicy).  The REAL Lean decision is

     originAllowed p o = p.allowAnyOrigin || p.allowedOrigins.contains o
     acaoValue p o     = if originAllowed p o then some o else none   (no creds,
                          no wildcard on the deployed corsPolicy)

   Modeled on the 2-fold + scalar-gate spine (the SAME shape C22/C23 close):
   fold #1 hashes the REQUEST origin arena, fold #2 hashes the POLICY
   allowed-origin arena, the scalar reads the allowAnyOrigin wildcard flag, and
   the gate reports the ACAO grant bit

     corsAllow wild origin allowed =
       if wild-flag set          then 1  (acaoValue = some origin, ACAO echoed)
       else if hash(origin)=hash(allowed) then 1  (exact-match allow)
       else                           0  (acaoValue = none, NO ACAO - no leak)

   which is `originAllowed` exactly (single-element allowlist: contains o =
   o = allowed, modeled by the hash-equality of the two arenas, as C22/C23 model
   key/route match).  The two hashBytes folds are REUSED verbatim from C22
   (cacheBodyA1/A2, cacheLoop1/2 + their generic framed cores); ONLY the gate +
   spec are new here - a wildcard-OR-match gate (an If/else over the two fold
   accumulators + the wildcard scalar).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     finite_mapTheory optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory foldWrapCommonTheory c14GenericTheory
     panAutoTheory;

val _ = new_theory "corsCore";

(* ---------- the composed Lean SPEC: the ACAO grant bit (originAllowed) -------- *)
(* wild = the allowAnyOrigin flag (bool-encoded as a word; 0 = false).  origin /
   allowed = the request origin arena and the policy's single allowed-origin
   arena.  hash-equality of the arenas models the single-element allowlist
   membership `["allowed"].contains origin` (as C22/C23 model key/route match). *)
Definition corsAllow_def:
  corsAllow (wild:num) (origin:num list) (allowed:num list) : num =
    if (n2w wild <> (0w:word64)) then 1n
    else if (n2w (hashBytesN origin) = (n2w (hashBytesN allowed):word64)) then 1n
    else 0n
End

(* ---------- the scalar GATE (verbatim emitted If/else; wildcard-OR-match) ----- *)
Definition corsGate_def:
  corsGate =
    If (Cmp NotEqual (Var Local «wild») (Const 0w))
       (Seq (Annot «location» «(44:4 44:10)»)
          (Assign Local «dec» (Const 1w)))
       (Seq (Annot «location» «(46:7 UNKNOWN)»)
          (If (Cmp Equal (Var Local «km») (Var Local «ku»))
             (Seq (Annot «location» «(47:6 47:12)»)
                (Assign Local «dec» (Const 1w)))
             (Seq (Annot «location» «(UNKNOWN UNKNOWN)») Skip)))
End

Theorem corsGate_noFFI:
  noFFI corsGate
Proof
  REWRITE_TAC [corsGate_def] >> EVAL_TAC
QED

(* the gate leaves «dec» = n2w (corsAllow ...) and touches only «dec» *)
Theorem evaluate_corsGate:
  FLOOKUP (s:(64,'ffi) panSem$state).locals «km» = SOME (ValWord (n2w (hashBytesN origin))) /\
  FLOOKUP s.locals «ku» = SOME (ValWord (n2w (hashBytesN allowed))) /\
  FLOOKUP s.locals «wild» = SOME (ValWord (n2w wild)) /\
  FLOOKUP s.locals «dec» = SOME (ValWord 0w) ==>
  ?s'. evaluate (corsGate, s) = (NONE, s') /\
       FLOOKUP s'.locals «dec» = SOME (ValWord (n2w (corsAllow wild origin allowed))) /\
       (!v. v <> «dec» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v) /\
       s'.ffi = s.ffi /\ s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\
       s'.clock = s.clock /\ s'.base_addr = s.base_addr
Proof
  strip_tac >>
  `eval s (Cmp NotEqual (Var Local «wild») (Const 0w)) =
     SOME (ValWord (if (n2w wild <> (0w:word64)) then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval s (Cmp Equal (Var Local «km») (Var Local «ku»)) =
     SOME (ValWord (if (n2w (hashBytesN origin) = (n2w (hashBytesN allowed):word64))
                    then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  Cases_on `n2w wild = (0w:word64)` >>
  Cases_on `n2w (hashBytesN origin) = (n2w (hashBytesN allowed):word64)` >>
  full_simp_tac (srw_ss()) [] >>
  simp [corsGate_def] >>
  asm_simp_tac (srw_ss()) [evaluate_If_reduce, Annot_Seq_eval, evaluate_Assign_const,
     evaluate_def, cond1w_ne0, set_var_def, corsAllow_def] >>
  gvs [FLOOKUP_UPDATE, set_var_def] >> rw [] >> gvs [FLOOKUP_UPDATE]
QED

val _ = export_theory ();
