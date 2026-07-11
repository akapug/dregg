(* ===========================================================================
   C26 probe, PART A — the SECURITY-HEADERS stage decision core, derived
   AUTOMATICALLY by the reusable `panLinkA_branch` tactic (no bespoke per-stage
   hand proof).

   THE STAGE: `Reactor.Stage.SecurityHeaders.securityheadersStage` — stage 13 of
   the real `Reactor.Deploy.deployStagesFull2` orb serve (drorb
   Reactor/Stage/SecurityHeaders.lean + SecurityHeaders.lean).  Its `onResponse`
   folds the RFC-6797 HSTS + companion security-header set onto the response.
   The header set is a compile-time constant of the deployed `policy`, so the
   whole-list fold is a straight-line transform; its reportable DECISION CORE is
   the RFC 6797 6.1.1 gate governing the headline HSTS `includeSubDomains`
   directive.

   THE SPEC: `SecurityHeaders.effectiveIncludeSubDomains h
                = h.includeSubDomains && (h.maxAge != 0)` (RFC 6797 6.1.1 NOTE:
   `max-age = 0` disables the policy and its `includeSubDomains` is ignored;
   Lean theorem `hsts_zero_disables`).  Specialized to the deployed policy's
   `includeSubDomains = true` (hstsPolicy in SecurityHeaders.lean), this is
   exactly `(maxAge != 0)`, i.e. `hstsEffective` below.  It is LOOP-FREE — a
   total single-guard `If`, no recursion, no `While` — so it compiles via the
   C15 loop-free Link-A path.

   `secheadersCore` is the VERBATIM `If` lifted from `functions secHeadersProg`
   (the verified parser's output on secheaders.pnk, dumped and transcribed
   exactly, Annot location strings included).  We prove, against real
   `panSem$evaluate`, that it writes EXACTLY the Lean spec's effective-flag
   `n2w (hstsEffective code)` into the local «result».
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open panAutoTheory;        (* signed_lt_n2w64, eval_lt_pinned, Annot_Seq_eval *)
open c14GenericTheory;     (* noFFI (generic, reused) *)
open panAutoLib;           (* panLinkA_branch — the reusable loop-free Link-A tactic *)

val _ = new_theory "secheadersCore";

(* --- the Lean SPEC, re-declared in HOL: byte-identical to
   `SecurityHeaders.effectiveIncludeSubDomains` specialized to the deployed
   policy's includeSubDomains = true, so effective iff maxAge != 0 iff ~(maxAge < 1). *)
Definition hstsEffective_def:
  hstsEffective (code:num) =
    if code < 1 then 0n else 1n
End

(* --- secheadersCore = the VERBATIM emitted If (from `functions secHeadersProg`),
   with the Const-assign leaves behind their location Annots.  Transcribed
   exactly from the parser AST dump (ast_dump.txt). --- *)
Definition secheadersCore_def:
  secheadersCore =
    If (Cmp Less (Var Local «maxage») (Const (1w:word64)))
       (Seq (Annot «location» «(33:4 33:13)») (Assign Local «result» (Const 0w)))
       (Seq (Annot «location» «(35:4 35:13)») (Assign Local «result» (Const 1w)))
End

(* --- the core relation: maxage/result in locals, range for the signed guard.
   The real domain is any HSTS max-age (a Nat of seconds); `code < 2^63` is the
   loose, template-uniform signed-positive bound (the deployed value 31536000 is
   well inside it). --- *)
Definition secheadersRel_def:
  secheadersRel (code:num) (r0:word64) (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals «maxage» = SOME (ValWord (n2w code)) /\
    FLOOKUP s.locals «result» = SOME (ValWord r0) /\
    code < 9223372036854775808
End

(* ===========================================================================
   The headline core equation, derived AUTOMATICALLY by the REUSABLE tactic
   `panAutoLib.panLinkA_branch`.  The ONLY per-stage inputs are the three
   definitional theorems and the finite (here singleton) guard-predicate list.
   No bespoke hand proof.
   =========================================================================== *)
Theorem evaluate_secheadersCore:
  secheadersRel code r0 s ==>
  evaluate (secheadersCore, s) =
    (NONE, set_var «result» (ValWord (n2w (hstsEffective code))) s)
Proof
  panLinkA_branch (secheadersRel_def, hstsEffective_def, secheadersCore_def)
    [“code < 1n”]
QED

(* --- framed: for the whole-main wrapper; NO clock precondition (branch-only) --- *)
Theorem evaluate_secheadersCore_framed:
  secheadersRel code r0 s ==>
  ?s'. evaluate (secheadersCore, s) = (NONE, s') /\
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (hstsEffective code))) /\
       (!v. v <> «result» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >> drule evaluate_secheadersCore >> strip_tac >>
  qexists_tac `set_var «result» (ValWord (n2w (hstsEffective code))) s` >>
  simp [set_var_def, FLOOKUP_UPDATE] >> rw [] >> simp [FLOOKUP_UPDATE]
QED

(* secheadersCore performs no FFI: reusing the generic noFFI predicate. *)
Theorem secheadersCore_noFFI:
  noFFI secheadersCore
Proof
  REWRITE_TAC [secheadersCore_def] >> EVAL_TAC
QED

val _ = export_theory ();
