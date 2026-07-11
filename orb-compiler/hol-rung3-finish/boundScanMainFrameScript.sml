(* ===========================================================================
   CN RUNG-3 FINISH — gap (1) ATTEMPT: the whole-`main` Link-A frame.

   Ground: CN-BOUNDSCAN-LINKA-REPORT §5 named, as the residual to a whole-`main`
   Link A, the `Dec`/`@load_vec`-FFI frame that establishes `loopInv … 0 0` plus
   the mechanical `If`+loop composition.  This theory pins EXACTLY what that frame
   must thread (a kernel-checked structural extraction of the `main` body from the
   verified-parser program) and discharges the loop-BODY frame lemmas the
   composition rests on.  It reports precisely the residual (§ report).

   Contents (all [oracles: DISK_THM] [axioms:], 0 theory axioms):
     scanBody_frame   — one loop-body iteration writes ONLY «acc»/«i»
     scanBody_res     — scanBody returns NONE or (SOME Error) (never Break/…)
     scanBody_clock   — scanBody preserves the clock (no Tick/While/Call)
     scanBody_fixclock— hence panSem's While `fix_clock` on scanBody is identity
     elseBranch_def / extract_else / elseBranch_faithful
                      — the If's else-arm (Dec «acc» 0; Dec «i» 0; scanLoop;
                        «result»:=«acc») IS the else-arm of the real boundScanProg
                        (structurally extracted from the C10 verified-parser AST,
                        kernel-checked by EVAL — NOT hand-transcribed).
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory pairTheory finite_mapTheory;
open panLangTheory panSemTheory;
open boundScanLinkBTheory boundScanLoopLinkATheory;

val _ = new_theory "boundScanMainFrame";

(* ---- the loop-body frame ingredients (the clocked-While frame rests on these) ---- *)

Theorem scanBody_frame:
  evaluate (scanBody, s) = (NONE, s2) ==>
  !v. v <> (strlit "acc") /\ v <> (strlit "i") ==>
      FLOOKUP s2.locals v = FLOOKUP s.locals v
Proof
  strip_tac >> qpat_x_assum `evaluate _ = _` mp_tac >>
  simp[scanBody_def, evaluate_def] >> rpt (CASE_TAC >> gvs[set_var_def]) >>
  rw[] >> gvs[FLOOKUP_UPDATE]
QED

Theorem scanBody_res:
  evaluate (scanBody, s) = (r, s') ==> r = NONE \/ r = SOME Error
Proof
  strip_tac >> qpat_x_assum `evaluate _ = _` mp_tac >>
  simp[scanBody_def, evaluate_def] >> rpt (CASE_TAC >> gvs[]) >> rw[] >> gvs[]
QED

Theorem scanBody_clock:
  evaluate (scanBody, s) = (r, s') ==> s'.clock = s.clock
Proof
  strip_tac >> qpat_x_assum `evaluate _ = _` mp_tac >>
  simp[scanBody_def, evaluate_def] >> rpt (CASE_TAC >> gvs[set_var_def]) >>
  rw[] >> gvs[]
QED

Theorem scanBody_fixclock:
  fix_clock t (evaluate (scanBody, t)) = evaluate (scanBody, t)
Proof
  Cases_on `evaluate (scanBody, t)` >> drule scanBody_clock >>
  rw[fix_clock_def, state_component_equality]
QED

(* ---- the If's else-arm, structurally extracted from the REAL boundScanProg ---- *)

Definition elseBranch_def:
  elseBranch =
    Seq (Annot (strlit "location") (strlit "(UNKNOWN 40:15)"))
      (Dec (strlit "acc") One (Const 0w)
         (Seq (Annot (strlit "location") (strlit "(UNKNOWN 40:15)"))
            (Dec (strlit "i") One (Const 0w)
               (Seq
                  (Seq (Annot (strlit "location") (strlit "(36:10 38:13)"))
                       scanLoop)
                  (Seq (Annot (strlit "location") (strlit "(40:4 40:15)"))
                       (Assign Local (strlit "result")
                          (Var Local (strlit "acc"))))))))
End

Definition extract_else_def:
  extract_else (Seq c1 c2) =
    (case extract_else c1 of SOME e => SOME e | NONE => extract_else c2) /\
  extract_else (Dec _ _ _ p) = extract_else p /\
  extract_else (If _ _ e) = SOME e /\
  extract_else _ = NONE
End

Definition extract_else_decl_def:
  extract_else_decl (Function fd) = extract_else fd.body /\
  extract_else_decl _ = NONE
End

Theorem elseBranch_faithful:
  extract_else_decl (HD boundScanProg) = SOME elseBranch
Proof
  rw[boundScanProg_def, extract_else_decl_def, extract_else_def,
     elseBranch_def, scanLoop_def, scanBody_def]
QED

val _ = export_theory ();
