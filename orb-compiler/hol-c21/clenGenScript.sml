(* ===========================================================================
   C21 — THE SECOND FOLD, CLOSED BY THE GENERATOR.  A SINGLE `mk_foldWrapper`
   call closes the Content-Length decimal fold spec->machine-code end-to-end:
   the whole-program wrapper (MainRefine + Sem + Install + EndToEnd) is generated
   mechanically from the ~8-line C19-style core (`clenCore`) + the fold data
   (`clenData`) + Link B — NO per-fold wrapper proof.  leanc out of the TCB
   (clenProg is the parser output).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory
     optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory clenCoreTheory clenDataTheory clenLinkBInstTheory;
open panWrapperLib;

val _ = new_theory "clenGen";

val clenRes =
  mk_foldWrapper
    { prefix        = "clen",
      ffiName       = "clenFFI",         ffiDef      = clenFFI_def,
      ctrlStagedDef = clenCtrlStaged_def,
      arenaOff      = "32w",             koff        = "8w",
      specWord      = "n2w (clenN input)",
      coreName      = "clenLoopCore",    coreFramed  = evaluate_clenLoopCore_framed,
      coreNoFFI     = clenLoopCore_noFFI,
      unfoldCore    = [clenLoopCore_def, foldGuard_def, clenBodyA_def],
      mainBodyName  = "clenMainBody",    mainBodyDef = clenMainBody_def,
      progName      = "clenProg",        progDef     = clenProg_def,
      linkB         = clenProg_linkB };

val _ = (clenRes : {mainRefine:thm, callMainRun:thm, mainSemantics:thm,
                    semanticsDecls:thm, machineCode:thm});

val _ = export_theory ();
