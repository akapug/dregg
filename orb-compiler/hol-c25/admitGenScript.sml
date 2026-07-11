(* ===========================================================================
   C23 — the SECOND composed stage closed spec->machine-code by ONE
   mk_composedWrapper call (the SAME generator that reproduced C22).  Reuses the
   two hashBytes fold cores + the cacheFFI/cacheStaged contract from C22; the
   ONLY new inputs are the 2-way admit gate + spec + program (admit.pnk).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory composedCommonTheory
     cacheKeyCoreTheory cacheKeyFrameTheory cacheKeyDataTheory
     admitCoreTheory admitDataTheory admitLinkBInstTheory;
open panComposedLib;

val _ = new_theory "admitGen";

val res = panComposedLib.mk_composedWrapper
  { prefix = "admit",
    ffiName = "cacheFFI", ffiDef = cacheFFI_def, ffiArgs = "method tgt age",
    stagedDef = cacheStaged_def, clockBound = "LENGTH method + LENGTH tgt", arena0 = "64w",
    fold0 = { arenaOff="64w", lenOff=NONE, lenExpr="LENGTH method", memArg="method",
              loopName="cacheLoop1", framed=cacheLoop1_framed, noFFI=cacheLoop1_noFFI,
              accWord="n2w (hashBytesN method)", saveVar="km" },
    fold1 = { arenaOff="2112w", lenOff=SOME "8w", lenExpr="LENGTH tgt", memArg="tgt",
              loopName="cacheLoop2", framed=cacheLoop2_framed, noFFI=cacheLoop2_noFFI,
              accWord="n2w (hashBytesN tgt)", saveVar="ku" },
    scalars = [ { off="16w", var="age", valWord="n2w age" } ],
    decVar = "dec", gateName="admitGate", gateThm=evaluate_admitGate,
    storeOff="24w", resultWord="n2w (admitDecide method tgt)",
    mainBodyName="admitMainBody", mainBodyDef=admitMainBody_def,
    progName="admitProg", progDef=admitProg_def, linkB=admitProg_linkB,
    unfoldCore=[admitMainBody_def, cacheLoop1_def, cacheLoop2_def, foldGuard_def,
                cacheBodyA1_def, cacheBodyA2_def, admitGate_def] };

val _ = export_theory ();
