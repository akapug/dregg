(* ===========================================================================
   C25 — the THIRD composed stage closed spec->machine-code by ONE
   mk_composedWrapper call (the SAME generator that closed C22 + C23).  Reuses
   the two hashBytes fold cores + the cacheFFI/cacheStaged contract from C22; the
   ONLY new inputs are the CORS wildcard-OR-match gate + spec + program
   (cors.pnk).  The generator applied DIRECTLY - no spine adaptation, no ML peel
   extension: CORS's originAllowed maps onto the 2-fold + scalar-gate shape with
   fold #1 = hash(request origin), fold #2 = hash(policy allowed origin),
   scalar = allowAnyOrigin wildcard.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory composedCommonTheory
     cacheKeyCoreTheory cacheKeyFrameTheory cacheKeyDataTheory
     corsCoreTheory corsDataTheory corsLinkBInstTheory;
open panComposedLib;

val _ = new_theory "corsGen";

val res = panComposedLib.mk_composedWrapper
  { prefix = "cors",
    ffiName = "cacheFFI", ffiDef = cacheFFI_def, ffiArgs = "origin allowed wild",
    stagedDef = cacheStaged_def, clockBound = "LENGTH origin + LENGTH allowed", arena0 = "64w",
    fold0 = { arenaOff="64w", lenOff=NONE, lenExpr="LENGTH origin", memArg="origin",
              loopName="cacheLoop1", framed=cacheLoop1_framed, noFFI=cacheLoop1_noFFI,
              accWord="n2w (hashBytesN origin)", saveVar="km" },
    fold1 = { arenaOff="2112w", lenOff=SOME "8w", lenExpr="LENGTH allowed", memArg="allowed",
              loopName="cacheLoop2", framed=cacheLoop2_framed, noFFI=cacheLoop2_noFFI,
              accWord="n2w (hashBytesN allowed)", saveVar="ku" },
    scalars = [ { off="16w", var="wild", valWord="n2w wild" } ],
    decVar = "dec", gateName="corsGate", gateThm=evaluate_corsGate,
    storeOff="24w", resultWord="n2w (corsAllow wild origin allowed)",
    mainBodyName="corsMainBody", mainBodyDef=corsMainBody_def,
    progName="corsProg", progDef=corsProg_def, linkB=corsProg_linkB,
    unfoldCore=[corsMainBody_def, cacheLoop1_def, cacheLoop2_def, foldGuard_def,
                cacheBodyA1_def, cacheBodyA2_def, corsGate_def] };

val _ = export_theory ();
