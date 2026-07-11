(* ===========================================================================
   C27 — the Basic-auth compare gate closed spec->machine-code by ONE
   mk_composedWrapper call (the SAME generator that closed C22 + C23 + C25).
   Reuses the two hashBytes fold cores + the cacheFFI/cacheStaged contract from
   C22; the ONLY new inputs are the single hash-equality gate + spec + program
   (basic.pnk).  The generator applied DIRECTLY - no spine adaptation, no ML peel
   extension: `verify` maps onto the 2-fold + scalar-gate shape with fold #1 =
   hash(presented credential), fold #2 = hash(configured credential), the scalar
   @+16 staged-but-unused (as C23 admit's age).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory composedCommonTheory
     cacheKeyCoreTheory cacheKeyFrameTheory cacheKeyDataTheory
     basicCoreTheory basicDataTheory basicLinkBInstTheory;
open panComposedLib;

val _ = new_theory "basicGen";

val res = panComposedLib.mk_composedWrapper
  { prefix = "basic",
    ffiName = "cacheFFI", ffiDef = cacheFFI_def, ffiArgs = "cred configured pad",
    stagedDef = cacheStaged_def, clockBound = "LENGTH cred + LENGTH configured", arena0 = "64w",
    fold0 = { arenaOff="64w", lenOff=NONE, lenExpr="LENGTH cred", memArg="cred",
              loopName="cacheLoop1", framed=cacheLoop1_framed, noFFI=cacheLoop1_noFFI,
              accWord="n2w (hashBytesN cred)", saveVar="km" },
    fold1 = { arenaOff="2112w", lenOff=SOME "8w", lenExpr="LENGTH configured", memArg="configured",
              loopName="cacheLoop2", framed=cacheLoop2_framed, noFFI=cacheLoop2_noFFI,
              accWord="n2w (hashBytesN configured)", saveVar="ku" },
    scalars = [ { off="16w", var="pad", valWord="n2w pad" } ],
    decVar = "dec", gateName="basicGate", gateThm=evaluate_basicGate,
    storeOff="24w", resultWord="n2w (basicAdmit cred configured)",
    mainBodyName="basicMainBody", mainBodyDef=basicMainBody_def,
    progName="basicProg", progDef=basicProg_def, linkB=basicProg_linkB,
    unfoldCore=[basicMainBody_def, cacheLoop1_def, cacheLoop2_def, foldGuard_def,
                cacheBodyA1_def, cacheBodyA2_def, basicGate_def] };

val _ = export_theory ();
