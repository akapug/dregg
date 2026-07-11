(* ===========================================================================
   C23 REGRESSION — mk_composedWrapper reproduces C22's composed end-to-end
   theorem from ONE generator call over the SAME parser-output cacheMainBody /
   cacheKeyProg.  The bespoke ~347-line MainRefine + tail (cacheKeyGen) becomes
   the record below + `mk_composedWrapper`.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory composedCommonTheory
     cacheKeyCoreTheory cacheKeyFrameTheory cacheKeyDataTheory cacheKeyLinkBInstTheory;
open panComposedLib;

val _ = new_theory "cacheKeyGen2";

val res = panComposedLib.mk_composedWrapper
  { prefix = "cacheKeyRegen",
    ffiName = "cacheFFI", ffiDef = cacheFFI_def, ffiArgs = "method tgt age",
    stagedDef = cacheStaged_def, clockBound = "LENGTH method + LENGTH tgt", arena0 = "64w",
    fold0 = { arenaOff="64w", lenOff=NONE, lenExpr="LENGTH method", memArg="method",
              loopName="cacheLoop1", framed=cacheLoop1_framed, noFFI=cacheLoop1_noFFI,
              accWord="n2w (hashBytesN method)", saveVar="km" },
    fold1 = { arenaOff="2112w", lenOff=SOME "8w", lenExpr="LENGTH tgt", memArg="tgt",
              loopName="cacheLoop2", framed=cacheLoop2_framed, noFFI=cacheLoop2_noFFI,
              accWord="n2w (hashBytesN tgt)", saveVar="ku" },
    scalars = [ { off="16w", var="age", valWord="n2w age" } ],
    decVar = "dec", gateName="cacheGate", gateThm=evaluate_cacheGate,
    storeOff="24w", resultWord="n2w (cacheServe method tgt age)",
    mainBodyName="cacheMainBody", mainBodyDef=cacheMainBody_def,
    progName="cacheKeyProg", progDef=cacheKeyProg_def, linkB=cacheKeyProg_linkB,
    unfoldCore=[cacheMainBody_def, cacheLoop1_def, cacheLoop2_def, foldGuard_def,
                cacheBodyA1_def, cacheBodyA2_def, cacheGate_def] };

val _ = export_theory ();
