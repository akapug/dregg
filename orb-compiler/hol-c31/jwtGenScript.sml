(* ===========================================================================
   C31 — the HS256 JWT admin gate's sig-verify + alg-confusion decision closed
   spec->machine-code by ONE mk_composedWrapper call (the SAME generator that
   closed C22 + C23 + C25 + C27).  Reuses the two hashBytes fold cores + the
   cacheFFI/cacheStaged contract from C22; the ONLY new inputs are the sig-equality
   + alg gate, the spec, and the program (jwt.pnk).  The generator applied DIRECTLY
   - no spine adaptation, no ML peel extension: the JWT admit decision maps onto the
   2-fold + scalar-gate shape with fold #1 = hash(HMAC digest), fold #2 =
   hash(decoded signature), and the ONE staged scalar @+16 = the token's declared
   alg tag (READ by the gate, unlike C27 where it was staged-but-unused): the gate
   is sig-equality (hash(digest)=hash(sig)) AND alg-confusion-absent (alg=HS256).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory composedCommonTheory
     cacheKeyCoreTheory cacheKeyFrameTheory cacheKeyDataTheory
     jwtCoreTheory jwtDataTheory jwtLinkBInstTheory;
open panComposedLib;

val _ = new_theory "jwtGen";

val res = panComposedLib.mk_composedWrapper
  { prefix = "jwt",
    ffiName = "cacheFFI", ffiDef = cacheFFI_def, ffiArgs = "digest sig alg",
    stagedDef = cacheStaged_def, clockBound = "LENGTH digest + LENGTH sig", arena0 = "64w",
    fold0 = { arenaOff="64w", lenOff=NONE, lenExpr="LENGTH digest", memArg="digest",
              loopName="cacheLoop1", framed=cacheLoop1_framed, noFFI=cacheLoop1_noFFI,
              accWord="n2w (hashBytesN digest)", saveVar="km" },
    fold1 = { arenaOff="2112w", lenOff=SOME "8w", lenExpr="LENGTH sig", memArg="sig",
              loopName="cacheLoop2", framed=cacheLoop2_framed, noFFI=cacheLoop2_noFFI,
              accWord="n2w (hashBytesN sig)", saveVar="ku" },
    scalars = [ { off="16w", var="alg", valWord="n2w alg" } ],
    decVar = "dec", gateName="jwtGate", gateThm=evaluate_jwtGate,
    storeOff="24w", resultWord="n2w (jwtAdmit digest sig alg)",
    mainBodyName="jwtMainBody", mainBodyDef=jwtMainBody_def,
    progName="jwtProg", progDef=jwtProg_def, linkB=jwtProg_linkB,
    unfoldCore=[jwtMainBody_def, cacheLoop1_def, cacheLoop2_def, foldGuard_def,
                cacheBodyA1_def, cacheBodyA2_def, jwtGate_def] };

val _ = export_theory ();
