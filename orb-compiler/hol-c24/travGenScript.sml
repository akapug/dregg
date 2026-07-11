(* ===========================================================================
   C24 — the traversal gate stage closed spec->machine-code by ONE
   mk_composedWrapper1 call (the N = 1 peel of the C23 composed generator).
   Single escape-scan fold (escLoop) + the state->decision gate (travGate); the
   generator emits MainRefine + Sem + Install + EndToEnd -> traversal_machine_code.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory composedCommonTheory
     travCoreTheory travDataTheory travLinkBInstTheory;
open panComposedLib;

val _ = new_theory "travGen";

val res = panComposedLib.mk_composedWrapper1
  { prefix = "traversal",
    ffiName = "travFFI", ffiDef = travFFI_def, ffiArgs = "input",
    stagedDef = travStaged_def, clockBound = "LENGTH input", arena0 = "32w",
    fold0 = { arenaOff="32w", lenOff=NONE, lenExpr="LENGTH input", memArg="input",
              loopName="escLoop", framed=escLoop_framed, noFFI=escLoop_noFFI,
              accWord="travEsc input", saveVar="acc" },
    decVar = "dec", gateName="travGate", gateThm=evaluate_travGate,
    storeOff="8w", resultWord="travDecide input",
    mainBodyName="travMainBody", mainBodyDef=travMainBody_def,
    progName="travProg", progDef=travProg_def, linkB=travProg_linkB,
    unfoldCore=[travMainBody_def, escLoop_def, foldGuard_def, escBody_def, travGate_def] };

val _ = export_theory ();
