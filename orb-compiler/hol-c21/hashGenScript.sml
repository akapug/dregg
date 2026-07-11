(* ===========================================================================
   C21 — REGRESSION: the C20 hand stack (MainRefine + Sem + Install + EndToEnd,
   ~400 hand lines) reproduced by a SINGLE `mk_foldWrapper` generator call.  The
   emitted `hash_machine_code` is the SAME spec->machine-code theorem C20 proved
   by hand (over the parser-output `hashBytesProg`, leanc out of the TCB).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory
     optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory hashCoreTheory hashDataTheory
     hashBytesLinkBInstTheory;
open panWrapperLib;

val _ = new_theory "hashGen";

val hashRes =
  mk_foldWrapper
    { prefix        = "hash",
      ffiName       = "hashFFI",         ffiDef      = hashFFI_def,
      ctrlStagedDef = hashCtrlStaged_def,
      arenaOff      = "32w",             koff        = "8w",
      specWord      = "n2w (hashBytesN input)",
      coreName      = "hashLoopCore",    coreFramed  = evaluate_hashLoopCore_framed,
      coreNoFFI     = hashLoopCore_noFFI,
      unfoldCore    = [hashLoopCore_def, foldGuard_def, hashBodyA_def],
      mainBodyName  = "hashMainBody",    mainBodyDef = hashMainBody_def,
      progName      = "hashBytesProg",   progDef     = hashBytesProg_def,
      linkB         = hashBytesProg_linkB };

(* The generator already `save_thm`s `hashMainBody_refines`, `hash_call_main_run`,
   `hash_main_semantics`, `hashProg_semantics_decls` and `hash_machine_code` into
   this theory segment; nothing more to declare. *)
val _ = (hashRes : {mainRefine:thm, callMainRun:thm, mainSemantics:thm,
                    semanticsDecls:thm, machineCode:thm});

val _ = export_theory ();
