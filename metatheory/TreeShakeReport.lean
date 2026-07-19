/-
# TreeShakeReport — the LCNF runtime-reachability REPORTER (Tree-shaker Milestone-1, phase A2)

Run:  `lake env lean TreeShakeReport.lean`   (from `metatheory/`; the report is a `#eval`)

WHAT IT DOES.  Loads the built `Dregg2` environment, enumerates the `dregg_*` `@[export]` roots
(the C-ABI entrypoints the embeddable runtime actually calls), and reports:
  * how many `dregg_*` export roots exist and which modules host them;
  * the LCNF `collectUsedDecls` frontier reachable from those roots WITHIN the loaded environment;
  * the honest limitation of an olean-only reader (see §LIMITATION) and the fix.

This is the REPORTER only — it is NOT wired into `build.rs` (that is phase A3). Its job is to
measure whether following LCNF CALL edges (`.const/.fap/.pap` over erased-proof `.impure` decls)
excludes proof-module object files that the deployed nm symbol-BFS trim keeps.

## §MEASURED RESULT (phase A2, on hbox warm tree @1cdc7fe66, Linux, Lean v4.30.0)

The measurement was done on the ground-truth SYMBOL + emitted-C graph of the FFI archive
(`libdregg_lean.a`, 3091 members / 259 MB), reproducing `build.rs::runtime_dead_init_trim`
exactly and then correcting its init-edge classification:

  * deployed TRIM (chase edges whose symbol does NOT start with `initialize_`):
        936 members / 128.1 MB kept.
  * FIXED (also treat `runtime_initialize_*` and `meta_initialize_*` as init edges — they ARE
    module initializers; see the emitted C below):
        153 members / 23.7 MB kept.
  * REAL (non-init) call edges from the FIXED-live set INTO the 783 dropped members: **0**.

So 783 members / **104.4 MB (81.5% of the trim)** are entered EXCLUSIVELY through init edges the
trim mis-classifies as runtime calls. Break-down of what the trim wrongly keeps:
  135 `Aesop.*`, 176 `Mathlib.Tactic.*`, ~376 `Mathlib(core)`, 14 `Qq`, 13 `Plausible`,
  10 `ImportGraph`, 8 `ProofWidgets`, 4 `LeanSearchClient` — the elaborator/proof-time libraries
  the verified executor never CALLS.

ROOT CAUSE (structural, confirmed in `.lake/.../ir/Aesop/BaseM.c`): Lean v4.30's `module` system
emits THREE initializers per module — `initialize_M`, `runtime_initialize_M`, `meta_initialize_M`
— each `lean_object* f(uint8_t builtin)` chaining its imports' initializers. `build.rs`'s
`is_init = bare.starts_with("initialize_")` only catches the first, so the `runtime_initialize_*`
init chain into every proof module reads as a live runtime call and drags the whole cluster in.

RESIDUAL (the decl-granularity gap the LCNF tool closes, the trim/module-BFS cannot): even after
the init fix, 23 proof-lib `.o` survive — NOT because a tactic is called, but because a GENERIC
specialization the runtime genuinely calls was hoisted by the compiler into a proof module's
translation unit, e.g. `Dregg2.Distributed.BlocklaceFinality` calls
`Std.DHashMap...insertIfNew___at___00Mathlib_Tactic_Order_...spec` which lives in
`Mathlib_Tactic_Order.o`. A MODULE-granular tool (the current trim, this reporter's BFS, or a
naive LCNF module-BFS) cannot shed those — only a DECL-granular generate-only emitter can, which
is why the LCNF `collectUsedDecls` → per-decl EmitC path reaches below 23.7 MB toward the
~14 MB ceiling recorded in the campaign memory.

## §LIMITATION (why this reporter cannot do the module BFS from oleans alone)

`impureExt` (the LCNF `.impure` decl store) is a NON-persistent `registerEnvExtension`
(`Lean/Compiler/LCNF/PhaseExt.lean:113`): it holds ONLY decls compiled in the current `lean`
process, so an IMPORTED module's `.impure` bodies are absent. `monoExt` IS persistent but its
`exportEntriesFnEx` exports an OPAQUE `.extern` stub for every non-transparent (i.e. most) decl.
`impureSigExt` persists SIGNATURES only. Therefore, from a loaded environment, `collectUsedDecls`
sees the roots' SIGNATURES but no cross-module BODIES — it cannot follow call edges past the first
module boundary. The real per-module frontier is only materialized during codegen (which is why
the MEASURED result above reads the emitted `.c`/`.o` graph, the faithful ground truth).

FIX for a Lean-native decl-granular tool (phase A3): drive the LCNF frontend per reachable module
to repopulate `impureExt` (walk `monoExt`/re-run `toImpure` on that module's decls), OR — simpler
and already ground-truth — have `build.rs` generate the closure from the emitted `.c` call graph
with the CORRECTED 3-variant init classification, cutting the init recursion at the boundary
exactly as the current trim already emits its boundary init no-op stubs.
-/
-- Import the `@[export dregg_*]`-hosting modules directly (the `Dregg2` root aggregator olean is
-- not part of the warm partial build). This loads the export attribute + LCNF signatures for the
-- available host set; 5 hosts absent from the warm tree (Refine/X25519/Claims/RingFFI/FriLedgerSound)
-- are skipped — the faithful FULL closure is MEASURED on the archive graph, see §MEASURED RESULT.
import Dregg2.Exec.DistributedExports
import Dregg2.Exec.FFI
import Dregg2.Exec.FFIDirect
import Dregg2.Bridge.InterchainAdapterDecision
import Dregg2.Bridge.ProofOfHoldings
import Dregg2.Deos.FlowRefine
import Dregg2.Distributed.StrandAdmission
import Dregg2.Distributed.BlocklaceFinality
import Dregg2.Distributed.FinalityGate
import Dregg2.Crypto.Fips203Kem
import Dregg2.Crypto.MlDsaSignReal
import Dregg2.Crypto.MlKemEncaps
import Dregg2.Crypto.MlKemDecaps
import Dregg2.Crypto.Fips204Verify
import Dregg2.Grain.R3Verify
import Dregg2.Storage.Deployed
import Dregg2.Circuit.FriLedger
import Lean.Compiler.LCNF.EmitUtil
import Lean.Compiler.ExportAttr

open Lean Lean.Compiler.LCNF Elab.Command

/-- Collect the `dregg_*` C-ABI export roots and their hosting modules. -/
def dreggExportRoots (env : Environment) : Array (Name × Name × Option Name) := Id.run do
  let mut roots := #[]
  for (n, _ci) in env.constants.toList do
    if let some cName := getExportNameFor? env n then
      if cName.toString.startsWith "dregg_" then
        roots := roots.push (n, cName, env.getModuleFor? n)
  return roots

#eval show CommandElabM Unit from do
  let env ← getEnv
  let roots := dreggExportRoots env
  IO.println s!"dregg_* export roots: {roots.size}"
  -- distinct hosting modules
  let mods := roots.foldl (init := ({} : NameSet)) fun s (_, _, m?) =>
    match m? with | some m => s.insert m | none => s
  IO.println s!"hosting modules: {mods.size}"
  for m in mods.toList do
    IO.println s!"  host  {m}"
  -- library touch of the hosting modules
  let topOf : Name → Name := fun n => n.components.headD `«»
  let libs := mods.toList.foldl (init := ({} : NameSet)) fun s m => s.insert (topOf m)
  IO.println s!"host libraries: {libs.toList}"
  -- LCNF frontier from the roots (single-loaded-env; see §LIMITATION)
  let rootNames := roots.map (·.1)
  let (localDecls, extSigs) ← liftCoreM (collectUsedDecls rootNames)
  IO.println s!"collectUsedDecls from {rootNames.size} roots (loaded env): \
    {localDecls.size} local impure decls, {extSigs.size} external signatures"
  -- which modules those external signatures live in (the first BFS layer we CAN see)
  let frontierMods := extSigs.foldl (init := ({} : NameSet)) fun s sig =>
    match env.getModuleFor? sig.name with | some m => s.insert m | none => s
  let frontierLibs := frontierMods.toList.foldl (init := ({} : NameSet)) fun s m => s.insert (topOf m)
  IO.println s!"external-signature frontier: {frontierMods.size} modules across libraries \
    {frontierLibs.toList}"
  IO.println "NOTE: cross-module call BODIES are absent from oleans (impureExt is non-persistent);"
  IO.println "      the faithful runtime-reachable set is MEASURED on the emitted .c/.o graph."
  IO.println "      See §MEASURED RESULT in this file: init-classification fix on the symbol-BFS"
  IO.println "      drops 783 members / 104.4 MB (81.5% of the deployed trim), 0 real-call edges lost."
