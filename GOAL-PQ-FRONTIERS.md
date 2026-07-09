<!-- ⚑ This repo runs MULTIPLE /goal lanes — see GOALS-INDEX.md. This is the PQ-FRONTIERS (retire-the-open) lane ONLY.
     Edit only THIS file; never clobber another lane's trail or files. -->

# GOAL — RETIRE EVERY HONESTLY-OPEN FRONTIER (crypto-to-protocol-soundness)

These are NOT genuine open problems — they are PUBLISHED results to be FORMALIZED. The bar is CLOSE each by
formalizing the literature's argument. Banned BOTH ways: (a) SMUGGLE an assumption as closure (laundering), and
(b) GIVE UP — call formalizable literature work "too hard / a genuine open problem." Formalizing a paper's proof
is WORK, not a research frontier. The ONLY terminal trusted base is the lattice/DL/hash floor + the leanc
toolchain. WHOLE-TREE green after every change (`lake build Dregg2`).

## The four frontiers (each CLOSED by formalizing its literature argument)
1. LOSS-FREE ADAPTIVE (AdaptiveTSUF.lean) — FORMALIZE the Unmasking-TRaccoon (2025) adaptive-security proof:
   the Gaussian/flooding masking lets the simulator answer ANY member's partial signatures on demand from the
   public transcript (grounded in HintTranscriptSimulatable / hint_mlwe_reduces_to_mlwe), so adaptive
   corruption is simulatable WITHOUT the corrupt set → DISCHARGE `AdaptiveErasure`, prove
   adaptive_ts_uf_reduces_lossfree UNCONDITIONALLY → MSIS∨MLWE∨HashCR. Close it.
2. FULL UC (UcSignature.lean) — FORMALIZE the Canetti UC framework: concurrent multi-session execution + the
   general universal-composition theorem (π using F_SIG, composed with the realization, is secure). Prove the
   composition theorem for the hybrid sig. Textbook — formalize it.
3. VERIFIED-FIPS204 crate↔spec (Fips204Spec.lean + dregg-pq) — make the FIPS-204 core EXECUTABLE Lean, EXTRACT
   via @[export] (the PROVEN storage-in-lean/BucketCommitment pattern — leanc, FFI), wire dregg-pq to the
   extracted verified core, DISCHARGE Fips204Correct with a Lean-verified object. Engineering — do it; the only
   residual trust is leanc/FFI (the toolchain TCB).
4. SURFACE-3 EXECUTOR SEAM (blocklace/node) — migrate run_finality_executor + finality_gate.rs VerifiedFinality
   participant projection to the hybrid id so NO live path projects identity through raw ed25519.

## Discipline
CLOSE by formalizing the literature (no giving up); NO named-carrier laundering (no smuggling); load-bearing
#guard teeth; whole-tree green; main loop wires Dregg2.lean imports; never touch other lanes' files / Cargo.lock
/ git add -A. Sign Co-Authored-By: Claude Opus 4.8. Terminal trusted base = the floor + leanc, NOTHING else.

## Next 3 moves
1. Fan out all 4 frontiers (ultracode Workflow); each drives to closure OR the precise obstacle.
2. Integrate: wire imports, whole-tree lake build green, commit each; Rust frontiers cargo-verified.
3. HORIZONLOG + memory the honest FINAL state (proved / true-open-with-obstacle / minimal trusted base).

## Done-log (newest last)
- (start) goal set; frontiers fanning out.
- ✅ ALL FOUR CLOSED: adaptive cb2699569 (AdaptiveErasure discharged, loss-free) · uc e7cb09c2d (multi-session
  + composition theorem) · fips204 d051ff9d1 (VERIFY extracted to leanc-native, Fips204Correct discharged) ·
  surface3 a618be80d (executor seam). Trusted base = lattice/DL/hash FLOOR + leanc/FFI toolchain ONLY. DONE.
