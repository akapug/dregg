# EffectVM AIR verification census — "what does the AIR NOT verify?"

A grounded, op-by-op audit of the EffectVM AIR (the deployed IR-v2 multi-table
descriptor circuit) answering one question: **for every op / declared column, is
the property GENUINELY forced in-circuit (so a light client that checks the STARK
witnesses it), or is the real check delegated to an out-of-circuit / off-AIR
verifier (a TRUSTED SURFACE the bare STARK does not witness)?**

Provenance: triggered by the `Effect::Custom` `proofBind` finding — the in-AIR op
is `| .proofBind _ => True` (`metatheory/Dregg2/Circuit/DescriptorIR2.lean:570`),
the genuine sub-proof check is the out-of-circuit Rust
`dregg_circuit_prove::custom_proof_bind::verify_proof_bind`
(`circuit-prove/src/custom_proof_bind.rs`). This census asks what ELSE is in that
class.

Verified against Lean (`DescriptorIR2.lean`, `CircuitOpenFronts.lean`) and the
deployed Rust AIR (`circuit/src/descriptor_ir2.rs`, `circuit/src/effect_vm/{air,
pi,trace,trace_rotated,columns}.rs`, `turn/src/executor/{proof_verify,authorize}.rs`)
at HEAD.

## Classification key

- **(1) GENUINELY ENFORCED** — a real in-AIR polynomial / bus constraint forces
  the property; the light client witnesses it. The good case.
- **(2) ROW-LOCAL-`True`, FORCED ELSEWHERE IN-CIRCUIT** — the per-row denotation
  is `True`, but the content is a GLOBAL leg realized by an in-circuit LogUp bus
  (memory / universal-memory balance). A bad witness cannot satisfy the bus →
  fail-closed → NOT a soundness hole.
- **(3) TRUSTED-OUT-OF-CIRCUIT** — the in-AIR op only records columns / PI; the
  real check is an off-AIR Rust verifier (recursive STARK verify, signature
  verify). The bare EffectVM STARK does NOT witness it. **These are the answer.**
- **(4) CARRIED-NOT-FORCED column** — a column the AIR records but no constraint
  binds (a column-level version of (3)).

## The op grammar (`VmConstraint2`, `DescriptorIR2.lean:372`)

| op | per-row semantics | in-circuit realization | class | honest? |
|----|-------------------|------------------------|-------|---------|
| `base (Gate/Boundary/Transition)` | polynomial `= 0` (`VmConstraint.holdsVm`) | `assert_zero` / `when_first/last/transition` | **1** | n/a |
| `base (PiBinding)` | `local[col] − pi[i] = 0` (`CircuitEmit.lean:525`) | boundary `assert_zero` binding column↔PI | **1** | n/a |
| `lookup (Lookup)` | `tuple.map eval ∈ table` (`DescriptorIR2.lean:432`) | LogUp bus (`BUS_FACT`, byte/range buses) | **1** | n/a |
| `mapOp (MapOp)` | `opensTo`/`writesTo` row-local (`:496`) | Poseidon2 Merkle path on the chip bus `BUS_P2`; functional under CR (`opensTo_functional :465`) | **1** | n/a |
| `memOp (MemOp)` | `True` row-local (`:567`) | global `Satisfied2` legs: `memDisciplined`/`memBalanced`/`memTableFaithful` → `BUS_MEM_LOG/CHECK/ADDRS` LogUp (Blum `memcheck_sound`) | **2** | honest |
| `umemOp (UMemOp)` | `True` row-local (`:569`) | global `Satisfied2U` legs: `umemBalanced`/`umemDisciplined`/`umemAddrs`/`umemNullifierInsertOnly` → `BUS_UMEM_LOG/CHECK/ADDRS` LogUp (`universal_memory_sound`) | **2** | honest |
| `windowGate (WindowConstraint)` | two-row poly `= 0` (`:357`) | windowed `assert_zero` (`when_transition`) | **1** | n/a |
| `proofBind (ProofBind)` | `True` row-local (`:570`) | **NONE in-AIR** — no bus, bounds-check only (`descriptor_ir2.rs:1299-1305`); content = `Satisfied2Custom.proofBound` leg, an `EngineBinding` named hypothesis; real check is off-AIR `verify_proof_bind` | **3** | honest |

`base`/`lookup`/`mapOp`/`windowGate` are genuinely enforced. `memOp`/`umemOp` are
row-local `True` but their content rides real in-circuit LogUp buses (the memory /
universal-memory balance arguments are arithmetized in the deployed descriptor —
`descriptor_ir2.rs:8-29`, bus constants `:275-284`), so they are fail-closed, not
holes. **`proofBind` is the only op kind with NO in-circuit realization at all** —
no bus, no polynomial; the column pair `(commit, vk)` is declaration-and-bounds
only, and the program-correctness recursion is delegated off-AIR.

## The PI-carried surfaces (column-level, not `VmConstraint2` ops)

The EffectVM AIR records many values in the public inputs that an **off-AIR
verifier** (`turn::executor::proof_verify` / `verify_effect_binding_proofs`) reads.
Two distinct sub-classes:

### Benign: off-AIR PI-MATCH reconstruction (class 2-equivalent)

The bulk of "off-AIR verifier" comments in `pi.rs` / `trace.rs` describe the
verifier RECONSTRUCTING a value from PUBLIC turn data (call_forest, ACTOR_NONCE,
emit-event counts, bilateral roots, note/burn schemas, …) and matching it to the
in-circuit-bound PI. Because (a) the PI is bound to the trace in-circuit via
`PiBinding`, and (b) the reconstruction is a deterministic function of public data,
**a light client reproduces both legs itself** — this is the standard public-input
contract, NOT a trusted surface. Examples: `pi.rs:125,485,512,564,594,627`;
`trace.rs:23,644,1018,1316`. No action needed; named here so they are not mistaken
for class (3).

### Trusted: off-AIR recursion / signature (class 3)

| surface | PI slots | real check (off-AIR) | status | honest? |
|---------|----------|----------------------|--------|---------|
| **Custom proof_bind** | `CUSTOM_PROOFS_*` + descriptor cols 68/72 | recursive STARK verify `verify_proof_bind` (`circuit-prove/src/custom_proof_bind.rs`) | LIVE; commitment 4-felt/~62-bit (below the 8-felt/~124-bit floor) | honest |
| **Sovereign transition proof (Phase 2)** | `SOVEREIGN_TRANSITION_PROOF_{VK_HASH,COMMITMENT}`, `HAS_TRANSITION_PROOF` (`pi.rs:240-250`) | off-AIR recursive STARK verify ("the off-AIR verifier reads … and recursively verifies the inner STARK", `pi.rs:209-213`; `proof_verify.rs:2485`) | **STAGED** — VK is sentinel-zero today (`proof_verify.rs:2483-2485`), recursive verifier "in a follow-up" | honest |
| **Sovereign witness signature + sequence** | `SOVEREIGN_WITNESS_{KEY_COMMIT,SEQUENCE}`, `IS_SOVEREIGN_CELL` (`pi.rs:223-235`) | Ed25519 signature verify off-AIR (`authorize.rs:889 verify_ed25519_signature`) + monotonic-sequence chain-walk at executor injection | LIVE; PI carries only a 4-felt key DIGEST + sequence, "backed off-AIR by the actual signature verification" (`pi.rs:217-222`) | honest |

All three are explicitly NAMED at the code level (the Lean comments, the Rust
`pi.rs`/`trace.rs` doc-comments, and `docs/deos/CUSTOM-VK-AUTHORIZATION.md` are all
scrupulous). None is a *laundered* overclaim (no code/doc asserts these are
in-circuit). They ARE genuine trusted surfaces: a light client that runs only the
aggregate EffectVM STARK does NOT witness them and must additionally run the
recursive verify / signature verify (or trust the federation verifier that does).

## Re-verdict on the two completeness claims

### (a) "proofBind was the last vacuous gate" (commit `b597fe342`)

**Partly true, but easy to misread.** What the commit actually did: it closed the
last vacuous per-effect *gate* (`Effect::Custom`'s `descriptorRefines` was vacuous
— a prover could bind any sub-proof) by adding a **verifier-side** genuine
recursive verify (`custom_proof_bind.rs`). The commit body is scrupulous:
"verifier-side soundness, VK-FREE; no Lean".

But it did NOT make `proofBind` enforced *in the AIR*:

- The in-AIR op is STILL `| .proofBind _ => True` (`DescriptorIR2.lean:570`,
  unchanged) and STILL bounds-only in Rust (`descriptor_ir2.rs:1299`).
- THREE row-local `=> True` ops remain (`memOp`, `umemOp`, `proofBind`). The first
  two are benign (class 2 — forced by in-circuit LogUp buses). `proofBind` is the
  one whose content is off-AIR.
- So "GENUINELY verifies" is true **verifier-side**, false **in-AIR**. proofBind
  remains a class-(3) trusted-out-of-circuit surface; the recursion soundness is
  the named `EngineBinding`/`recursive_sound` hypothesis (`DescriptorIR2.lean:867`),
  not an arithmetized constraint.

The real in-AIR fix (verify the sub-proof IN-AIR via the recursion verifier
`verify_p3_batch_proof_circuit` already used by `ivc_turn_chain.rs` for turn-leaves,
+ lift the commitment 4→8 felt) is VK-affecting and parked with the umem VK epoch.

### (b) `Circuit.CircuitOpenFronts.countOpenFronts = 0` / "32/32 effects"

**Honest for what it measures; it UNDERCOUNTS the trusted-surface class.**
`countOpenFronts` is `openFronts.length` (`CircuitOpenFronts.lean:88-117`), and
`openFronts` is the **per-effect adversarial-witness-EXTRACTION** lane (circuit ⊑
spec refinement: an arbitrary PI-bound satisfying trace forces the genuine kernel
step). That lane is genuinely closed for the 32 enumerated effects.

What the metric does NOT count:

1. Row-local `=> True` ops whose content is a global leg (`memOp`/`umemOp` — benign
   anyway, but invisible to this count).
2. The `proofBind`/Custom off-AIR recursion (and `Effect::Custom` is not even one of
   the 32 — it rides the `closedLogExtract_all_genuine` catch-all
   `| (n+1) => rds.other (n+1)`, `ClosureFanoutGenuine.lean:1009`; see the apex
   memory correction).
3. The sovereign off-AIR signature / transition-proof surfaces (table above).

So `countOpenFronts = 0` is NOT a "the AIR verifies everything" certificate — it is
"no open refinement front in the extraction lane." The trusted-out-of-circuit
surfaces sit OUTSIDE its accounting. The Custom undercount was already corrected in
`project-circuit-soundness-apex.md`; the sovereign surfaces are an additional class
this census surfaces.

## Ranked answer — "what else does the EffectVM AIR NOT verify?"

1. **Custom program correctness** (`Effect::Custom` / `proofBind`) — the bound
   sub-proof's verification is off-AIR (`verify_proof_bind`); commitment 4-felt
   (~62-bit, below the 124-bit floor). Already documented
   (`docs/deos/CUSTOM-VK-AUTHORIZATION.md`, `docs/reference/lean-circuit.md:196`).
2. **Sovereign inner transition proof (Phase 2)** — recursively verified off-AIR;
   the VK binding is sentinel-zero today (STAGED, recursive verifier is a follow-up).
   Was NOT surfaced in the soundness census docs before this audit.
3. **Sovereign witness Ed25519 signature + replay sequence** — signature verified
   off-AIR (`authorize.rs`), replay via off-AIR chain-walk; the AIR carries only a
   4-felt key digest + sequence. By design the signature binds the full 256-bit key
   off-circuit; honest but a genuine trusted surface for the bare STARK.

Everything else in the EffectVM AIR is genuinely enforced (class 1) or fail-closed
via an in-circuit LogUp bus (class 2). The trusted-surface class is exactly these
three off-AIR recursion/auth surfaces — and the broad benign off-AIR PI-match
reconstruction surface (light-client-reproducible, not a hole).
