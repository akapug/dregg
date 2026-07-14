# Fixture / Toy / Placeholder Audit — the "hunt the theater" pass

**Date:** 2026-07-14 · **Mode:** read-only (grep + read + one ground-truth run) · **Scope:** whole `breadstuffs` tree, focus on this session's crates + the deployed paths.

**Headline (honest):** this tree is *disciplined*. The overwhelming majority of what a naive grep flags as "theater" is **honestly-labeled deliberate placeholder (B)** or **ember-gated ceremony (C)** — the iterative-approximative method working as designed: labeled inadequacies on a sharpening trajectory, each naming its real successor. **Genuine yeet-now theater (A) is rare and minor.** I did not manufacture A items to pad the list; over-flagging a deliberate placeholder is itself a failure this audit is supposed to avoid.

The single most important ground-truth finding: **`fhegg_uniform` is NOT broken.** It builds (via autobins) and reproduces the "baked" `drex-viz-data.js` UNIFORM snapshot **byte-for-byte** — verified by running the exact `.provenance` command this session. The viz "baked snapshots" are real, reproducible engine output, not fabrication.

## Counts per class

| Class | Meaning | Count (material items) |
|---|---|---|
| **A — YEET-NOW** | toy-as-real, or trivially replaceable with the real thing now | **3** (all minor; see below) |
| **B — DELIBERATE TRACKED PLACEHOLDER** | labeled low-res floor/envelope on a trajectory — REAL work, keep | **~dozen categories** (the bulk) |
| **C — EMBER-GATED** | real version needs ember's button (ceremony / broadcast / key) | **4** |

`metatheory/` is effectively **`sorry`/`admit`-free**: 0 `sorry`/`admit` as proof terms (all 7 textual hits are prose — "sorry-free", "NOT a `sorry`", "admitting the conflict object"). The 3257 `by decide` / 332 `native_decide` are legitimate decision procedures over decidable props, not toy-scale `ZMod 5` shortcuts. The named carriers (PortalFloor, HashCR, HidingFriPcs, RevealBundle.reveal_law) are **B**, per the project's floor discipline — audited by statement, not shape.

---

## (A) YEET-NOW — genuinely replaceable now

Honestly, this list is short. Nothing here is dangerous; these are hygiene/wiring nits where the real thing already exists in-tree.

### A1. `fhegg_uniform` has no explicit `[[bin]]` entry — register it
- **Where:** `fhegg-solver/Cargo.toml:28-57` lists 7 bins; `fhegg_uniform.rs` is absent. `fhegg-solver/src/bin/fhegg_uniform.rs` (238 lines, complete).
- **What:** the bin builds and runs *only* because edition-2021 autobins auto-discovers `src/bin/*.rs`. Its siblings are all explicit `[[bin]]`. This inconsistency is almost certainly why it was reported as "produced no output" (someone assumed it wasn't a target).
- **Ground truth:** I ran `cargo build --bin fhegg_uniform` (OK) and piped the `drex-viz-data.js` provenance book through it — output matches the baked UNIFORM snapshot exactly (p*=0.60, V*=160, fills 100/60/0/64/40/56).
- **Real replacement:** add the 3-line `[[bin]] name = "fhegg_uniform" / path = "src/bin/fhegg_uniform.rs"` block. **Not theater — build hygiene.** (Not touched: read-only pass.)

### A2. `compile_dfa` wasm binding returns a zeroed stub while `dfa/` crate exists
- **Where:** `wasm/src/bindings.rs:1634-1652` — returns `DfaStub { states: 0, transitions: 0, note: "…pending DFA-RATIONALIZATION + dfa feature gate" }`.
- **What:** a placeholder that returns honest zeros + a note (does NOT fabricate a plausible-looking DFA — so it is not *dangerous*), but the real engine (`dfa/` crate: `dregg_dfa::compiler` + air) is present in the tree.
- **Real replacement:** delegate to `dregg_dfa::compiler` behind the named `dfa` feature gate. Borderline A/B — labeled pending, but wireable now since the crate exists. Left as B-if-gate-blocked; flagged A because the dependency is in-repo.

### A3. `withdraw.rs` mock selector constant
- **Where:** `chain/src/withdraw.rs:290-291` — `let selector: [u8;4] = [0x9a,0x03,0x14,0x2c]; // placeholder` used only under `#[cfg(feature="mock")]`.
- **What:** a hand-written function selector used only in mock mode ("in production alloy computes this"). Behind the opt-in `mock` feature, so it never reaches a non-mock build, but it's a hardcoded magic constant where alloy's `Function::selector()` is the real derivation.
- **Real replacement:** derive via alloy in mock too. Lowest priority (mock-only).

---

## (B) DELIBERATE TRACKED PLACEHOLDER — real work, KEEP (do not yeet)

These are labeled floors/envelopes on the sharpening trajectory. Each names its successor. Yeeting these would delete real, honestly-scoped work.

### B1. The measured FHE envelope (`fhegg-fhe/`)
- `fhegg-fhe/ADDITIVE-FOLD-ENVELOPE.md:10`, `MEASURED-ENVELOPE.md:8`, `src/bin/additive_bench.rs:16,95`: **"Real crypto both sides, no mock:"** `tfhe-rs 1.6.3` + `fhe.rs 0.1` (BFV). The doc *explicitly* labels every extrapolated number. This is the canonical deliberate-envelope — real libraries, measured, honestly bounded. **B.**

### B2. The DrEX viz "baked snapshot" + STARK-stage floor (`drex-web/`)
- `drex-viz-data.js:1-21` — labeled REAL engine stdout with reproducible `.provenance` commands (verified A1). Serves live via `serve.mjs`; falls back to baked only as a bare file. **Not a fixture-as-real.**
- `drex-viz-data.js:44-49` `starkStage.status: "NAMED, not run in this demo"` + `app.js:217-226`, `index.html:100,148,206`, `styles.css:258` — the commit-reveal "floor" and the reveal-nothing STARK (`shielded_ring_clears`, `cert_f_air.rs`) are **NAMED as the upgrade, not faked**. The UI literally says "an honest floor being upgraded, not how DrEX ultimately works." Textbook labeled floor. **B.**
- `drex-web/offerings.js:26,39` `sampleOrders()` / `mode: ['sample','random']` — demo *input* for a demo surface (not a faked *result*). **B.**

### B3. The chain `mock` feature (`chain/src/{prove,verify,mock,credential,withdraw}.rs`)
- NO default feature (`chain/Cargo.toml:41-47`); `mock` must be opted into; without a wrap prover the real path hard-errors `WrapProverMissing` (`error.rs:18-20`), and `README.md:36` states a build **NEVER silently substitutes** a simulated proof. `MOCK_PROGRAM_VKEY = "PLACEHOLDER_VKEY_MOCK_ONLY"` (`lib.rs:61`) is namespaced so it can't masquerade. This is the *gold standard* of an honest test double. **B (test infra), not theater.**

### B4. The gnark/apex fixtures (`circuit-prove/`, `chain/gnark/fixtures/`)
- `apex_shrink_gnark_export.rs`, `gnark_witness_export.rs`, `bilateral_aggregation_emit_gate.rs` (`turn_id_fixture`/`counts_fixture`/`roots_fixture`): these "fixtures" are **real-proof export artifacts + Fiat-Shamir transcript vectors** — the exact absorb/squeeze run of the real challenger (`transcript_fixture_w16()` runs the REAL verifier challenger), self-checked every export. `apex_shrink_fri_real.json` (982 KB) is a real shrink proof's opening data. These are cross-language differential *test vectors*, not stand-in results. **B.**

### B5. Named metatheory floors / carriers
- `metatheory/Market/RevealNothing.lean:60,75,190,431` — the reveal-nothing consequence rests on the explicit `RevealBundle.reveal_law` **structure FIELD** ("NAMED FLOOR… NOT a `sorry`, NOT proven"), conditional-on-hypothesis by design.
- `Dregg2.lean:45` PortalFloor — `@[extern]` crypto kernels as soundness-Prop carriers taken as explicit hypotheses; reference instances discharge them only in toy ℤ/ℕ for **non-vacuity**, honestly stated.
- `Market/ZKOpenRel.lean:18-21,799` — "turns prose into real sorry-free Lean… never a `sorry`, never an open field." **B (audited by statement).**

### B6. Labeled scaffolds / sketches
- `fhegg-rtl/hardware/cosim/cosim_harness.rs:1-11,31,60` — header says **"SCAFFOLD (honest TODOs)"**, explicitly NOT a Cargo workspace member (can't break builds), with a contributor 3-step contract. `todo!()`s are the contributor's fill-in. **B.**
- `circuit-prove/sketches/gpu_dft_prototype.rs`, `sketches/gpu-dft-plonky3/`, `sketches/wgpu-babybear-ntt/` — `unimplemented!("PROTOTYPE")` in a `sketches/` dir. **B.**
- `dregg-sdk-net/src/channels.rs:363-377` — `TreeKem` `unimplemented!` is the "**named successor seam**"; the DEPLOYED schedule is `SenderKeys` (the wrapper routes through the working path). **B.**
- `cell-crypto/src/value_commitment.rs:70,240`, `circuit/src/predicate_program.rs:331` (NOT-operator honest error), `cell/src/derivation.rs:44` — all "planned / not-yet-implemented" honest labels. **B.**

### B7. The wasm Studio educational sim (`wasm/src/runtime.rs`, `bindings.rs`)
- `SimFederation` / `simulate_consensus_round` (`runtime.rs:907-934`, `bindings.rs:1451-1592`) — an **educational carve-out** for the Studio UI ("sim is educational carve-out"); builds a real `AttestedRoot`, but "all nodes vote (wasm doesn't run BLS pipeline)". Labeled sim, not a claimed consensus. Various inspector "Placeholder until `prove_turn` populates the cache" states (`runtime.rs:344,361`, `bindings.rs:2246,2908`) are scope-0 UI states, not fake data. **B.**
- `wasm/src/lib.rs:258-270` — the "toy `MerkleStarkAir`" comment is **historical**: it now drives the REAL arity-4 Poseidon2 path (`prove_vm_descriptor2`/`verify_vm_descriptor2`). The word "toy" describes what it *used to* be. **B (already upgraded).**
- `wasm/src/lib.rs:2008-2022` — `IncrementNonce` as the "canonical extension broadcast placeholder" for non-transfer actions; the extension submits to a **real node** which executes the ledger effect. Design choice (node routes by method-name string), labeled. **B.**

### B8. launchpad-web "no mock" surfaces
- `launchpad-web/{server,node-launch-driver,node-indexer,gate/receipt,gate/e2e}.mjs` + `README.md:94` — every field read back from **deployed `DreggLaunchpad` bytecode** (29/29 gate pass, "No faked launch"). `contracts/launchpad/{IClearingAttestor,ILaunchEligibility}.sol` interfaces tested via a mock in Solidity tests (the standard interface-wiring pattern). The receipt banner honestly says "static snapshot of a REAL launch… No value at stake; a demonstration receipt." **B.**

---

## (C) EMBER-GATED — the real version is ember's button

### C1. The dev single-party Groth16 ceremony → production MPC ceremony
- `chain/DEPLOYMENTS.md:19-20`, `chain/script/DeploySettlement.s.sol:57-62`, `chain/codegen/extract_vk_spec.py:67` — the settlement VK is from a **dev single-party ceremony (toxic-waste-known)**. Explicitly labeled "not production MPC." **Gated real version:** a multi-party trusted-setup ceremony (ember's coordination). This is the classic C — a toy *because* the real version is a ceremony only ember can run.

### C2. The Base-Sepolia "fixture proof" → a live user turn
- `chain/DEPLOYMENTS.md:5,19`, `chain/script/DeploySettlement.s.sol:23,40,99-113` — the on-chain settle tx (`0xbd2cac…963b`, provenHeight=2) is a **REAL proof verified on-chain via the Solidity pairing**, but of a **pre-generated 2-turn apex fixture**, not a live user turn. **Gated real version:** proving + settling a live devnet user turn (needs the devnet standup + broadcast). **⚠ WATCH (see Dangerous below).**

### C3. drex-web / launchpad devnet-DEMO → public broadcast + live tokens
- `drex-web/offerings.mjs:21,91`, `offerings.js:193`, `launchpad-web/server.mjs:42` — the engine runs LOCAL; "Public devnet broadcast + live tokens = the ember-gated step (named, not run)." **C.**

### C4. Federation standup (single-node dev → n-node)
- `launchpad-web/server.mjs:42` "single-node dev", the wasm `SimFederation` educational stand-in — the real multi-node federation standup is in-progress ember work (per MEMORY federation epoch). **C.**

---

## ⚠ DANGEROUS — a real artifact that could be *over-claimed* as more than it is

**The Base-Sepolia settlement tx (C2).** Not theater — the proof is real and the on-chain verification is real — but it is the one item where a reader skimming past the "Honest:" line could cite "dregg settles live on Base-Sepolia" as if it were a production, live-user, MPC-ceremony settlement. It is: a *fixture* turn, under a *dev single-party* ceremony with *known toxic waste*, from a *throwaway deployer*. The `DEPLOYMENTS.md` labeling is correct and present — the danger is purely in *citation out of context*. **Keep the artifact; never quote the tx without the fixture + dev-ceremony qualifier.** This is the highest-priority "handle honestly," not a yeet.

Secondary watch: nothing else rises to misleading. The `mock` feature (B3) is the kind of thing that *would* be dangerous if it were default — it is explicitly not, and hard-errors otherwise.

---

## Top 5 YEET-NOW (with real replacements)

Because the tree is disciplined, only 3 true-A items exist; rounding out the "worth-doing-now" list with the two highest-value hygiene fixes:

1. **`fhegg_uniform` → add explicit `[[bin]]`** (`fhegg-solver/Cargo.toml`). Real replacement: the 3-line bin block. Removes the "no output / not a target" confusion; the bin already works and reproduces the viz snapshot.
2. **`compile_dfa` wasm stub → delegate to `dregg_dfa::compiler`** (`wasm/src/bindings.rs:1634`). Real replacement: wire the in-tree `dfa/` crate behind the `dfa` feature.
3. **`withdraw.rs` mock selector → alloy `Function::selector()`** (`chain/src/withdraw.rs:290`). Mock-only; low priority.
4. *(hygiene, not A)* Register the same for any other autobin-only `fhegg-solver` bins if added later — keep the `[[bin]]` list authoritative.
5. *(handle-honestly, not A)* Add the fixture + dev-ceremony qualifier inline wherever the Base-Sepolia tx is cited outside `DEPLOYMENTS.md` (C2 danger mitigation).

## Bottom line

The theater-hunt's honest verdict: **there is very little theater to yeet.** The codebase rigorously follows the labeled-placeholder discipline — floors name their successors, mocks are opt-in and namespaced, fixtures are real-proof export vectors, and the one live on-chain artifact is honestly captioned. The real value of this pass is the *confirmation* that the flagged items are overwhelmingly deliberate (B) or gated (C), plus the ground-truth that `fhegg_uniform` works and the DrEX viz snapshots are byte-reproducible. The three A items are wiring hygiene, and the one thing to guard is *citation discipline* around the Base-Sepolia fixture settlement.
