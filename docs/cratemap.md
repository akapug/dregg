# cratemap — the target topology (A-with-B)

**Axis (A):** slice by *dependency weight / portability* — what a crate must link to exist.
**Naming (B):** name the core by the dregg nouns/verbs, so the code mirrors the theory.
**Law:** a capability is a *crate you depend on*, never a *feature that strips the core*.

The topology is three rings + apps. "Done" = no feature answers "which part of dregg /
which guarantee," and **Ring 0 builds on every target with no flags**.

---

## Ring 0 — the portable verified core  (pure Rust · builds identically on native / wasm / seL4-PD / pg · NO crypto, proving, FFI, or platform)

| crate | holds (the dregg vocabulary) |
|---|---|
| `dregg-types` | the **nouns as data**: `CellId`, `CellState`, `Cap`, `Predicate`, `Delegation`, `Commitment`-as-data, `Ledger` (grow it; it already has 57 dependents) |
| `dregg-cell` | the cell structure + program/predicate logic (crypto-free — ✅ already, post split #1) |
| `dregg-turn` | the **verbs**: executor semantics, cap algebra, turn application — FFI-free (✅ post exec-lean carve) |
| `dregg-coord/-captp/-federation/-intent` *(core halves)* | the pure coordination logic + the **seams** (traits) their verified gates are injected through |

Ring 0 should compile on **stable or any nightly** — no gpui, no servo, no Lean link, no plonky3.

## Ring 1 — capability adapters  (each a crate you compose in; pulls the heavy deps)

| crate | the capability | kills the feature |
|---|---|---|
| `dregg-cell-crypto` | bulletproofs / dalek / commitments / ZK construction | `cell/crypto` ✅ |
| `dregg-circuit-verify` | the STARK verifier (light — light clients dep only this) | `circuit/verifier` |
| `dregg-circuit-prove` | the plonky3 prover (heavy) | `*/prover` (11-crate cascade) |
| `dregg-exec-lean` | the Lean-FFI verified executor + shadow/producer | `turn/no-lean-link` ✅ |
| *(lean-impls)* | the verified gates of coord/captp/federation/intent (the unified FFI boundary — folds into / beside exec-lean) | their `no-lean-link` |

**One FFI boundary:** all `dregg-lean-ffi` linkage lives in Ring-1 lean crates. Everything
else is FFI-free. (This is also the single home for the FFI ladder — JSON → binary →
generated-direct `lean_object*` — see CRATE-SPLIT-PLAN.md.)

## Ring 2 — platform shells  (compose Ring 0 + the adapters the target affords; OWN their platform/toolchain quirks)

| shell | composes | property |
|---|---|---|
| `dregg-node` (native) | core + crypto + prove + exec-lean + network | the full node |
| `dregg-wasm` (wasm32) | core + crypto + verify | FFI-free **by construction** (no exec-lean dep) |
| `sel4/verifier-pd` (seL4) | core + verify | **Lean-free** because it doesn't depend on a lean crate — the invariant is now *structural*, not a flag everyone must remember |
| `pg-dregg` (postgres) | core + prove | pgrx `pgNN` ABI features stay (framework-forced — legit) |
| `starbridge-v2` (desktop) | core + crypto + gpui/servo backends | **owns the rolling-nightly quirk** — its own standalone workspace + vendored servo patch (already so) |
| `dregg-tui`, `chain` (standalone) | core + … | each contains its own platform needs |

## Ring 3 — apps  (`starbridge-apps/*`): compose Rings 0–2.

---

## The toolchain split is a Ring-2 property, not a workspace wart

The pain ember named — root pins old `nightly-2026-01-01` (servo era), starbridge-v2 needs
rolling nightly (gpui `cold_path`) — is **isolated to the platform shells.** Ring 0 (the
portable core) builds on stable/any nightly; the rolling-nightly + servo-patch tax is paid
*only* by whoever builds the desktop shell. The reorg doesn't make the two-nightly fact go
away, but it **confines** it: node/wasm/pg/seL4/core never touch gpui or servo, so they
never need the rolling nightly. "Which nightly" becomes "which shell," same as "which
guarantee" becomes "which adapter."

## Status against this map

✅ `dregg-cell-crypto` · ✅ `dregg-turn` FFI-free + `dregg-exec-lean` · ✅ chain mock fail-closed
· ✅ cockpit/program god-modules (reviewability, off critical path)
◻ `dregg-circuit-{verify,prove}` (prover cascade) · ◻ sdk core-gates → dep the real crates
· ◻ the lean-impls FFI boundary for coord/captp/federation/intent · ◻ tail (zkvm, threshold-sig,
starbridge embedded-executor)

~4 cuts + a tail. Finishable. Then the FFI ladder (post-reorg).
