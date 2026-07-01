# FAKEOUTS-core — the federation/node/consensus + verified-core + substrate-twins sweep

A read-only sweep (HEAD, 2026-06-30) for the **worst class of defect**: something
PRESENTED as `verified` / `attested` / `conserved` / `finalized` / `proven` that is
actually a **twin / stub / constant / vacuous check**. In a *verify-don't-trust* system a
fake "verified" undermines the whole thesis, so this census hunts specifically for:

- a **marshal-only / unverified path presenting as the verified core** (the flagship);
- a **twin presented as the proven primitive** (the soundness-twins defect);
- a **vacuous consensus / finality check** (always-passes, short-circuit, hardcoded);
- a **constructed "attestation"** (a proof/root/receipt fabricated from a constant).

**HEADs:** `dregg`/`breadstuffs` `0d01c9157` · `DreggNet` `12ce657`.
**Scope read:** `breadstuffs/{dregg-lean-ffi, node, blocklace, exec-lean, pg-dregg}` +
`DreggNet/{umem, store, durable, receipt, storage, webapp}`.
Cross-refs: `SOUNDNESS-TWINS-CENSUS.md`, `STAND-INS-CENSUS.md`,
`breadstuffs/docs/LEAN-PERF-AUDIT.md`, `VK-EPOCH-DESIGN.md`. **No code touched — this doc only.**

**Method note (honest in both directions).** The sin is a *fake* "verified" — a
constructed attestation or a twin dishonestly presented as the proven core. It is NOT a
sin to ship a **fail-closed stub that never false-attests + is labeled**, a **twin that is
documented as a twin with a live closure lane**, or a **circuit VK-epoch seam** (the
executor enforces; the pure light-client can't yet witness). Those are HONEST FLOORS and
are classified as such below.

---

## Headline

**No CRITICAL fake-verified was found.** Nothing on a live path fabricates an
attestation from a constant; no consensus/finality check is vacuous; the two most
dangerous prior soundness-twins (the FNV content-roots, the blake3 umem root) have been
**genuinely raised to meet the claim** — they now compute the REAL sorted-Poseidon2 root
the substrate proves. The differential is Lean-authoritative (divergence is surfaced, not
swallowed into the unverified Rust path). The pg-dregg proof verifier's default-build stub
is an honest fail-closed refusal, never a false attest.

The **single worst residual fake-verified risk** is not a constructed fake at all — it is
the **marshal-only SOLO node**: when `lean_available()==false` (gitignored/stale Lean
seed) a *solo* node runs the UNVERIFIED Rust executor and serves its API as a normal node.
This is now **loudly surfaced** (a startup `error!` + a per-turn `warn!` + an opt-in hard
build panic) and **fail-closed for the verified-consensus (full BFT) role**, but the
*solo-executor* degrade is **log-only, not a refusal**, and the build gate is **opt-in**.
So the archetype fakeout is **substantially caught, with a named residual** — see §M.

---

## Ranked table

| # | file:line | pretends | does | severity | class | fix |
|---|-----------|----------|------|----------|-------|-----|
| M | `node/src/main.rs:1073` (tripwire is log-only); `dregg-lean-ffi/build.rs:1332` (gate opt-in) | a running node is the verified core | a marshal-only **solo** node runs the UNVERIFIED Rust executor + serves; tripwire only `error!`s (no exit); build gate off by default | **HIGH** (residual) | SUBSTANTIALLY-CAUGHT fakeout — the silent path is closed for consensus, log-only for the solo executor | make the executor tripwire refuse (exit) for non-solo *or* default `DREGG_REQUIRE_LEAN=1` in distribution builds; add a running-state trip |
| 1 | `durable/src/settle.rs:218-259` (`ConservingLedger`) + `durable/src/conserve.rs:154-161` | the proven conservation primitive (Σδ=0) | in-process `i64` `HashMap` arithmetic proven only by unit tests in the DEFAULT build; the real `dregg_cell::CellState` path is `#[cfg(feature="dregg-conserve")]`, off by default | **HIGH** | HONEST TWIN (labeled; real-primitive lane exists but off; S3 flip named) | make `dregg-conserve` default, or land the S3 on-chain `Payable` flip |
| 2 | `durable/src/verified.rs:81,99-119` (`cell_root`/`ledger_root`) | the kernel's Poseidon2 content commitment | **blake3** content-binding stand-in (S3-gated), backed by a real recompute/reject `revalidate` tooth | **MEDIUM** | HONEST STAND-IN (`S3_GATED_SEAM` const; the last blake3 content-root in the set) | swap to real Poseidon2 `ledger_root` — the same weld storage/webapp already did |
| 3 | `receipt/src/lib.rs:307-359` (`verify_chain`) | the proven kernel receipt discipline (`chain_tamper_evident`) | a real blake3+ed25519 tamper-evident chain, but a re-impl ABOVE the kernel, not the kernel's own `TurnReceipt` | **MEDIUM** | HONEST TWIN (sound-by-construction; catches tamper for real; `turn_receipt_hash` link already present) | project product receipts as typed VIEWS over the real `TurnReceipt` |
| 4 | `pg-dregg/src/attest.rs:403-416` (`verify_serialized_proof`, default build) | (nothing — it is labeled) | decodes the transport then returns `Err("…not yet wired…")`: attests NOTHING, never a false attest | **n/a** | HONEST FAIL-CLOSED FLOOR (real plonky3 verify behind `--features tier-c` at `circuit-prove/src/ivc_turn_chain.rs:1883`) | flip tier-c on the S3 lane; widen the 8-felt anchor transport (named) |
| 5 | `node/src/blocklace_sync.rs:1063-1077` (tau differential) | detects any Rust↔Lean order divergence | compares only the sorted `(creator,seq)` **multiset** + length, not the order — insensitive to within-cohort reorders (OPEN-CM-XSORT) | **MEDIUM** | HONEST LIMITATION (soundness unaffected: the Lean order is what EXECUTES; only the detector is coarse) | tighten to order-equality once XSORT closes |
| 6 | `node/src/blocklace_sync.rs:1106-1117` (per-poll FFI-ERR) | verified ordering every poll | a transient Lean-FFI ERR AFTER a clean startup falls back to Rust `tau` for that poll (loud `warn!`); the tripwire only checks at boot | **MEDIUM** | HONEST NARROW-WINDOW residual | add a running-state trip / bounded consecutive-ERR halt |
| 7 | (whole circuit VK) `VK-EPOCH-DESIGN.md` G1/G2/G4/G5 | a pure light-client witnesses every effect | the EXECUTOR enforces (real, load-bearing); the in-AIR/VK tooth is the named shadow (e.g. G2 `Effect::Custom` proofBind in-AIR `True`) | **MEDIUM** | HONEST FORWARD SEAM (executor tooth real; circuit tooth = its named shadow) | the coordinated VK-epoch (reviewed human go) |

---

## §M — The marshal-only verdict (the flagship: caught, or claimed-caught?)

The archetype fakeout: `dregg-lean-ffi` links the verified Lean executor archive
(`libdregg_lean.a`) — but that archive is a **gitignored, per-host seed**. When it is
absent/stale, `lean_available()==false` and the node **silently ran the UNVERIFIED Rust
executor while presenting as verified**. Historically the only signal was a
`cargo:warning=…`, trivially lost in a release log. The recent work (commits `3485c2332`,
`2fc33f0cc`) closes this at **three** points; graded honestly:

1. **Build gate — `DREGG_REQUIRE_LEAN` (`build.rs:1332-1349`).** With the env var set,
   every marshal-only degrade (no archive / unresolvable sysroot / non-linkable target)
   becomes a **hard build panic** naming the cause. **Real** — but **OPT-IN**: unset (the
   default) preserves warn-and-degrade. A distribution/CI build that forgets to set it can
   still produce a marshal-only artifact.
2. **Startup tripwire (`node/src/main.rs:1073-1089`).** Unconditionally logs `error!`
   when `lean_available()==false`, before any role logic — so a marshal-only artifact can
   never deploy *silently*. **But it is a LOG, not a refusal**: a **solo** node keeps
   running the unverified executor and serves its API. The only runtime defense for the
   solo-executor role is that an operator reads the log.
3. **Verified-consensus hard-check (`node/src/main.rs:1108-1136`).** A **FULL (multi-party
   BFT)** node with `tau_order_available()==false` **refuses to start (`exit(1)`)** unless
   `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1` is explicitly set. This is **genuinely fail-closed**
   for the verified-consensus role — the "silently degrade to unverified Rust ordering"
   hole is closed. The absent-export FFI paths all return
   `Err("… not exported by the linked archive")` (fail-closed, never false-attesting).

At runtime the executor selection is honest and labeled: `execute_via_producer`
(`node/src/executor_setup.rs:120-181`) routes through `produce_via_lean`; when Lean is
available the **verified Lean post-state is authoritative** and installed verbatim, with
Rust demoted to a differential cross-check (a covered-turn disagreement is treated as the
*Rust* bug, never allowed to override — `executor_setup.rs:150-167`); a root-gap/unmappable
turn falls back to Rust **with a logged `warn!`, never a silent commit of divergent state**
(`exec-lean/src/lean_shadow.rs:798-821`). When Lean is *unavailable*, every turn takes that
fallback — surfaced, but not refused for a solo node.

**Verdict: SUBSTANTIALLY CAUGHT, with a named residual.** The degrade is no longer silent
(startup `error!` + per-turn `warn!` + opt-in build panic) and is **fail-closed for the
verified-consensus (full BFT) role**. The residual: the **solo-executor** degrade is
**log-only** (the tripwire does not exit), and the build gate is **opt-in** (default off).
An operator who ignores logs and never sets `DREGG_REQUIRE_LEAN` can still deploy a
marshal-only *solo* node whose API presents as verified. This is the single worst residual
fake-verified surface — not a constructed fake, but the archetype's last log-only corner.
Close it by making the executor tripwire *refuse* (not just log) for a non-solo/verified
role and defaulting `DREGG_REQUIRE_LEAN=1` in distribution builds.

---

## The honest floors (twins/stubs that are honestly labeled — NOT fakeouts)

- **pg-dregg tier-c proof verifier** (`attest.rs:403-416`) — the default-build stub decodes
  the transport then **refuses** (`Err`), attesting nothing. It explicitly contrasts the
  §10.3 forbidden mode ("a stub returning *success* / attesting forged state") and does the
  opposite. `attest_range` emits `AttestedTurn` rows ONLY on `Attested`, never on `Refused`.
  The real plonky3 verify (`verify_turn_chain_recursive_from_blobs`) exists behind
  `--features tier-c` (`circuit-prove/src/ivc_turn_chain.rs:1883`) with fail-closed
  VK-pin/publics/root teeth. **Honest fail-closed floor.**
- **umem content-root** (`umem/src/cell.rs:38,121`) — depends on the REAL
  `dregg_cell::compute_heap_root` (sorted-Poseidon2, the Rust shadow of Lean
  `Substrate.Heap.root` pinned by `root_binds_get`) via a git dep on `emberian/dregg`.
  `Checkpoint::verify` fail-closes on `boundary_root() != root`. **Not a twin — it IS the
  proven primitive** (the census #4/#5 fix, genuinely landed).
- **webapp/storage content-root** (`webapp/src/hosting.rs:1036-1070`,
  `storage/src/object.rs:54-62`) — the census's FNV-1a finding (worse-than-a-twin, not
  collision-resistant) is **RESOLVED**: both now call
  `dregg_circuit::poseidon2::hash_many_8`, pinned to the same `emberian/dregg` rev, with a
  regression test (`content_root_is_the_real_poseidon2_root_not_fnv`). Residual `fnv1a`
  hits are only in `polyana/` demo adapters + `net/httpe` load-balancing (non-soundness).
- **Finality / super-ratify** (`blocklace/src/ordering.rs:233-345`) — real DAG causal-past
  quorum: `supermajority_threshold(n)=(n*2/3)+1`, `n=0 ⇒ 1` (fail-closed empty committee),
  `is_super_ratified` counts distinct wave-end ratifiers ≥ supermajority. No hardcoded
  height, no always-true, no short-circuit. Solo (n≤1) is the honest committee-of-one.
- **Finalization votes** (`node/src/finalization_votes.rs:98-105,258-285`) — real Ed25519
  `verify_strict` + distinct-signer threshold; the consensus-wide "Attested" quorum is
  observability-grade only (`is_consensus_attested` is `#[allow(dead_code)]`, drives
  metrics), and the code cleanly distinguishes `FinalityLevel::Attested` from `Ordered`,
  so nothing is misrepresented as the execution gate.
- **A1 execution-FFI overlay** (`node/src/blocklace_sync.rs:4015-4038`) — the concurrency
  guard is real validate-or-reject: on a concurrent same-cell write it `error!`s and
  returns WITHOUT installing (the turn re-applies from the durable cursor); disjoint writes
  pass. Not vacuous (test `a1_overlay_installs_poststate_and_guards_concurrent_writes`).
- **The circuit VK-epoch seam** (`VK-EPOCH-DESIGN.md`) — the G-series gaps (e.g. G2
  `Effect::Custom` in-AIR `proofBind` is vacuously `True`, 4-felt commitment) are
  light-client-witness gaps where the **executor enforces the invariant**; the in-AIR/VK
  tooth is the named shadow, to be closed in one coordinated VK epoch (reviewed human go).
  Honest forward seam, not a fake-verified.

---

## One sentence

Across the federation/node/consensus core and the cloud's verified-substrate deps there is
**no constructed fake-verified and no vacuous consensus/finality check** — the differential
is Lean-authoritative, super-ratify is a real DAG quorum, the pg-dregg attest stub
fail-closes, and the two dangerous soundness-twins (FNV/umem roots) were genuinely lifted to
real Poseidon2 — leaving as the single worst residual the **marshal-only SOLO node**, whose
unverified-executor degrade is now loudly surfaced and fail-closed for the BFT-consensus role
but remains **log-only (not a refusal) for the solo executor** with an **opt-in** build gate,
plus a short tail of **honestly-labeled twins** (`ConservingLedger` i64 conservation, the
blake3 `ledger_root`, the above-kernel receipt chain) each carrying a named closure lane.

---

*Method: read both trees at HEAD; traced the executor selection from `execute_via_producer`
down to the real `extern "C" dregg_exec_full_forest_auth_str`, the tau path down to
`dregg_tau_order_str`, and the attest stub's both arms; grounded every file:line; confirmed
the FNV→Poseidon2 and blake3→`compute_heap_root` welds actually landed. Cross-checked against
`SOUNDNESS-TWINS-CENSUS.md` (four of its six twins now improved: FNV+umem fixed, receipt +
conservation still honest twins) and `LEAN-PERF-AUDIT.md` (the A1 fix is committed at
`2fc33f0cc`). No code touched.*

( ⌐■_■ )  *the fence came down and the theorem got imported — the only ghost left is the seed
you forgot to bootstrap, and now it screams instead of whispering.*
