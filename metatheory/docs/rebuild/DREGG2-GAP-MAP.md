# DREGG2-GAP-MAP — what is still MISSING / under-implemented in the Lean dregg2 model that real execution needs

> ⚑ **GROUND-CHECKED vs live Lean 2026-06-02** (post-2-compaction drift-repair); REAL / DECORATIVE /
> ASPIRATIONAL tags carry file:line receipts. **This map's central 2026-05 premise — "the executable turn
> is a 5-effect scalar kernel" — has been OVERTAKEN BY THE CODE and is now HISTORICAL.** The META-FILL
> landed: the FFI now exports a **46-effect, per-asset, tree-shaped, auth-gated** turn
> (`FullForest.execFullForestA` / `FullForestAuth.execFullForestG`, exported as `dregg_exec_full_turn_wide`
> at `FFI.lean:2732` and `dregg_exec_full_forest_auth` at `FFI.lean:3027`). The old narrow path
> (`execFullTurn` over the 5-arm `FullAction`, `dregg_exec_full_turn`, `FFI.lean:938`) still exists as
> legacy but is no longer the frontier. FILLs 1/2/3 and the META-FILL are DONE; the live frontier is
> **FILL J (the codec roundtrip, in-flight — 5 keystones currently sorry-carrying, build RED)** and the
> **#138 forest-delegation edge gap (genuinely OPEN — edges discarded at `FullForest.lean:124`).** Each
> FILL below carries a `[STATUS]` line. Drift was repaired IN THE GOOD DIRECTION: the code is stronger
> than this doc said.

> **Scope / method.** Originally a READ-ONLY assessment synthesizing the grounding/design docs
> (`docs/rebuild/EFFECT-ISA-DESIGN.md`, `GROUND-AUTH-ATTESTATION.md`, `GROUND-STORAGE-PROGRAMS.md`,
> `CARRY-FORWARD-SYNTHESIS.md`, the two `FAITHFULNESS-AUDIT*.md`, `COVERAGE-{AUTHORITY,DISTRIBUTED}.md`)
> against a direct read of the Lean (`metatheory/Dregg2/**`). The driving directive: **carry forward the
> Rust semantics (or a coherently-extrapolated vision), not a Lean fiction.** The SWAP framing is
> non-negotiable: routing the node through the Lean FFI is a MASSIVE staged rewrite gated on (a) the
> executor being complete, (b) the FFI hosting a real turn, and (c) the differential (kernel-vs-new-Rust,
> NEVER vs the buggy old dregg1) as the safety net. This map prioritizes the genuine fills, gives each a
> soundness-criticality, rough size, and the verification it needs, then orders them by dependency and
> splits PREREQUISITE-FOR-SWAP from ABOVE-CORE.

---

## 0. The structural finding that reframed everything — NOW LARGELY RESOLVED: the executable turn was narrow, and was widened

> **DRIFT-REPAIR HEADLINE (2026-06-02).** When written, the most important fact was that the FFI's
> executable turn was **far narrower than the proved law-surface** — a 5-effect scalar kernel. **THE CODE
> HAS SINCE CLOSED THIS.** The META-FILL (#130 META-FILL A, #131 Wave 1, #132 META-FILL D, #135 META-FILL I)
> widened the dispatch into the genuine effect core. The paragraphs below are kept as the historical
> framing with the resolution interleaved.

**[HISTORICAL]** The 2026-05 swap routed the node through `@[export] dregg_exec_full_turn`
(`Dregg2/Exec/FFI.lean:938`), which marshalled a `List FullAction` and ran `TurnExecutorFull.execFullTurn`.
`FullAction` (`Dregg2/Exec/TurnExecutorFull.lean:271-281`, **still exactly five variants today**:
`balance`/`delegate`/`revoke`/`mint`/`burn`; `execFull` dispatch at `:296-301`) was the whole executable
surface. Everything else dregg2 had proved lived in separate law-modules the FFI could not dispatch.

**[REAL — RESOLVED]** The dispatch was widened. The live executable surface is now `FullActionA`
(`TurnExecutorFull.lean:1928`), an inductive with **exactly 46 constructors** (per-asset
`balanceA`/`mintA`/`burnA` + `delegate`/`revoke` + 5 pure-state field/log effects + 7 authority/c-list
effects + supply/spawn + the escrow/obligation/note/committed cluster + bridge lock/finalize/cancel + 6
seal/sovereign/refusal effects + 4 ring-buffer queue effects + 4 CapTP swiss-table effects). `execFullA`
(`TurnExecutorFull.lean:2236`) dispatches all 46 fail-closed over the per-asset `RecChainedState`. The
tree wrapper `FullForest.execFullForestA` (`FullForest.lean:113`) runs that 46-arm node-op as an
**all-or-nothing, per-asset, tree-shaped transaction**, and the auth-gated `FullForestAuth.execFullForestG`
(`FullForestAuth.lean:501`) wraps it in the 3+1-part gate. Both are exported:
`@[export dregg_exec_full_turn_wide]` (`FFI.lean:2732`, runs `execFullForestA`) and
`@[export dregg_exec_full_forest_auth]` (`FFI.lean:3027`, runs the gated `execFullForestG`).

So the recurring shape the original map flagged — *"the law is proved in module X, but X is not wired
into the dispatch the FFI exports"* — **has been discharged for the effect core, the per-asset vector, the
escrow/note cluster, and the auth/caveat/revocation gate.** What REMAINS un-wired into the *same single
executable* is narrower and named precisely in the surviving FILLs: the **cross-cell CG-5 half-edge**
(proved in `Exec/CrossCellForest.lean`, *routed-to* but deliberately not baked into `execFullForestA` —
FILL 6, an honest division of labor rather than a gap), the **ρ_in/ρ_out vat membrane as a typed effect**
(FILL 7), the grown **`StateConstraint` evaluator** for storage userspace (FILL 4), real **WAL
durability** (FILL 5), and the **caveat/attestation crypto substance** (FILL 8). The codec that marshals
the wide turn across the wire (`FFI.lean` §W-codecs + `CodecRoundtrip.lean`) is itself the live frontier
(FILL J / #136, in-flight).

The original's optimism — *"each facet is already proved in isolation, so the integration is re-binding
proved lemmas to a wider dispatch, not greenfield theory"* — **proved correct.** That is exactly how the
META-FILL landed: the wide spine (`execFullForestA_conserves_per_asset`,
`execFullForestG_conserves_per_asset`, `execFullForestA_no_amplify`, `execFullForestA_each_attests`) is
read off the linear per-asset laws through a single bridge theorem `execFullForestA_eq_execFullTurnA`
(`FullForest.lean:171`), all `#assert_axioms`-pinned kernel-clean.

---

## 1. The prioritized fill-list

Criticality scale: **SOUNDNESS-CRITICAL** (a wrong/absent model lets the kernel accept an invalid state
transition — the kernel would be *unsound* as a replacement) · **INTEGRATION-CRITICAL** (the semantics
are proved but not in the executable turn the FFI runs — the swap can't route through them) ·
**FIDELITY** (a Lean abstraction is load-bearingly thinner than the Rust; not unsound but the proof
covers less than the running system does) · **ABOVE-CORE** (a genuine capability, not a prerequisite for
a sound minimal swap).

---

### FILL 1 — Per-asset-class balance: the `CONSERVATION_VECTOR` (the former #1 soundness gap)

**[STATUS: DONE on the executable kernel — task #129. The per-asset vector is now IN the record kernel
and rides the whole `execFullForestA`/`execFullForestG` spine. REAL, `#assert_axioms`-pinned. The legacy
scalar `recTotal` survives only on the OLD 5-arm path.]**

- **What (now RESOLVED).** When written, the executable kernel conserved **one scalar** (`balOf`
  reading a single `"balance"` field). **The record kernel now carries a genuine per-asset ledger.**
  `RecordKernelState.bal : CellId → AssetId → ℤ` (`RecordKernel.lean:304`); the conserved measure is the
  asset-indexed `recTotalAsset` (`RecordKernel.lean:508`) and, with the holding-store,
  `recTotalAssetWithEscrow` (`RecordKernel.lean:1136`). The keystone is **REAL** and on the *record*
  kernel, not a sibling toy: `recKExecAsset_conserves_per_asset` (`RecordKernel.lean:544`, the docstring
  explicitly: *"the multi-asset refinement of `recKExec_conserves`, no longer a `MultiAsset` toy"*), with
  the negative property the original demanded — `recKExecAsset_no_cross_asset_leak` (`RecordKernel.lean:589`).
  The forest spine inherits it: `execFullForestA_ledger_per_asset` (`FullForest.lean:213`) and
  `execFullForestA_conserves_per_asset` (`FullForest.lean:224`) move `recTotalAssetWithEscrow b` by
  EXACTLY the net per-asset delta **for every asset `b` independently** — a scalar aggregate provably
  cannot state this (the doc's own counterexample: a mint of asset B netting a burn of asset A). The
  auth-gated executor preserves it through the gate: `execFullForestG_conserves_per_asset`
  (`FullForestAuth.lean:790`, `#assert_axioms`-pinned at `FullForestAuth.lean:1074`).
- **[DECORATIVE — superseded] The `MultiAsset.lean` sibling.** The original located the correct law in
  `Dregg2/Exec/MultiAsset.lean` as "unintegrated." That role is OVER: the per-asset ledger and its
  conservation now live natively in `RecordKernel`. `MultiAsset.lean` remains as the original abstract
  template; the live law is `recKExecAsset_conserves_per_asset`, not `maExec_conserves_per_asset`.
- **[REAL — legacy scalar still present, scoped]** The scalar `recTotal` (`RecordKernel.lean:325`) and
  `recKExec_conserves` (`RecordKernel.lean:429`) still exist and back the OLD 5-arm `execFullTurn` /
  `dregg_exec_full_turn` (`FFI.lean:938`). They are not removed, but they are no longer the conserved
  measure of the wide turn the swap targets. The original's worry — that a scalar kernel "would accept a
  turn that mints asset B while burning asset A" — is closed for the wide path by
  `recKExecAsset_no_cross_asset_leak`.
- **Soundness-criticality.** **WAS SOUNDNESS-CRITICAL (the single biggest one); now DISCHARGED for the
  wide kernel.** `EFFECT-ISA-DESIGN.md:323,343` is satisfied for `execFullForestA`/`G`.
- **Remaining.** Only the FFI wire codec for the per-asset `BAL` ledger needs its parse∘encode THEOREM —
  and that leaf IS proved: `parseBalEntry_encode`/`parseBal_encode` (`CodecRoundtrip.lean:675,1862`,
  `#assert_axioms`-pinned). The cross-cell (multi-ledger) per-asset axis is FILL 6's cross-cell forest,
  which carries its own joint-family total. So FILL 1 proper is closed; what's left is folded into FILL J
  (codec) and FILL 6 (cross-cell).

---

### FILL 2 — Integrate the escrow holding-store / note nullifier-set into the executable turn

**[STATUS: DONE — the escrow/obligation/note/committed cluster is now IN `execFullA` (12 of the 46 arms).
REAL, conservation proved over `recTotalAssetWithEscrow`.]**

- **What (now RESOLVED).** FID-ESCROW (#116) had landed a faithful holding-store but it was stranded
  outside the dispatch. **It is now wired in.** `execFullA` (`TurnExecutorFull.lean:2236`) dispatches the
  escrow/note cluster directly: `createEscrowA → createEscrowChainA` (`TurnExecutorFull.lean:1307`),
  `releaseEscrowA → releaseEscrowChainA` (`:1314`), `refundEscrowA → refundEscrowChainA` (`:1320`),
  `noteSpendA → noteSpendChainA` (`:1333`), `noteCreateA → noteCreateChainA` (`:1328`), plus
  `createObligationA` and the committed triple (see FILL 3). These chained primitives thread the per-asset
  holding-store state `RecChainedState`. So `execFullForestA` / `dregg_exec_full_turn_wide` /
  `dregg_exec_full_forest_auth` CAN lock escrow, settle, refund, and spend/create a note.
- **[REAL] Conservation over the combined total.** The conserved measure for the escrow legs is
  `recTotalAssetWithEscrow` (`RecordKernel.lean:1136`, per-asset cell-ledger + holding-store), and it is
  the measure the forest spine moves: `escrow_create_conserves_combined` (`RecordKernel.lean:887`),
  `releaseEscrow_conserves_combined` (`:1008`), `refundEscrow_conserves_combined` (`:1022`) — all PROVED.
  The note path's anti-double-spend is real: `note_no_double_spend` (`RecordKernel.lean:1052`) +
  `note_spend_inserts` (`:1057`) ⇒ a re-spend of the same nullifier is rejected.
- **[was INTEGRATION-CRITICAL → DISCHARGED]** The original gap ("the swap can't route an escrow/note
  turn through the kernel at all") is closed. A node CAN now lock escrow and spend a note through the
  exported wide turn.
- **Remaining.** Only the FFI wire codec for the escrow/note side-tables needs its parse∘encode THEOREM —
  and those leaves ARE proved & pinned: `parseEscrow_encode`/`parseEscrows_encode`
  (`CodecRoundtrip.lean:1899,1982`), the nullifier/commitment lists via `parseNats_encode` (`:1746`). So
  FILL 2 proper is closed; the residue is in FILL J.

---

### FILL 3 — Committed-escrow + `noteCreate` through the holding-store (the FID-ESCROW coverage REGRESSION, task #121)

**[STATUS: DONE — task #121. The committed-escrow triple + `noteCreate` now ride the SAME holding-store /
nullifier-set as plain escrow; no shadow remains in the executable turn. REAL.]**

- **What (now RESOLVED).** The committed triple and `noteCreate` are de-shadowed. In `execFullA`
  (`TurnExecutorFull.lean` §execFullA, the escrow arms): `createCommittedEscrowA` /
  `releaseCommittedEscrowA → releaseEscrowChainA` / `refundCommittedEscrowA → refundEscrowChainA` —
  i.e. the committed variant runs the **same lock/settle automaton over the `escrows` holding-store** as
  plain escrow (the project's design intent), and `noteCreateA → noteCreateChainA`
  (`TurnExecutorFull.lean:1328`) is the commitment-insert dual of `noteSpend`, inserting into the
  commitment side-table — no longer the old `pairedStep` two-cell transfer. The crypto (Pedersen/range
  proof) stays a `CryptoPortal` hypothesis, exactly as `noteSpend` carries it.
- **[REAL] Where.** Holding-store + nullifier/commitment side-tables: `RecordKernel.lean:283-304`
  (the `nullifiers`/`commitments` sets), `:865-1069` (the escrow + note theorems). The committed arms
  reuse the `escrowChainA` family, so `escrow_create_conserves_combined`/`releaseEscrow_conserves_combined`
  cover them by construction (same primitive). The original's grep finding — *"no holding-store
  definition of the committed triple"* — is OBSOLETE: they share the plain-escrow primitive.
- **[was FIDELITY (regression) → DISCHARGED]** The exact failure mode FID-ESCROW rejected once (a
  committed escrow modeled as a balance-conserving two-cell transfer) is not re-introduced; the committed
  variant is a single-cell-debit-into-holding-store, conserving the combined per-asset total.
- **Remaining.** None at the executable level; the codec leaf is in FILL J. (Note: the `noteCreate →
  noteSpend` round-trip conserving the note supply is exercised by the `#eval` non-vacuity block in
  `FullForest.lean` §11 and the escrow theorems; a dedicated round-trip *theorem* over the wide turn would
  be a nice-to-have, not a gap.)

---

### FILL 4 — `StateConstraint` vocabulary → ~74 (the storage programs need it)

**[STATUS: GENUINELY OPEN / ASPIRATIONAL — unchanged in the load-bearing way. The grow-to-74 work has NOT
happened; `boundDelta` still returns `true`; the `RelayOperator`/`BlindedQueue`/`CapInbox` modules exist
but carry honest `-- OPEN:` notes for the missing constraint kinds.]**

- **What (still missing).** `StateConstraint` (`Program.lean:82-103`) is a wrapper inductive with **9
  constructors** — `simple` (lifting the whole `SimpleConstraint` sub-family: `fieldEquals/Ge/Le`,
  `immutable`, `writeOnce`, `monotonic`, `strictMono`, `fieldDelta`, `not`), plus `fieldLeField`,
  `sumEquals`, `sumEqualsAcross`, `fieldDeltaInRange`, `allowedTransitions`, `anyOf`, and `boundDelta`
  (the "~16 variants" the original cited counts the SimpleConstraint sub-family). The Rust
  `cell/src/program.rs` evaluator has **74 variants**, and the storage templates still need ones the Lean
  **does not have**: `RateLimit`/`RateLimitBySum`, `SenderAuthorized`, `WitnessedPredicate`,
  `TemporalGate`, `PreimageGate`, `BoundedBy` (`GROUND-STORAGE-PROGRAMS.md:189-190,214,257-263`).
  `Program.lean:20-23` still *honestly defers* these, and **`boundDelta`'s single-cell evaluator STILL
  returns `true`** (`Program.lean:151` — `| .boundDelta _ _ _ _, _, _ => true`).
- **[ASPIRATIONAL — the storage modules exist as honest scaffolds, NOT fully-evaluated programs.]** The
  templates the thesis rests on are now *partly* modeled but with the missing constraints declared as
  `-- OPEN:` rather than evaluated:
  - `Exec/RelayOperator.lean` models the bond-floor/anti-bond-drain via `anyOf [monotonic, strictMono]`
    (`RelayOperator.lean:80`) and the within-epoch quota via `fieldLe` (`:64`), but the per-epoch RESET
    of `bytesThisEpoch` (the real `RateLimitBySum`), the DFA route-table `WitnessedPredicate`, the
    `SenderAuthorized` gate, and the multi-cell relay dispatch are ALL `-- OPEN:`
    (`RelayOperator.lean:82,86,90,93,221`).
  - `Exec/BlindedQueue.lean` models the queue but the `WitnessedPredicate::Custom { vk_hash }` is an
    interface stub, and the tight `Invariant s → Invariant s'` cross-field link is `-- OPEN:`
    (`BlindedQueue.lean:19,201`).
  - `Exec/CapInbox.lean` models the inbox but the proper cross-slot capacity `head - tail ≤ capacity` and
    the `SenderAuthorized → sender_set_root` issuer-root binding are BOTH still `-- OPEN:`
    (`CapInbox.lean:85,318-325` — exactly the spot the original flagged; `sendAuthorized` proves a token
    was presented but does NOT bind it to the inbox's `sender_set_root`).
- **Where.** `Program.lean:82-103` (catalog) + `:110-160` (`evalSimple`/`eval`); the deferral note
  `:20-23`; the `boundDelta` no-op `:151`. Rust ground truth: `cell/src/program.rs`.
- **Soundness-criticality.** **FIDELITY → SOUNDNESS-CRITICAL for storage userspace.** A `RelayOperator`
  whose `RateLimitBySum` quota-reset and the `SenderAuthorized`/`WitnessedPredicate` gates are
  *unevaluated* is an unenforced economic cell-program — the "moved-complexity" trap
  (`EFFECT-ISA-DESIGN.md:371-377`). The bond-floor and anti-drain ARE now real; the quota-reset and the
  witnessed/sender gates are the surviving holes.
- **Rough size.** **Medium.** Add the ~6 missing variants with a real `eval`; the load-bearing ones are
  still `SenderAuthorized`→sender-set binding and `WitnessedPredicate` discharge (the registry exists,
  `Authority/Predicate.lean`).
- **Verification.** `eval` soundness per new variant; the `RelayOperator`/`BlindedQueue` invariants
  re-proved against the *evaluated* (not deferred) constraints; the `CapInbox`
  `SenderAuthorized`→`sender_set_root` binding closed (`CapInbox.lean:318-325`, still `-- OPEN:`).

---

### FILL 5 — Storage durability: the `CellRuntime` checkpoint `rfl`-fiction vs the real WAL

**[STATUS: OPEN / ASPIRATIONAL for the durability SEMANTICS; the requested RELABEL has happened in the
docstring (the `rfl` is now described as a "rebuild the running cell" / cache-rebuild law, not a
durability claim), but there is still NO WAL / fault / crash model.]**

- **What (still the case).** `Dregg2/Exec/CellRuntime.lean` names `checkpoint`/`restore`/`replay` but
  they remain pure in-memory `Snapshot` round-trips: `checkpoint_restore_roundtrip` is **still `= rfl`**
  (`CellRuntime.lean:60`), `restore ∘ checkpoint = id` by definitional equality (`:64`). There is still
  NO WAL, NO fsync, NO torn-write recovery, NO log truncation, NO crash model anywhere in `Dregg2/Exec/*`
  (grep for `WalLog`/`recover_from_wal`/`torn` returns NOTHING). The Rust durability semantics
  (`storage/src/wal.rs`: log-before-apply + fsync + per-line BLAKE3 torn-write checksum + replay +
  truncate; redb ACID + atomic note-spend, `persist/src/lib.rs:625`) are still un-modeled
  (`GROUND-STORAGE-PROGRAMS.md:217,238-246`).
- **[the partial RELABEL the original asked for: DONE in prose.]** The danger the original flagged — that
  the `rfl` reads as "durability proved" — has been softened: the `checkpoint_restore_roundtrip` docstring
  (`CellRuntime.lean:56-59`) now explicitly frames it as *"re-seeds the anamorphism's carrier ... asserts
  the token captured enough to rebuild the running cell — not the identity the chain-shaped design would
  settle for,"* i.e. a cache-rebuild law, not a crash-recovery law. So the honesty relabel is in place;
  the real crash/recovery semantics are not.
- **Where.** `CellRuntime.lean:54-101`. Rust ground truth: `storage/src/wal.rs`, `persist/src/lib.rs`.
- **Soundness-criticality.** **FIDELITY (below-ISA), now honestly labeled.** Durability is infrastructure
  *below* the ISA (`CARRY-FORWARD-SYNTHESIS.md:88-91`); if the verified kernel is to *replace* the Rust,
  the crash/recovery contract should eventually be modeled (a log + a fault point +
  replay-equals-pre-crash-state).
- **Rough size.** **Medium-Large** for real semantics (the relabel is already done, so the cheap-honesty
  posture is satisfied). Recommended next: a minimal `WalLog` + fault injection + `recover (crash (apply
  log s)) = s`.
- **Verification.** `recover_from_wal` replay equals the pre-crash state under a torn-write fault; atomic
  note-spend (nullifier-insert + commitment-store) all-or-nothing across a crash. (The relabel is done;
  this is the genuine remaining work.)

---

### FILL 6 — The cross-cell BoundDelta half-edge (CG-5) as a CORE effect

**[STATUS: SUBSTANTIALLY LANDED as a SEPARATE executable module + the "not final" framing CORRECTED.
There is now an executable N-ary cross-cell forest (`Exec/CrossCellForest.lean`) with the Σ=0 binding
PROVED, deliberately ROUTED-TO from `FullForest.lean` rather than baked into `execFullForestA` (an honest
division of labor, not a gap). What is NOT done: a single fused executable that runs BOTH the intra-cell
46-arm tree AND the cross-cell half-edges in one dispatch.]**

- **What (now mostly RESOLVED).** dregg has **no global ledger**; a bilateral turn moves value out of
  ledger A into ledger B, conserving only the cross-side aggregate. The N-ary cross-cell CG-5 is now
  **PROVED on an executable cross-cell forest**, not merely a bespoke `BiTurn`:
  - `Exec/CrossCellForest.lean` defines `execCrossForest` (`CrossCellForest.lean:192`), a forest whose
    nodes touch DIFFERENT cells, with the whole-forest conservation as the inviolable Σ=0 binding carried
    as a HYPOTHESIS (correctly NOT derivable, because cross-cell halves need not individually cancel):
    `crossForest_conserves` (`CrossCellForest.lean:241`, the N-ary CG-5 keystone, `#assert_axioms`-pinned
    at `:371`), `crossForest_no_amplify` (`:217`, pinned `:370`), `crossForest_attests` (pinned `:372`),
    `crossForest_bilateral_balanced`/`_conserves` (pinned `:376-377`), and a forward-sim
    `crossForest_bilateral_refines_crossAbs` (pinned `:378`).
  - The original `joint_cg5_conserves` bilateral law still backs it (`JointCell.lean`, referenced from
    `CrossCellForest.lean:22`).
  - `FullForest.lean` (§9, `:317-335`) DELIBERATELY routes any cross-target subtree to
    `Exec/CrossCellForest.lean` and does NOT bake a cross-target branch into `execFullForestA` — an
    explicit, documented division of labor: the intra-cell per-asset vector is *derived* in
    `execFullForestA`, the cross-cell Σ=0 is *binding-carried* in `execCrossForest`.
- **[CORRECTION — the "νF₁⊗νF₂ not final" framing is RETIRED.]** The original cited `νF₁⊗νF₂` is not
  final (`EFFECT-ISA-DESIGN.md:325`) as the irreducibility. **That framing is FALSE and has been retired
  in the Lean.** The product of final coalgebras IS final for the product (`Hyperedge.lean:486` says
  exactly this). The REAL obstruction is that **sound joint-turns form a PROPER SUBOBJECT of the
  product**: `hyper_binding_is_proper` (`Hyperedge.lean:164`, PROVED — was renamed from the old
  `hyper_not_all_admissible`), the N-ary analogue of `JointTurn.binding_is_proper`. The cross-side
  existence binding is irreducible *because the admissible configurations are a proper subobject*, not
  because the product is non-final.
- **Where.** Executable + proved: `Exec/CrossCellForest.lean:192-378`; the binding obstruction
  `Hyperedge.lean:164`; the routing note `FullForest.lean:317-335`. Rust seed: `action.rs:96`
  (`balance_change: Option<i64>`), `StateConstraint::BoundDelta` (the deferred Lean `boundDelta`,
  `Program.lean:151`, FILL 4's companion).
- **Soundness-criticality.** **SOUNDNESS-CRITICAL for multi-cell atomicity — now satisfied by the
  cross-cell forest module.** A cross-cell atomic move is modeled with the correct Σ=0 binding, NOT the
  wrong global-ledger transfer.
- **Remaining.** A *fused* executable (one dispatch running the intra-cell 46-arm tree and the cross-cell
  half-edges together, with the cross-target branch inside `execFullForestA` instead of routed out) — if
  the wholesale swap wants a single entry point. The current honest posture is two cooperating executors.
- **Verification (now PROVED).** `execCrossForest` conserves the cross-side aggregate
  (`crossForest_conserves`); the bilateral balance (`crossForest_bilateral_balanced`); `no_amplify` across
  cells (`crossForest_no_amplify`); the forward-sim to the abstract cross-step. The single fail-close
  negative test (one half commits, the other doesn't) is the binding-as-hypothesis discipline.

---

### FILL 7 — Vat-boundary ρ_in / ρ_out as typed CORE effects (the membrane)

**[STATUS: PARTIALLY LANDED. The CapTP *swiss* flavor of the cap↔key crossing IS now executable in the
46-arm dispatch (`exportSturdyRefA`/`enlivenRefA`/`swissHandoffA`/`swissDropA`). The *biscuit-token*
flavor — a `ρ_out`/`ρ_in` `exportKey`/`importKey` effect serializing a cap-slot to a key-as-cap — is STILL
absent. The admissibility law AND the lossiness functor `phi_functorial` are BOTH PROVED now (the latter
was a `sorry` when the doc was written — that drift is REPAIRED).]**

- **What (partly RESOLVED).** The cap↔key crossing is *the* vat membrane. The Lean has the vat-boundary
  *admissibility law* `vat_boundary_law` (now at `Exec/VatBoundary.lean:88`; the doc cited `:67-118`) —
  PROVED: cross-vat ⇒ a presented keys-as-caps token must discharge the request. **The CapTP swiss
  membrane is now a real executable effect set**: `execFullA` dispatches `exportSturdyRefA`/`enlivenRefA`/
  `swissHandoffA`/`swissDropA` (4 of the 46 arms) via the chained wrappers
  `swissHandoffChainA`/`swissDropChainA` (`TurnExecutorFull.lean:1571,1581`) over `RecordKernel`'s real
  swiss-table registry `swissExportK`/`swissEnlivenK`/`swissHandoffK`/`swissDropK` (with refcount GC), and
  the swiss export amplification hole was closed (#137). So a held cap-slot CAN be exported to a swiss
  number and enlivened back through the executable turn.
- **[STILL MISSING] The biscuit-key `ρ_out`/`ρ_in`.** There is still **no `exportKey`/`importKey`
  effect** that serializes a cap-slot → a biscuit `Authorization::Token` key-as-cap (attenuation-only) and
  verifies a key → mints a c-list slot (grep for `exportKey`/`importKey`/`ρ_out` is EMPTY). dregg1's
  `Authorization::Token` carrier is modeled in the auth layer but not as a unifying *effect*. This is the
  surviving FILL-7 gap.
- **[CORRECTION — `phi_functorial` is PROVED, not a sorry.]** The original said the lossiness morphism's
  functoriality is "a by-design `sorry` over an abstract `Verifiable`, `VatBoundary.lean:401`." **That is
  STALE.** `phi_functorial` is now a real term-proved theorem (`Spec/VatBoundary.lean:422`, a `where`
  structure proof using the `NonDegenerate.accepts` witness) with a concrete instance `phi_functorial_concrete`
  (`Spec/VatBoundary.lean:508`). No sorry in `Spec/VatBoundary.lean`'s proof terms (WF-ZERO-SORRY #128).
- **Where.** Admissibility (proved): `Exec/VatBoundary.lean:88`. Lossiness functor (proved):
  `Spec/VatBoundary.lean:422,508`. Swiss membrane (executable): `TurnExecutorFull.lean:1542-1610`. Missing
  biscuit `ρ_out`/`ρ_in`: not in `FullActionA`.
- **Soundness-criticality.** **SOUNDNESS-CRITICAL for cross-vat.** The swiss half is satisfied; the
  biscuit-token half is the residue. Sequence after FILLs 1-2 (now both DONE), so this is unblocked.
- **Rough size.** **Medium → Small** now (the swiss membrane proves the pattern). Add
  `exportKey`/`importKey` to `FullActionA`; reuse `Token.attenuate`/`attenuate_narrows` for the cap→key
  serialization and the cap-graph-add for the key→slot mint; `phi_functorial` is the lossiness witness.
- **Verification.** ρ_out only attenuates (granted ≤ held on serialization — the swiss path already has
  this via #137); ρ_in mints only a slot the presented key discharges; round-trip ρ_in ∘ ρ_out is
  lossy-but-authority-non-amplifying.

---

### FILL 8 — The caveat / attestation FACE: the cryptographic substance (the overlooked dimension)

**[STATUS: SUBSTANTIALLY LANDED as faithful FIDELITY models (#122 GROUND-AUTH + #124 carry-forward). The
original's headline — "the cryptographic substance is absent / a `Bool` flip" — is now WRONG: 8a/8b/8c/8f
each have a dedicated ~22-24KB Authority module that models the chain STRUCTURE / two-key split / subset
disclosure / verifier-indexed dial, with the unforgeability/encryption carried as HONEST §8 Prop-portals
(class fields, never faked theorems). What remains: wiring these into the EXECUTED `caveatsDischarged`
gate (the gate exists — `FullForestAuth.caveatsDischarged` — but reads a tiered within-cell meet + a
macaroon-tail check, not yet the full CaveatChain), and 8f's DV-ZK circuits.]**

The turn is a **three-faced generator** — effects ⊕ caveat-gates ⊕ attestation
(`CARRY-FORWARD-SYNTHESIS.md §0`). dregg2 grew the EFFECTS face deeply; the CAVEAT/ATTESTATION faces are
where the Rust *was* substantially richer than the Lean. These are FIDELITY fills; the algebraic
discipline was always proved, and the cryptographic *structure* is now modeled too:

- **8a. HMAC caveat-chain integrity — [REAL (structure) + Prop-portal (unforgeability)].** Now modeled:
  `Authority/CaveatChain.lean` (the macaroon as a REAL append-only HMAC chain `T₀ = HMAC(root, nonce)`,
  `Tᵢ = HMAC(Tᵢ₋₁, encode(Cᵢ))` via `Chain.append`, with a constant-time tail compare). The original's
  "cannot even express that an adversary can't *remove* a caveat" is REPAIRED: `removal_breaks_tag`,
  `tamper_breaks_tag`, `wrong_root_breaks_tag` are stated as negative theorems **relative to** a
  `MacUnforgeable` Prop-carrier (`CaveatChain.lean:40`, the honest §8 portal — the HMAC PRF assumption is
  not a Lean theorem, by design). *Criticality: FIDELITY — now mostly discharged.*
- **8b. Third-party discharge crypto — [REAL (protocol structure) + Prop-portal (seal/recovery)].** Now
  modeled: `Authority/ThirdPartyDischarge.lean` (the ticket/VID two-key split `ticket = seal(K_A, {r,
  caveats})`, `VID = seal(tail, r)`, the bind-to-parent `binding_hash` with `DischargeUnbound` on
  mismatch, freshness). The encryption/recovery ("only the 3P recovers the ticket", "only the verifier
  recovers `r`") is the `cryptoSound` Prop-portal (`ThirdPartyDischarge.lean:65,89` — never a Lean "no
  forgery" theorem). The original's "a `Bool` flip" is OBSOLETE. *Criticality: FIDELITY — structure
  discharged.*
- **8c. Credential selective disclosure + predicate proofs — [REAL].** Now modeled:
  `Authority/SelectiveDisclosure.lean` — subset disclosure (`disclose_set` filter) + `Gte/Lte/InRange`
  (and `Gt/Lt/Neq`) predicate proofs over HIDDEN attributes, with the headline theorem
  `presentation_hides_undisclosed` (two credentials agreeing on the disclosed subset + every proven
  predicate's truth produce the SAME presentation — the hiding statement). The original's "`VC.claim` is
  one opaque `Nat`, all-or-nothing, has no analog" is REPAIRED. *Criticality: FIDELITY — discharged.*
- **8d. Anonymous multi-show unlinkability, WIRED to the credential — [PARTIAL].** The hiding law existed
  (`Privacy.lean`) but was disconnected. `SelectiveDisclosure.lean` now carries the anonymous-multi-show
  axis ("anonymous multi-show: S, split & disconnected"), so this is partly wired. The one remaining
  TRIVIAL-ONLY finding is task **#127 DV-BLINDEDSET** (HolderAnonymity de-vacuify) — still `pending`.
  *Criticality: FIDELITY.*
- **8e. Stealth + StarkDelegation as first-class auth modes — [PARTIAL / verify].** Stealth invocation +
  StarkDelegation-default + `Authorization::Token` were addressed Rust-side (#79 W3-F, completed). On the
  Lean side, confirm whether `AuthModes.lean`'s mode set now includes Stealth (the original found it
  omitted); the `Authorization::Token` carrier is modeled (the FILL-7 biscuit layer). *Criticality:
  FIDELITY.*
- **8f. The repudiation / designated-verifier DIAL — [REAL (the NEW axis is BUILT) + Prop-portal
  (DV-ZK)].** The original called this "a genuinely NEW axis" that dregg "LACKS entirely (grep-confirmed,
  no ring/chameleon/disavowal anywhere)." **That gap is now FILLED at the model level:**
  `Authority/DesignatedVerifier.lean` defines the **verifier-indexed discharge** `DischargedFor : Verifier
  → Statement → Proof → Prop` (`DesignatedVerifier.lean:29`), with PUBLIC/transferable = `∀ V,
  DischargedFor V s p` (`:32`) vs DESIGNATED = `DischargedFor V₀ s p` for a specific `V₀`, and the
  deniability via a `simulate` (the verifier's own transcript-forger) carried as a §8 Prop-portal
  (`:43-49` — `verifyFor`/`simulate`/the indistinguishability are class fields, the DV-NIZK/chameleon-hash
  obligations, not faked theorems). *Criticality: ABOVE-CORE (a privacy capability + new circuits, not a
  swap prerequisite) — but the verifier-indexed `Discharged` the original prescribed is BUILT.*

> **Counter-note (carry the Lean FORWARD here):** CapTP non-amplification `granted ≤ held` is *proved* in
> `AuthModes.lean:268-296` and was *missing* from Rust `verify_captp_delivered` — task #94 already fixed
> the Rust to match. This is the FID-ESCROW pattern in reverse (the Lean is the better spec); it is DONE,
> noted here only so the gap map is complete (`GROUND-AUTH-ATTESTATION.md:241-249`, `COVERAGE-AUTHORITY.md §2`).

---

### FILL 9 — The higher-order handler tier (the comodel-morphism frontier)

**[STATUS: ABOVE-CORE, frontier — UNCHANGED in essence (the keystone weld is still honestly OPEN), but
with MORE proved scaffolding than the original credited. The swap does not depend on it.]**

- **What.** `HandlerTransformer.lean` proves a genuine `safe_transformer_composes` (`:163`, safe
  transformers compose, instantiated twice — camera + forest — with teeth: `unsafe_transformer_rejected`).
  Now also PROVED: `forest_gluing_is_proofForest_sound` (`:335`) and `proofForest_sheaf_sound` (`:386`,
  the sheaf-soundness of the proof-forest — a real theorem, not the OPEN keystone). It STILL **honestly
  leaves OPEN** the conjecture's keystone — that `Fpu`-preservation *IS* the gluing condition (one law,
  not two) — which is explicitly a `-- OPEN:` NOTATION PUN on different carriers (`:492-503`,
  `instSafeStepFpu` and the forest gluing live on different carriers), and the higher-order
  **recursive-camera** tier (`-- OPEN:` at `:504-520`). The `act` functor is supplied externally because
  the real `Await.Handler` functor is not yet built. So the higher-order tier is a *frontier*.
- **Where.** `HandlerTransformer.lean` (proved: `:163,335,386`; the OPEN keystone+tier `:492-520`);
  context in `HANDLER-TRANSFORMER-CONJECTURE.md`, `DREGG2-FOUNDATIONS.md`.
- **Soundness-criticality.** **ABOVE-CORE.** The dregg4 generalization (`CARRY-FORWARD-SYNTHESIS.md §4`),
  not a kernel-soundness prerequisite.
- **Rough size.** **Large / research.** Needs a shared carrier (a real `Handler → Handler` with a built
  `act` functor) before the weld stops being a pun.
- **Verification.** `Fpu`-preservation ⟺ gluing (the keystone biconditional, still OPEN); the
  recursive-camera tier (still OPEN).

---

### FILL 10 — Distributed-conformance gaps (consensus model, gossip, Stingray, revocation)

**[STATUS: mixed — 10a and 10f have LANDED (the correct models exist); 10e is PARTLY proved (checkable
content) + partly honest-`sorry`; 10b/10c/10d remain ABOVE-CORE portals/gaps.]** Per
`COVERAGE-DISTRIBUTED.md`, the Lean is a strong **consensus-theory sandbox**. These matter for a *node*,
not the *single-cell kernel turn*, so they sequence after the core kernel; several are CRITICAL for a
faithful node:

- **10a. Consensus model fit — [REAL — RESOLVED].** `Proof/BFT.lean` modeled classical voting-round BFT;
  dregg1 runs Cordial Miners DAG. **The actual DAG consensus is now modeled** in `Proof/CordialMiners.lean`
  with `SuperRatification` *derived from the real lace* — `SuperRatification.ofLace` PROVED
  (`CordialMiners.lean:282`, the audit-gap closer; #106 MG-CONSENSUS + #111/#113 DV-CORDIAL/CONSENSUS2 all
  completed). The original's "verify it supersedes BFT" is satisfied: the lace-derived super-ratification
  is the node's safety evidence, not the inapplicable BFT rounds. *Criticality: CRITICAL for a node-level
  claim — DISCHARGED.*
- **10b. Gossip / cordial dissemination — [ASPIRATIONAL / honest-portal].** All network-dependent proofs
  still rest on the `World.recv_mono` oracle (`COVERAGE-DISTRIBUTED.md §II.2`); the push/pull/pull-response
  protocol that must *achieve* `recv_mono` is unformalized. *Criticality: ABOVE-CORE / honest-portal —
  document the oracle explicitly.*
- **10c. Stingray bounded counters** (Layer 3, `coord/budget.rs`) — concurrent spending still unmodeled
  (`COVERAGE-DISTRIBUTED.md §II.5`). *Criticality: ABOVE-CORE. [ASPIRATIONAL].*
- **10d. Federation revocation Merkle tree** (`federation/revocation.rs`) — note: kernel-state revocation
  for the EXECUTABLE turn IS now done (`RecordKernel.revoked` side-table + `revocationGate` in the auth
  gate, #139 — see FILL D below). The *federation-wide Merkle* revocation tree remains absent.
  *Criticality: ABOVE-CORE, security feature. [PARTIAL — local done, federation-tree ASPIRATIONAL].*
- **10e. Coordination deadlock-freedom — [PARTIAL].** `Coordination.lean` still carries 8 `sorry` bodies
  for the FULL fidelity/deadlock-freedom bisimulations (honest obligations, `COVERAGE-DISTRIBUTED.md §II.4`).
  BUT the crispest *checkable* content IS proved: `projection_sound` (`Coordination.lean:416`) has a REAL
  proof term (`:427-428`, `rw [hG]; simp …`) of head-duality at a communication — the `sorry` at `:415` is
  INSIDE THE DOCSTRING (describing the un-attempted full bisimulation), NOT in the theorem's proof.
  *Criticality: ABOVE-CORE.*
- **10f. CapTP promise GC cross-vat cycle-freedom — [REAL — RESOLVED CORRECTLY].** `Exec/CapTP.lean` left
  it `-- OPEN:`; **`Exec/CapTPGC.lean` now closes it by a LEASE-BASED reclaim model** — the honest answer.
  It proves `crossvat_cycle_leaks` / `dead_undecidable` (why proven-death reclaim across vats is
  *impossible* — one vat cannot decide a cross-vat cycle dead) and routes reclamation through a cross-vat
  lease instead of faking a "decide dead across vats" theorem (`CapTPGC.lean:4-28`). *Criticality:
  ABOVE-CORE — DISCHARGED via the correct mechanism.*

---

### FILL 11 — The deferred coalgebra faces: return-projection + fork (after the living cell)

**[STATUS: ABOVE-CORE, mostly UNCHANGED. The `Await` engine grew (zkpromise/discharge/promiseGraph are
real structures now), and the living cell is sound (`livingCell_sound`, `Exec/Cell.lean:102` PROVED), but
return-projection and fork are STILL absent as typed effects in `FullActionA`.]**

- **What.** Turns are one-directional today. The typed `Obs`-delta **return projection** (the callee
  commits, the caller awaits — the zkRPC second observation) and **fork-as-span/pushout** (the one
  structural hole; time-travel and merge derive from it) are MISSING as typed effects in `FullActionA`.
  The await engine is no longer an embryo: `Await.lean` carries real `zkpromise`/`discharge`/`promiseGraph`
  structures with a `zkpromise.toCore` (`Await.lean:342-406`, the proof-carrying resolver, #82 in-flight);
  but the one-shot linear continuation typing and the return-delta-as-effect are still absent.
- **Soundness-criticality.** **ABOVE-CORE** (CORE-but-after-the-living-cell-lands). Not a minimal-swap
  prerequisite.
- **Rough size.** **Large.** New coalgebra ops. checkpoint/restore/replay/time-travel/merge are then
  *theorems*, NOT effects — adding them as effects is a category error.

---

### FILL D-gap (NEW, the most decision-relevant OPEN item) — forest-delegation edges are DISCARDED (#138)

**[STATUS: GENUINELY OPEN — task #138 in-flight. This is the one place where the wide executable turn is
DECORATIVE about delegation: the call-forest's per-edge `holder`/`keep`/`parentCap` are dropped on the
floor, so children run against UNCHANGED authority state with no `Caps.derive` handoff. No-amplify is
therefore VACUOUS on execution — the `forestEdgesA` law is about the *data*, not what runs.]**

- **What.** `execFullChildrenA` (`FullForest.lean:122-127`) pattern-matches each child edge as
  `⟨_, _, _, sub⟩` — **discarding `holder`, `keep`, and `parentCap`** — and runs `execFullForestA s sub`
  against the parent's UNCHANGED chained state. There is NO attenuated cap installed into the child
  holder's slot before the subtree runs. So `execFullForestA_no_amplify` (`FullForest.lean:251`) is a
  STRUCTURAL fact about the edge *data* (`forestEdgesA`), correctly proved, but it asserts nothing about
  the executed handoff because no handoff happens.
- **The fix (decided).** Route each edge onto `recKDelegateAtten` — the faithful attenuated-delegate that
  ALREADY EXISTS (`TurnExecutorFull.lean:234-241`, with `recKDelegateAtten_non_amplifying` REAL-rights ⊆
  held and `recKDelegateAtten_frame` touching only `caps` ⇒ `ledgerDeltaAsset = 0` ∀ asset). Because the
  handoff is balance-neutral, the per-asset conservation keystone (`execFullForestA_conserves_per_asset`)
  lifts for free; the new content is binding the edge's `keep`/`parentCap` through the install and
  re-proving no-amplify over the *executed* edge (`granted ≤ held`) instead of the edge data.
- **Where.** The discard: `FullForest.lean:124`. The target primitive: `TurnExecutorFull.lean:234`. (The
  sibling holes #2/#5 in #138 are the same threading; revocation root-of-trust #3 is already CLOSED, see
  FILL D below.)
- **Soundness-criticality.** **SOUNDNESS-CRITICAL for delegated authority** — until closed, a delegated
  subtree's authority is whatever the parent's slot already held, not the attenuated `keep`. This is the
  top OPEN integration gap in the wide turn.

---

## 2. Dependency order — UPDATED 2026-06-02 (the top of the tree has LANDED)

```
   ┌──────────────────────────────────────────────────────────────────────────────┐
   │  META-FILL [DONE #130/#131/#132/#135]: FullActionA (46 effects) + execFullA +  │
   │  execFullForestA (tree) + execFullForestG (auth-gated) over the PER-ASSET      │
   │  RecChainedState; spine re-proved via execFullForestA_eq_execFullTurnA bridge, │
   │  #assert_axioms-pinned. FILLs 1,2,3 ABSORBED HERE.                             │
   └──────────────────────────────────────────────────────────────────────────────┘
                                          │
  FILL 1 (per-asset vector) ──── [DONE #129] recTotalAssetWithEscrow IS the conserved measure of
                                  the wide spine; recKExecAsset_no_cross_asset_leak proved.
  FILL 2 (escrow/note) ───────── [DONE] 12 of the 46 arms; conserves recTotalAssetWithEscrow.
  FILL 3 (committed/noteCreate) ─ [DONE #121] committed triple rides the plain-escrow primitive.

  ══════════════════════ THE LIVE FRONTIER (what gates the swap NOW) ══════════════════════

  FILL J (wire codec roundtrip) ── [IN-FLIGHT #136, build RED] ~30 productions PROVED & pinned;
   the LEAF parseCellW_encode + its assemblers (parseCellsW/parseWState/parseForestW/
   parseChildrenW) currently depend on sorryAx — the 5 sorry-carrying keystones. THE blocker.

  #138 forest-delegation edges ─── [OPEN #138] execFullChildrenA discards holder/keep/parentCap
   (FullForest.lean:124); route onto recKDelegateAtten. SOUNDNESS-CRITICAL for delegated authority.

  FILL 7-biscuit (ρ_in/ρ_out) ──── [PARTIAL] swiss membrane executable; biscuit exportKey/importKey
   still absent from FullActionA.

  ══════════════════════ STILL GENUINELY OPEN (below the wide turn) ══════════════════════

  FILL 4 (StateConstraint →74) ─── [OPEN] boundDelta returns true; RelayOperator/BlindedQueue/
   CapInbox carry -- OPEN: notes for RateLimitBySum/WitnessedPredicate/SenderAuthorized.
  FILL 5 (WAL durability) ──────── [RELABEL done, SEMANTICS open] still rfl; no crash model.
  FILL 6 (cross-cell fused) ────── [LANDED as a SEPARATE module] crossForest_conserves PROVED in
   Exec/CrossCellForest.lean; a single FUSED intra+cross executable is the residue.

  ══════════════════════ ABOVE-CORE (node-level / research / privacy) ══════════════════════

  FILL 8 (caveat/attestation) ──── [8a/8b/8c/8f MODELED as Authority modules + Prop-portals;
   8d/8e PARTIAL; wiring CaveatChain into the executed gate is the residue]
  FILL 9  (higher-order handler) ─ [ABOVE-CORE] keystone weld still OPEN (notation pun).
  FILL 10 (distributed) ────────── [10a/10f RESOLVED; 10e PARTIAL; 10b/10c/10d portals]
  FILL 11 (return-projection/fork) [ABOVE-CORE] await engine grew; effects still absent.
```

**The critical-path insight (REVISED):** the original's insight — *do FILL 1 (per-asset vector) first
because it sets the conserved measure everything else re-proves against* — **was followed and is now
HISTORY.** `recTotalAssetWithEscrow` is the measure; the wide spine is proved over it. The remaining
critical path to the swap is now: **FILL J (close the 5 sorry-carrying codec keystones — the build is RED
on them) → #138 (route the forest-delegation edges onto `recKDelegateAtten`, balance-neutral so
conservation lifts free) → FILL 7-biscuit + FILL 4 (storage evaluation)**, with FILL 5's crash semantics
and the FILL 8 gate-wiring carried in parallel.

---

## 3. PREREQUISITES-FOR-SWAP vs ABOVE-CORE

The swap = delete the Rust kernel, route the node through the Lean FFI, with the differential
(kernel-vs-new-Rust) as the net. The kernel the FFI exports must be **sound** (no invalid transition
accepted) and must **host a real turn** (the executable turn must cover the effects a dregg node performs).

### PREREQUISITE FOR THE SWAP — status as of 2026-06-02

| Fill | Status | Why it gates the swap |
|---|---|---|
| **META — widen to FullActionA (46 effects) + tree + auth gate** | **DONE** #130/#131/#132/#135 | The FFI turn is no longer 5 effects. `execFullForestA`/`execFullForestG` host the wide turn; exported as `dregg_exec_full_turn_wide` / `dregg_exec_full_forest_auth`. |
| **FILL 1 — per-asset vector** | **DONE** #129 | `recTotalAssetWithEscrow` is the conserved measure of the wide spine; `recKExecAsset_no_cross_asset_leak` proved. |
| **FILL 2 — escrow/note in the executable turn** | **DONE** | 12 of the 46 arms; conserves the combined per-asset total. A node CAN lock escrow + spend a note. |
| **FILL 3 — committed-escrow/noteCreate (#121)** | **DONE** | Committed triple rides the plain-escrow holding-store primitive; no shadow. |
| **"FILL D" — executed credential+caveat+revocation auth gate** | **DONE** #132/#139 | `FullForestAuth.execFullForestG` gates each node on `credentialValidG ∧ capAuthorityG ∧ caveatsDischarged ∧ revocationGate`; conservation survives the gate (`execFullForestG_conserves_per_asset`). Revocation is a real kernel-state side-table (`RecordKernel.revoked`, #139). |
| **FILL J — wire codec parse∘encode THEOREM** | **IN-FLIGHT** #136, **build RED** | The differential's safety net. ~30 productions proved & pinned; the cell-value leaf `parseCellW_encode` + its assemblers (`parseCellsW`/`parseWState`/`parseForestW`/`parseChildrenW`) currently depend on `sorryAx`. **This is the active blocker.** |
| **#138 — forest-delegation edges** | **OPEN** #138 | `execFullChildrenA` discards `holder`/`keep`/`parentCap` (`FullForest.lean:124`); delegated subtrees run on UNCHANGED authority. Route onto `recKDelegateAtten` (balance-neutral, conservation lifts free). |
| **FILL 7 — ρ_in/ρ_out membrane** | **PARTIAL** | Swiss flavor (`exportSturdyRefA`/`enlivenRefA`/…) executable; biscuit `exportKey`/`importKey` still absent. |
| **FILL 4 — StateConstraint →74** | **OPEN** | `boundDelta` returns `true`; the storage modules carry `-- OPEN:` for `RateLimitBySum`/`WitnessedPredicate`/`SenderAuthorized`. Moved-complexity until evaluated. |
| **FILL 6 — cross-cell CG-5** | **DONE (separate module)** | `crossForest_conserves` proved in `Exec/CrossCellForest.lean`, routed-to from `FullForest.lean`. A FUSED single executable is the residue. The `νF₁⊗νF₂`-non-final framing is RETIRED; the real obstruction is `hyper_binding_is_proper`. |
| **FILL 5 — WAL durability honesty** | **RELABEL done; SEMANTICS open** | The `rfl` is now docstring-relabeled as a cache-rebuild law; a real crash/recovery model is still absent. |
| **FILL 8a/8b — caveat-chain integrity, 3P discharge** | **MODELED (structure) + Prop-portal** | `Authority/CaveatChain.lean` + `ThirdPartyDischarge.lean` model the chain/two-key split with removal/tamper negative theorems relative to honest §8 portals. **Residue: wire `CaveatChain` into the executed `caveatsDischarged` gate** (today the gate uses a tiered meet + a macaroon-tail check). |

### ABOVE-CORE (genuine capabilities / node-level / research; NOT swap prerequisites)

| Fill | Status | Note |
|---|---|---|
| **FILL 8c/8d — selective disclosure, multi-show unlinkability** | 8c MODELED; 8d PARTIAL | `SelectiveDisclosure.lean` carries subset disclosure + predicate proofs + the anonymous-multi-show axis. The one TRIVIAL-ONLY HolderAnonymity de-vacuify is #127 (`pending`). |
| **FILL 8f — repudiation / designated-verifier dial** | **BUILT (model) + Prop-portal** | The verifier-indexed `DischargedFor` axis the original prescribed EXISTS (`Authority/DesignatedVerifier.lean`); the DV-ZK circuits are the §8 portal. |
| **FILL 9 — higher-order handler tier** | ABOVE-CORE | More proved scaffolding (`proofForest_sheaf_sound`), keystone weld still OPEN. |
| **FILL 10 — distributed conformance** | 10a/10f RESOLVED; 10e PARTIAL; 10b/c/d portals | Cordial-Miners DAG modeled (`SuperRatification.ofLace`); CapTP GC closed by lease (`CapTPGC.lean`). Gossip/Stingray/federation-Merkle remain. |
| **FILL 11 — return-projection + fork** | ABOVE-CORE | Await engine grew (zkpromise/discharge); the two coalgebra effects still absent. |

---

## 4. The honest one-paragraph summary — REWRITTEN 2026-06-02

The Lean dregg2's executable turn is **no longer a 5-effect scalar kernel.** The META-FILL landed: the FFI
now exports a **46-effect, per-asset, tree-shaped, auth-gated** turn — `FullForest.execFullForestA`
(46-arm `execFullA` over the per-asset `RecChainedState`, all-or-nothing tree) and
`FullForestAuth.execFullForestG` (the same wrapped in `credentialValid ∧ capAuthority ∧ caveatsDischarged
∧ revocationGate`), exported as `dregg_exec_full_turn_wide` (`FFI.lean:2732`) and
`dregg_exec_full_forest_auth` (`FFI.lean:3027`). The former top-priority fills are **DONE**: (1) the
per-asset conservation vector is native to the record kernel (`recTotalAssetWithEscrow`,
`recKExecAsset_no_cross_asset_leak`, all `#assert_axioms`-pinned), #129; (2) the escrow holding-store + note
nullifier/commitment sets are 12 of the 46 arms, conserving the combined per-asset total; (3) the
committed-escrow + `noteCreate` regression is closed (#121); and the executed credential+caveat+revocation
auth gate is built (#132/#139). The cross-cell CG-5 is proved as an executable module
(`Exec/CrossCellForest.lean`, `crossForest_conserves`), routed-to rather than fused; the caveat/attestation
crypto FACES are modeled as dedicated Authority modules (`CaveatChain`, `ThirdPartyDischarge`,
`SelectiveDisclosure`, `DesignatedVerifier`) with the unforgeability/encryption as honest §8 Prop-portals —
the "everything is a `Bool`" framing is retired. **The LIVE frontier is now two things:** **FILL J** (the
wire-codec parse∘encode THEOREM, #136, in-flight — ~30 productions proved & `#assert_axioms`-pinned, but
the cell-value leaf `parseCellW_encode` and its assemblers `parseCellsW`/`parseWState`/`parseForestW`/
`parseChildrenW` currently depend on `sorryAx`, so the build is RED on exactly those 5 keystones), and the
**#138 forest-delegation gap** (`execFullChildrenA` discards each edge's `holder`/`keep`/`parentCap` at
`FullForest.lean:124`, so delegated subtrees run on UNCHANGED authority — route them onto the existing
`recKDelegateAtten`, balance-neutral so conservation lifts free). Below those: FILL 4 (grow
`StateConstraint`; `boundDelta` still returns `true`), FILL 5 (the `rfl` checkpoint is relabeled but a
crash/recovery model is unbuilt), FILL 7-biscuit (the swiss membrane is executable; the biscuit
`exportKey`/`importKey` is not). Above-core: the higher-order handler keystone weld (still an OPEN notation
pun), distributed gossip/Stingray/federation-Merkle, and the coalgebra return/fork effects. Two important
framing CORRECTIONS the code forced: the *`νF₁⊗νF₂` is non-final* obstruction is FALSE and RETIRED (the
product of finals IS final; the real obstruction is `hyper_binding_is_proper` — sound joint-turns are a
PROPER SUBOBJECT of the product, `Hyperedge.lean:164`), and `phi_functorial` is now a real PROVED theorem
(`Spec/VatBoundary.lean:422`), not the by-design `sorry` this doc once narrated.

---

*A closing couplet, re-warmed now that the egg has grown:*
*forty-six effects in the turn, and the vector conserved — / the proofs moved INTO the machine, as the doc once observed;*
*now the codec wants its left-inverse and the delegation its keep — / two seams from the swap, and the kernel will not sleep.* 🐉🥚
