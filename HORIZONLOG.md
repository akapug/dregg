# HORIZONLOG — the named-follow-up burn-down

*(Standing rule: when a lane/commit NAMES a follow-up, residue, or closure lane,
it gets a line HERE in the same breath — "named in a report" is not durable.
Each line: what · where it was named · the closure shape. Remove lines when
closed (git history is the record). This is a burn-down list, not a parking
lot: per WE-DO-NOT-NAME-WE-SHIP, anything that sits here across many sessions
should be either scheduled or explicitly demoted to the Research tier with a
reason.)*

Last sweep: 2026-06-13 (flagged-items burndown — removed ~14 landed/struck items,
deduped the DreggDL/sel4/snapshot landings into git history, kept live tails).

## Rides THE ROTATION (dies at or lands with the one VK epoch — do not do separately)

- sbox_registers→0 descriptor metadata (chip uses inline x⁷; named in 0b05afc1a) — flip at the closing-ceremony regen.
- RESERVED mask removal + 186→159 column compaction (REORIENT EPOCH STATUS).
- registers 8→16 + FactoryDescriptor.fields · PI v3 (committed-height + rateBound/challengeWindow) · heap_root register.
- iroot bound into recStateCommit (non-omission obligation, 9dcd42cd9).
- cap-reshape phase D (in-circuit cap crown completion; #103 audit: A–E + RevokeCapability done. The 2026-06-13 burn-down to fully-coherent left TWO ember-decisions characterized under "Decisions pending (ember)": the two-AIRs sovereign-path soundness item + the 4-ary-vs-sorted membership-leg retire-or-keep. The stale-`EffectVmEmitCapRoot` item resolved NO-OP: that module is the load-bearing Phase-A digest spine under the whole cap family, already coherently scoped — clarified its V2/Phase-E layering with a forward-pointer doc note, not retired).
- #150 confirmation: does the umem `absent` + sorted-gap boundary fully retire DslRevocationTree (TREE_DEPTH=4)? One read-pass at cutover.
- fresh-key sorted-INSERT map-op (reuses MapAbsent adjacency; named in cff8509ba).
- per-turn chip amortization (blocked on an IR-v2 turn assembly; named in 0b05afc1a).
- MMR §6 CommitBindsMMR layout fact (node writes both roots at dense positions; the Receipt-apex residual premise, 7894e5789) — discharged-by-construction at the flag-day.
- balance/nonce → NAMED-register assignment (RotatedLimbs carries no separate balance/nonce limbs; the umem projection maps them to the heap domain — pick ONE canonical story; ember-visible decision, ROTATION-CUTOVER.md §2 note).
- cells_root + iroot per-turn PRODUCERS in turn/ (`turn/src/rotation_witness.rs`, NAMED in EffectVmEmitRotationV3.lean §3) + lifecycle/epoch trace carriers — ROTATION-CUTOVER.md §5 items 3-5. The staged-additive producers + trace builder + cell≡circuit differential ALREADY LANDED GREEN (51850ee91, no VK bump); these notes track the FLIP consumption. SEQUENCING: build the rest WITH the flip's rotated trace builder, not before.
- guardAtom IR kind (umem adapter c) confirmed NOT landed (absent from DescriptorIR2.lean + descriptor_ir2.rs): in-circuit policy/caveat enforcement for v2/v3 = cap-crown phase D + Policy.lean line, rides rotation.
- HEAP-KEYED CAVEATS executor runtime discharge (named premise `HeapCaveatRuntimeDischarge`; template = `verify_slot_caveat_manifest`; semantics welded via `tagHeapAtom`→`HeapAtom.lift`→`evalHeap`) — ROTATION-CUTOVER §5 item 9; at the flag-day the staged 29-felt manifest replaces the live 25-felt slot manifest in the regenerated PI region. (Wire shape STAGED; live v1 manifest untouched.)
- PI v3 rateBound/challengeWindow: carried-only (producer copies context into PI 202/203; verifier pins ZERO sentinels, proof_verify.rs:269-270). Enforcement arrives with optimistic-proving/dispute (#169) which owns these slots — nothing further pre-#169.

## THE ROTATION FLIP — the irreversible tail (ember-COMMISSIONED, a4c7368ae; touches cell/+live registry+executor PI)

*(The genuinely-new long pole — staged producers + rotated trace builder + cell≡circuit
differential — is DONE and GREEN beside v1, no VK bump. Two MORE staged-additive stages landed
2026-06-13 (Opus, G3-authority + G4-cohort); what remains is the deliberate live-path rewrite +
flip:)*

- ✅ DONE (staged-additive, green): **G3 AUTHORITY-DIGEST DESIGN** — the v9 rotated commitment now
  binds the FULL authority state (not a subset). `cell/src/commitment.rs::compute_authority_digest_felt`
  folds permissions/VK/delegate/delegation/program/mode/token_id + visibility/commitments/proved/
  side-table roots + fields[8..16] into register r23 (Lean welds leave r23 free → the anti-ghost
  keystone binds it, ZERO Lean change). Three-way agreement (cell v9 / producer rotation_witness /
  trace generator) holds — all derive r23 from the same fn. Tooth: `v9_binds_full_authority_state`.
  Doc: ROTATION-CUTOVER §2a. (cell + turn, no VK bump, v8 untouched.)
- ✅ DONE (staged-additive, green): **G4 COHORT-GENERAL GENERATOR** — `trace_rotated::
  rotated_descriptor_name_for_effect` resolves any of the 26 cohort effects to its `*VmDescriptor2R24`
  (fail-closed for non-cohort), `effect_vm::trace::effect_selector` extracted as the single source of
  truth; `sdk::prove_effect_vm_rotated_ir2_with_caveat` is the cohort-general rotated prover. Teeth:
  `resolvers_cover_exactly_the_rotated_registry` (=26), `non_cohort_effects_resolve_to_none`. Doc:
  ROTATION-CUTOVER §2c.
- ⚠ **NEWLY SURFACED BLOCKER (the cohort boundary).** The rotated `v3Registry` is only the 26
  v2-graduated effects. The LIVE path proves MORE: `MakeSovereign`/`CreateCell`/`CreateCellFromFactory`/
  `SpawnWithDelegation`/`ReceiptArchive`/`CellUnseal`/`GrantCapability`/`RevokeCapability`/`EmitEvent`/
  `Custom` are NOT in the rotated registry. Flipping to rotated-ONLY + deleting v1 would BRICK these
  effects (no rotated descriptor to prove them). RESOLUTION before "v1 deleted": extend the Lean
  `v3Registry` to emit rotated descriptors for these (a Lean-emission act, the same `rotateV3` lift) +
  re-pin the registry TSV. This is the gate that makes "the rotated path is the ONLY path" actually
  cover all effects. (Until then v1 must stay reachable for them.)
- REMAINING (the live-path rewrite + flip, the deep multi-day tail): route `prove_full_turn` →
  rotated `Ir2BatchProof` as the only path (changes `AttachedSubProof` wire shape + `compose_aggregate`
  + `ComposedProof` effect-vm leg) · rewrite `verify_full_turn`/`verify_effect_vm_proof_with_cutover`
  to the rotated verifier · rewrite executor `proof_verify.rs::verify_and_commit_proof` PI
  reconstruction (v1 `pi::ACTIVE_BASE_COUNT` shape + bespoke `stark::verify` → the rotated 38-PI
  Ir2BatchProof + v9 commitment) · `aggregate_bilateral_prover.rs` · reroute ~70 v1 call-sites
  (node/sdk/verifier/lightclient/perf/preflight) · un-gate (remove `recursion`/`DREGG_ROTATED_PROVER`).
  THEN regen EmitAllJson→`v3Registry` live · cell `CANONICAL_COMMITMENT_CONTEXT` v8→v9 · re-emit the
  R=16 `columns::rotation` staged-probe module at R=24 (the `rotation_layout_matches_lean` drift guard
  + SHA pin re-anchor — NOTE the LIVE rotated path is ALREADY R=24 via `trace_rotated`/`caveat`; only
  the staged-probe reference module is R=16) · re-pin ~58 byte artifacts + 11 drift guards · VK epoch +
  succession · DELETE v1 (`effect_vm_p3_full_air.rs`, `lean_descriptor_air.rs` v1, `CutoverFallback`,
  the v1 PI layouts, the ~40 test call-sites in `effect_vm_descriptor_cutover_harness.rs` +
  `effect_vm_{grant,attenuate}_non_amp.rs`). ROTATION-CUTOVER §3 steps 2-6 / §4 pins.

## Metatheory closures (Lean-side, lane-sized — tails of landed work)

- ASSURANCE §5 Stage-1 / CRITICAL-2 codec-in-TCB: the LEAN half is now CLOSED — `Dregg2/Exec/FFI/Refine.lean` proves `execFullForestAuthStep` (the `@[export dregg_exec_full_forest_auth]` body) REFINES the model (`export_refines_on_parseable`/`_endToEnd`, composed with the existing `CodecRoundtrip.parseWWire_encode`), so the turn/effect wire codec is inside the proof (pinned in Claims §28b). RESIDUAL = the RUST codec, two named obligations, NOT closed: (1) **translation-validation of `dregg-lean-ffi/src/marshal.rs`** — a 2231-line hand-rolled byte-for-byte mirror of the Lean grammar (`marshal_turn_hosted` emit at `marshal.rs:617`; `unmarshal_result` decode at `:1710`), upheld TODAY only by `dregg-lean-ffi/src/marshal_roundtrip.rs` differential vs the real FFI symbol — the obligation is `marshal_turn_hosted(w) = encodeWWire(lift w)` as a theorem (generate the Rust from Lean, or a verified-Rust mirror), not a test corpus; (2) the **Lean→C / `libdregg_lean.a` link** boundary (no binary-correspondence statement that the linked `.a` IS the `@[export]`ed Lean) — the seL4 C-to-binary analogue. Both are the §5 Stage-1 remainder; obligation #1 is the sharper "translation-validation" one. → dregg-lean-ffi/, post-rotation (disjoint from the proof-wire flip).
- Argus joint-AIR fold (Silver→Gold layer: per-leg descriptors folded; not an Argus/ statement).
- Coeffect dst-liveness (named in the 4dd84a3ae audit; outside the four apex modules).
- BiorthRelational: threshold-D iff at Shamir t-of-n (proved at 2-of-2 additive); n-ary trace statement (reduced to the adjacent-step atom).
- Trustline: `settled`-era pureCredit — Lean has both collateral points; the Rust pureCredit realization (issuer-well draws) is open (7da845758 divergence 1-as-Rust).
- Quorum unification (#170) consumer migration: `BlsQuorumCert.lean`/`EpochReconfig.lean` still transcribe the historical `n−⌊n/3⌋` + carry `StrictBft`; `MembershipSafety.lean` still has the `n=0↦0` guard. The unified `supermajorityThreshold` Lean twin LANDED (QuorumThreshold.lean) — migrate the consumers onto it (bls_quorum_diff.rs/epoch_diff.rs/membership_safety_differential.rs pin the relations until migration).
- Channels delegation_epoch wire carrier: the Lean-producer/wire path has no per-cell `delegation_epoch` carrier yet (a `DelegationEpochEquals` program evaluated there fails closed — wire lockstep before channels ride the producer); pre-atom channel cells keep the old program (no live-cell program-upgrade verb).
- Channels CountGe tails: per-element approval binding (exhibited ≠ "approved THIS turn" — the actor-bound approval-slot ceremony must write the quorum commitment slot before `councilGated` replaces `senderIs admin` in the deployed program); CountGe AIR projection (witness-side scalar only).

## Node / runtime closures

- **Stage-5 consensus de-vac (Klein/HIGH-6) — `docs/STAGE5-CONSENSUS-DEVAC.md`.** LANDED: the running-node witness that consensus runs at n>1 — `scripts/devnet-n3-ordering.sh` + `node/tests/three_node_ordering_rule.rs` boot 3 REAL nodes in `--federation-mode full` (3-validator genesis, supermajority(3)=3) and assert [A] full-mode multi-party tau path engaged + [B] cross-node block exchange over the real gossip wire (both PASS). Verified: the Lean BFT model is NON-vacuous (`bft_safety` is adversary-parametrized, liveness reduced to a DLS88/HotStuff `Pacemaker`; the empty-adversary inhabitant is only a satisfiability witness) and the tau rule faithfully refines the Rust (`BlocklaceFinality.lean`). **STILL OPEN = S5-1 (the blocker):** the running node does NOT yet COMMIT a turn through the rule at n≥2 — `latest_height` stays 0, the finality executor never fires, because the gossip DISSEMINATION (eager/lazy Plumtree over unidirectional QUIC streams, `net/src/gossip.rs`; eager set seeded from dialed `peer_addrs` at `blocklace_sync.rs:1140`) delivers blocks ASYMMETRICALLY at small N, so no node assembles a supermajority of creators' round-blocks and `is_super_ratified` (`ordering.rs:263`) never fires (observed at n=2 AND n=3). NOT the rule (verified) nor the Lean (non-vacuous) — a deployment-fidelity gap in dissemination. Closure = make the eager set bidirectional / drive frontier-pull to drain orphans before each wave / eager-push to ALL committee peers for intra-committee sync; acceptance test EXISTS (flip `three_node_ordering_rule.rs` [C] hard via `DREGG_TEST_REQUIRE_FINALITY=1` → must go green: all 3 reach an AGREED attested root). Then S5-2 live commit refinement, S5-3 #170 quorum-consumer migration, S5-4 consensus leg of the composed apex, S5-5 equivocator Lean↔Rust differential pin, S5-6 finality-on-demand (`docs/CONSENSUS-FLEX.md`). → net/gossip + blocklace/dissemination + node/blocklace_sync.
- Stale-cap c-list sweep (channels 72d43dc64 residue): epoch-step turn should `RevokeCapability` superseded grants. STILL OPEN — a real verb gap, NOT a quick fix: `member_cap_grants` installs into each MEMBER's c-list, while `RevokeCapability {cell,slot}` removes from a cell's OWN c-list; sweeping a departed member needs cross-cell `Delegate` authority the operator doesn't hold. `RevokeDelegation` epoch bump already DARKENS prior-epoch group caps at admission (R7 `CapabilityStale`) → this is c-list GC (storage), not soundness. Honest closure = a new verb shape (member-initiated self-revoke or group-scoped revoke authority). → node/turn, post-flip.
- Adjudication: bond cell → program-toothed obligation cell; tau-exclusion via a membership cell (court is the value leg only; 460d4d6bd residues). STILL OPEN — bond is a plain operator cell, not yet deployed via the obligation factory; deferred to AFTER the FLASH-WELL/blueprint `obligation_factory_descriptor` lands+verifies, then `post_bond` deploys via the factory in one slice. (That pattern now landed — unblocked for a future lane.)
- Storage: erasure coding + dedup-beyond-content-addressing — IN-CRATE half closed (storage/src/availability.rs, 10 tests). REMAINS: the node put/get HTTP route (gated by storage-gateway-mandate cell) can now CALL the in-crate availability route — the "weld to the shell" half. → node, post-flip.
- Trustline payment-channel parity: channel close (TL_STATE_CLOSED residual-escrow return) · one-factory collateral parameter · MCP `dregg_extend_trustline` · remote-silo pubkey registration (n=1 collapses it) · multilateral rippling (TRUSTLINES.md §7).
- Trustline pureCredit HTTP lane: node OpenRequest has no `collateral` field → HTTP open is fullReserve-only; `trustline_service::parse_collateral` is dead (`#[allow(dead_code)]`+TODO(collateral-axis)). Rust semantics+SDK exist; wiring the request field is the lane. → turn/node.
- Hosted-operator epoch-key custody posture (sovereign-member groups ride the SDK noun client-side; channels residue — partly an ember-decision).
- Divergence-ledger doc churn: `turn/tests/rust_lean_divergence_finder.rs:684` overwrites the git-tracked `metatheory/docs/rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md` on every run, dirtying trees + blocking persvati pushes — emit to a build-artifact path (or commit deliberately). One-line fix. → turn/ (off-limits this run; STILL LIVE, tree dirty at HEAD).
- CLI `config init` not path-injectable: `cli/src/config.rs::config_path()` hardcodes `~/.dregg` → `dregg config init` mutates real home, preflight can only gate read-only `config show`. Honor `DREGG_HOME`-style override, then restore a hermetic preflight `cli_config_init` check. → cli/.
- node recovery overlay first-writer-wins bug (surfaced by the snapshot lane): `node/src/state.rs` recovery uses `insert_cell` (strict insert), so a post-checkpoint write to a cell the checkpoint ALREADY holds is silently dropped; the convergence root-mismatch only LOGS, does not fail closed. Fix = `upsert_cell` (the verified `CrashRecovery.upd` point-update needs remove-then-insert). → node/persist, post-flip.
- persist snapshot wire half: in-crate `ship_snapshot`/`apply_snapshot`/`apply_snapshot_verified`/`install_snapshot` LANDED green (persist/src/snapshot.rs, 7 tests, shape = CrashRecovery.lean). REMAINS: node-side `GET /snapshot/{from}` serve + joiner consume route so a fresh node bootstraps over the network. → node, post-flip.
- checkpoint-prune → commit-log compaction (§2.1): `prune_before` trims attested roots but commit-log records below a finalized checkpoint are never compacted (unbounded WAL). Add `CommitLog::compact_below(height)` preserving the index-audit invariant. → persist.

## Product surfaces (post-rotation)

- dregg-query: attested-queries feature only (Q2 of docs/EPISTEMIC-DATALOG.md) — NOT the full Datalog engine.
- Flash-well: `BalanceDeltaGte` relative-balance atom (one evaluator arm + Lean `Exec.Program` twin) collapses the fee-ratchet ladder into one constraint + closes the donation-cushion residue; `Dregg2.Apps.FlashWell` keystones land with it. The blueprint + SDK are AUTHORED (cell/src/blueprint.rs flash-well, sdk/src/flashwell.rs) but sprint-UNVERIFIED.
- Willow geometry for storage caps (3D area caveats, range reconciliation) — adopted design, not scheduled.
- range-based set reconciliation (§1.5/§3.2d, Willow shape): the shared primitive behind scalable anti-entropy (O(diff·log) not O(state)) AND storage partial-sync; cap chains as the pluggable authorization. Adopt the geometry, keep our proofs.
- eclipse hardening at scale (§1.1): peer_score buckets by SocketAddr today; add /24·/48 prefix + AS-diversity bucketing so a single cloud /24 cannot fill the eager set.
- availability route follow-ons (§3.1): swap XOR-prototype erasure (erasure.rs:11) for real Reed–Solomon; real Merkle-path chunk proof vs manifest.root (erasure.rs:226 is integrity-only).
- proving-modality dial #169 (§4.1): make prove-on-demand vs checkpoint vs eager a CONFIGURED axis, not hardcoded policy; settlement/pipelining depth (§4.2) parameterized by topology (n=1 = immediate settlement). Owns the PI 202/203 slots.
- Room-as-OS + delay-tolerant polis (docs/ROOM-AS-OS.md, docs/DELAY-TOLERANT-POLIS.md).
- **pg-dregg M3** (named 2026-06-13; M2 mirror + Tier-C chain-gate + the §11 write outbox LANDED + live on pg17 — `cargo pgrx test pg17` 39 green, `scripts/e2e-live.sh` walks it on a standalone psql db; `node/src/pg_mirror.rs` `pg_live::PgSink` writes through over tokio-postgres incl. caps/memory in one txn): two orthogonal closures. (a) **the outbox drainer** (docs/PG-DREGG.md §11.4): a node-side tokio task drains `dregg.submit_queue` pending rows as `dregg_kernel`, runs the submit gates + `execute_via_producer` (the #171 executor), and resolves the row + mirrors back — closes "a pg-user submits a verified turn FROM pg" end-to-end. (b) **the per-turn PROOF gate** (§10.2): `dregg_verify_turn` honestly does ONLY the structural chain re-validation per-row (a CommitRecord carries no per-turn proof); the soundness half is the whole-chain IVC light client (`circuit::ivc_turn_chain::verify_turn_chain_recursive`) attesting a receipt RANGE — wire it behind the `tier-c` feature as a range-attest SRF, NOT a per-row STARK. → pg-dregg/node, post-flip. Tier D (executor in-backend) stays the north star, gated on the pg/Lean process-model spike.

### SDK polyglot crypto/binding closures

- **sdk-ts organ-noun crypto closures** (named 2026-06-13; sdk-ts now mirrors two-nouns + organ-noun as thin typed clients, green): three crypto ops stay node/wasm-side (pure TS has no Poseidon2/X25519/STARK): (a) `mailbox-verify-dequeue-proof-in-ts` (re-run storage queue Merkle verify over a drained batch); (b) `channel-seal-open-in-ts` (X25519→HKDF→ChaCha20-Poly1305 epoch-key seal/open so a TS member decrypts the fan-out — example uses placeholder ciphertext today); (c) `attested-verify-in-ts` (`verify_full_turn` STARK + federation threshold-sig check so `AttestedQuery` returns a CHECKED verdict — the light-client crown, likely waits on a wasm `verify_full_turn` export). (a)+(b) are the first users of `@dregg/sdk/wasm`.
- **userspace-verify TS/Py binding** (named 2026-06-13; `dregg-userspace-verify/` landed green, 22 tests): expose `analyze()` to TS/Py so `sdk-ts`/`sdk-py` call it pre-submission. (a) cheap path: SDK serializes its forest to JSON, shells/WASM-calls `dregg-uverify --json`; (b) integrated: a `#[no_mangle]` FFI `uverify_analyze(json_ptr,len)->json` in a small cdylib, bound from TS (napi/wasm) and Py (ctypes/pyo3 — the bridge already links libdregg). `Assurance`/`Finding`/`Locus` are Serialize+Deserialize → wire shape settled; the lane is the glue + an SDK `analyze()` sugar at `.sign()`-time.
- **DreggDL node `POST /deploy` ingress** (follow-up to the landed `dregg-deploy` + its TS/Py bindings, a7734efcc/a49448d09): a node endpoint accepting a DreggDL doc → `dregg-deploy::check` (refuse non-conserving/amplifying up front) → lower + submit per-root turns → return receipt chain + resolved factory_vks/cell-ids. Static check = pre-submission gate; executor stays the trust boundary. `dregg-deploy apply` = the same flow SDK-side. → node, post-flip.
- **sdk-py self-contained wheel**: (carried — packaging the Py binding as a standalone wheel that bundles libdregg). → sdk-py.

## APPS-POLISH lane (starbridge-apps demo-worthiness)

- **compute-exchange/ + gallery/ stub dirs** carry only a `manifest.json` (no crate) — decide: build them or delete the stubs.
- **escrow-market follow-ups** (escrow-market, 12 tests green): (a) the no-burn equality is settle-scoped in `child_program_vk` but NOT in the executor-installed flat `state_constraints` (executor installs `Predicate(state_constraints)`, evaluated unconditionally — apply.rs); to enforce exact conservation on the settle turn, either teach factory-birth install to use the cell's `Cases` program (`child_program_vk`) OR add a settle-gated relational atom. Until then no-burn rests on `build_settle_action` emitting a balanced split. (b) real ledger-balance binding — ESCROWED/RELEASED/REFUNDED are slot integers, not moved balance; wire settle to a real value transfer (trustline/flashwell `.turn()`) for the organ-true version. → starbridge-apps/turn, post-flip.
- **userspace-verify integration point** (depends on the landed toolkit): escrow's `released+refunded==escrowed` conservation predicate is the first app-level customer for the static checks — lift it to a published checker. Same shape for agent-provenance `verify_chain` + bounty-board lifecycle monotonicity.
- **polis factory-birth co-location**: polis's executor-path teeth live in `sdk/tests/polis_*_e2e.rs`, not a `polis/tests/factory_birth.rs` like the other apps — co-locating a birth test makes it self-contained.
- **privacy-voting ballot unlinkability** (named in its README): the app gives one-vote-per-ballot + monotone tamper-evident tallies, NOT ballot/voter unlinkability (no mixnet/nullifier-set). True secrecy is a separate, stronger lane.

## HANDOFF READINESS (the pug bar — a stranger evaluates dregg as a finished, usable thing)

*(ember 2026-06-12: hand the system to pug to evaluate usefulness/usability for HIS purposes.
Everything here is judged by "works without ember in the loop.")*

- FRESH-CLONE BUILD: clone → documented steps → running node, no tribal knowledge. The FFI archive seeding (elan on PATH, lake build, seed-dregg2-closure.sh) is tribal-knowledge-heavy + bit US twice this session — it must be ONE documented command (or build.rs does it) with a loud, teaching failure mode.
- QUICKSTART re-verified against POST-ROTATION reality, every command actually run (it was verified pre-rotation; #110's closure predates the organs + rotation).
- The organs reachable as a STRANGER would: SDK two-nouns + trustline/channel/mailbox/storage nouns each with a copy-paste example that runs against a local node; error messages that teach.
- An evaluator's README: what dregg IS, what it guarantees (AssuranceCase in human terms), what it does NOT yet do (honest scope), the three things to try in the first ten minutes.
- The site/playground consistent with the shipped system (no stale pre-rotation surfaces).
- One real end-to-end story pug can run start-to-finish (two agents · trustline · channel · mailbox — money moves, messages flow, a removed member goes dark, every receipt checkable). The demo IS the evaluation artifact.

## Crypto / protocol artifacts (bounded, sequenced after the rotation)

- DKG ceremony-as-cell-app: rounds over blocklace broadcast + seal-pair channels + slashable complaints (core landed 29509149d; transport is the artifact). Slash itself defers to the court→obligation-cell lane (node-closures adjudication item).
- ECVRF per-agent sortition: LANDED (federation/src/vrf.rs — RFC 9381, sortition_select/verify_sortition, SDK surface in sdk/src/identity.rs). REMAINS: full compile+test gauntlet (authored in-sprint); ticket transport serde (byte codecs only); dalek `decompress` canonicality vs §5.5 unaudited; juror-seat binding of ticket pubkey → key-set opening is documented, not yet a checked verb.
- KERI identity event-log export: LANDED (node/src/identity_export.rs — portable KEL, route GET /identity/export/{cell}). REMAINS: full compile+test gauntlet; per-cell state-commitment openings against `ledger_root` (today the snapshot↔turn binding rests on the exporting node's commit log); cooling-window length check needs charter data.
- Proactive resharing anchored in epoch-transition certs; proactive-deletion requirements (dkg.rs NOTES).
- drand-style beacon chaining (only once heights can fork; one line in beacon_message).
- OCapN netlayer adapter (2–4 week artifact): the enabling `Netlayer`/`ocapn://` trait LANDED in captp (captp/src/netlayer.rs). REMAINS the adapter: Syrup codec + `op:start-session` handshake + descriptor translation onto our session/gc tables + a wire Goblins speaks → a Goblins peer holding a dregg sturdy ref.
- MLS/TreeKEM fan-out swap for channels (replaces only `seal_epoch_key_to_roster`; cell interface unchanged).
- VRF-grade public beacon (its own later effort; ORGANS §6).

## PRIVACY/OFFLINE-CELL lane

- **Rust private-participant turn role** (design + Lean model landed: docs/PRIVATE-OFFLINE-CELLS.md + Dregg2/Distributed/PrivateLeg.lean, keystone joint_turn_sound_with_private_legs, #assert_axioms-clean). To SHIP: a private-participant leg type in `coord/src/atomic.rs` — an AtomicForest participant whose contribution is (commitPre, commitPost, proof) not an applied action, with a commit-path verify-gate implementing MixedAdmissible (every private leg's STARK verifies + binds the shared jid); the AIR the `CarrierEncodesPrivLeg` hypothesis names (recKExecAsset + recStateCommit state-root opening, producible offline); state-root continuity across turns (commitPost[i]=commitPre[i+1], mirroring HistoryAggregation.ChainBound). Liveness out of scope (a dark private participant aborts the all-or-none turn). Crypto floor = STARK extractability (no new assumption). → coord/turn, post-flip.

## seL4 / DreggDL lane (design+scoping landed)

*(Scoping docs: docs/SEL4-EMBEDDING.md (bootable-image roadmap; THE blocker = libuv-free/IO-free
Lean leanrt+GMP on musl/seL4) + docs/CAPDL-POLYGLOT-DX.md (DreggDL = describe the cap graph once,
3 SDKs instantiate it). The dregg-deploy parser crate + TS/Py bindings + sel4 verifier-PD scaffold
ALL LANDED (a7734efcc / a49448d09 / 152e6b3a5). Remaining lanes:)*

- **sel4 cross-build tail** (verifier-PD scaffolded, `no-lean-link` PROVEN Lean-free at HEAD): the actual cross-build to `aarch64-sel4-microkit` (needs Microkit SDK + rust-sel4 toolchain, absent here) + `getrandom`-custom / `p3-maybe-rayon` serial-fallback for the bare target. → sel4/.
- **Lean runtime bottom-half port (THE blocker, weeks–quarter)**: IO-free, libuv-free `leanrt`+GMP so `libdregg_lean.a` links on musl/seL4. Blocks the **executor PD only** — the verifier PD is UNBLOCKED (`no-lean-link` proves it links Lean-free). Until the port, `no-lean-link` builds the node marshal-only (shadow-off) — bring-up scaffold ONLY, never the authoritative ship.
- **First rbg→seL4 port: `DirectoryFactory` → `seL4_Untyped_Retype`** (sel4/RBG-TO-SEL4.md): the smallest real port turning an rbg idea into a kernel-enforced mechanism (factory's slot-caveat becomes the Untyped retype template). Additive, NOT gated on the Lean-runtime blocker; belongs in a `sel4/factory-pd/` sibling once rust-sel4 is wired.

## STARBRIDGE-V2 (native gpui shell — embedded verified executor)

*(The master interface EMBEDS the real verified executor + runs a live local dregg world natively
— headless heart gpui-free + `cargo test`-able, 16 tests green; the window OPENS via gpui
`runtime_shaders`. Build-out lanes from docs/STARBRIDGE-V2.md coverage matrix:)*

- **organ panels** (trustline/channel/mailbox/court — types catalogued) + whole-graph ocap layout (per-cell edges live) + intents/factories/obligations/nullifiers panels.
- **proof-attach + STARK verification-status view**; native federation/remote-node panel (NodeClient::Http exists; reqwest gated to sel4-thin for now); seal/unseal/destroy/burn/factory-birth verbs (reachable via World::turn — UI affordance); multi-action call-forest composer.
- **live node connection** — move reads to gpui's async executor; wire `/api/events/stream` SSE into ReceiptInspector with `cx.notify()` (snapshot today).
- **seL4 framebuffer backend** — a gpui renderer targeting a framebuffer cap (SEL4-EMBEDDING end state) + **seL4 channel transport** (a `NodeClient::Channel` over an seL4 endpoint, same contract over IPC not TCP).
- **single-source wire types** — replace `starbridge-v2/src/model/` hand-mirrors with a shared `dregg-wire-types` crate depended on by both node + shell.
- **finish-the-window (HOST gap, not a crate defect)**: the runtime-shader path opens the window; the offline Metal Toolchain download is blocked by a damaged Xcode `DVTDownloads.framework`. The remaining ahead-of-time-shader option = provision the Metal Toolchain on a healthy Xcode.

## DREGG-ANALYZER (forensic/observability trace analysis)

*(New crate dregg-analyzer/ — ingests CAPTURED TRACES, ATTESTS via the REAL verifiers, 14 tests.
Build-out lanes:)*

- **live-capture hooks** — a node trace-export mode emitting `BlocklaceCapture`/`ReceiptStrandCapture`/`WalCapture` from the running node (the on-disk/wire types are already exact, so an export endpoint is a thin dump). → node.
- **Studio/Workbench visualization binding** — render the `AnalysisReport` (DAG w/ equivocation fork, finality bar, receipt link graph, WAL replay overlay) in the Starbridge/starbridge-v2 shell (report is already JSON-serializable).
- **gossip capture provenance** — the network source is `Observed`-only (gossip = liveness); a signed dissemination-receipt would graduate some eclipse signals to `Verified`.

## Decisions pending (ember)

- #93 proof-audit: build a harness, or declare `#assert_axioms` + non-vacuity-both-polarities + the Convergence gauntlet its successor and close. (Recommendation: the latter — WRITTEN UP as docs/ASSURANCE.md §4 with the close-rationale; awaiting ember's flip to close.)
- Hosted key custody posture (above).
- starbridge-apps stub dirs compute-exchange/gallery: build or delete (above).
- **#103 cap-crown — TWO EffectVM AIRs, the weaker one LIVE on the sovereign path (SOUNDNESS-shaped, not janitorial).** There are two constraint systems for the EffectVM proof: (a) the AUDITED p3-batch-stark `EffectVmP3Air` (`circuit/src/effect_vm_p3_full_air.rs`), which carries the GRADUATED cap-crown Phase-B gates (sorted-tree membership-open + leaf-update + submask + expiry-monotone, its `attn` module ~`:189-310`; the non-amp gauntlets `circuit/tests/effect_vm_{attenuate,grant,revoke}_non_amp.rs` exercise exactly these); and (b) the BESPOKE FRI `EffectVmAir` (`circuit/src/effect_vm/air.rs`), whose `eval_constraints` still pins AttenuateCapability `cap_root` as the LEGACY nested-digest `new_cap_root = H2(old_cap_root, H2(slot_hash, narrower))` (`air.rs:1365-1374`) — it has NO sorted-open / submask / non-amp tooth (verified: no `cap_root::`/`CAP_TREE_DEPTH`/membership markers in air.rs). The default full-turn path emits + verifies the p3 proof (`prove_full_turn`→`prove_effect_vm_p3`, stored in `FullTurnProof.proof_bytes`; verified live via `dregg_sdk::verify_full_turn`/`verify_full_turn_bound`, `node/src/turn_proving.rs:246/414/532`) — so the graduated AIR gates the default path. BUT the bespoke `EffectVmAir` IS still live on the **sovereign-cell bespoke-STARK path**: `AgentCipherclerk::execute_sovereign_turn_with_proof` produces `stark::prove(&EffectVmAir,…)` bytes into `turn.execution_proof` (`sdk/src/cipherclerk.rs:5160-5166`, also `:6305`), and `TurnExecutor::verify_and_commit_proof` verifies them via `stark::verify(&EffectVmAir,…)` (`turn/src/executor/proof_verify.rs:420-421`), reached when `turn.execution_proof.is_some()` && cell is sovereign (`turn/src/executor/execute.rs:476`). The two species CANNOT silently cross — `stark::proof_from_bytes` requires a `b"DREG"` magic header and fails closed on the postcard p3 blob (`circuit/src/stark.rs`). **Reachability (severity calibration):** `execute_sovereign_turn_with_proof` is a `pub fn` SDK API (not cfg-gated) but its ONLY in-repo callers are `tests/src/sovereign_proof.rs:73/125`; NO service/binary (node/cli/discord-bot/demos/starbridge) drives it — so this is a LATENT public-API-surface gap exercised only by in-repo tests, NOT a shipped-node-flow hole. (The sibling `execute_with_program` `:6278/:6305` is the other bespoke `execution_proof` writer, same API-surface posture.) NET: on the sovereign bespoke path, an `AttenuateCapability` is checked only for the legacy digest-advance shape, NOT for in-circuit non-amplification (`granted ⊑ held` against the authenticated `cap_root`) — so a caller of that API gets the weaker cap guarantee. **Decision shapes:** (i) graduate the sovereign path onto the p3 AIR (cut `cipherclerk.execute_sovereign_turn_with_proof` over to `prove_effect_vm_p3` + `verify_effect_vm_p3`, retire the bespoke `EffectVmAir` cap arm) — the coherent close, lands the same non-amp guarantee everywhere; or (ii) declare the sovereign bespoke-STARK path deprecated/decommissioned (no live caller ships it) and delete it wholesale; or (iii) accept the weaker sovereign cap-binding as an explicit documented scope-limit. NOT deleted: deleting only the `air.rs:1365-1374` cap arm while the sovereign path still verifies through `EffectVmAir` would BREAK that path's cap-root binding (left intact pending this decision). CROSS-REF: the ROTATION FLIP tail above ALREADY plans to "rewrite executor `proof_verify.rs::verify_and_commit_proof` … bespoke `stark::verify` → the rotated Ir2BatchProof" and to DELETE `effect_vm_p3_full_air.rs` — so decision-shape (i)/(ii) has a natural landing AT the flip; the open question is whether the sovereign cap-binding gap is acceptable in the interim (it is live on the bespoke path TODAY, pre-flip) or wants an earlier targeted fix. Named: cap-crown #103 burn-down, 2026-06-13.
- **#103 cap-crown Phase-D — the 4-ary c-list `membership` leg vs. the sorted `cap-membership` leg (retire-or-keep).** `sdk/src/full_turn_proof.rs` attaches TWO distinct membership sub-proofs to a cap-gated turn, proving DIFFERENT claims: (a) the **4-ary c-list `membership` leg** (`:978-1012`, witness `MembershipWitness` `:177`, `prove_membership_p3` over the generic positions-indexed `P3MerklePoseidon2Air`, PI `[leaf_hash, root]`, vk `merkle_poseidon2_descriptor`) proves "an opaque capability `leaf_hash` is present in A Merkle tree at the witnessed positions" — a GENERIC membership statement; its root is not structurally pinned to the authenticated `cap_root`, and the leaf is an opaque hash (not the typed 7-field cap preimage). (b) the **sorted `cap-membership` leg** ("cap Phase D", `:1075-1100`, witness `CapMembershipWitness` `:212` ← `ConsumedCapWitness`, `prove_cap_membership_p3` over the SORTED `CanonicalCapTree`, directional path, vk `cap_membership_circuit_descriptor`, expectation `CapMembershipExpectation` `:239` pins `pi[CAP_ROOT]` to the trusted root `:248`) proves "the SPECIFIC CONSUMED capability's full 7-field leaf preimage opens against THE holder's real sorted `cap_root` tree" — the authority leg that ties the acting/consumed cap to the authenticated cap-state, with sorted single-leaf-per-slot semantics. **The two are not redundant:** the sorted leg gives the strictly stronger, structurally-pinned, typed-leaf guarantee; the 4-ary leg gives a weaker generic membership over an unpinned root with an opaque leaf. **Retire-vs-keep tradeoff:** for a cap-gated turn the sorted `cap-membership` leg SUBSUMES the authority claim the 4-ary leg makes (consumed-cap-in-the-real-cap_root ⊃ opaque-leaf-in-some-4-ary-tree), so the 4-ary leg is retireable FOR CAP-GATED TURNS on the claim alone. **Live-producer evidence (the deciding fact):** there is currently NO live producer that sets `membership: Some(MembershipWitness{..})` — the only two build sites (`full_turn_proof.rs:2303`, `:2774`) are both inside `#[cfg(test)] mod tests` (`:2107`) using `merkle_test_witness`; the only LIVE membership-leg producer is `cap_membership` (`node/src/turn_proving.rs:518`, `CapMembershipWitness::from_consumed`). So today the 4-ary `membership` leg is dead on the live path — its `Option`/`P3MerklePoseidon2Air`/`merkle_poseidon2_descriptor` plumbing is wired + SDK-tested but unfed. **The keep argument** is therefore forward-looking, not current: the 4-ary leg is the GENERIC credential/c-list membership primitive (opaque leaf, witnessed root, no sorted `cap_root` to open against) that a NON-cap predicate-credential turn-shape WOULD use — retiring it removes that future affordance and the `merkle_poseidon2` descriptor's only full-turn consumer. **Recommendation (ember to ratify):** keep the 4-ary leg as the general-membership primitive but DO NOT couple it to cap-gated turns (the sorted leg is the cap authority leg of record); OR, if no near-term non-cap credential turn-shape is planned, demote the 4-ary leg + its descriptor to a clearly-labelled "general membership, no live producer" status (Research tier) so it stops reading as a live cap-authority alternative. Before any removal, confirm no in-flight feature wires a live `membership: Some(..)`. Named: cap-crown #103 Phase-D map, 2026-06-13. (Left intact — characterization only, per the brief.)

## Research tier (explicitly not scheduled)

- Transcendental-syntax S3 (substructural recovery from the dregg side) + S5 (stella instantiation).
- UC-security / CryptHOL (#31) + research pillars (revocation/info-flow/metadata).
- Hypersystem/simplicial joint turns (dregg4 vision).
