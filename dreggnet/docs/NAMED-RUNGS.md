# NAMED-RUNGS — the accountable burn-down of every named-but-never-climbed rung

The discipline is *"named = a burn-down, never a parking lot."* But named
follow-ups accumulate across reports, `HORIZONLOG.md`, the memory topic files,
and the live transcript until they ARE a parking lot. This catalog surfaces
them all in one place so we can climb them.

**Sources gathered (2026-06-29):** `HORIZONLOG.md` (the standing-practice log,
6349 lines) · `~/dev/DreggNet/docs/*` (GO-REAL, COMPUTE-TIERS, RUN-LOCALLY,
DEVELOPERS, ORCHESTRATION-LOOP, MONITORING, WEB-HOSTING,
RED-TEAM-FINDINGS) · the memory topic files (`~/.claude/projects/.../memory/`) ·
the current session's lane outputs · `cv` transcript search.

**Status legend.** `OPEN` = genuinely uncimbed at HEAD. `DONE-SINCE` = named
earlier, climbed by later work (do not re-climb). `SUPERSEDED` = the rung was
dissolved/proven-unwarranted, not climbed. `OPEN?` = older-epoch named rung with
no clear closure signal — verify against HEAD before scheduling.

> Memories are dated/point-in-time. Where a row's status leans on a memory or a
> log entry rather than code at HEAD, treat it as a SHAPE and verify the STATE.

---

## The table

| # | Rung (what was named) | Source | Status | Domain | Value | Rough effort |
|---|---|---|---|---|---|---|
| 1 | **Gentian FLIP** — the in-AIR authority-digest→selector gadget is discharged, but the flip is blocked on the commit-target: limb 24 (`B_AUTHORITY_DIGEST`) holds the byte-domain `compute_authority_digest_felt`, not `hash_many(floor)`, so an honest escrow turn can't produce a light-client-accepted gentian proof. Sound fix = a NEW dedicated felt-domain floor-digest limb + new Lean absorption proof + retarget `gentianAuthDigestCol` off limb 24 (limbs 24..37 fully packed → width/layout flag-day). | HORIZONLOG OPEN-BURN-DOWN #1; `IN-AIR-AUTHORITY-DIGEST-GADGET.md` §7 | OPEN | circuit | High — makes escrow SATISFACTION light-client-witnessed, not just executor-enforced | Large (layout flag-day) |
| 2 | **Tags 18/19 welds** — range-check gadget (discharge due-ness) + multi-limb-product gadget (vault no-dilution; the product overflows BabyBear). Comes after #1. | HORIZONLOG OPEN-BURN-DOWN #2; VK-EPOCH-CONSTRAINT-BINDING §6 BLOCKER 2 | OPEN | circuit | High — completes the house-capacity circuit weld | Medium-large, gated on #1 |
| 3 | **Gentian escrow flip — precise remaining (3 steps):** (a) a PRODUCER emitting a satisfying rotated trace for the welded descriptor (field-override + GROUP-4/rotated commit-recompute surgery for the two leg field limbs) → full STARK prove/verify against the committed VK; (b) commit the welded VK + bind the selector to the committed declaration's required-tag floor IN-AIR (`DeclCommitBinds`); (c) the range-check + overflow-safe-product in-AIR gates (= #2), then the flip. | HORIZONLOG "PRECISE REMAINING to a flippable escrow weld"; lane outputs | OPEN | circuit | High — the deployed default is unchanged; SATISFACTION still not light-client-witnessed in production | Large |
| 4 | **node-image** — the Lean-on-Linux dregg-node build (a builder was being provisioned) → unblocks full staging end-to-end. | HORIZONLOG OPEN-BURN-DOWN #3; INFRA-STATE "staging seam" | OPEN | ops | High — gates the whole live-staging proof | Medium |
| 5 | **Solana mainnet-real** — geyser / custom-RPC validator plugin for real accounts-hash inclusion proofs (RPC exposes neither real bank hash nor Merkle inclusion → can't have real-vote-sig + real-inclusion both today). | HORIZONLOG OPEN-BURN-DOWN #4; `MONITORING.md` "the mainnet gap" | OPEN | bridge | Medium-high — the Solana bridge is trustless-complete only modulo this | Large |
| 6 | **Owned native/interpreter engine (Caged tier)** — the `native`/`python`/`node` langs are a fail-closed seam (`ExecError::NotWired`, label `dreggnet-native (seam)`) today; owning an in-crate engine for them is future work. Sub-rungs: an owned native-process engine with `instantiate_with_caps` cap/tenant-env override; per-language interpreter engines (python, node); runtime cap-mutation on respawn. | HORIZONLOG OPEN-BURN-DOWN #5; `COMPUTE-TIERS.md` | OPEN | compute | Medium — the Caged tier is a seam; the owned engine is the gap | Medium-large |
| 7 | **DreggNet real-dregg-lease wire** — `dregg-verify` feature needs the root arkworks `[patch]` (serde_with fork + vendored lockstitch); the verified decode is real, the **remaining step is the light-client RPC transport that fetches the receipt-log records**. Flip-on is a workspace-lock + AGPL-derivative-work step (deliberate, not default). | HORIZONLOG OPEN-BURN-DOWN #6a; `ORCHESTRATION-LOOP.md`, `GO-REAL.md` | OPEN | bridge/ops | High — the verified-read upgrade on the live loop | Medium |
| 8 | **DreggNet durable store unification** — durable per-request pg store + meter-ledger unification. | HORIZONLOG OPEN-BURN-DOWN #6b | OPEN | ops | Medium | Medium |
| 9 | **DreggNet federation multi-node** — needs the fleet. | HORIZONLOG OPEN-BURN-DOWN #6c | OPEN | ops/consensus | Medium-high — multi-provider is the network moat | Large (needs hardware) |
| 10 | **DreggNet private GitHub remote** — the `dev` branch has no remote; all commits local. | HORIZONLOG OPEN-BURN-DOWN #6d | OPEN | ops | Low-medium — backup/collab hygiene | Small |
| 11 | **Hackathon — Hermes Accelerated Business demo** (Nous/NVIDIA/Stripe), DUE TUE JUN 30. Demo ready (live-Stripe-trigger + on-camera crash-resume). | HORIZONLOG OPEN-BURN-DOWN #7 | OPEN (time-boxed) | demo/ops | High (deadline) | Small (polish) |
| 12 | **CommitBindsMMR Gap B** — weld `mroot` into the EPOCH commitment so a checkpoint *carries* the receipt-index root; today `/checkpoint/latest` doesn't expose the MMR-root field, so the anchor's `mmr_root` is established out-of-band (operator/TOFU). VK-affecting, rotation-epoch gated. When it lands, only the *provenance* of `mmr_root` changes (read it from the verified checkpoint). | `GO-REAL.md` §trusted-root; `COMMIT-BINDS-MMR.md` | OPEN | circuit/bridge | Medium-high — closes the trusted-root TOFU seam | Medium (rides the VK epoch) |
| 13 | **Live-edge operator step** — the full live e2e (verified lease → schedule → dispatch → meter → settle real Transfer → reap) is gated on: (1) unlock the node + export its bearer; (2) mint a real funded execution-lease grant via the lease factory. The edge node's log is currently empty. | `GO-REAL.md` "Live-edge proof status" | OPEN | ops | High — the actual money-moving live proof | Small-medium (operator action) |
| 14 | **firecracker-provider** — the named remaining production compute work: vsock+JSON guest-invocation wire, microVM kernel/rootfs image build, jailer (chroot + cgroup) for production hosts. Until the vsock wire lands, a booted VM surfaces a "guest plane not yet wired" error on `call`. | `COMPUTE-TIERS.md` | OPEN | compute | Medium — the production hardened-isolation tier | Large |
| 15 | **create→fulfill durable launch seam** — `create` admits the machine (`created`); the durable launch (`MachineGateway::fulfill`) is async, the `httpe` Handler is synchronous, so it's driven by a control loop, not the request path. | `DEVELOPERS.md`, `RUN-LOCALLY.md` "What is live vs deferred" | OPEN | ops | Medium | Medium |
| 16 | **`dregg.works` live deploy** — DNS + Caddy routing (design only; owned by the `deploy/` lane). | `WEB-HOSTING.md` | OPEN | ops | Medium — public web surface | Small-medium |
| 17 | **mainnet relayer wire** — the trustless geyser inclusion-proof path is verified in the bridge crate but not wired to a live mainnet relayer the dashboard reads; today's reachable path is devnet/oracle. (Overlaps #5.) | `MONITORING.md` | OPEN | bridge/ops | Medium | Medium |
| 18 | **workload args threading** — the durable `WorkloadSpec` does not yet carry args; threading them through to the owned sandbox is named. | `COMPUTE-TIERS.md` | OPEN | compute | Low-medium | Small |
| 19 | **metrics scrape wiring** — DIAGNOSED (2026-06-30): the scrape pipeline is CORRECT — Prometheus scrapes `dregg-node:8420/metrics` (target UP), 17 `dregg_*` families land when the node is healthy, and the Grafana dashboards reference the right metric names (verified no phantom-name bug). The recurring "No data" / Grafana confusion is NOT a scrape/dashboard misconfig: it is (a) the node's lazy/partial eager-registration — the deployed `n4` binary only pre-seeds the 4 security counters, while HEAD `node/src/metrics.rs` (`eade56d0c`, 06-29 09:11Z) also pre-seeds `dregg_block_height`/`dregg_turns_submitted_total`/`dregg_proofs_verified_total` so idle panels read `0` not "No data" → **rides the redeploy (#21)**; and (b) NO dashboard surfaces gossip at all — the gossip-storm had zero visibility (the node logs `Rejecting stream … per-peer limit` but emits no rejection counter; `dregg_gossip_messages_total` exists but is undashboarded + the deployed binary isn't emitting it). The standalone open work is a node-side gossip-rejection counter + a Protocol-dashboard gossip panel (node-code, redeploy/orchestration lane). | lane outputs (ops) | DIAGNOSED → redeploy + (node) gossip counter | ops | Low | Small |
| 20 | **persvati hardware config does not persist a reboot** — **DONE-SINCE (2026-06-30): persistence implemented + verified + version-controlled.** `/etc/modprobe.d/thinkpad_acpi.conf` (fan_control=1) + the enabled `persvati-thermal-config.service` oneshot (`/usr/local/sbin/persvati-thermal-config.sh`: fan level 3, boost 1, max_freq 3300000, governor powersave, EPP balance_power) ran cleanly on the last real boot and re-applies idempotently. Artifacts committed to `deploy/persvati-tuning/`; runbook (`runbooks/HARDWARE-PERSVATI.md`) updated with install + verify steps. | lane outputs (ops) | **DONE-SINCE** | ops | Low-medium — the box silently de-tunes on reboot | Small |
| 21 | **genesis-baseline recovery fix rollout** — **CONFIRMED STALE LIVE (2026-06-30).** The deployed edge `dregg-node:n4` image was built `2026-06-29T08:43:11Z`; it predates and is MISSING: the recovery fix `6aa2ddc2e` (2026-06-29 23:34, `recover_to_last_consistent` reseeds the genesis baseline on a sub-checkpoint power-cycle — supersedes the older `1a61dc16d`), the gossip-storm fix `923becc66` (2026-06-29 09:40, bound gossip streams + receiver backpressure), and the metrics eager-seed `eade56d0c` (2026-06-29 09:11). The gossip-storm fix's absence is OBSERVABLE LIVE: the edge node is currently wedged in a per-peer stream storm from snoopy (100.64.0.3) with `/status` timing out (ops PAGE `node_down`). Redeploy lane owns the rebake; do NOT restart the stale binary (its recovery path is the buggy one). | lane outputs (ops) | OPEN → redeploy lane | ops | Medium — durability/recovery safety; live incident | Small-medium (rebake images) |
| 22 | **Custom / `proofBind` in-AIR weld** — Lean half CLOSED (`CustomApex.lean`, axiom-clean, 2026-06-26: the apex covers Custom under the staged in-AIR verifier + `EngineBinding`/FRI carrier). Remaining = the deployed VK epoch ONLY: flip the deployed `holdsAt` proofBind gate `True→boundAt`, lift `custom_proof_commitment` 4→8 felt (~62→~124 bit), column re-pin (coordinate with the umem flip). | memory `project-circuit-soundness-apex.md`; `CUSTOM-VK-AUTHORIZATION.md` | OPEN (partial) | circuit | High — Custom program-correctness is otherwise enforced only out-of-circuit (a pure light client doesn't witness it) | Medium (rides VK epoch) |
| 23 | **umem VK epoch** — commit the wide-welded VK + flip the deployed default + flip `umem_witness_enabled` (verified still FALSE at `turn/src/executor/mod.rs:815`). 7th-refusal burn-down first: demonstrate ONE domain-2 (capability) welded mint + wire-verify + executor-commit with a *consistent* cap-root witness → resolve the `OodEvaluationMismatch` → sweep the 13 cap-root-shaped siblings → THEN flip. | memory `project-umem-as-primitive-epoch.md` | OPEN (deliberately gated) | circuit | High — universal-memory becomes consensus-load-bearing; the be-thoughtful zone | Large (the VK epoch) |
| 24 | **IVC #1 codex-named follow-ups (none critical):** online-accumulator port to the 4-lane digest (MEDIUM); widen the digest past 4 lanes for conservative 128-bit (LOW); doc-drift comments (LOW). | HORIZONLOG 2026-06-25; memory | OPEN (minor) | circuit | Low-medium | Small-medium |
| 25 | **settle_umem_stitch into production** — wire it into `ForkMembraneHost::stitch_pair` / the chat-lane path so the settlement gate runs live, not only in the demo (MEDIUM). Plus (LOW) `RestHashIffFrame`'s revoked conjunct realized at the wire (the #139 revocation-channel root absorbed into the finalized commitment). | HORIZONLOG 2026-06-25 SETTLEMENT-SOUND | OPEN | circuit/compute | Medium | Medium |
| 26 | **Rust executor agent-lifecycle admission gate** — the executor (`execute.rs`) has no agent-lifecycle admission gate, so it admits TERMINAL (Destroyed/Migrated) agents the verified spec now rejects via `cellLifecycleCanAuthor`. Mirror: reject `agent_cell.is_terminal()` at admission (both entries ~L382/L1436). | HORIZONLOG 2026-06-26 kernel-align | OPEN | compute/kernel | Medium — a narrow Rust under-enforcement | Small |
| 27 | **cap-open SDK exercise route** — `full_turn_proof.rs` `cap_open_route_for_run` arm is gated behind the shared non-TB cap-open prove-through plumbing landing (another session owns that dispatch). The exercise descriptor + Lean apex are closed; only the end-to-end prover lookup-balance is the residual. | HORIZONLOG ~L5879 | OPEN? | circuit/sdk | Low-medium | Medium |
| 28 | **pg-dregg tier-c test port** — port `tests/tier_c_real_proof.rs`'s internal `dregg_circuit::{ivc_turn_chain,joint_turn_aggregation}` paths onto the split `dregg-circuit-prove` crate (test is wholly `#[cfg(feature="tier-c")]`; does not block core). Plus: one-command PG18 bundle packaging + auto-load. | HORIZONLOG ~L5938 | OPEN? | ops/circuit | Low | Small |
| 29 | **constant-VK perpetual fixed-point** — a TRUE constant-VK perpetual aggregate (`aggregate(A,B)`'s preprocessed commitment is not yet a fixed point); host-only fix is provably impossible, needs unbuilt machinery. | HORIZONLOG ~L6091 | OPEN (research) | circuit | Low-medium (elegance/cost) | Large/research |
| 30 | **attenuate v3-registry "recompute descriptor" residual** — routing attenuate through the cap-reshape recompute descriptor. | memory `project-cap-reshape-plan.md`; HORIZONLOG 2026-06-25 | **SUPERSEDED** | circuit | — (routing to it would DOWNGRADE the deployed sorted-Merkle `map_op` write) | none |
| 31 | **RefreshDelegation census residual** — the kernel `delegate` parent-pointer never carried on the wire. | HORIZONLOG ~L5914 | **DONE-SINCE** | compute | — (closed: new 12th WState field `delegate` across the FFI seam) | none |
| 32 | **`∀ e, descriptorRefines` assembly** — the per-effect closure fan-out. | memory `project-circuit-soundness-apex.md` | **DONE-SINCE** (assembled `933443172`); residual is the terminal FRI/STARK + Poseidon2-CR + DeployedFaithful crypto floor — by-design, not a dregg open | circuit | — | terminal floor |

### Older-epoch named rungs (deos / consensus — pre-2026-06-28; verify vs HEAD, kept off the shortlist)

These were named in earlier epochs and lack a clean closure signal in the current
record. Most are deos-desktop or consensus-internal, not the live DreggNet/circuit
frontier. Verify against HEAD before scheduling; do not assume open.

- **web-deos PAINT** — the gpui_web fork's run-loop closure-reentrancy stops before first paint (`OPEN?`, deos, 2026-06-23).
- **chat-LIVE homeserver** — cockpit chat uses MockSource, not a live homeserver (`OPEN?`, deos).
- **Hermes live Bedrock path** — real but not yet wired to the input box (`OPEN?`, deos).
- **S5 consensus legs** — S5-2 live-commit refinement, S5-3 #170 quorum-consumer migration, S5-4 consensus leg of the composed apex, S5-5 equivocator Lean↔Rust differential pin, S5-6 finality-on-demand (`OPEN?`, consensus; `CONSENSUS-FLEX.md`).
- **DreggDL node `POST /deploy` ingress** — node endpoint for a DreggDL doc → static check → lower → submit (`OPEN?`, post-flip).
- **escrow-market follow-ups** — (a) settle-scoped no-burn in the executor-installed flat constraints; (b) real ledger-balance binding for ESCROWED/RELEASED/REFUNDED (`OPEN?`, post-flip).
- **adjudication bond via obligation factory** — `post_bond` should deploy via the obligation factory, not a plain operator cell (`OPEN?`; the factory pattern has since landed → likely unblocked).
- **live-capture node hooks** — a node trace-export mode emitting `BlocklaceCapture`/`ReceiptStrandCapture`/`WalCapture` (`OPEN?`, node-side).
- **federation_id surfacing** — surface `federation_id` on a configured federation (`OPEN?`, small).
- **Windows native-full one-command reproducibility** (`OPEN?`, ops, 2026-06-20).
- **N5 killer-demo deferred step-5** — the four-surface headline demo's final step (`OPEN?`, starbridge-v2).

---

## Climb-next shortlist (genuinely-OPEN, high-value)

Ordered by value × tractability. The VK-epoch cluster (1/2/3/12/22/23) is the
single biggest payoff but is the deliberately-gated, be-extremely-thoughtful zone
— it wants design care, not a trigger-pull.

1. **#13 Live-edge operator step + #4 node-image** (ops, small→medium). The
   cheapest path to a *real* money-moving end-to-end proof: bake the Lean-on-Linux
   node image, unlock the edge node, mint one funded lease. Highest value-per-effort
   on the board and unblocks the staging story. Pairs with **#7** (the verified-read
   RPC transport) for the trustless version.

2. **#11 Hackathon demo polish** (demo, small) — hard deadline TUE JUN 30; demo is
   ready, so this is finish-and-rehearse, not build.

3. **#23 umem VK epoch — the domain-2 burn-down** (circuit, medium-into-large).
   Not the flip itself; the *next untested layer*: demonstrate ONE capability-domain
   welded mint end-to-end with a consistent cap-root witness and resolve the
   `OodEvaluationMismatch`. This is the honest precursor that earns the flip, and the
   7-refusal history says it's where the real work is.

4. **#1 Gentian commit-target limb** (circuit, large) — the deep one: a dedicated
   felt-domain floor-digest limb + Lean absorption proof + retarget off limb 24. The
   keystone for light-client-witnessed escrow SATISFACTION. Worth a careful design
   pass even before building (the width/layout flag-day is shared with the umem epoch
   — sequence them together).

5. **#26 Rust executor agent-lifecycle admission gate** (compute, small) — a narrow,
   well-scoped under-enforcement with the spec already aligned; a clean small win that
   tightens the executor↔spec covenant. (Mind the named caution: don't touch untested
   Migrated-agent flows blindly.)

6. **#21 genesis-baseline recovery rollout** (ops, small-medium) — a durability-safety
   fix already committed in code (`1a61dc16d`); just needs every deployed node image to
   carry it. Low effort, real safety value.

7. **#22 Custom/proofBind VK weld** (circuit, medium) — the Lean half is closed; the
   remaining deployed-VK-epoch work (gate flip + 4→8-felt commitment lift) rides the
   same VK epoch as #23/#12, so batch them. Until then, Custom program-correctness is
   enforced only out-of-circuit — a real light-client gap worth closing.

**Batch the VK-epoch flag-day.** Rungs 1, 2, 3, 12, 22, and 23 all want the same
rotation/VK epoch and several share the limb-layout flag-day. They should be
designed and flipped together, once, deliberately — not piecemeal. That single
coordinated epoch is the largest accountable item on this board.

**SUPERSEDED / DONE-SINCE (do not re-climb):** #30 (attenuate recompute — routing
to it would downgrade), #31 (RefreshDelegation — closed via the 12th WState field),
#32 (`∀ e, descriptorRefines` — assembled; residual is the terminal crypto floor).
</content>
</invoke>
