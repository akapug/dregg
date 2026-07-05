# LIVE-BYZANTINE — adversarial audit of the deployed distributed protocol

Attacks the **live** consensus/federation a Byzantine node runs (the layer the
N3 testnet exercised) — NOT an idealized model. The single-turn soundness proof
(`CircuitSoundness.lean::lightclient_unfoolable`) and the whole-history fold
(`lightclient::verify_history`) do not cover this: they attest ONE turn / ONE
folded chain, but say nothing about whether a Byzantine committee member can
split finality, wedge liveness, or serve a state a light client would accept.

Scope read: `blocklace/src/{finality,ordering,evidence}.rs`,
`node/src/{finalization_votes,finality_gate,prove_pool,blocklace_sync,state}.rs`,
`persist/src/federation.rs`, `lightclient/src/lib.rs`.

Verdict key: **CLOSED-by-X** (a deployed gate closes it) · **LIVE-GAP** (a real
hole with a forge) · **RESIDUAL** (a named honest floor, not a bug).

---

## Attack 1 — EQUIVOCATION (double-sign two conflicting heads) — CLOSED

**Question.** Can a Byzantine committee member sign two conflicting blocks/turns
at the same height/slot and split finality into two committee-ratified heads —
two valid quorum certs for conflicting states?

**Verdict: CLOSED**, at two independent layers.

1. **Ordering excludes the equivocating leader.**
   `blocklace/src/ordering.rs::find_all_final_leaders` (line 386) finalizes a
   wave leader ONLY when `leader_blocks.len() == 1` — a leader that produced two
   blocks at the wave-start round is *skipped entirely* (no finalization that
   wave). A non-leader equivocator is excluded from every leader's coverage by
   `has_equivocation_in_past` (`ordering.rs:160`, consumed at `tau` line 547).
   So a double-signer's blocks are never ordered.

2. **Quorum intersection forbids two super-ratifications.** Super-ratification
   (`is_super_ratified`, `ordering.rs:305`) needs `supermajority_threshold(n) =
   ⌊2n/3⌋+1` distinct participants ratifying at the wave-end round. Two such
   quorums intersect in strictly more than the Byzantine budget `f=⌊(n-1)/3⌋`
   for **every** n (proven: `ordering.rs::test_supermajority_quorum_intersection_unconditional`,
   line 1048). The `2f+1` honest participants cannot form two disjoint
   supermajorities, so at most one of two conflicting blocks can be
   super-ratified. No two ratified heads.

3. **Detection + eviction is deployed.** `Blocklace::detect_equivocation`
   (`finality.rs:835`) implements the paper's content-independent Def 4.2
   (incomparable same-creator pair — catches forks at *different* seq too), runs
   on BOTH the live `receive_block` (line 647) and `merge` (line 720) paths and
   on the untrusted-checkpoint recovery path (`from_checkpoint`, line 1193). The
   equivocator's tip is withdrawn and the creator marked; evidence is retained
   as a lace-free-certifiable wire value (`evidence.rs::EvidenceOfEquivocation`,
   two Ed25519 checks + three equalities).

**Existing teeth.** `blocklace/tests/consensus_fault_sim.rs::
byzantine_equivocation_excluded_safety_and_liveness_held` delivers the two forks
in OPPOSITE orders to different honest nodes (the split-brain attempt) and
asserts order-independent detection + identical finalization + exclusion.

**New tooth (this audit).** `blocklace/tests/byzantine_finality_split.rs::
equivocating_leader_cannot_super_ratify_two_heads` builds the concrete
two-conflicting-leader-blocks DAG and asserts `tau` finalizes NEITHER head — the
direct refutation of "two quorum certs for conflicting states."

**Residual (named).** The FINALITY-VOTE layer (`finalization_votes.rs`) keys
votes by `block_id`, so a Byzantine member CAN emit a valid vote for each of two
conflicting block-ids. This does not split finality because (a) honest nodes
only vote for a block their local `tau` finalized (gated at
`blocklace_sync.rs:3674` on `has_voted`), and by (1)+(2) at most one conflicting
block is ever `Ordered` in an honest view; and (b) the vote is a distinct-signer
count toward *order* agreement, never a state cert (see Attack 5). The equivocator
gains nothing but its own eviction.

---

## Attack 2 — WITHHOLDING / CENSORSHIP — CLOSED (graceful) + liveness RESIDUAL

**Question.** Can a Byzantine node withhold a turn/block worse than fail-stop —
a withholding pattern that wedges finality where a crash would not?

**Verdict: CLOSED for safety; liveness degrades gracefully.**

- Finalization needs a supermajority of *cordial* wave-end blocks
  (`ordering.rs::is_cordial`, line 569, `> 2n/3` predecessors from the prior
  round). A withholder contributes ≤ f; the `2f+1` honest supermajority still
  super-ratifies. Withholding to a subset only *delays* (the block reaches the
  supermajority via CRDT union-merge gossip; `tau` is monotone —
  `ordering.rs::test_monotonicity`), it never forks (the same quorum-intersection
  as Attack 1).
- A withholding LEADER is *strictly weaker* than a crashed one: if it reveals its
  leader block to nobody, the wave is skipped exactly as for a dead leader; if it
  reveals to some, either the block reaches a supermajority (all converge and
  finalize it) or it does not (no one super-ratifies). There is no "reveal to
  exactly a sub-quorum" pattern that finalizes for one honest node but not
  another — super-ratification is evaluated against each observer's own causal
  past and requires a supermajority, which is a single set the honest majority
  cannot be split across.

**Existing teeth.** `consensus_fault_sim.rs::{n4_survives_f_kills_and_stalls_at_f_plus_one,
n7_survives_two_kills_and_stalls_at_three}` — f fail-stops tolerated, f+1 STALLS
(safe, never forks). The N3 partition drill confirmed finality freezes correctly
with 1 node down.

**Residual (named, TERMINAL).** Sustained targeted withholding by ≤ f nodes is a
*liveness* degradation (slower finality), never a safety one — the standard BFT
liveness-under-partial-synchrony floor. Not a bug.

---

## Attack 3 — COMMITTEE-RESTART blast radius — LIVE-GAP (liveness DoS), safety intact

**Question.** The N3 run found committee nodes FAIL-CLOSED on restart (persisted
attested root carries 1 sig vs threshold 3). Is the fail-closed genuinely SAFE,
or can an adversary FORCE restarts to wedge the committee permanently (a liveness
DoS)?

**Verdict: SAFE-but-DoS-able — a LIVE liveness gap; safety is correct.**

The mechanics, grounded:

- The recovery anchor `state.rs::verify_signed_anchor_and_rollback` (line 1221)
  calls `StoredAttestedRoot::verify_signatures` (`persist/src/federation.rs:84`),
  which requires `quorum_signatures.len() >= threshold` valid committee
  signatures over the root's `signing_message()`. A same-epoch root with a
  sub-quorum count hits the `else` at line 1283 → **refuses to start**.
- The producer under-feeds it: `blocklace_sync.rs:4589` pushes ONLY the local
  node's signature (`1 < threshold` in full mode). The detailed honest diagnosis
  is inline at `blocklace_sync.rs:4552-4588`.

**Safety: CORRECT.** The node never serves a finalization it cannot anchor to a
committee quorum. `verify_signatures` also binds the *state root* (three sigs
over a DIFFERENT `merkle_root` are refused — `persist/src/tests.rs:182`), and the
NODE-2 anti-rollback floor (`state.rs:1308`) refuses a recovered head below a
witnessed finalized height (no nullifier resurrection). This is correct hardening.

**⚠ Fix B is HALF-LANDED at HEAD (a parallel lane is welding it live).** As of
this audit the `StoredAttestedRoot::finalization_quorum` field +
`verify_finalization_quorum` (`persist/src/federation.rs:74,144`) exist, and the
deployed `FinalizationVote` was upgraded to v2 to bind the state root —
`dregg_types::finalization_vote_signing_message = dregg-finalization-vote-v2 ||
block_id || merkle_root` (`types/src/lib.rs:412`; `node/src/finalization_votes.rs`
now carries a `merkle_root` field). So the *cryptographic* binding exists. What is
NOT yet wired: (i) the commit-path producer does not back-fill `finalization_quorum`
into the persisted root (no `finalization_quorum` write in `blocklace_sync.rs`), and
(ii) the restart anchor `verify_signed_anchor_and_rollback` does not yet call
`verify_finalization_quorum` (no reference in `state.rs`). Until both land, a
full-mode committee node STILL fail-closes on restart — the gap remains LIVE, now
with a clearly half-built fix.

**Liveness: BROKEN, and adversarially amplifiable.** Any full-mode committee node
that finalized ≥1 height and then restarts — crash, deploy, OOM, power — cannot
rejoin: no adversary is even required for the failure, and an adversary who can
*induce* restarts (a crash bug, resource pressure; note F-DOS-1's inline-prover
wedge, now fixed by `prove_pool.rs`, was exactly such a lever) can knock out
committee members one by one. Once more than `n - supermajority_threshold(n)`
nodes are down-and-refusing, the committee loses quorum **permanently** (nothing
re-admits a fail-closed node). Fail-closed here converts a transient restart into
a permanent exit.

**Also named — a fail-OPEN sibling.** If `committee` is empty at boot
(`state.rs:1232`) the signed anchor is SKIPPED (best-effort HWM only). A boot
path that loses its committee keys (config corruption) downgrades to the
tamperable-redb backstop. Trusted-boot assumption; named residual.

**Fix direction (Fix B, from the inline diagnosis).** A DETERMINISTIC attested
root (drop the wall-clock `timestamp` from the signed preimage) + a signed-gossip
exchange of committee signatures over the root, aggregated to ≥threshold and
persisted once the quorum assembles — OR extend `FinalizationVote` to bind the
finalized `merkle_root` and retain those sigs. Both also close Attack 5's state
gap. Pinned by `persist/src/tests.rs::
full_mode_single_sig_root_is_refused_genuine_quorum_accepted`.

---

## Attack 4 — PARTITION EDGES beyond the drill — CLOSED for order; state = Attack 5

**Question.** Asymmetric partitions, a heal with divergent committed prefixes, a
minority that thinks it finalized. Can a healed partition produce two histories
that BOTH verify (a partition analog of the closed prefix-hiding)?

**Verdict: CLOSED at the ordering + light-client-cert layer.**

- A minority partition below `supermajority_threshold` finalizes NOTHING new
  (`consensus_fault_sim.rs::partition_heals_without_conflicting_finalization`): it
  cannot super-ratify, so it never "thinks it finalized." The majority finalizes
  a longer prefix; on heal, CRDT union-merge converges all nodes to the identical
  `tau` order, and the pre-heal majority prefix survives (monotonicity). No two
  finalized histories.
- For a light client that never saw the lace, the FORK analog is closed by the
  **committee-anchored** finality cert: `lightclient::FinalityCert::
  has_committee_quorum` (lib.rs:427) counts a ratifying signature ONLY if the
  signer is in the client's TRUSTED committee AND the Ed25519 signature verifies
  over `(finalized_root, participant_count)`. An equivocating prover that folds a
  valid aggregate over a fork and mints fresh keypairs cannot raise the count
  (its keys aren't in the committee — `NoQuorum`, lib.rs:471). The genesis anchor
  closes the dual prefix-hiding (`GenesisMismatch`, lib.rs:461).

**Residual → Attack 5.** The committee-anchored cert is SOUND and verified, but
it binds the *state root* — and **no deployed node produces it** (only the demo
binary `lightclient/src/bin/whole_history_demo.rs` does). The deployed cross-node
quorum (`FinalizationVote`) binds `block_id` (order), not the root. So Attack 4
is closed for ORDER (re-executing validators converge deterministically) and for
a light client *if it is handed a state-root cert* — but the deployed path does
not hand it one. See Attack 5.

---

## Attack 5 — EXECUTOR as the soundness boundary + the async prove window — RESIDUAL (the headline find)

**Question.** `execute_via_producer` commits state BEFORE the async prove pool
attests. Can a Byzantine node commit an INVALID turn (that the async prove would
reject) and serve it before the proof catches up — a window where committed state
and provable state diverge on a Byzantine node, visible to a light client?

**Two distinct sub-questions; two distinct verdicts.**

### 5a — the async-prove window, for a re-executing validator: CLOSED

`prove_pool.rs` (module docs, lines 18-25) makes the design explicit: the
executor is the soundness boundary; the STARK proof is *additive attestation*,
generated off the commit path. In `execute_finalized_turn` the state overlay is
installed ONLY from the pre→post `Cell` diff of a `TurnResult::Committed`
execution (`blocklace_sync.rs:4034` diff, gated by the `Committed` match arm at
line 4080). A `TurnResult::Rejected` execution mutates nothing on the cloned
`exec_ledger`, so `touched_ids` is empty and no state change is installed — an
invalid turn simply does not commit. Every honest node re-executes the
BFT-ordered turn deterministically (via the same `execute_via_producer` / verified
Lean producer) and reaches the identical `Committed`/`Rejected` verdict and the
identical `canonical_ledger_root`. A Byzantine node that force-commits a divergent
state cannot make honest nodes agree with it — they re-execute and diverge. So
for the re-executing validator population, the async-prove window is a *liveness*
property of the attestation layer (a dropped proof self-heals; `prove_pool.rs:48`),
never a safety hole.

### 5b — the LIGHT-CLIENT state binding: RESIDUAL (the real gap; Fix B in flight)

A light client does NOT re-execute — that is the whole point. It must rely on a
certificate. Here the deployed path leaves a genuine hole (with a fix landing):

- **Order was BFT-certified; state binding is landing.** The cross-node committee
  artifact the live node assembles is the `FinalizationVote` quorum. At the time
  the gap was first opened it signed `block_id || level` only (order). A parallel
  lane has since upgraded it to **v2**, binding the state root:
  `finalization_vote_signing_message = dregg-finalization-vote-v2 || block_id ||
  merkle_root` (`types/src/lib.rs:412`, `node/src/finalization_votes.rs`). So the
  vote NOW binds state — but see the wiring caveat below.
- **The state attestation carries no committee quorum yet.** The per-node
  `StoredAttestedRoot` binds the `merkle_root` but in full mode carries ONLY the
  producing node's single signature (`blocklace_sync.rs:4589`; diagnosis
  4552-4588). There is no code path that aggregates ≥threshold committee
  signatures over a `merkle_root`.
- **The certificate a light client needs exists but is unfed.**
  `lightclient::FinalityCert` (signatures over `finalized_root`, lib.rs:278/427)
  is the sound, committee-anchored state cert — but it is produced ONLY in the
  DEMO binary. No deployed node emits one.
- **The served surface is count-only.** `GET /api/federation/roots`
  (`api.rs:4901`) returns `merkle_root` + `signatures: quorum_signatures.len()`
  with NO committee verification. A light client trusting this sees a `merkle_root`
  backed by a bare count — a single Byzantine node can present any forged root
  with `signatures: 1` (or a self-threshold-1 federation with a self-`verify`-valid
  root), and there is no committee cert to arbitrate two conflicting equal-height
  roots.

**Consequence.** Until the `finalization_quorum` back-fill lands, a Byzantine node
can serve a light client a `merkle_root` the committee never collectively
certified in the SERVED artifact. This is NOT a consensus-*order* break
(Attacks 1/4 hold) and NOT a break against re-executing validators (5a). It is a
**missing state-finality certificate on the deployed light-client path** — the
same shape as the DreggNet "DEAD lightclient path" note. The single-turn and
whole-history proofs assume they are HANDED a committee-finalized `final_root`;
the deployed node does not yet assemble that binding into what it serves. The v2
vote (state-bound) + `verify_finalization_quorum` are the two pieces already in
place; the producer back-fill + a served committee cert are the remainder.

**New tooth (this audit).** `persist/tests/byzantine_state_attestation.rs::
byzantine_conflicting_state_roots_both_pass_count_only_gate` forges two
`StoredAttestedRoot`s with the SAME `blocklace_block_id` + height but CONFLICTING
`merkle_root`, each self-signed, and asserts (a) BOTH satisfy the count-only
`is_structurally_complete()` gate the API surfaces, and (b) NEITHER satisfies a
genuine ≥threshold committee `verify_signatures` — proving the deployed
state-attestation has no BFT binding a light client can use, and that the closing
gate is exactly the committee quorum the producer fails to assemble.

**Fix direction.** Identical to Attack 3's Fix B — a deterministic, committee-quorum-
signed state root (or a `merkle_root`-binding `FinalizationVote`), fed to the
already-sound `FinalityCert::has_committee_quorum`. Closing 3 and 5b is ONE weld.

---

## Summary

| # | Attack | Verdict | Closing gate / gap |
|---|--------|---------|--------------------|
| 1 | Equivocation | **CLOSED** | single-leader-per-wave + unconditional quorum intersection (`ordering.rs:386,236`) + detect/evict (`finality.rs:835`) |
| 2 | Withholding | **CLOSED** (+liveness residual) | supermajority cordiality; withholding ≤ fail-stop (`ordering.rs:569`) |
| 3 | Committee restart | **LIVE-GAP** (liveness DoS; safe) | anchor correct (`state.rs:1258`), producer under-feeds 1 sig (`blocklace_sync.rs:4589`) |
| 4 | Partition edges | **CLOSED** (order + LC cert) | minority can't super-ratify; committee-anchored cert (`lightclient:427`) |
| 5 | Executor / async prove | **5a CLOSED / 5b RESIDUAL** | re-exec deterministic (`prove_pool.rs:18`); state root has no deployed committee cert (`finalization_votes` binds block_id, `FinalityCert` unfed) |

**Highest-value find:** Attacks 3 and 5b are the SAME missing weld — the deployed
committee certifies ORDER (`block_id`) but never STATE (`merkle_root`). Order-safety
is genuinely BFT (a confirmed-safe consensus, itself valuable); the honest gap is a
state-finality certificate for the non-re-executing light client, and its absence
also fail-closes committee restarts. One deterministic-root + committee-signature
weld closes both. No consensus-ORDER Byzantine break was found.
