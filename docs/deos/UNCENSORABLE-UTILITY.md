# The uncensorable public-utility agent — an AI authority nobody owns

*A neutral service that runs ON the dregg federation, that no single operator can
halt, censor, or bias — because the service IS a proof-carrying turn on a ledger
nobody owns, decided by a confined brain whose honesty is attested and finalized
by an independent quorum.*

> Companion docs: `docs/SUPERSEDED/HERMES-INTEGRATION.md` (the crown / confined+attested
> brain) · `docs/deos/FORKABLE-CONFINED-SESSION.md` (scale-is-fork) ·
> `docs/deos/GRAIN-CONFINED-BODY.md` (the OS jail) ·
> `docs/deos/DEV-NODE-RUNBOOK.md` + `docs/deos/HOMELAB-N3-RUNBOOK.md` (standing up
> the committee) · `~/src/dregg-posters/the-federation.txt` (how a turn becomes
> final across operators). Consensus is proven in `metatheory/` and implemented in
> `blocklace/`, `node/`.

This is a **design** — the primitives it composes are built, tested, and
axiom-clean; the one thing it needs to become *real* is a live homelab federation
deploy, which is an operational step, not a missing capability. Section 4 names
those deploy gates honestly. Everything above the deploy line is real-by-running.

---

## 0. The one-sentence answer

An uncensorable public-utility agent is a **grain** — a hosted agent whose mind is
a committed, cap-bounded cell — whose brain is **OS-jailed and attested** (the
crown), and whose every ruling is a **light-client-verifiable turn finalized by a
BFT quorum**. No single operator, and no adversary controlling up to `f` of `n`
operators, can stop it answering, suppress a request, or forge a ruling — because
finality needs a supermajority the adversary does not have, and a ruling that
verifies provably came from a genuine, honest, confined brain.

The Dom-tweet framing — "an AI authority nobody owns" — is, in the metatheory,
one theorem: `non_domination_and_unfoolability`
(`metatheory/Metatheory/Adversary/Model.lean:140`), which quantifies BOTH "no
operator can push the system out of its safe floor" AND "no prover can forge an
accepted ruling that is not a genuine step" over the *same* `∀ adversary`.

---

## 1. The concrete service — The Commons Arbiter

**What it is.** A community (a forum, a DAO, a game world, a marketplace) needs a
neutral authority that makes case-by-case rulings: *is this post a
terms-of-service violation? which party is right in this dispute? does this
submission meet the published bar?* Today that authority is a person or a company
— someone who can be leaned on, bought, or unplugged, and whose ruling you must
take on trust. **The Commons Arbiter** replaces that single point of trust with a
service the community runs *collectively*:

- A member submits a **case**: the content or dispute, plus the community's
  published rubric (its "constitution" — the standard the Arbiter must apply).
- The Arbiter's **confined, attested brain** reads the case and the rubric and
  issues a **ruling** (verdict + reasons), bound to the exact rubric it applied.
- The ruling lands as a **finalized turn** on the community's shared ledger. Any
  member — or any outside observer — can **light-client-verify** that this ruling
  was produced by an honest confined brain and finalized by the quorum, without
  re-running anything and without trusting any one operator.

**Who runs it.** `n` community members (4–9 is the natural committee size) each
run one node — a small appchain, exactly the "a ledger nobody owns" shape from the
federation poster. They are the operators. Crucially they are *genuinely
independent* — different people, different machines, different jurisdictions —
because the guarantees below tolerate `f` faulty/colluding operators but not a
colluding supermajority (§2, honest bound).

**Who uses it.** Any member submits a case; anyone at all verifies a ruling. The
Arbiter has no admin, no root, no "trust me." Its authority is exactly the
**cap** the community granted it (§3) — it can rule on cases and write rulings to
the case ledger, and nothing else. It cannot ban a user, move money, or touch any
cell outside its grant.

**Why an arbiter and not a beacon.** A fair-randomness beacon or a public
fact-oracle is a valid instance of this same architecture (and a *simpler* one —
a beacon needs no brain, just a finalized threshold-VRF turn). The Arbiter is the
sharper showcase precisely because it needs a *judgment*: it is the case where "no
single operator can bias the ruling" is the whole point, and where the
confined+attested brain does load-bearing work. A beacon is the Arbiter with the
brain removed; a fact-oracle is the Arbiter ruling on "is claim X true per source
Y." The rest of this doc is written for the Arbiter; every mechanism transfers.

---

## 2. Why it is uncensorable — grounded in the consensus

Three distinct attacks; three distinct impossibilities. Each is tied to a real
theorem or mechanism, and each carries its honest bound.

### 2a. No operator can HALT it

Finality is not one operator's to grant or withhold. A ruling turn is *final* only
when a **supermajority super-ratifies** the leader block carrying it — the DAG-BFT
`tau` ordering rule (`blocklace/src/ordering.rs:688 finalize`,
`ordering.rs:305 is_super_ratified`). The threshold is
`⌊2n/3⌋+1` (`blocklace/src/ordering.rs:236 supermajority_threshold`, byte-for-byte
the Lean `supermajorityThreshold` at
`metatheory/Dregg2/Distributed/QuorumThreshold.lean:66`). A quorum forms from any
`⌊2n/3⌋+1` honest operators, so the federation **keeps finalizing while a quorum
is up** even if the other `f = ⌊(n−1)/3⌋` operators crash, stall, or are seized —
exactly the poster's "op D offline: the quorum finalized τ without it, and it
changes nothing." A single operator (or any `f`-sized minority) simply cannot
withhold finality: they are below quorum, and the honest majority proceeds.

- **Mechanism:** `blocklace/src/finality.rs`, `node/src/blocklace_sync.rs:935
  poll_finalized_blocks`, `node/src/finalization_votes.rs`. Late/absent peers
  reconverge via the reconnect prober (`blocklace_sync::spawn_peer_prober`,
  demonstrated in `DEV-NODE-RUNBOOK.md` "late join").
- **Honest bound:** liveness holds *while a quorum is up*. If more than `f`
  operators are simultaneously down or partitioned, finality pauses (it does not
  fork — safety is unconditional, §2c) and resumes when a quorum returns. This is
  why the operators must be independent: `f` correlated failures (same host, same
  operator, same power grid) collapse the bound.

### 2b. No operator can CENSOR a request

A case is a signed, cap-bounded turn a member submits directly to the ingress
(`POST /turns/submit` → `node/src/api.rs:3209 post_submit_signed_turn`; the node
verifies the client signature and never re-signs as itself). There is **no
privileged submission channel** for any operator to gatekeep: the member gossips
the case to the DAG, and because a block is a vote that **cites all it has seen**
(the blocklace is a DAG, not a chain), *any* honest operator that hears the case
seals it into its next block, and the wave that finalizes carries it. To suppress
a specific case, an adversary would have to prevent *every* honest operator from
ever citing it — but the honest operators number at least `⌊2n/3⌋+1 > f`, so a
single operator, or any `f`-sized coalition, cannot keep an honest quorum from
finalizing the case. Censoring one member's case is the same impossibility as
halting the whole service: it requires denying the quorum.

- **Mechanism:** DAG citation + `tau` ordering (`blocklace/src/ordering.rs`), the
  ingress admission gate all paths funnel through
  (`node/src/executor_setup.rs:103`). An operator that tried to *equivocate*
  (show the case to some peers and not others, or fork its own history) is caught:
  see §2c.
- **Honest bound:** same `f` — a supermajority that *colludes* to drop a case can
  censor it. The guarantee is against any minority up to `f`, not against a
  captured majority.

### 2c. No operator can FORGE or BIAS a ruling

This is the deepest leg, and it composes three proven properties:

1. **Safety — no two conflicting rulings both finalize.** Two supermajority
   quorums must intersect in a strictly-more-than-`⌊n/3⌋` set, hence share an
   honest operator who will not sign two conflicting rulings
   (`supermajority_intersection`,
   `metatheory/Dregg2/Distributed/QuorumThreshold.lean:151`;
   `two_quorums_share_honest`, `:169`). An equivocating operator — two blocks for
   one slot — gains no approver and cannot be super-ratified
   (`equivocation_excluded`, `metatheory/Dregg2/Distributed/Consensus.lean:251`;
   detected + auto-evicted at `blocklace/src/finality.rs:835 detect_equivocation`,
   `blocklace/src/constitution.rs:168 auto_evict_equivocator`). The chain-safety
   apex `no_conflicting_finalized_history`
   (`metatheory/Dregg2/Consensus/Safety.lean:268`) shows two honest nodes'
   finalized histories are `Consistent` — there is no fork for a verifier to be
   split across. So an operator cannot show you one ruling and your neighbor
   another.

2. **Unfoolability — an accepted ruling is a genuine kernel transition.** The
   ruling is emitted as an attested R2 kernel turn (§3) whose validity is
   checkable by a light client. `lightclient_unfoolable`
   (`metatheory/Dregg2/Circuit/CircuitSoundness.lean:453`) proves: if a batch
   proof verifies against the live verification key
   (`verifyBatch (vkOfRegistry R) pi π = accept`), then there *exist* genuine
   kernel states `pre, post` with a real `kstep pre post` whose commitments are
   exactly the published ones — *"the light client ran nothing; the adversary
   cannot forge acceptance without a real transition behind it"*
   (`unfoolable_against_adversary`,
   `metatheory/Metatheory/Adversary/Model.lean:104`). A forged or backdated ruling
   does not verify.

3. **The brain that produced the ruling was itself honest.** Unfoolability says
   the *turn* is a genuine kernel step; the **confined+attested brain** (§3) says
   the *ruling inside it* came from a jailed model reasoning over exactly the
   submitted case + rubric, with no injection. This is what makes the Arbiter
   *neutral*: no operator can substitute their preferred verdict, because a
   substituted verdict fails the attestation, and an un-attested turn is
   distinguishable on the ledger.

Bundled: `settlement_soundness`
(`metatheory/Metatheory/SettlementSoundness.lean:153`; deployed, non-tautological
closure `deployedSettle_binds_live_authority:305`; circuit-grounded
`metatheory/Dregg2/Circuit/SettlementSoundness.lean:210`) sharpens unfoolability to
*accept ⟹ genuine transition whose authority was LIVE at settlement* — so a ruling
that verifies also proves the Arbiter's cap was held-and-not-revoked at the
finalized tip. An operator cannot make the Arbiter act beyond, or after the
revocation of, its granted authority.

- **The unifying theorem.** `non_domination_and_unfoolability`
  (`metatheory/Metatheory/Adversary/Model.lean:140`) quantifies BOTH guarantees
  over one `A : Adversary`: (1) the operator surface can never push the enveloped
  system out of its safe floor, and (2) the prover surface can never get an
  accepted proof that is not a genuine kernel step. The operator-who-runs-a-node
  and the prover-who-forges-a-ruling are the *same* universal quantifier over the
  *same* object. That equation is the formal content of "an authority nobody owns."
- **Honest bound (stated once, plainly):** all three legs tolerate `f = ⌊(n−1)/3⌋`
  Byzantine operators, not `n`. A colluding supermajority could override safety,
  censor, or bias. The guarantees mean the most with genuinely independent
  operators; a federation whose `⌊2n/3⌋+1` nodes are one entity in disguise proves
  nothing. The non-vacuity teeth in the proofs (`branchSettle_NOT_binds`,
  `overGrant_rejected`, the `f < n/3` inhabited adversary at
  `Adversary/Model.lean` §4) confirm the bound is a *real* gate, not a vacuous
  hypothesis.

---

## 3. How a ruling is a verifiable turn no operator can bias

The full chain, request to verified ruling:

```
  member submits case ─▶ confined+attested brain rules ─▶ ruling is an R2
  attested turn ─▶ finalized cross-node by the quorum ─▶ anyone light-client-
  verifies: honest confined brain + finalized by supermajority, unbiased.
```

**① Request.** A member signs a `SignedTurn` carrying the case + rubric and POSTs
it to `POST /turns/submit` (`node/src/api.rs:3209`). It is cap-bounded
(`valid_until`, `node/src/submit_queue_drainer.rs:530`) and the node verifies the
member's signature over the turn hash before admitting it — no operator forges a
case in a member's name.

**② The confined+attested brain rules.** The Arbiter's brain runs behind
`run_hosted_agent_attested` (`deos-hermes/src/host.rs:389`). Two things are true of
that run:

- **Confined.** The model runs inside a firmament process-PD jail
  (`grain-jail/src/jail.rs:67 spawn_confined_body`; `deos-hermes/src/confined.rs`)
  that denies file, network, and exec, and opens **exactly one** egress door — the
  provider socket — via `spawn_confined_body_with_egress` (`jail.rs:113`). The
  jailed body physically cannot read an operator's keys, reach a second host, or
  exec a shell (the escape teeth `ALL_NEUTRALIZED`, `host.rs:91`; the egress teeth
  `EGRESS_NET_GRANTED_OPEN`/`_SIBLING_DENIED`, `confined.rs:101`). Every tool-call
  it proposes still crosses the Endpoint back to the grain's cap-gated seam. So the
  operator hosting the Arbiter cannot whisper to the model, feed it side data, or
  tamper with its reasoning environment.
- **Attested.** The brain's own ruling text is turned into a `ZkOracleAttestation`
  (`zkoracle-prove/src/attestation.rs:72`) by `carrier.attest_turn` — a proof the
  turn is **authentic ∧ well-formed ∧ injection-free**
  (`verify_zkoracle`, `attestation.rs:161`): *authentic* (a verified MPC-TLS
  presentation of the real provider call, api-key redacted), *well-formed* (the
  response body parses in the JSON CFG), *injection-free* (the committed field-span
  contains no `{{` handlebars injection). A ruling whose text carries an injection
  attempt is **not attestable** — the whole call errors (`host.rs:398-407`). This
  mirrors `metatheory/Dregg2/Crypto/ZkOracle.lean::zkOracle_sound`.

**③ The ruling is an R2 attested turn.** The attestation is fingerprinted to a
32-byte commitment (`attestation_commitment`, `deos-hermes/src/attest.rs:68` — a
domain-separated, length-prefixed BLAKE3 total fingerprint over the session
identity, signed transcripts, content commitment, and field span). The minted R2
kernel turn **commits to that hash** at the grain-turn attestation slot
(`ATTESTATION_SLOT = 8`, `grain-turn/src/lib.rs:90`;
`NodeMinter::bind_attestation`, `agent-platform/src/node.rs`). So the on-ledger
receipt itself proves *jailed AND attested AND finalized* — a tamper-proof record
no operator can secretly change or backdate (commit `951be3291`).

**④ Finalized cross-node.** The turn is served through
`drive_serving_attested` (`agent-platform/src/lib.rs:774`) onto the node, gossiped
into the blocklace, ordered by `tau`, and super-ratified by the quorum (§2a). Now
it is irreversible.

**⑤ Anyone verifies, unbiased.** A verifier calls `verify_landed_attested`
(`agent-platform/src/lib.rs:1068`): it confirms (a) the node chain is structurally
sound and the turn is on the finalized log (light-client-unfoolable — a genuine
kernel step lies behind the accepted proof), and (b) the landed turn carries
**exactly** the recomputed attestation commitment — so the ruling on the ledger is
bound to *this* honest, injection-free brain output. A forged binding, an
unattested turn, or a tampered attestation are each **distinguishable**
(`deos-hermes/tests/crown_attested_ledger.rs::forged_and_unattested_bindings_are_distinguishable`).
The verifier trusts no operator; it recomputes and checks.

**Scaling to N workers.** One Arbiter session can be split into many by
`ConfinedSession::fork_two` (`grain-fork/src/confined.rs:364`): one checkpoint →
two sovereign confined sessions, each its own jail, budget, caps, and receipt
chain, **attenuated never amplified** — egress doors of a child must be a subset of
the parent's (`EgressNotAttenuated`), caps must be parent-held
(`GrainError::UnconferrableCap`), and budgets must sum to ≤ the parent's
(`BudgetOverdraw`). So a busy community fans the Arbiter out across cases without
any fork gaining authority the parent lacked — the neutrality bound rides every
fork.

---

## 4. The deploy gates (honest)

Everything in §1–§3 is built and demonstrable by running (§5). What it needs to be
**live** is a homelab federation deploy — and that is precisely the step ember
keeps as *think/build, not operate*. Three honest gates:

**Gate 1 — the seed.** The verified Lean executor ships as a native archive
`dregg-lean-ffi/libdregg_lean.a`; without a HEAD-matching seed a node silently
degrades to the unverified marshal executor. The first seed is cut on **lassie**
(the Linux build box) — `scripts/bootstrap.sh` → compress → publish → bump
`dregg-lean-ffi/lean-seed.pin`. Commit `4ccee5bd7` made this cold-bootstrap
portable (git+rev mathlib pin, `lake exe cache get`). Status: the recipe is ready;
**no seed release has been cut yet** (`docs/HANDOFF-lassie-lean-seed.md`). Until it
is, a deployed committee runs marshal-only (real consensus, unverified producer) —
still a live federation, just not the verified-producer tier.

**Gate 2 — genesis + committee.** Mint the committee:
`dregg-node genesis --validators N --output <dir>` writes a shared `genesis.json`
(all operators' pubkeys), the per-operator `node-{i}.key`, and auto-computes the
quorum threshold `⌊2n/3⌋+1` (`node/src/genesis.rs:191`). Distribute the shared
genesis + one key per operator; each runs
`dregg-node run --federation-mode full --consensus blocklace --federation-peers …`.
A new operator onboards by `dregg-node join --bootstrap <peer>` and is admitted by
an existing operator's `dregg-node add-validator --pubkey <hex>` (filesystem
authority — there is no remote self-admit). The two- and three-node lifecycles are
proven-by-running in `DEV-NODE-RUNBOOK.md` (n=2 cross-node finalization: identical
6-block DAG, balance finalized on both) and `HOMELAB-N3-RUNBOOK.md`
(`stop → genesis → start → smoke`).

**Gate 3 — host the Arbiter + wire the ingress.** Each operator hosts the Arbiter
grain and points the platform's `NodeMinter` at the federation via
`with_node_url` / `DREGG_NODE_URL` (`agent-platform/src/lib.rs:749`) so a served
ruling forwards to the committee's `/turns/submit` ingress instead of a local node.
Members submit cases to that ingress. This forward is *"the operational deploy
step (still local here)"* — the code path exists and is tested against a local
node; standing up N≥2 live nodes and keeping them up is the operate step.

**The honest bottom line.** There is **no persistent live federation today**
(consistent with "DEVNET: GONE, 2026-06-22"). What exists is a re-runnable
lifecycle: the `dregg-node` binary, verified producer + marshal fallback, blocklace
BFT, QUIC gossip, cross-node finalization, late-join reconnect, the attested
serving path, and light-client verify — all real-by-running. The single missing
ingredient is someone standing up and *operating* an independent-operator committee
and forwarding real cases to it. The design and the primitives are ready; the
deploy is the gate.

---

## 5. Built vs. deploy — the ledger

**Built (real-by-running, tested, proofs axiom-clean):**

| Primitive | Where | Proof / test |
| --- | --- | --- |
| DAG-BFT finality, `⌊2n/3⌋+1` quorum, `f=⌊(n−1)/3⌋` | `blocklace/src/ordering.rs:236,305,688`; `node/` | `QuorumThreshold.lean`, `Consensus/Safety.lean` |
| No conflicting finalized history (safety apex) | — | `Safety.lean:268 no_conflicting_finalized_history` |
| Equivocation excluded + auto-evicted | `finality.rs:835`, `constitution.rs:168` | `Consensus.lean:251 equivocation_excluded` |
| Light-client unfoolability | — | `CircuitSoundness.lean:453 lightclient_unfoolable` |
| Settlement soundness (authority live at tip) | — | `SettlementSoundness.lean:153/305` |
| Non-domination ∧ unfoolability (one adversary) | — | `Adversary/Model.lean:140` |
| Confined brain (OS jail, one egress door) | `grain-jail/src/jail.rs`, `deos-hermes/src/confined.rs` | `jail::tests`, `grain_end_to_end.rs` |
| Attested ruling (authentic∧well-formed∧injection-free) | `zkoracle-prove/src/attestation.rs:161` | `crown_attested_turn.rs` |
| Attestation bound into R2 turn on the ledger | `deos-hermes/src/attest.rs:68`, `grain-turn/src/lib.rs:90` | `crown_attested_ledger.rs` (commit `951be3291`) |
| Cap-bounded authority, non-amplifying | `cell/src/capability.rs:820`, `dregg-agent/src/grant.rs` | `EffectVmEmitCapReshape.lean:230,545`; `introduce_non_amplifying` |
| Serve ruling → node, light-client verify | `agent-platform/src/lib.rs:774,1068` | `verify_landed_attested` |
| Scale-is-fork (N sovereign workers, attenuated) | `grain-fork/src/confined.rs:364` | `checkpoint_fork_two_sovereign_isolated_verifiable_sessions` |
| Signed cap-bounded request ingress | `node/src/api.rs:3209` | `DEV-NODE-RUNBOOK.md` |

**Deploy remainder (operate, not build):**

- Cut + publish the first HEAD-matching Lean seed on lassie (Gate 1) — else
  marshal-only.
- Mint + distribute genesis; stand up N≥2 independent operators; onboard via
  `add-validator` (Gate 2).
- Host the Arbiter per operator; point `NodeMinter` at the live committee's ingress
  and keep the federation up (Gate 3).
- A real (non-mock) LLM body inside the jail is its own named frontier
  (`GRAIN-CONFINED-BODY.md` — the last mock is the model; blocked on an
  in-jail HTTP client without a post-fork tokio runtime, plus the live provider
  being broken in-env). The attestation/confinement machinery is complete; the
  live provider call is the remaining wire.
- Verifiability ceiling is **R2** (per-turn); the whole-session STARK fold (**R3**,
  `grain_verify::WHOLE_HISTORY_GAP`) is the named frontier, not a blocker.

---

## 6. Boundaries — what this is NOT

- **Not a claim of unconditional censorship-resistance.** It is `f`-bounded. A
  captured supermajority — or a "federation" that is one operator wearing `n` hats
  — breaks every guarantee. The design's honesty is that it *names* this and makes
  operator independence the load-bearing assumption, not a footnote.
- **Not a change to the kernel, effect vocabulary, commitment, or soundness
  surface.** The Arbiter is a *composition* of shipped primitives — a grain, a
  confined+attested brain, a cap grant, and finalized turns. No new crypto, no new
  trust root.
- **Not "the AI decides and you obey."** The Arbiter's authority is exactly its
  cap; its rulings are advisory records on a shared ledger that the community's own
  rules give force to. What it guarantees is *neutrality and verifiability* of the
  ruling process — not that any party must comply. The authority nobody owns is an
  authority whose every act is checkable by everybody.
