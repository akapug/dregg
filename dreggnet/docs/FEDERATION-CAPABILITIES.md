# DreggNet federation capabilities — the grounded, honest reference

> Purpose: a source-of-truth a public post can be crafted from **without overclaiming**.
> Every claim is tagged **PROVEN** (a Lean theorem, `#assert_axioms`-clean) / **IMPLEMENTED**
> (running code, file:line) / **LIVE** (actually deployed on the mesh right now) /
> **DESIGNED** (built, not yet live). When in doubt, downgrade the tag.
>
> Grounded to `~/dev/breadstuffs` (the dregg substrate: `blocklace/`, `node/`, `metatheory/`)
> and `~/dev/DreggNet` (the operated deployment) at HEAD, 2026-06-30.

---

## 0. The one-sentence answer to "can no single node or government shut it down?"

A DreggNet app runs on a **committee of independent operators**, not one server. A turn (an app
operation) becomes final only when a **supermajority quorum** of the committee ratifies it. That
quorum keeps working while up to **f = ⌊(n−1)/3⌋** operators are offline, malicious, *or seized*.
So there is no single node to shut down: to **halt** it you must take down more than f operators;
to **censor** a turn you must stop *every* honest quorum from forming; to **forge/rewrite** state
you must break the safety proofs or the underlying cryptography.

This is real and mathematically backed **up to the fault threshold f** — not unconditionally.
The honest bound is spelled out in §5. It is only as strong as (a) how large n is, (b) how
*independent* the operators actually are (distinct people / machines / jurisdictions), and
(c) the standard crypto assumptions (STARK/Poseidon2) the light-client proof carries.

---

## 1. The consensus algorithm — what it IS

DreggNet's ledger is a **blocklace**: a DAG of signed blocks, each block carrying hash-pointers to
the predecessors it has seen. It is a **leaderless DAG-BFT** design in the **Cordial-Miners**
family, with membership governed by **Constitutional Consensus**:

- **Blocklace DAG** — Almog–Lewis–Naor–Shapiro, arXiv:2402.08068. Content-addressed
  (BLAKE3), Ed25519-signed blocks; each participant grows its local view monotonically by
  CRDT union-merge; equivocation (a creator forking its own chain) is detectable from the
  structure itself. `blocklace/src/finality.rs`, `blocklace/src/lib.rs`.
- **Total order `tau`** — Cordial Miners, arXiv:2205.09174. The DAG is cut into **waves**
  (default `wavelength = 3` rounds). Each wave has a **round-robin leader**. A leader block
  becomes a **final leader** when it is **super-ratified** — a supermajority of the committee,
  at the wave's last round, ratify it (and each of those ratifiers itself saw a supermajority
  approve the leader). `tau` then walks the final leaders in order, collecting each leader's new
  causal past and sorting it deterministically. `blocklace/src/ordering.rs::tau` (line 486).
- **Constitutional membership** — arXiv:2505.19216. The committee (the "constitution") is an
  amendable participant set + threshold; joins/leaves pass by supermajority vote carried in
  blocks; equivocators are **auto-evicted without a vote** (the proof is self-evident); silent
  nodes time out. `blocklace/src/constitution.rs`.

> **IMPLEMENTED.** All three layers are running Rust. The finalization rule `tau` is also
> modeled executably in Lean (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean`), and the
> node **gates the live commit on the Lean rule** (§3, §6).

"A turn is final when a supermajority of the committee super-ratifies the wave that orders it."

---

## 2. Committee, threshold, fault-tolerance

**The one quorum formula** (there is exactly one, system-wide):

```
supermajority_threshold(n) = ⌊2n/3⌋ + 1      # blocklace/src/ordering.rs:236
                           = n − ⌊(n−1)/3⌋    # equivalent closed form, n ≥ 1
```

The Byzantine fault budget is **f = ⌊(n−1)/3⌋**. Up to f operators may be offline, malicious, or
seized and the federation still (a) finalizes — a quorum of `n − f` honest nodes remains — and
(b) stays safe — any two quorums overlap in an honest node (§4).

| n (operators) | quorum (threshold) | f tolerated |
|---|---|---|
| 1 | 1 | 0 |
| 4 | 3 | 1 |
| **5** | **4** | **1** |
| 7 | 5 | 2 |
| 10 | 7 | 3 |
| 13 | 9 | 4 |

Note the strict `+1` at multiples of 3 (`n=3 → 3`, not 2; `n=6 → 5`): this is the choice that makes
quorum intersection **unconditional** (no "3 ∤ n" caveat). It closes the historical `n − ⌊n/3⌋`
hole where at `n = 3f` two quorums could intersect in a single, possibly-Byzantine, member.

> **IMPLEMENTED + PROVEN.** Formula: `supermajority_threshold` (ordering.rs:236), delegated to by
> the federation and the constitution (`compute_threshold`, constitution.rs:739) — one formula, no
> drift. Intersection: `supermajority_intersection` / `two_quorums_share_honest`
> (`metatheory/Dregg2/Distributed/QuorumThreshold.lean:151, 169`), both `#assert_axioms`-clean.

---

## 3. Multi-operator + the Rust↔Lean differential

The point of a federation is that **n *independent* operators** run validators; finality needs a
quorum *across operators*, so no one operator can decide the ledger. DreggNet adds a second,
orthogonal correctness check on top:

- **Two independent executor implementations** — a **Rust** executor and a **Lean** executor —
  run the *same* turns. They must agree; divergence is refused, not silently resolved. This is a
  differential test running **in production on every block**, not just in CI. The finalized order
  itself is also gated: the node hands the same `(wavelength, participants, lace)` to the verified
  Lean rule and admits a block to the executor **only if the verified rule finalizes it**
  (`node/src/finality_gate.rs`; default ON via `DREGG_FINALITY_GATE`).
- The gate's guarantee is a theorem: `gate_admits_iff_verified_finalizes`
  (`BlocklaceFinality.lean`) — gating on the gate *is* gating on the verified `tau`.
- **Fail-open honesty:** if a node's Lean archive is stale/missing, the gate falls back to the
  Rust order **with a loud warning + a logged divergence record** — the node keeps running but the
  operator is told the verified gate is not active. (finality_gate.rs:27-35.)

> **IMPLEMENTED + LIVE.** The deployed staging committee is a deliberately **mixed** Lean↔Rust
> committee (see §7). The agreement is also a unit differential:
> `ordering::tests::test_tau_differential_against_lean_model` and its equivocator-exclusion twin.

---

## 4. What is PROVEN in Lean

All theorems below are **`#assert_axioms`-clean** (they reduce to Lean's standard kernel axioms
`{propext, Classical.choice, Quot.sound}`) and **sorry-free** on the consensus path. Where a
theorem carries a *named, typed hypothesis* (the honest floor — e.g. the BFT honest-majority model,
or a standard crypto assumption), that is stated explicitly, not hidden.

**Consensus safety (no two honest nodes finalize conflicting histories):**
- `no_conflicting_finalized_history` — *the chain-safety apex.* Two honest nodes holding different
  partial laces cannot finalize conflicting leaders at the same wave → their finalized histories
  never disagree; there is no fork a light client can be split across.
  `metatheory/Dregg2/Consensus/Safety.lean:268`.
- `cordial_no_conflicting_final_leaders` / `cordial_agreement_via_bft` — two distinct
  super-ratified leaders in one wave cannot both finalize under the honest BFT model.
  `metatheory/Dregg2/Proof/CordialMiners.lean:407, 445`.
- `finalLeaders_one_per_wave` — the *executable* rule the node runs returns at most one final
  leader per wave. `metatheory/Dregg2/Distributed/BlocklaceFinality.lean:615`.

**Equivocation exclusion:**
- `equivocation_excluded` — a double-signer leaves a self-incriminating, detectable incomparable
  pair; its leader candidate is repelled from ratification and contributes no finalized block.
  `metatheory/Dregg2/Distributed/Consensus.lean:251` (non-vacuity demo at :290). Mirrored by the
  Rust↔Lean differential `test_tau_differential_equivocator_excluded`.

**Consensus → executor (the order drives verified execution):**
- `tau_drives_verified_run` / `tau_execution_agreement` — the computed finalized order drives the
  verified executor, and two replicas with the same lace reach the same state.
  `metatheory/Dregg2/Distributed/BlocklaceFinality.lean:657, 670`.

**Settlement soundness (a settled turn is final / irreversible):**
- `settlement_soundness` — a settled turn necessarily exercised authority that was *live at the
  settlement tip* (held as an attenuation AND honored by the tip's finalized revocation set).
  `metatheory/Metatheory/SettlementSoundness.lean:153` (abstract) and
  `metatheory/Dregg2/Circuit/SettlementSoundness.lean:210` (circuit form); both clean.

**Light-client unfoolability (a light client can't be fooled about state):**
- `lightclient_unfoolable` — a batch that verifies under the live verification key proves the
  existence of a *genuine* kernel transition with the published commitments.
  `metatheory/Dregg2/Circuit/CircuitSoundness.lean:453` (clean at :1058).

**Quorum intersection (§2):** `supermajority_intersection`, `two_quorums_share_honest`
(`QuorumThreshold.lean:151, 169`).

**The named honest floor (carried hypotheses, never `axiom`s):**
- `BFTModel` — honest supermajority + at most f Byzantine (the *standard* BFT assumption; the
  post-GST dissemination that the union of two nodes' pools meets it is a named residual, off the
  safety-critical path).
- `StarkSound`, `Poseidon2SpongeCR`, and the commitment collision-resistance set — the standard
  cryptographic carriers under `lightclient_unfoolable` / `settlement_soundness`. These are the
  *floor everyone stands on* (FRI/STARK soundness, hash CR), not a dregg-specific gap.

One honest in-tree residual worth naming: the two finalization models — the BFT algebra
(`Proof.CordialMiners`) where safety is proven, and the executable rule
(`Distributed.BlocklaceFinality`) the node runs — are bridged by the `OPEN-CM-SUPERRATIFY-BRIDGE`
lane (they share the `n − f` ratifier-count shape). Safety is proven on the algebra side and the
executable rule is proven single-leader-per-wave directly; welding the two conclusions is the next
rung, not an assumed step.

---

## 5. Censorship-resistance — the honest "Dom" answer

The motivating question: can an agent run as an **uncensorable public utility** — one that no
single node or government can shut down? Here is what holds **by construction**, and the bound.

**Why no single point can HALT it.** Finality requires a quorum of `⌊2n/3⌋ + 1`. A quorum still
forms while up to **f = ⌊(n−1)/3⌋** operators are down or seized (`n − f ≥` quorum). Taking one
operator offline — or f of them — does not stop finalization. (PROVEN backbone: quorum
intersection + `finalLeaders_one_per_wave`.)

**Why no single point can CENSOR a turn.** Any honest quorum can super-ratify a wave whose causal
past contains the turn. An adversary controlling ≤ f operators cannot prevent the remaining honest
supermajority from finalizing it. (Liveness of inclusion holds under the same honest-majority +
eventual-delivery assumptions BFT always needs.)

**Why no single point can FORGE or REWRITE state.** A finalized turn is irreversible
(`settlement_soundness`); a light client following any honest node's finalized chain lands on the
same history and cannot be fed a fake state (`lightclient_unfoolable` + `no_conflicting_finalized_history`);
and a fabricated turn is caught twice — by the two independent executors (§3) and by the verified
finality gate.

**The bound — stated plainly, because a public post must not lie:**
- It tolerates **f**, not **n**. A coalition that controls the fault budget — i.e. seizes/coerces
  **more than f** operators, or musters a colluding supermajority — *can* halt or fork it. There is
  no protection against a majority that is itself dishonest. This is inherent to BFT, not a DreggNet
  shortcoming.
- **f is small until n is large.** At n=4, f=1 (one seizure tolerated). At n=7, f=2; n=10, f=3.
  A serious "uncensorable against a government" posture wants a **large committee spread across many
  people and jurisdictions**, so that seizing > f is politically/physically infeasible.
- **Independence is a real, physical requirement,** not automatic. The math assumes the f faults are
  *distinct*. If several "operators" share a machine, a host, or a legal owner, they are one fault
  domain and the effective f is smaller. (The current staging deployment does not yet run four
  fully-independent operators — see §7.)
- The light-client guarantee rests on the **standard crypto carriers** (STARK/Poseidon2). If those
  break, so does everyone's.

So: **an agent running on a sufficiently large, sufficiently independent DreggNet committee is an
uncensorable public utility up to the fault threshold f** — there is no one node to seize. That is a
true statement with an explicit, honest boundary; it is not "unstoppable no matter what."

---

## 6. What a "small appchain-ish construct" looks like

A small committee of **N operators (4–9 is a natural range)** can run one app or agent as a
**mini-appchain nobody owns**:

- **The app's state = the federated ledger.** dregg cells hold the app's data (owned state,
  balances, an agent's memory, a drone-fleet's command cells).
- **The app's operations = turns.** Each operation is a signed, proof-carrying turn over owned
  state, leaving a verifiable receipt.
- **"The app decides" = the quorum agrees.** An operation takes effect when the committee
  super-ratifies the wave that orders it. No operator can unilaterally act or block.
- **Nobody owns it.** There is no admin key and no privileged node; the committee *is* the
  authority, and membership is itself governed by the committee.

**Spinning one up** (the shape; the tooling exists as the node + constitution layer):
1. Fresh **genesis** + **N operator keypairs** (Ed25519), one per independent operator.
2. A **constitution** = the N participant set, threshold auto-computed as `⌊2N/3⌋ + 1`
   (`Constitution::new`, constitution.rs:63).
3. Operators run nodes, dial each other (`--federation-peers`), gossip blocks over QUIC, and run
   `tau` to finalize.
4. **Grow N** later via a constitutional `Join` proposal (voted, super-ratified, applied at a wave
   boundary — constitution.rs `apply_if_passed`). Shrink via voluntary `Leave`, **auto-evict** for
   an equivocator (no vote), or **timeout** auto-leave for a silent node. This is exactly the
   committee re-roll / grow-N move used to go from one staging committee generation to the next.

The result is a purpose-built BFT ledger for one app, cheap to stand up, owned by its operator set
rather than by any one of them.

> **IMPLEMENTED (substrate) + DESIGNED (turnkey UX).** The genesis / constitution / join-vote /
> auto-evict / timeout machinery is all running Rust in `blocklace/` + `node/`. A one-command
> "spin up an app committee" onboarding is a product surface, not a new protocol.

---

## 7. The honest live state (2026-06-30)

**LIVE (deployed, running now):**
- A **staging BFT committee of n=4, threshold 3, f=1** — `edge` (node-index 0) + `node-a` (Lean
  executor) + `node-a-rust` (Rust executor) + `node-b` (Lean) — full-mesh QUIC gossip over the
  overlay. `deploy/staging/docker-compose.yml:377` (`--federation-size 4`, threshold 3).
- The **Rust↔Lean differential runs in production on every block** (mixed committee), and the
  **finality gate is ON by default**, gating admission on the verified Lean rule.

**IN PROGRESS (hardening, landing now):**
- The **A1 execution-FFI fix** — `2fc33f0cc` (2026-06-30) — moved the finalized-turn execution FFI
  off the async worker + global lock. It was the root cause of turns not advancing at n=4/n=5 (the
  worker + producer/super-ratify loop were being starved). Landed green with tests
  (`a1_finalized_turn_advances_height_zero_to_one_off_lock`). This unblocks sustained live
  finalization.
- **Finalization is connected but not yet producing live finalized data.** The live edge node is
  reachable read-only but its receipt log is currently empty and it has no finalized checkpoint;
  the submit path is operator-locked pending an operator unlock + a funded execution-lease mint.
  The wiring is proven end-to-end in-process (`node/src/node_integrator_e2e.rs`); the live mesh has
  not yet been driven to sustained finality. The deployed edge binary is also **stale** (predates
  several recovery/gossip fixes) and needs a redeploy.

**DESIGNED / NEAR-TERM (not yet live):**
- **n=5** by bringing operator **`node-e`** online to replace `node-b-rust` (per the ops queue) —
  threshold would become 4, f stays 1. This is a hardware-availability step, not new protocol.
- **True operator independence.** Today two of the executors share machines/fault domains (the
  Lean/Rust pair), so the deployment is not yet four *fully independent* operators. Independence
  across people + machines + jurisdictions is the work that turns the math in §5 into a real
  censorship-resistance posture.

---

## 8. What a public post can truthfully claim

**Safe to say (grounded):**
- "DreggNet runs apps/agents on a **committee of operators using leaderless DAG-BFT consensus**
  (blocklace / Cordial-Miners family). A turn is final when a **supermajority quorum**
  (`⌊2n/3⌋+1`) super-ratifies it."
- "It tolerates up to **f = ⌊(n−1)/3⌋** operators being offline, malicious, or **seized** — no
  single node (or government seizing ≤ f nodes) can halt it, censor a turn, or forge state."
- "The core guarantees are **machine-checked in Lean and `#assert_axioms`-clean**: consensus
  safety (no conflicting finalized histories), single-leader-per-wave, equivocation exclusion,
  settlement soundness (finalized = irreversible), and light-client unfoolability."
- "It runs a **live Rust↔Lean differential on every block** plus a verified finality gate — two
  independent implementations must agree."
- "You can stand up a **small app-committee (a mini-appchain nobody owns)** and grow it by vote."

**Must accompany any of the above (the honest boundary):**
- The guarantee is **up to f, not unconditional** — a colluding supermajority can override it;
  f is small until n is large; and the operators must be **genuinely independent**.
- The Lean proofs carry the **standard BFT + crypto assumptions** (honest supermajority,
  STARK/Poseidon2 soundness).
- **Live status is n=4 staging with finalization being hardened right now** (A1 fix landed today;
  sustained live finality + n=5 + fully-independent operators are the immediate next steps). The
  *algorithm and the proofs* are done; the *live-finalizing multi-jurisdiction mesh* is in progress.

Do **not** claim: a live n=5 mainnet; sustained live finality today; unconditional / "unstoppable
no matter what" censorship-resistance; or four fully-independent operators today.
