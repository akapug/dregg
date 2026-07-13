# Verifiable Game Design

## Status and thesis

`attested-dm` should become a game engine in which creative narration remains flexible, but every state-changing outcome is determined by explicit rules and can be independently checked. The AI proposes tone, description, and intent; the engine alone decides state transitions.

The existing foundation is strong:

- `resolve_action(map, world, typed_action)` deterministically resolves a closed `GameAction` (`Move`, `Take`, `Use`, `Examine`, or `Attack`).
- Every landed move creates a previous-entry-linked `LedgerEntry` binding sequence number, narration, effect, prompt and game identities, and an attestation.
- `DmCaps` gates grants.
- The `.dungeon` format is readable and has parsing and validation.
- `GameSession::verify()` detects tampering with the recorded chain.

Two boundaries must remain explicit:

1. The current attestation's authenticity leg is an in-tree fixture. It is not production identity or hardware-backed authenticity.
2. Current verification authenticates recorded history but does not replay `resolve_action`. It proves that history was not altered after recording, not that every recorded effect followed the rules.

The target claim is therefore: **a session is verifiable under the deployed prover, cryptographic, and randomness-source assumptions**. It is not “trustless from first principles.” In particular, dregg has real circuit, circuit-proving, folding, and WASM light-client machinery, but ultimate STARK soundness remains an assumption rather than a discharged proof.

## Design laws

The following laws should constrain every extension:

1. **Narration cannot mutate the world.** It may describe only an engine-produced effect and public observations derived from the post-state.
2. **Every transition has a canonical input.** The action, pre-state commitment, ruleset identity, randomness input, capability witness, and relevant persistent-state roots must be bound before resolution.
3. **Randomness is explicit data, never ambient state.** No resolver path may read a clock, process RNG, thread scheduling, map iteration order, or uncommitted external input.
4. **Verification is layered.** Cheap deterministic replay is the baseline; succinct proofs are an acceleration and privacy mechanism, not an excuse to omit an executable specification.
5. **Rules are versioned content.** A game binds a canonical ruleset hash and `.dungeon` hash. Upgrades create a declared boundary rather than silently changing old sessions.
6. **Capabilities authorize; they do not determine outcomes.** A valid `DmCaps` witness permits an attempted transition, while the resolver still enforces all rules.
7. **Failure is a transition.** Rejected or ineffective actions receive canonical effects and enter the ledger, preventing selective omission.

## Receipt and transition model

The ledger should evolve from “attested narrative entry” into a transition receipt. Conceptually, each entry binds:

```text
TransitionReceipt {
    game_binding,
    ruleset_hash,
    seq,
    prev_receipt_hash,
    pre_state_root,
    action_commitment,
    capability_commitment,
    randomness_context,
    effect_commitment,
    post_state_root,
    narration_commitment,
    persistence_roots,
    execution_evidence,
    attestation,
}
```

The canonical transition statement is:

```text
(post_state, effect) = resolve_action(
    ruleset,
    map,
    pre_state,
    typed_action,
    authorized_caps,
    randomness
)
```

`execution_evidence` initially means “replayable inputs,” and later may additionally carry a folded proof. A verifier must reject an entry if any commitment, sequence link, authorization, randomness derivation, effect, or post-state root fails its selected verification tier.

Narration should bind to the action and resolved effect, but it should not be part of the deterministic state transition. This preserves creative freedom without allowing prose changes to alter game state.

## Verifiable randomness

### Requirements

Game randomness must be:

- unpredictable before both sides are committed;
- bound to exactly one game, sequence number, ruleset, pre-state, and action;
- domain-separated by purpose, so combat, loot, and encounter rolls cannot influence one another;
- non-reusable and replay-detectable;
- publicly derivable or accompanied by compact verification evidence;
- non-grindable by both server and player.

Plain server randomness fails because the server can reroll. Plain player randomness fails because the player can withhold or retry. Two-party commit-reveal improves this, but it still permits last-revealer aborts and creates awkward timeout policy. It is a useful fallback, not the preferred endpoint.

### Options

#### Server VRF

A server VRF produces a deterministic pseudorandom output and proof from a secret key over a bound message:

```text
vrf_message = H(
    "attested-dm/randomness/v1",
    game_binding,
    ruleset_hash,
    seq,
    prev_receipt_hash,
    pre_state_root,
    action_commitment,
    randomness_domain
)
```

The output is unique for the key and message, and anyone can verify its proof. This prevents the server from sampling many random values for the same finalized input. It does **not** alone prevent the server from choosing among keys, delaying service, or presenting players with multiple candidate game identities. Production use therefore requires a key registered before the session, a key epoch bound into `game_binding`, and an auditable rotation policy.

Difficulty: low to medium. Verification is compact and practical; key lifecycle and abort accountability are the real work.

#### Public randomness beacon

A public beacon supplies a timestamped, independently produced value after the action is finalized. The receipt binds a beacon identity, round, value, and proof. Randomness is derived from the beacon output and the transition context.

This removes unilateral server choice and is attractive for high-value events. Its costs are latency, availability dependence, reorganization/finality semantics, and the need to define exactly which future round applies. A malicious player must not be able to wait to see a beacon round before selecting an action, so the action receipt must fix a future round before that round becomes known.

Difficulty: medium. The cryptography is straightforward; robust round selection, offline play, and availability policy are harder.

#### In-circuit randomness verification

The proof circuit can verify that a VRF proof or beacon signature is valid and that all random draws are derived correctly. This does not create randomness; it proves correct use of an external source. Hash-based expansion should derive an indexed stream:

```text
seed = H(source_output, transition_context)
draw_i = H("attested-dm/draw/v1", seed, subsystem, i)
```

For bounded integers, the rules must use an unbiased construction such as rejection sampling with a circuit-friendly fixed bound or an explicitly analyzed mapping. A casual modulo reduction introduces bias.

Difficulty: high. Signature/VRF verification and unbiased sampling can dominate constraint cost unless the chosen primitives are circuit-friendly.

### Recommended construction: delayed beacon plus registered VRF

Use a hybrid, with commit-reveal only as an offline fallback:

1. The player signs or otherwise authenticates a canonical action commitment that binds the current pre-state and sequence number.
2. The server acknowledges it and fixes a specific future beacon round according to a public rule.
3. The server computes a VRF output over the finalized transition context using a session-registered key.
4. After the beacon round finalizes, derive:

   ```text
   seed = H(
       "attested-dm/hybrid-seed/v1",
       beacon_id,
       beacon_round,
       beacon_output,
       vrf_public_key,
       vrf_output,
       transition_context
   )
   ```

5. The resolver consumes only domain-separated indexed draws from that seed.

The beacon prevents the server from knowing the result when acknowledging the action; the VRF prevents a player from precomputing outcomes from public beacon values alone and binds the registered server identity. Neither party can vary its input after the action and round are fixed. Both can still abort, but cannot silently reroll. Aborts should be recorded as signed timeout receipts, and game policy should assign a deterministic consequence rather than permitting the transition to disappear.

The receipt's `randomness_context` should include the source identifiers, beacon round and proof, VRF key/output/proof, derivation version, and a commitment to the exact draw transcript. Replay verification regenerates every draw; circuit verification proves the same derivation and use.

For offline or private sessions, use two-party commit-reveal with deposits, counters, or deterministic timeout outcomes where appropriate. Be candid that it has last-revealer liveness risk. Never describe it as non-abortable randomness.

## Verifiable rule execution

Closing the execution gap requires two complementary tracks.

### Track A: deterministic re-execution light client

The first complete verifier should replay the game, not merely inspect hashes.

For each receipt, it should:

1. Verify the previous hash, sequence, game and ruleset bindings, and attestation policy.
2. Load the exact canonical ruleset and `.dungeon` content committed by the game.
3. Reconstruct the pre-state from the prior verified post-state or a verified checkpoint.
4. Decode the closed typed action from its canonical bytes and reject unknown or non-canonical encodings.
5. Verify `DmCaps` authorization and consumption rules.
6. Verify randomness evidence and regenerate the indexed random transcript.
7. Run the same deterministic `resolve_action` implementation.
8. Compare the computed effect and post-state root with the receipt.
9. Check that narration is bound to, but cannot substitute for, the resolved effect.

This verifier should be a library shared by native tools and the WASM light client. The resolver needs a narrow, portable, deterministic core: no filesystem, network, clock, floating point, platform-dependent iteration, hidden global state, or unstable serialization. Golden transition vectors should run against native and WASM builds.

Replay verification is the semantic reference. Even after succinct proofs exist, it remains necessary for debugging, proof-system migrations, and users who prefer direct execution over prover assumptions.

Large sessions can use verified checkpoints. A checkpoint binds the full canonical state root and the receipt prefix root; a verifier either replays from genesis or trusts/verifies a checkpoint under an explicit policy. “Fast” must never silently mean “skipped history.”

### Track B: resolver invariants in dregg's fold machinery

The proof path should encode a transition relation and fold one proof step per receipt. The public statement should minimally bind:

```text
(game_binding, ruleset_hash, seq, pre_state_root,
 action_commitment, randomness_commitment,
 effect_commitment, post_state_root)
```

Each folded step proves that the committed witness decodes canonically, authorization checks pass, randomness is correctly derived, the transition relation holds, and the resulting state root becomes the next step's pre-state root. The final folded proof attests to an entire prefix without exposing private state beyond the chosen public commitments.

Do not begin by circuitizing the whole engine. Start with a tiny invariant whose semantics are stable and whose failure is materially harmful.

**Smallest invariant worth proving first: a successful `Move` changes only the actor's position to a traversable adjacent destination and leaves all unrelated committed state unchanged.**

More precisely, prove:

- the actor exists and is authorized by the action/capability witness;
- the destination is adjacent under the bound movement rule;
- the map witness authenticates the destination tile against the bound map root;
- that tile is traversable;
- the post-state actor position equals the destination;
- the remaining world commitment is unchanged.

This is better than proving only “the state hash links,” because it establishes the first real semantic rule. It is smaller than combat or inventory transfer, avoids randomness initially, exercises authenticated map/state reads, and forces a sound state-update gadget that later invariants can reuse.

Suggested invariant sequence:

1. Move locality and traversability.
2. Take conserves item identity: one item moves from location to inventory, with no duplication.
3. Use consumes or transforms exactly the specified resource and applies only an allowed effect.
4. Attack verifies target legality, random draw derivation, damage bounds, and health saturation.
5. Full transition equivalence between the executable resolver and circuit relation.

The hard part is specification alignment. A circuit can faithfully prove the wrong rule. Maintain one canonical transition specification, differential vectors for executable and circuit implementations, versioned semantics, and explicit proof-system parameters. The honest external claim remains “verified under the deployed dregg/STARK assumptions.”

## Ambitious capabilities

### Overworld

**What it is.** A large, possibly streamed world composed of regions, terrain, points of interest, encounter tables, travel costs, and visibility rules. Regions may be authored in `.dungeon`-like modules and connected by a committed world manifest.

**World-resolved and verifiable.** Bind a world root whose leaves are region manifests. A travel action supplies Merkle witnesses for the current and destination regions, plus any path segment needed by the movement rule. The resolver determines reachability, time/resource cost, discovery, and encounters. Unrevealed regions can remain committed and private until entered; reveal receipts prove that disclosed region content was fixed under the original world root. Random encounters use the receipt-bound random stream.

**Difficulty.** Medium for a fully public static overworld; high for fog-of-war, procedural generation, or streamed private content. The major design risks are witness size, content availability, and preventing a server from selectively withholding unfavorable committed regions.

Opinion: start with region-to-region movement over a sparse committed graph, not a giant tile circuit. Prove local edge validity and resource cost; keep pathfinding outside the circuit until the semantics stabilize.

### Turn-based combat engine

**What it is.** Initiative, legal targets, action economy, status effects, damage/healing, equipment modifiers, death/downed states, and a deterministic round/turn state machine.

**World-resolved and verifiable.** Combat state is a committed substate with an explicit phase and active actor. Every command is a typed combat action; the engine checks phase, capability, target, range, costs, cooldowns, and status modifiers. Random draws are indexed by semantic purpose, such as `(combat_id, round, turn, action_index, "hit")`, so adding a flavor roll cannot shift damage rolls. The receipt binds the combat pre/post roots and draw transcript. Folded proofs establish turn-order progression, legal state updates, and bounded arithmetic.

**Difficulty.** High. Interacting status effects and rule ordering cause more complexity than arithmetic. Define a strict effect queue and total ordering; avoid free-form scripting in the trusted transition core. A small first combat ruleset should have one attack, one defense, integer health, and no nested triggers.

### Character progression

**What it is.** Experience, levels, attributes, skills, equipment eligibility, learned abilities, quests, and respec policy.

**World-resolved and verifiable.** Progression is a state machine driven only by verified receipts: defeated enemies, completed objectives, consumed training items, or explicit grants authorized by scoped `DmCaps`. Tables and formulas live in the versioned ruleset. Every grant names its source receipt, making rewards non-duplicable. Level-up choices are typed player actions. The resolver checks prerequisites and computes the new character commitment.

**Difficulty.** Medium if formulas and trees are static; high if AI-authored abilities or arbitrary mods can create executable rules. Prefer a bounded declarative effect language whose interpreter is deterministic and eventually circuitized. Do not let narration mint XP or items.

### Cross-session persistence with proofs

**What it is.** Characters, inventories, achievements, and world changes survive a session and can be imported into later games without trusting a database administrator.

**World-resolved and verifiable.** End a session with a finalized export receipt binding the terminal session root, character/object commitment, provenance, ruleset, and a nullifier or monotonic version. A new session imports it only after verifying the source chain or folded proof and checking compatibility policy. The new game's genesis receipt references the export. A global or account-scoped sparse Merkle root tracks the latest version and consumed one-shot exports. Updates require proofs of membership and valid transition; nullifiers prevent cloning an item into multiple descendant sessions.

Cross-ruleset transfers require an explicit, versioned migration function that produces a migration receipt. There is no safe implicit equivalence between items or stats from different rulesets.

**Difficulty.** Very high. Cryptographic validity does not itself solve global double-spend, data availability, finality, account recovery, or concurrent offline forks. A practical first version should use a transparency log or sequencer for ordering while keeping transition correctness independently verifiable. Decentralizing ordering can come later; the trust assumption must be stated.

## Verification tiers

Expose verification as named tiers rather than one overloaded boolean:

- **Integrity:** receipt hash chain, bindings, and configured attestation policy are valid.
- **Replay:** integrity plus deterministic re-execution of every transition.
- **Succinct:** a folded proof verifies for the committed session prefix under named dregg/prover parameters.
- **Anchored:** succinct or replay verification plus required beacon, persistence-log, and finality checks.

The UI and API should report the achieved tier, ruleset hash, verifier version, proof parameters, attestation mode, randomness source, and any trusted checkpoint. A fixture attestation must be visibly labeled as such.

## Phased roadmap

### Phase 0 — Canonical transition envelope

- Define canonical bytes for actions, effects, state roots, capabilities, ruleset identity, and randomness context.
- Extend ledger entries with pre-state root, action commitment, ruleset hash, randomness context, and post-state root.
- Record rejected actions as deterministic receipts.
- Publish transition test vectors.

Exit criterion: a receipt contains everything an independent implementation needs to attempt replay.

### Phase 1 — Replay verifier

- Extract a deterministic, portable resolver core.
- Make `GameSession::verify_replay()` walk receipts and re-run `resolve_action`.
- Share the core with the WASM light client.
- Differential-test native and WASM results over golden and generated sessions.
- Preserve existing chain-only verification as the explicitly named integrity tier.

Exit criterion: mutating an effect or producing a rule-invalid but correctly rehashed transition is rejected.

### Phase 2 — Non-grindable randomness

- Register a per-session VRF key and bind its epoch into the game identity.
- Define action finalization and future beacon-round selection.
- Implement beacon and VRF verification, domain-separated draw expansion, timeout receipts, and deterministic abort consequences.
- Add commit-reveal as a clearly labeled offline fallback.

Exit criterion: neither player nor server can obtain a different landed outcome without creating publicly detectable equivocation or abort evidence.

### Phase 3 — First folded semantic proof

- Specify the authenticated state/map layout.
- Implement the successful-`Move` locality and traversability circuit.
- Fold consecutive move proofs with dregg's existing machinery.
- Bind proof parameters and public inputs into session verification.
- Cross-check circuit witnesses against replay vectors.

Exit criterion: the WASM light client verifies a session prefix proof establishing real movement semantics under the deployed prover assumptions.

### Phase 4 — Inventory and combat

- Add item-conservation proofs for `Take` and bounded transformations for `Use`.
- Introduce the minimal combat state machine.
- Prove turn legality, random derivation, and bounded damage before adding complex effects.

Exit criterion: a complete small encounter is replay-verifiable and fold-verifiable.

### Phase 5 — Overworld and progression

- Add region-rooted overworld content and reveal proofs.
- Add receipt-sourced XP, level-up actions, and declarative abilities.
- Define content-availability and ruleset-upgrade policies.

Exit criterion: travel, encounters, rewards, and level-ups compose without narration-controlled mutation.

### Phase 6 — Cross-session persistence

- Define export/import and migration receipts.
- Add version/nullifier tracking and a transparent ordering service.
- Prove valid state evolution across session boundaries.
- Specify recovery, forks, finality, and data-availability assumptions.

Exit criterion: a character can move between sessions with independently checkable provenance and without silent duplication.

## The one-day, highest-leverage first step

**Add a canonical `TransitionInput` to each new ledger entry and implement replay verification for `Move` only.**

`TransitionInput` should bind:

```text
ruleset_hash
pre_state_root
canonical_typed_action
capability_commitment
randomness_context_or_none
```

Then add `verify_replay_move()` (or an internal equivalent selected by action type) that reconstructs the prior world, runs `resolve_action` for `Move`, and compares the canonical effect and post-state root. Include one adversarial test that constructs a hash-valid chain with an impossible move and proves that integrity verification accepts it while replay verification rejects it.

This is buildable in a day because `Move` is deterministic and avoids the unresolved randomness design. It has unusually high leverage because it:

- turns the honest verification gap into an executable failing test;
- forces the receipt to bind the action and pre-state required by every later verifier;
- establishes the separation between integrity and replay tiers;
- creates golden inputs for the first movement circuit;
- reveals serialization and resolver-purity problems before proof engineering multiplies their cost.

Do not start with a circuit or beacon integration. First make the rule-correct statement fully replayable and testable. Succinct proof work should compress a transition relation that already has a clear executable meaning.

## Security and claim discipline

Every release should publish a compact assumption manifest covering:

- attestation mode and key provenance;
- resolver and ruleset hashes;
- canonical encoding version;
- randomness sources, finality, key registration, and abort policy;
- proof system and parameter identifiers;
- checkpoint or persistence-log trust;
- data-availability expectations;
- verification tier actually achieved.

Appropriate claim: “This history is untampered and its state transitions were replayed,” or, after the proof path lands, “This session prefix satisfies the committed resolver invariants under the deployed dregg prover assumptions.”

Inappropriate claim: “The AI is trusted because it was attested,” “the chain proves the rules were followed” when only integrity was checked, or “the system is trustless from first principles.”

The core product promise is narrower and stronger: **the AI may invent the story, but it cannot invent the outcome.**
