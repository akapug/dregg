# `dregg-dice`: verifiable randomness for `attested-dm`

Status: design record. The crate is implemented at `dice/` (package `dregg-dice`) and
**diverges from this document on named protocol choices** — where they differ, the crate
is the wire-format authority. The divergences:

- **Sources.** The crate ships the full production endpoint, not a mock-first slice:
  the real post-quantum LB-VRF `ServerVrf` (`pqvrf`, Esgin et al. Set I), a
  genesis-committed VRF `KeyChain`, a real threshold `DrandBeacon` (BLS pairing check)
  plus the offline `HashChainBeacon`, and `Hybrid` with timeout finalization
  (`dice/src/lib.rs`). The design's `Deterministic` and `CommitReveal` sources also
  exist, honestly labeled.
- **Bounded mapping.** The crate uses a fixed-width, reject-free wide
  multiply-and-shift (`dice/src/draw.rs` `draw_bounded`) — deliberately **never**
  data-dependent rejection sampling, the opposite of this document's original
  normative algorithm. Rationale under "Unbiased bounded mapping" below.
- **Event identity.** The shipped `EventId::derive` binds
  `(game_binding, seq, pre_state_root, action_hash, event_kind, draw_count)`
  (`dice/src/event.rs:35`) — not this document's
  `(game_id, parent_receipt_hash, action_commitment, event_ordinal)`.
- **API shapes.** The shipped source/evidence types are
  `Deterministic / CommitReveal / MockBeacon / ServerVrf / Hybrid` with their own
  shapes; the Rust signatures in this document are the design's proposal, kept as a
  record of the reasoning, not a description of the crate's surface.

The protocol *obligations* this document derives — commit-before-result two-stage
binding, fixed `draw_count`, indexed random-access draws, domain separation, unbiased
bounded mapping, honest per-source trust labels — are what the crate satisfies, by its
own encodings.

## Purpose and security boundary

`dregg-dice` is a self-contained Rust crate that turns a request committed by the
game engine into a deterministic, indexed stream of verifiable random draws. The
crate separates two concerns:

1. a pluggable `RandomnessSource` produces and verifies seed material; and
2. a source-independent XOF stream derives unbiased bounded outcomes by index.

The crate does not decide game rules, receipt validity, or ledger ordering. The
`attested-dm` engine owns those decisions and commits requests and evidence into its
receipt chain. Given the same request and valid evidence, every implementation and
light client must derive exactly the same seed and draw sequence.

The recommended production source is a server-VRF/delayed-public-beacon hybrid,
and the crate implements it: `Hybrid` combines the genesis-committed LB-VRF
key-chain with a verified schedule-bound beacon and timeout finalization. The
deterministic and commit-reveal sources also exist for tests and offline play;
commit-reveal by itself is not fully non-grindable — a party that sees an
unfavorable outcome can selectively abort, and the crate's docs label it exactly
so.

## Cryptographic suite and canonical encoding

All hashes and XOF operations are versioned. This design proposed an explicit
`RandomnessSuite` enum; the shipped crate versions through its domain-separation
strings instead — every hashed object absorbs a literal versioned tag such as
`dregg-dice/event-id/v1` (`dice/src/event.rs:16`), with length-prefixed absorption
of variable-length fields. V1 uses BLAKE3 derivation and BLAKE3 XOF output.
Protocol objects must have a single canonical byte encoding; the design's
recommendation is explicit fixed-width field encoding rather than general-purpose
serialization:

- integers: unsigned little-endian, with their width fixed by the field type;
- byte arrays: raw bytes;
- variable-length byte strings: `u32` little-endian length followed by bytes;
- optional fields: one-byte tag (`0` or `1`) followed by the value when present;
- structs: fields in declaration order; and
- enums: fixed `u8` discriminant followed by variant fields.

Never derive protocol hashes from Rust's `Hash`, debug output, JSON, platform-sized
integers, or an encoding with more than one representation. Unknown suite versions
must fail closed.

## Public API (design proposal — the crate's surface differs)

The signatures below are the surface this design proposed. The shipped crate
diverged (see the divergence ledger at the top); read `dice/src/{lib,event,draw}.rs`
for the real surface. The section stands as the record of what each type is *for*.

```rust
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

use alloc::vec::Vec;

pub const SEED_LEN: usize = 32;
pub const HASH_LEN: usize = 32;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum RandomnessSuite {
    V1Blake3 = 1,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct EventId(pub [u8; HASH_LEN]);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Seed(pub [u8; SEED_LEN]);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RequestCommitment(pub [u8; HASH_LEN]);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RandomnessRequest {
    pub suite: RandomnessSuite,
    pub event_id: EventId,
    /// Commitment to the accepted game action/state transition that needs dice.
    pub action_commitment: [u8; HASH_LEN],
    /// Number of draw indices authorized for this event: `0..draw_count`.
    pub draw_count: u32,
    /// Source-specific public schedule/input fixed before the result is known.
    pub source_binding: SourceBinding,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceBinding {
    DeterministicMock {
        scenario_id: [u8; 32],
    },
    CommitReveal {
        commitment: [u8; 32],
        participant_id: [u8; 32],
    },
    ServerVrf {
        key_id: [u8; 32],
        public_key: Vec<u8>,
    },
    Beacon {
        network_id: [u8; 32],
        round: u64,
    },
    Hybrid {
        vrf_key_id: [u8; 32],
        vrf_public_key: Vec<u8>,
        beacon_network_id: [u8; 32],
        beacon_round: u64,
        deadline_unix_ms: u64,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RandomnessEvidence {
    pub suite: RandomnessSuite,
    pub event_id: EventId,
    /// Must equal `request.commitment()`.
    pub request_commitment: RequestCommitment,
    pub proof: SourceEvidence,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceEvidence {
    DeterministicMock {
        seed_material: [u8; 32],
    },
    CommitReveal {
        reveal: Vec<u8>,
    },
    ServerVrf {
        output: Vec<u8>,
        proof: Vec<u8>,
    },
    Beacon {
        round: u64,
        output: Vec<u8>,
        proof: Vec<u8>,
    },
    Hybrid {
        vrf_output: Vec<u8>,
        vrf_proof: Vec<u8>,
        beacon_round: u64,
        beacon_output: Vec<u8>,
        beacon_proof: Vec<u8>,
        /// Present only on the scheduled timeout path.
        timeout: Option<TimeoutEvidence>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TimeoutEvidence {
    pub deadline_unix_ms: u64,
    pub finalized_at_unix_ms: u64,
    pub authorization: Vec<u8>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Draw {
    pub event_id: EventId,
    pub index: u32,
    pub upper_bound: u64,
    /// A value in `0..upper_bound`.
    pub value: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RandomnessError {
    UnsupportedSuite,
    InvalidRequest,
    RequestMismatch,
    WrongSource,
    InvalidEvidence,
    InvalidProof,
    InvalidCommitment,
    InvalidBound,
    IndexOutOfRange,
    Exhausted,
    ArithmeticOverflow,
}
```

### Event identity and domain separation

An event ID is derived by the engine when it accepts an action, not by the
randomness source:

```rust
impl EventId {
    pub fn derive(
        game_id: &[u8; 32],
        parent_receipt_hash: &[u8; 32],
        action_commitment: &[u8; 32],
        event_ordinal: u32,
    ) -> Self;
}

impl RandomnessRequest {
    pub fn canonical_bytes(&self) -> Vec<u8>;
    pub fn commitment(&self) -> RequestCommitment;
    pub fn validate(&self) -> Result<(), RandomnessError>;
}
```

The V1 definitions are:

```text
EventId = H("dregg-dice/event-id/v1" ||
            game_id || parent_receipt_hash || action_commitment ||
            LE32(event_ordinal))

RequestCommitment = H("dregg-dice/request/v1" ||
                      canonical(RandomnessRequest))
```

`event_ordinal` distinguishes multiple random events caused by one action. The
parent receipt hash prevents the same action bytes in different ledger positions
from sharing an event. `action_commitment` binds all game inputs that can affect
how draws are interpreted. The source must neither choose nor rewrite `EventId`.

The shipped derivation satisfies the same obligations with different bindings:
`EventId::derive(game_binding, seq, pre_state_root, action_hash, event_kind,
draw_count)` (`dice/src/event.rs:35`) — `seq` + `pre_state_root` play the
ledger-position role, `event_kind` is a purpose tag that domain-separates
subsystems (`"combat/hit"`, `"loot"`, …), and `draw_count` is bound directly into
the event id so it cannot be varied after the fact.

Seed derivation is source-independent after the source has verified its evidence:

```text
Seed = KDF("dregg-dice/seed/v1",
           RequestCommitment ||
           source_kind_tag ||
           canonical_verified_source_output)
```

For Hybrid, `canonical_verified_source_output` contains both the verified VRF
output and the verified beacon output, including beacon network and round. On the
timeout path it contains the protocol's predetermined timeout contribution; it
must never contain server-selected fallback entropy.

### Pluggable sources

The core verification interface is synchronous and has no I/O. Fetching a beacon,
waiting for a deadline, or asking a VRF signer belongs in an adapter outside this
crate. This keeps verification deterministic and `no_std`-friendly.

```rust
pub trait RandomnessSource {
    /// Stable source tag included in seed derivation.
    fn source_tag(&self) -> &'static [u8];

    /// Check that this source can service the request and that all fixed public
    /// inputs (key, beacon round, deadline, commitment) are acceptable.
    fn validate_request(
        &self,
        request: &RandomnessRequest,
    ) -> Result<(), RandomnessError>;

    /// Produce evidence from already-available local/source inputs. Production
    /// adapters may gather those inputs asynchronously before calling this.
    fn finalize(
        &self,
        request: &RandomnessRequest,
    ) -> Result<RandomnessEvidence, RandomnessError>;

    /// Verify evidence and return canonical source output. Returning bytes rather
    /// than a seed ensures the shared derivation below cannot be bypassed.
    fn verify(
        &self,
        request: &RandomnessRequest,
        evidence: &RandomnessEvidence,
    ) -> Result<Vec<u8>, RandomnessError>;

    fn derive_seed(
        &self,
        request: &RandomnessRequest,
        evidence: &RandomnessEvidence,
    ) -> Result<Seed, RandomnessError> {
        let verified_output = self.verify(request, evidence)?;
        derive_seed(request, self.source_tag(), &verified_output)
    }
}

pub fn derive_seed(
    request: &RandomnessRequest,
    source_tag: &[u8],
    verified_source_output: &[u8],
) -> Result<Seed, RandomnessError>;

pub struct DeterministicMock { /* test-only fixed root material */ }
pub struct CommitReveal { /* participant policy and maximum reveal length */ }
pub struct ServerVrf<V: VrfVerifier> { /* genesis-bound key and verifier */ }
pub struct Beacon<B: BeaconVerifier> { /* network/genesis and round verifier */ }
pub struct Hybrid<V: VrfVerifier, B: BeaconVerifier> { /* both policies */ }

impl RandomnessSource for DeterministicMock { /* ... */ }
impl RandomnessSource for CommitReveal { /* ... */ }
impl<V: VrfVerifier> RandomnessSource for ServerVrf<V> { /* ... */ }
impl<B: BeaconVerifier> RandomnessSource for Beacon<B> { /* ... */ }
impl<V: VrfVerifier, B: BeaconVerifier> RandomnessSource for Hybrid<V, B> { /* ... */ }
```

`ServerVrf::verify` checks the proof over the exact request commitment and accepts
one canonical output for that input. `Beacon::verify` checks the network identity,
the round copied from the precommitted request, and the beacon proof. `Hybrid`
checks both and combines their outputs only after both proofs pass. Concrete VRF
and beacon algorithms should live behind small verifier traits or optional crate
features so the core has no networking dependency.

### Indexed XOF draw stream

Draws are random-access by `(event_id, index, upper_bound)`. They are not obtained
by consuming mutable XOF state, so a verifier can detect an omitted or reordered
draw and reproduce any index independently.

```rust
pub struct DrawStream {
    request: RandomnessRequest,
    seed: Seed,
    next_index: u32,
}

impl DrawStream {
    pub fn new(request: RandomnessRequest, seed: Seed)
        -> Result<Self, RandomnessError>;

    pub fn request(&self) -> &RandomnessRequest;
    pub fn next_index(&self) -> u32;

    /// Random-access derivation; does not advance the cursor.
    pub fn draw_at(&self, index: u32, upper_bound: u64)
        -> Result<Draw, RandomnessError>;

    /// Derives at `next_index` and advances exactly once on success.
    pub fn next_bounded(&mut self, upper_bound: u64)
        -> Result<Draw, RandomnessError>;

    pub fn remaining(&self) -> u32;
    pub fn finish(self) -> Result<(), RandomnessError>;
}

pub fn reproduce_draws(
    request: &RandomnessRequest,
    seed: Seed,
    upper_bounds: &[u64],
) -> Result<Vec<Draw>, RandomnessError>;
```

`index >= request.draw_count`, `upper_bound == 0`, and any attempt to advance past
`draw_count` fail. `finish` fails unless exactly `draw_count` successful draws were
consumed. The receipt records the ordered bounds as well as the values; bounds are
semantic inputs and may not be supplied only by an uncommitted verifier-side rule.

For each draw, V1 creates an independent XOF reader:

```text
XOF input = "dregg-dice/draw/v1" ||
            Seed || EventId || RequestCommitment ||
            LE32(index) || LE64(upper_bound)
```

#### Unbiased bounded mapping

Using `x % upper_bound` is forbidden because it is biased unless the bound divides
`2^64`. The shipped mapping (`dice/src/draw.rs`, `draw_bounded`) is a fixed-width,
**reject-free** wide multiply-and-shift — the fixed-width variant of Lemire's
method without the rejection step:

```text
draw_bounded(index, n) = ((raw(index) as u128 * n as u128) >> 64) as u64
```

A uniform 64-bit word is scaled into `0..n` by taking the high word of the 128-bit
product. The residual bias is at most `n / 2^64` — negligible for game-scale
bounds (< 2⁻⁵⁹ for a d20).

This design originally specified deterministic rejection sampling over consecutive
XOF words as the normative algorithm; the crate rejects that choice, deliberately.
Rejection sampling makes the number of raw words consumed *depend on the values
seen*, so the transcript length is not a public constant — and a public, fixed
draw count is exactly what lets `draw_count` be bound inside the `EventId` up
front. The fixed-width mapping consumes exactly one raw draw per index regardless
of the value drawn, keeping the transcript shape committed before any result
exists. The implementation must not expose an API that lets a caller provide a
retry nonce or choose among candidates.

## What the crate contains

The crate (`dice/`) carries the full source set, not a mock-first subset:

- BLAKE3 domain-separated event ID, request commitment, and seed derivation;
- the random-access `DrawStream` with the reject-free bounded mapping;
- serde-serializable `RandomnessRequest` / `RandomnessEvidence` and error types;
- `Deterministic` for stable test vectors and reproducible offline play;
- a `CommitReveal` source, labeled selectively-abortable;
- the real post-quantum LB-VRF `ServerVrf` (`pqvrf`, one-time Set I keys) with a
  genesis-committed `KeyChain` of per-event key epochs;
- beacons: the production threshold `DrandBeacon` (real drand-BLS, verified by a
  pairing check) and the offline/test `HashChainBeacon`, plus the unverified
  `MockBeacon` wiring stand-in; and
- `Hybrid` — key-chain VRF + schedule-bound beacon + timeout finalization, the
  recommended production endpoint.

### Deterministic source

The `Deterministic` source (`dice/src/source.rs:102`) is for tests, fixtures, and
reproducible offline play only: whoever knows the context knows every draw. It is
not feature-gated out of production builds; the guard is the honest trust label —
configuration and receipts must surface which source produced a seed, and a
deployment policy that accepts `Deterministic` evidence has chosen predictable
randomness. (This design originally prescribed a
`cfg(any(test, feature = "insecure-mock"))` gate; the shipped crate relies on the
labeled-source discipline instead.)

### Commit-reveal

Before action acceptance, the participant publishes:

```text
commitment = H("dregg-dice/commit-reveal/v1" ||
               participant_id || game_id || reveal)
```

The engine puts the commitment and participant ID into `SourceBinding`, then binds
the entire request in the action-accepted ledger entry. Finalization reveals the
preimage. `CommitReveal::verify` validates the commitment and returns a canonical
hash of the reveal as source output; the common `derive_seed` function then binds
it again to the request.

This is a useful deterministic protocol skeleton, not production-grade public
randomness. A revealer can withhold after learning whether the reveal leads to a
favorable result. A timeout can make the ledger progress, but unless its fallback
entropy was independently fixed and unpredictable, it does not prevent selective
abort or make the outcome fair. Production deployments should use Hybrid.

### Engine call shape

The intended first-slice flow is:

```rust
let request = RandomnessRequest { /* event, action, N, source binding */ };
let request_commitment = request.commitment();

// Engine first appends ActionAccepted containing request + commitment.
ledger.append(action_accepted_entry(&request, request_commitment))?;

// Only after acceptance may the source be finalized.
let evidence = source.finalize(&request)?;
let seed = source.derive_seed(&request, &evidence)?;
let mut stream = DrawStream::new(request.clone(), seed)?;

let mut draws = Vec::with_capacity(request.draw_count as usize);
for bound in game_rule_bounds.iter().copied() {
    draws.push(stream.next_bounded(bound)?);
}
stream.finish()?;

// Engine appends RandomnessFinalized containing evidence and ordered draws.
ledger.append(randomness_finalized_entry(&request, &evidence, &draws))?;
```

The engine must determine `game_rule_bounds` and `draw_count` before seed evidence
exists. If later game logic would conditionally use fewer random values, it should
still commit the maximum fixed count and consume every authorized index, recording
unused-but-consumed draws or using distinct precommitted random events. It must not
stop early after seeing a value.

## Receipt-chain binding

Randomness uses two ledger entries because a single receipt containing both request
and result would not prove that the request existed first.

### Stage 1: action accepted

The engine validates the player action and appends a `LedgerEntry` whose payload
contains:

```rust
pub struct RandomnessRequestedPayload {
    pub request: RandomnessRequest,
    pub request_commitment: RequestCommitment,
    /// Canonical ordered bounds expected at indices `0..draw_count`.
    pub draw_bounds: Vec<u64>,
}
```

The entry's normal chain fields bind it to its predecessor. The request's
`parent_receipt_hash` input is that predecessor, while its `action_commitment`
commits the accepted action and relevant pre-action state. The engine checks:

- recomputed `EventId` equals `request.event_id`;
- recomputed request commitment equals the payload commitment;
- `draw_bounds.len() == request.draw_count`;
- every bound is nonzero;
- the source binding satisfies genesis/game policy; and
- no prior accepted event has the same `EventId`.

This entry is signed/attested and durable before source finalization begins. The
randomness provider must receive this exact committed request, not a reconstructed
mutable request object.

### Stage 2: randomness finalized

A later `LedgerEntry` references the accepted entry and contains:

```rust
pub struct RandomnessFinalizedPayload {
    pub request_commitment: RequestCommitment,
    pub accepted_entry_hash: [u8; 32],
    pub evidence: RandomnessEvidence,
    pub draws: Vec<Draw>,
    pub finalization: FinalizationKind,
}

pub enum FinalizationKind {
    Normal,
    ScheduledTimeout,
}
```

The engine may apply the random-dependent state transition only with this finalized
entry (or atomically with its append). The final entry binds the exact evidence,
draw indices, bounds, values, accepted-entry hash, and resulting game state through
the existing `LedgerEntry` receipt-chain commitment.

`verify_ledger_replay` handles the pair as a small state machine:

```text
Absent --ActionAccepted--> Pending(request, bounds, accepted_hash)
Pending --RandomnessFinalized--> Finalized
```

Replay rejects finalization without a pending request, duplicate finalization,
request/evidence event mismatch, a finalization pointing to another accepted
entry, or any intervening rule violation. For each finalization it verifies source
evidence, derives the seed, recomputes draws for indices `0..draw_count`, compares
every recorded `(event_id, index, upper_bound, value)`, requires exact length, and
then re-executes the state transition. A pending event may be resolved only by its
normal source evidence or by the one timeout rule fixed in its accepted request;
retrying with a new event ID or changed source binding is not a timeout.

Whether unrelated actions may appear between the two stages is a game policy. The
safest first slice blocks actions that depend on the pending transition, while
allowing replay to track pending events by `EventId` rather than assuming adjacent
entries.

## Non-grindability and honest trust labels

The six required escape hatches divide as follows.

| Escape hatch | Deterministic / commit-reveal sources | VRF/beacon Hybrid (shipped) |
|---|---|---|
| Server key bound at genesis | Representable and policy-checkable, but unused by mock/commit-reveal | Required: `key_id` and public key must match genesis policy |
| Beacon round from fixed schedule | Representable in `SourceBinding`, but no beacon verification | Required: derive/validate the round from accepted height/time schedule; server cannot choose it |
| Player action bound before beacon deadline | Two-stage receipt proves action/request acceptance before finalization; local tests can verify ordering | Required: acceptance timestamp/height must precede the committed beacon deadline |
| VRF one output per input | Not provided by mock or commit-reveal | VRF proof is over the exact request commitment and has one canonical verified output |
| Timeout finalization prevents withholding reroll | State machine can forbid a second request and model a fixed timeout, but commit-reveal fallback is not automatically fair | Required: scheduled timeout deterministically finalizes using protocol-fixed evidence/contribution; never grants a fresh event or server-chosen entropy |
| `draw_count` fixed before seed; indexed XOF | Fully closed: request and ordered bounds are committed in Stage 1; indices are fixed and replayed | Same mechanism; source choice does not alter draws |

Additional source-independent protections are real but narrower:

- domain separation prevents cross-game, cross-event, request/seed/draw, and index
  reuse;
- request/evidence matching prevents evidence transplantation;
- exact stream consumption prevents skipping an unfavorable draw;
- unbiased mapping prevents modulo bias; and
- immutable receipt ordering detects a result chosen before the recorded request.

Trust levels must be surfaced in configuration and receipts:

- `Deterministic`: **insecure/test-only**. Anyone knowing the context predicts all
  outcomes and a producer can choose the material.
- `CommitReveal`: **reproducible but abortable**. A valid reveal proves the result,
  but a participant can selectively withhold it. A single committer may also grind
  commitments before publishing unless some earlier protocol fixes the reveal.
- `ServerVrf`: **publicly verifiable but server-withholdable**. The shipped VRF is
  the post-quantum LB-VRF (`pqvrf`, one-time Set I keys, one epoch per event): a
  forged output or proof is rejected, and output uniqueness reduces to Module-SIS.
  But a server can refuse to publish an unfavorable output unless timeout policy
  removes that leverage.
- beacons: **public-beacon trust**. Security depends on the selected beacon's
  unpredictability, proof, schedule, and liveness. The shipped production beacon is
  the threshold `DrandBeacon` (drand-BLS, verified by a pairing check); the
  `HashChainBeacon` is offline/test; the `MockBeacon` verifies nothing.
- `Hybrid`: **recommended production mode**. With the VRF key-chain committed at
  genesis, a scheduled beacon round, pre-deadline action binding, unique VRF
  output, and a deterministic timeout, neither source alone can reroll by choosing
  fresh inputs.

The Hybrid does not magically repair arbitrary policy. If operators may change the
genesis key, deadline, beacon network, round schedule, draw count, bounds, or
timeout fallback after acceptance, the system remains grindable. Replay must treat
those as consensus inputs and fail closed.

## Verification rules

A verifier processes every random event using these checks in order:

1. Decode canonically and reject unknown suites, duplicate fields, oversized
   evidence, invalid enum tags, and noncanonical encodings.
2. Recompute event identity from its full committed transition context (in the
   shipped derivation: game binding, sequence, pre-state root, action hash, event
   kind, and draw count).
3. Validate `draw_count`, exact bounds length, nonzero bounds, and configured size
   limits before allocating.
4. Recompute the request commitment and confirm the Stage 1 receipt-chain binding.
5. Confirm evidence suite, event ID, request commitment, and source variant match.
6. Verify source evidence and source policy, then derive the common seed.
7. Recompute every draw at exactly indices `0..draw_count`; require exact equality
   with the finalized receipt, including bounds and values.
8. Reject missing, duplicated, reordered, skipped, or extra indices.
9. Re-execute the game transition and verify the resulting ledger commitment.
10. Mark the pending event finalized so it cannot be used again.

Resource limits—maximum draw count, evidence byte length, reveal length, and XOF
words per bounded draw—are consensus/versioned policy and must be checked before
expensive work.

## Test plan

Tests must use fixed vectors as well as property tests. A producer and verifier
calling the same unchecked helper is not sufficient; verification tests should
decode receipt bytes and independently exercise the public verification path.

### Canonical and domain-separation vectors

- Freeze V1 vectors for canonical request bytes, `EventId`, request commitment,
  derived seed, and draws at several indices and bounds.
- Assert changing each event-ID component changes the event ID.
- Assert changing suite, action commitment, event ordinal, draw count, source
  binding, index, or bound changes the appropriate commitment/output.
- Assert noncanonical or unknown-version encodings fail rather than normalize.

### End-to-end reproduction

Build a Stage 1 accepted entry with `draw_count = 5` and bounds such as
`[2, 6, 20, 100, u64::MAX]`. Finalize it through the deterministic mock and append
Stage 2. Serialize both entries, give them to the re-execution verifier, and assert
that it independently verifies evidence, reproduces all five draws, consumes every
index, and reaches the same final game state commitment.

Repeat with commit-reveal. Assert that a correct reveal succeeds, while a changed
reveal, participant, game ID, event ID, accepted-entry hash, or request commitment
fails.

### Count, index, and consumption attacks

- Change Stage 2 from five draws to four while leaving Stage 1 unchanged: reject.
- Change Stage 1 `draw_count` without rebuilding the accepted receipt: reject at
  its receipt commitment. Rebuild Stage 1 but reuse old evidence: reject because
  the request commitment and derived seed differ.
- Delete index 2 and renumber later draws: reject on value/index comparison.
- Delete index 2 without renumbering: reject on exact length/contiguous indices.
- Duplicate, reorder, or append an index: reject.
- Change only a recorded bound or value: reject.
- Call `finish` after consuming fewer than N draws: return `Exhausted` (or a
  dedicated incomplete-consumption error); call `next_bounded` after N: return
  `IndexOutOfRange`.
- Attempt a second finalization for the same accepted event or a finalization
  referring to a different accepted entry: reject.

### Unbiased mapping tests

The implementation must make biased shortcuts detectable, not merely claim
uniformity:

- Freeze hand-computed word fixtures whose multiply-and-shift result differs from
  the word's residue mod the bound. A `% bound` implementation returns the residue
  and fails against the fixture.
- Test difficult bounds (`1`, `2`, `3`, `6`, `2^32 - 1`, `2^32 + 1`,
  `2^63 + 1`, and `u64::MAX`) against a small independent reference mapper.
- Property-test that every result is `< bound`, that `bound == 0` is rejected, and
  that random access at index `i` is stable regardless of access order.
- Assert the mapping consumes exactly one raw word per index for every bound —
  the reject-free property the transcript commitment depends on.
- Add a lint or code-review gate forbidding direct `% upper_bound` in the public
  draw path outside the specified mapper.

Statistical frequency tests may supplement these tests but must not replace them;
they are flaky and often fail to detect small modulo bias.

### Two-stage and timeout ordering

- Reject finalization before acceptance, evidence attached to the acceptance entry
  as if it proved prior commitment, and acceptance whose request was mutated after
  its receipt hash was computed.
- Verify a pending event cannot be replaced with a new event after a missing
  commit-reveal.
- For the Hybrid, test acceptance immediately before and after the beacon
  deadline, the exact scheduled round, wrong-network proofs, wrong-key VRF proofs,
  VRF evidence replayed across requests, normal finalization, and the
  deterministic timeout path.

## Implementation layout and feature policy

The crate's layout:

```text
dice/                (package dregg-dice)
  Cargo.toml
  src/
    lib.rs           public types, exports, and the trust-level docs
    event.rs         EventId derivation and domain separation
    request.rs       RandomnessRequest / commitment
    draw.rs          indexed XOF stream and the reject-free bounded mapping
    source.rs        RandomnessSource trait + all sources (Deterministic,
                     CommitReveal, MockBeacon, ServerVrf, Hybrid, beacons)
    error.rs
    util.rs
  tests/
    randomness.rs
    weighted.rs
```

Default features should be minimal. `alloc` is acceptable for evidence and receipt
objects; hashing, seed derivation, draw generation, and verification should avoid
`std`. Networking, clocks, storage, and async runtimes stay outside the crate.
Secret material should use zeroization where applicable, avoid `Debug`, and never
be included in error messages. Verification accepts public material only.

## Acceptance criteria

The obligations the implementation must satisfy (by its own encodings):

1. the engine can commit a request for N bounded draws in an action-accepted
   `LedgerEntry` before producing evidence;
2. every source's evidence produces a domain-separated seed only after
   verification;
3. the engine records exactly N indexed draws in a finalized `LedgerEntry`;
4. replay verification reconstructs and compares the complete draw stream and
   resulting state transition from serialized ledger entries;
5. the count/index/bound/value mutation tests fail verification;
6. a fixture that distinguishes the specified unbiased mapping from naive modulo
   passes; and
7. public documentation labels `Deterministic` as insecure and commit-reveal as
   selectively abortable, with `Hybrid` as the production endpoint — which the
   crate's module docs do.

