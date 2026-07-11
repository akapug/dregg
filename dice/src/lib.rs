//! # dregg-dice — verifiable randomness for the attested-dm game engine
//!
//! This crate is the minimal first slice of Phase 2 ("Non-grindable randomness")
//! of `docs/DESIGN-verifiable-game.md`. It provides the *derivation and
//! verification* machinery for game randomness, with the unpredictability source
//! itself behind a trait so a VRF/beacon backend drops in later.
//!
//! ## What it gives you
//!
//! - [`EventId::derive`] — a domain-separated binding of a draw to its full
//!   transition context: game, sequence, pre-state, action, purpose
//!   (`event_kind`), and `draw_count`. Distinct domain tags per hashed object
//!   prevent cross-protocol preimage collisions.
//! - [`RandomnessSource`] — a pluggable source: a producer ([`RandomnessSource::evidence`])
//!   and a pure verifier ([`RandomnessSource::seed`]) that re-derives the seed and
//!   checks the evidence. Implemented: [`CommitReveal`], [`Deterministic`],
//!   [`MockBeacon`], and the real post-quantum [`ServerVrf`] (the one-time `pqvrf`
//!   LB-VRF). Designed-but-stubbed (beacon + genesis key-chain required): [`Hybrid`].
//! - [`DrawStream`] — an indexed XOF draw stream from a verified [`Seed`], with an
//!   **unbiased, reject-free** bounded mapping ([`DrawStream::draw_bounded`]).
//! - [`RandomnessRequest`] / [`RandomnessEvidence`] — serde-serializable
//!   structures mirroring the design, plus [`RandomnessRequest::commitment`], the
//!   receipt-shaped hash an engine stores before the result exists.
//!
//! ## Trust levels — read this before claiming anything
//!
//! **The seed-derivation and draw-stream verifier are correct regardless of
//! source.** Given a `Seed`, everyone reconstructs the identical draw stream, and
//! the transcript commitment binds `draw_count` and every draw. Grinding by
//! changing `draw_count`, `event_kind`, the action, or the pre-state is *always*
//! detectable, because all of those move the [`EventId`], hence the seed, hence
//! the transcript.
//!
//! **The unpredictability guarantee depends entirely on the source:**
//!
//! - [`Deterministic`] provides **no** unpredictability. Whoever knows the
//!   context knows every draw. It is for tests and reproducible offline play.
//! - [`CommitReveal`] prevents either party from *unilaterally choosing* the
//!   outcome (the server is bound to a pre-published commitment; the player's
//!   contribution is mixed in). **But commit-reveal does NOT prevent selective
//!   abort:** the last party to reveal learns the result first and can simply
//!   refuse to reveal on an unfavorable outcome, so the transition never lands.
//!   This crate deliberately does not describe commit-reveal as non-abortable.
//!   Closing the abort gap needs timeout finalization with a deterministic
//!   consequence (a follow-up) so a withheld reveal cannot silently reroll.
//! - [`MockBeacon`] folds in a beacon output but does **not** verify the beacon's
//!   signature or finality — it is a wiring/test stand-in, not a guarantee.
//! - [`ServerVrf`] is the real post-quantum **LB-VRF** (`pqvrf`, Esgin et al. Set I):
//!   the output is the unique VRF value for a `(key, input)` pair — a forged output
//!   or proof is rejected by `pqvrf::verify`, its uniqueness reducing to Module-SIS.
//!   This is the lattice replacement for the rejected classical ECVRF. The key is
//!   one-time (Set I); each event uses its own committed key epoch. Output
//!   pseudorandomness rests on MLWE (assumed).
//! - [`Hybrid`] (delayed beacon + genesis-committed LB-VRF key-chain) is the
//!   recommended endpoint that closes unilateral reroll on *both* sides. It still
//!   requires the beacon + key-chain backend and is stubbed here.
//!
//! ### The six non-grindability escape hatches, honestly
//!
//! The design names six things that make randomness non-grindable. This slice,
//! with the [`CommitReveal`]/[`Deterministic`] sources, closes some and leaves
//! others to the VRF/beacon backend:
//!
//! | # | Escape hatch | Status in this slice |
//! |---|---|---|
//! | 1 | Server key bound at genesis | **Follow-up** — [`ServerVrf`] uses a per-event committed key; a genesis-committed key-chain (epoch = seq) is the [`Hybrid`] |
//! | 2 | Beacon round from a fixed schedule | **Needs beacon** — [`MockBeacon`] is unverified |
//! | 3 | Player action bound before the beacon deadline | **Closed** — `action_hash` is bound into the `EventId` before the seed exists |
//! | 4 | VRF one-output-per-input | **Closed by [`ServerVrf`]** — the LB-VRF output is the *unique* value for `(key, input)`; a forged output/proof fails `pqvrf::verify` (uniqueness reduces to Module-SIS) |
//! | 5 | Timeout finalization so withholding can't reroll | **Open** — the last-revealer abort; needs timeout receipts |
//! | 6 | `event_kind` + `draw_count` bound before the seed exists | **Closed** — both are in the `EventId`; the transcript commitment enforces them |
//!
//! So the honest summary: **CommitReveal closes hatches 3 and 6** and prevents
//! unilateral *choice*; **[`ServerVrf`] additionally closes hatch 4** — the output
//! is not *chosen* by the server but is the LB-VRF's unique value for the committed
//! key and the event id, and a forgery is caught by `pqvrf::verify`. Hatches 1, 2,
//! and 5 — a genesis-committed key-chain, a real verified beacon, and
//! timeout-no-reroll — remain the delayed-beacon + key-chain [`Hybrid`] follow-up.
//!
//! ## Follow-ups (out of scope here)
//!
//! - The [`Hybrid`] delayed-beacon seed with a genesis-committed LB-VRF key-chain
//!   (epoch = seq) and timeout receipts — closing hatches 1, 2, and 5.

mod util;

pub mod draw;
pub mod error;
pub mod event;
pub mod request;
pub mod source;

pub use draw::{DOMAIN_DRAW, DOMAIN_TRANSCRIPT, DrawStream, Seed};
pub use error::{DrawError, VerifyError};
pub use event::{DOMAIN_EVENT_ID, EventId};
pub use request::{
    DERIVATION_VERSION, DOMAIN_REQUEST_COMMITMENT, EvidenceKind, RandomnessEvidence,
    RandomnessRequest,
};
pub use source::{
    CommitReveal, DOMAIN_COMMIT, DOMAIN_LB_VRF_KEY_COMMITMENT, DOMAIN_SEED, Deterministic, Hybrid,
    MockBeacon, RandomnessSource, ServerVrf, VrfEvalError,
};
