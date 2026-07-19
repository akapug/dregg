//! # `crowd_round` — the crowd-stream round driver (the WIRING layer)
//!
//! The converge-later half of the crowd-stream engine (`docs/CROWD-STREAM-ENGINE-DESIGN.md`):
//! it feeds live-stream votes into the REAL quorum-certified vote engine and lands ONE certified
//! world turn per round. Where [`dregg_stream_ingest`] is the pure, dep-light mapping (platform
//! payload → [`WeightedBallot`]), THIS module pays for the offering-stack deps and closes the
//! seam onto [`dungeon_on_dregg::collective::CollectiveRound`] — the tested
//! "signed-ballot tally → one verified turn" primitive.
//!
//! ```text
//! StreamEvent stream                (ingest here, over a round window)
//!   → events_to_ballots / aggregate (one ballot per distinct voter, their strongest option)
//!   → weight-replicated custody seats (a $5 Super Chat = 5 seats, capped)
//!   → CollectiveRound.cast × N       (each seat a REAL ed25519-signed ballot turn)
//!   → resolve_into_world             (the quorum gate → ONE certified TurnReceipt on the game)
//! ```
//!
//! ## What is real vs. the named residuals
//!
//! * **Real:** every seat casts a genuine `ed25519`-signed ballot the engine authenticates; the
//!   quorum `AffineLe` gate (`Σ TALLY ≥ M`) still certifies; `resolve_into_world` still binds the
//!   certified decision into the world cell and fires ONE real `TurnReceipt`. A sub-quorum window
//!   or a quorum-certified-but-illegal command is refused exactly as the collective's own tests
//!   prove. This driver only *sources the ballots*; it cannot vote past the executor's teeth.
//! * **Named residual — per-voter custody.** The design's electorate-scaling gap: the demo derives
//!   a seat's `ed25519` secret from its `author_id` string ([`seat_custodian`], via
//!   `Custodian::demo`), so the **platform (us) mints and holds every viewer's key** — it is NOT
//!   real per-viewer custody (the viewer never signs on their own device). Real custody needs a
//!   viewer-held key enrolled out-of-band; until then a Super Chat is authenticated as *coming
//!   through YouTube*, not as *signed by that human*.
//! * **Named residual — dynamic electorate.** `CollectiveRound` fixes its roster at open
//!   ("muster"). We honor that by materializing the electorate at **close** from exactly who voted
//!   this window, opening a fresh round each window. Join/leave within a window is fine; a
//!   persistent cross-window electorate + rotation is future work.
//! * **Named residual — the floor.** The certified turn inherits the deployed ledger's undischarged
//!   FRI/STARK floor; "certified" here means quorum-certified + executor-admitted, not
//!   FRI-sound-on-chain.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use dregg_stream_ingest::{
    PlatformAdapter, StreamEvent, WeightedBallot, YouTubeAdapter, events_to_ballots,
};
use dungeon_on_dregg::collective::{
    CertifiedTurn, CollectiveError, CollectiveRound, Custodian, FEDERATION, Proposal, Seat,
};
use spween_dregg::{Scene, WorldCell};

/// The `blake3::derive_key`-style seat-id domain: a voter's derived custody seats are keyed by
/// this string so a crowd-stream seat can never collide with the collective's own demo roster.
const SEAT_DOMAIN: &str = "crowd-stream/youtube";

/// **A live crowd-stream round.** Holds the poll question + proposals, the matchable option
/// keywords (index-aligned with the proposals), the quorum threshold, and the buffer of events
/// ingested during the current window. [`ingest`](Self::ingest) accumulates; [`preview`](Self::preview)
/// reports the running weighted tally (what the overlay pushes); [`close_into_world`](Self::close_into_world)
/// resolves the window into ONE certified world turn and advances to the next.
pub struct CrowdRound {
    question: String,
    proposals: Vec<Proposal>,
    /// Matchable keywords for each option (index-aligned with `proposals`). A viewer's chat/Super
    /// Chat text is matched against THESE (short — e.g. `"press on"`), not the full proposal label.
    options: Vec<String>,
    quorum: u64,
    federation: [u8; 32],
    /// Events ingested during the current (open) window.
    buffer: Vec<StreamEvent>,
    /// The certified turns this driver has landed, oldest first (an audit trail of the run).
    landed: Vec<CertifiedTurn>,
    /// The cap on how many custody seats one voter's weight may materialize — the paid-influence
    /// ceiling / DoS guard (a single whale cannot mint an unbounded electorate).
    max_weight_per_voter: u64,
}

/// The default per-voter seat cap: a single voter tops out at 64 seats of influence in one window.
pub const DEFAULT_MAX_WEIGHT_PER_VOTER: u64 = 64;

/// One option's running weighted tally in a [`TallyPreview`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OptionTally {
    /// The option's display label (the proposal label).
    pub label: String,
    /// The summed vote weight for this option this window.
    pub votes: u64,
}

/// A snapshot of a round's running weighted tally — the shape the overlay renders + pushes. It is
/// computed from the buffered events exactly as [`close_into_world`](CrowdRound::close_into_world)
/// will resolve them (per-voter aggregation + the weight cap), so the overlay never shows a total
/// the close won't honor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TallyPreview {
    /// The poll question.
    pub question: String,
    /// Per-option running tallies (index-aligned with the round's proposals).
    pub options: Vec<OptionTally>,
    /// Total weighted votes this window (Σ of the capped per-voter weights) — the value the quorum
    /// gate compares against `quorum`.
    pub total: u64,
    /// Distinct voters this window.
    pub voters: u64,
    /// The quorum threshold `M` (a seat/weight count; `total ≥ quorum` ⇒ the window can certify).
    pub quorum: u64,
    /// The current leader's option index (max weight, `> 0`), or `None` if no votes yet.
    pub leader: Option<usize>,
}

impl TallyPreview {
    /// Whether the running total has met quorum (a certify would resolve this window).
    pub fn quorum_met(&self) -> bool {
        self.total >= self.quorum
    }
}

impl CrowdRound {
    /// Open a crowd-stream round. `proposals` and `options` are index-aligned (option `i`'s
    /// keyword matches proposal `i`'s command); `quorum` is the weight threshold `M`. Uses the
    /// collective's demo [`FEDERATION`] and the default per-voter seat cap.
    ///
    /// Panics if `proposals` and `options` differ in length (a programming error — they are two
    /// views of the same option list).
    pub fn open(
        question: impl Into<String>,
        proposals: Vec<Proposal>,
        options: Vec<String>,
        quorum: u64,
    ) -> CrowdRound {
        Self::open_with(
            question,
            proposals,
            options,
            quorum,
            FEDERATION,
            DEFAULT_MAX_WEIGHT_PER_VOTER,
        )
    }

    /// [`open`](Self::open) with an explicit federation id + per-voter weight cap.
    pub fn open_with(
        question: impl Into<String>,
        proposals: Vec<Proposal>,
        options: Vec<String>,
        quorum: u64,
        federation: [u8; 32],
        max_weight_per_voter: u64,
    ) -> CrowdRound {
        assert_eq!(
            proposals.len(),
            options.len(),
            "proposals and option keywords must be index-aligned (one keyword per proposal)"
        );
        CrowdRound {
            question: question.into(),
            proposals,
            options,
            quorum,
            federation,
            buffer: Vec::new(),
            landed: Vec::new(),
            max_weight_per_voter: max_weight_per_voter.max(1),
        }
    }

    /// The poll question.
    pub fn question(&self) -> &str {
        &self.question
    }

    /// The round's proposals (index-aligned with the options / the tally).
    pub fn proposals(&self) -> &[Proposal] {
        &self.proposals
    }

    /// The matchable option keywords as `&str`s (what [`events_to_ballots`] matches against).
    pub fn option_keywords(&self) -> Vec<&str> {
        self.options.iter().map(String::as_str).collect()
    }

    /// The quorum threshold `M`.
    pub fn quorum(&self) -> u64 {
        self.quorum
    }

    /// Ingest one normalized event into the current window.
    pub fn ingest(&mut self, event: StreamEvent) {
        self.buffer.push(event);
    }

    /// Ingest many normalized events into the current window.
    pub fn ingest_batch(&mut self, events: impl IntoIterator<Item = StreamEvent>) {
        self.buffer.extend(events);
    }

    /// Convenience: parse a raw YouTube `liveChatMessages` JSON payload with the [`YouTubeAdapter`]
    /// and buffer the events. Returns how many were ingested.
    pub fn ingest_youtube(&mut self, raw: &str) -> usize {
        let events = YouTubeAdapter.parse(raw);
        let n = events.len();
        self.ingest_batch(events);
        n
    }

    /// How many events are buffered in the current window.
    pub fn buffered(&self) -> usize {
        self.buffer.len()
    }

    /// The certified turns landed so far (oldest first).
    pub fn landed(&self) -> &[CertifiedTurn] {
        &self.landed
    }

    /// **Aggregate the window to one ballot per distinct voter.** Each voter's per-option weights
    /// are summed and the voter is assigned the option they backed hardest (max summed weight; on
    /// a tie the higher option index wins — deterministic). This collapses a viewer who chatted the
    /// same option twice, and resolves a viewer who flip-flopped to their strongest signal. The
    /// returned weights are pre-cap (the cap is applied when seats are materialized).
    fn aggregate(&self) -> Vec<WeightedBallot> {
        let opts = self.option_keywords();
        let raw = events_to_ballots(&self.buffer, &opts);
        // voter → (option index → summed weight)
        let mut per_voter: BTreeMap<String, BTreeMap<usize, u64>> = BTreeMap::new();
        for b in raw {
            *per_voter
                .entry(b.voter)
                .or_default()
                .entry(b.option_idx)
                .or_default() += b.weight;
        }
        per_voter
            .into_iter()
            .filter_map(|(voter, opts)| {
                // max_by_key keeps the LAST max on a tie; BTreeMap iterates options ascending, so
                // a tie resolves to the higher option index — deterministic.
                let (option_idx, weight) = opts.into_iter().max_by_key(|&(_, w)| w)?;
                Some(WeightedBallot {
                    voter,
                    option_idx,
                    weight,
                })
            })
            .collect()
    }

    /// The running weighted tally over the open window (what the overlay pushes). Computed from the
    /// SAME aggregation + cap [`close_into_world`](Self::close_into_world) uses, so preview and
    /// resolve agree.
    pub fn preview(&self) -> TallyPreview {
        let ballots = self.aggregate();
        let mut votes = vec![0u64; self.options.len()];
        let mut total = 0u64;
        for b in &ballots {
            let w = b.weight.clamp(1, self.max_weight_per_voter);
            if b.option_idx < votes.len() {
                votes[b.option_idx] += w;
                total += w;
            }
        }
        let leader = votes
            .iter()
            .enumerate()
            .max_by_key(|&(_, &v)| v)
            .and_then(|(i, &v)| (v > 0).then_some(i));
        let options = self
            .proposals
            .iter()
            .zip(votes.iter())
            .map(|(p, &v)| OptionTally {
                label: p.label.clone(),
                votes: v,
            })
            .collect();
        TallyPreview {
            question: self.question.clone(),
            options,
            total,
            voters: ballots.len() as u64,
            quorum: self.quorum,
            leader,
        }
    }

    /// **THE SEAM — close the window, resolve into the world.** Materializes the electorate from
    /// who voted this window (each voter's weight expands to capped custody seats), opens a real
    /// [`CollectiveRound`] over that electorate, casts every seat's `ed25519`-signed ballot, and
    /// [`resolve_into_world`](CollectiveRound::resolve_into_world) → ONE certified [`CertifiedTurn`]
    /// on the game executor.
    ///
    /// On success the certified turn is recorded and the window is reset (advanced). On refusal the
    /// window is **left intact** so the caller can decide (retry after more votes, or drop):
    /// * no votes / below quorum → [`CollectiveError::BelowQuorum`] (the world does not move);
    /// * a quorum-certified but illegal command → [`CollectiveError::World`] (the executor's teeth).
    pub fn close_into_world(
        &mut self,
        world: &WorldCell,
        scene: &Scene,
    ) -> Result<CertifiedTurn, CollectiveError> {
        let ballots = self.aggregate();

        // Materialize the electorate: each voter's (capped) weight expands to that many custody
        // seats, all voting the voter's aggregated option. Weight-as-replicated-seats is how a paid
        // vote earns more influence on the one-ballot-per-seat engine (a $5 Super Chat = 5 seats).
        let mut seated: Vec<(Custodian, usize)> = Vec::new();
        for b in &ballots {
            let n = b.weight.clamp(1, self.max_weight_per_voter);
            for k in 0..n {
                seated.push((seat_custodian(&b.voter, k), b.option_idx));
            }
        }
        // No votes ⇒ below quorum, without troubling the engine with an empty electorate.
        if seated.is_empty() {
            return Err(CollectiveError::BelowQuorum);
        }

        let electorate: Vec<Seat> = seated.iter().map(|(c, _)| c.seat()).collect();
        let mut round = CollectiveRound::open_with(
            self.question.clone(),
            self.proposals.clone(),
            &electorate,
            self.quorum,
            self.federation,
        )?;
        let poll = round.poll();
        for (custodian, option) in &seated {
            round.cast(&custodian.sign_ballot(poll, *option))?;
        }

        let cert = round.resolve_into_world(world, scene)?;
        self.landed.push(cert.clone());
        self.advance();
        Ok(cert)
    }

    /// Reset the window for the next round (drop the buffered events). Called automatically after a
    /// successful [`close_into_world`](Self::close_into_world); call it directly to abandon a window
    /// (e.g. after a persistent illegal-command refusal).
    pub fn advance(&mut self) {
        self.buffer.clear();
    }
}

/// The per-voter, per-seat **demo** custody keypair — `Custodian::demo(SEAT_DOMAIN ‖ voter ‖ #k)`.
/// Deterministic so a window's tally is reproducible, and domain-separated so it can never collide
/// with the collective's own roster.
///
/// NAMED RESIDUAL: this derives the seat's `ed25519` secret from the `author_id` string — the
/// platform holds the key, the viewer does not. It authenticates a ballot as *coming through the
/// platform*, not as *signed by that human*. Real per-viewer custody (a viewer-held key enrolled
/// out-of-band) is the electorate-scaling follow-up.
pub fn seat_custodian(voter: &str, k: u64) -> Custodian {
    Custodian::demo(format!("{SEAT_DOMAIN}/{voter}#{k}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_stream_ingest::EventKind;
    use dungeon_on_dregg::narrator::Command;
    use dungeon_on_dregg::{deploy_keep, keep_scene};
    use spween_dregg::Value;

    /// The keep round proposals: option 0 = trade blows, option 1 = press on (the same moves the
    /// collective's own tests drive).
    fn keep_round(quorum: u64) -> CrowdRound {
        CrowdRound::open(
            "The gate-warden bars the way — what does the party do?",
            vec![
                Proposal::new("Trade blows with the gate-warden", Command::trade_blows()),
                Proposal::new("Press past into the plundered hall", Command::press_on()),
            ],
            vec!["trade blows".to_string(), "press on".to_string()],
            quorum,
        )
    }

    fn chat(author: &str, text: &str) -> StreamEvent {
        StreamEvent {
            platform: "youtube".into(),
            author_id: author.into(),
            kind: EventKind::Chat,
            amount_micros: 0,
            text: text.into(),
            ts: 0,
        }
    }

    fn super_chat(author: &str, text: &str, micros: u64) -> StreamEvent {
        StreamEvent {
            platform: "youtube".into(),
            author_id: author.into(),
            kind: EventKind::SuperChat,
            amount_micros: micros,
            text: text.into(),
            ts: 0,
        }
    }

    #[test]
    fn preview_aggregates_weighted_votes_per_voter() {
        let mut round = keep_round(3);
        round.ingest(chat("A", "press on"));
        round.ingest(chat("A", "press on")); // same voter, same option — collapses to one voter.
        round.ingest(super_chat("B", "TRADE BLOWS", 5_000_000)); // weight 5.
        round.ingest(chat("C", "trade blows"));

        let p = round.preview();
        assert_eq!(p.voters, 3, "A/B/C are three distinct voters");
        // press on: A's max option is press-on (weight 2 summed). trade blows: B(5) + C(1) = 6.
        assert_eq!(
            p.options[1].votes, 2,
            "A's two press-on chats sum to weight 2"
        );
        assert_eq!(
            p.options[0].votes, 6,
            "B's $5 + C's chat = 6 on trade blows"
        );
        assert_eq!(p.total, 8);
        assert_eq!(p.leader, Some(0), "trade blows leads");
        assert!(p.quorum_met(), "8 ≥ quorum 3");
    }

    #[test]
    fn quorum_certified_crowd_vote_fires_a_real_world_turn() {
        let scene = keep_scene();
        let mut world = deploy_keep(30);
        world.seed_var("hp", Value::Int(50)); // the gate-warden fight begins at 50 HP.

        let mut round = keep_round(3);
        // Three viewers back trade-blows (option 0) with total weight ≥ 3.
        round.ingest(super_chat("whale", "trade blows!!", 3_000_000)); // weight 3.
        round.ingest(chat("viewerA", "trade blows"));
        round.ingest(chat("viewerB", "press on")); // a dissenter.

        let cert = round
            .close_into_world(&world, &scene)
            .expect("the quorum-certified crowd winner fires a real world turn");

        assert_eq!(
            cert.command,
            Command::trade_blows(),
            "trade-blows certified + resolved"
        );
        assert_ne!(
            cert.receipt.turn_hash, [0u8; 32],
            "a genuine committed world turn"
        );
        assert_eq!(
            world.read_var("hp"),
            30,
            "the world resolved trade-blows (50 → 30)"
        );
        assert_eq!(round.landed().len(), 1, "the certified turn is recorded");
        assert_eq!(
            round.buffered(),
            0,
            "the window advanced (buffer reset) after close"
        );
    }

    #[test]
    fn sub_quorum_window_does_not_move_the_world() {
        let scene = keep_scene();
        let mut world = deploy_keep(31);
        world.seed_var("hp", Value::Int(50));

        let mut round = keep_round(5); // demand more weight than the crowd supplies.
        round.ingest(chat("A", "trade blows"));
        round.ingest(chat("B", "trade blows")); // total weight 2 < quorum 5.

        match round.close_into_world(&world, &scene) {
            Err(CollectiveError::BelowQuorum) => {}
            other => panic!("a sub-quorum window must not move the world, got {other:?}"),
        }
        assert_eq!(world.read_var("hp"), 50, "the world did not move");
        assert_eq!(
            round.buffered(),
            2,
            "a refused window is left intact for retry"
        );
    }

    #[test]
    fn no_votes_is_below_quorum() {
        let scene = keep_scene();
        let world = deploy_keep(32);
        let mut round = keep_round(1);
        round.ingest(chat("noise", "hello everyone")); // names no option.
        match round.close_into_world(&world, &scene) {
            Err(CollectiveError::BelowQuorum) => {}
            other => panic!("no option-naming votes ⇒ below quorum, got {other:?}"),
        }
    }
}
