//! # `PartyOffering` — a **playable roster + fork-ballot** over [`dreggnet_party`].
//!
//! A first-class party: a fixed roster of seated identities sharing ONE run, each seat's held
//! capabilities ARE its role. This Offering surfaces the two play motions: a seat **acts in its
//! role** (a real committed turn on the shared world — a move OUTSIDE the seat's role is a real
//! `CapabilityNotHeld` refusal, "nobody plays your seat"), and the party **resolves a fork** through
//! the real quorum-certified vote engine via [`advance_collective`](Offering::advance_collective) —
//! the crowd's [`CollectiveDecision`] drives a genuine signed party ballot into the shared world.
//!
//! ## Honest scope
//!
//! This is a *playable* Offering. [`advance`] fires a real seated move ([`Party::act_in_role`] →
//! [`Outcome::Landed`]); a cross-role misplay is a real executor refusal. [`advance_collective`]
//! opens a real [`PartyFork`], casts a quorum of the seats' signed ballots for the crowd's winning
//! option, and resolves the certified shared move into the party world (a real committed turn) —
//! while a solo [`advance`] of a fork is refused (a fork needs the crowd). The [`Outcome::Landed`]
//! receipt carries the genuine committed turn hash; [`dreggnet_party`] folds its full [`TurnReceipt`]
//! to a turn-hash through its public [`ActOutcome`]/[`ForkResolution`] API, so the surface carries the
//! real receipt id and leaves the unexposed chain fields default — surfacing the full receipt is a
//! one-line named-next in [`dreggnet_party`]. NAMED NEXT: role ability kits + the on-ledger loot
//! split as affordances (the `dreggnet_party` residuals).

use dregg_app_framework::TurnReceipt;
use dreggnet_offerings::{
    Action, CollectiveDecision, DreggIdentity, Offering, OfferingError, Outcome, RunCost,
    SessionConfig, Surface, VerifyReport,
};
use dreggnet_party::{ActOutcome, FOCUS_BUDGET, Party, PartyMove, ROLE_SLOT, Role};

use crate::{action_menu, menu, pill, row, section, text};
use deos_view::ViewNode;

/// The affordance verb a seat fires to act in its own role (`arg` = the seat index).
pub const TURN_ACT: &str = "act";
/// The affordance verb that fires a seat's move OUTSIDE its role (`arg` = the seat index) — the
/// forge probe: a real `CapabilityNotHeld` refusal ("nobody plays your seat").
pub const TURN_MISPLAY: &str = "misplay";
/// The affordance verb that resolves a fork (`arg` = the winning option index). Collective:
/// [`advance_collective`](Offering::advance_collective) casts a quorum of signed ballots for it.
pub const TURN_FORK: &str = "fork";

/// The two fork paths the party can take (label + the value written into the fork gate).
fn fork_options() -> Vec<(String, u64)> {
    vec![
        ("Left, the sunken stair".to_string(), 1),
        ("Right, the warded arch".to_string(), 2),
    ]
}

/// **A live party session** over the real mustered [`Party`] — the shared world, the committed-turn
/// count, and the last resolved fork's label (for the render).
pub struct PartySession {
    party: Party,
    turns: usize,
    last_fork: Option<String>,
}

impl PartySession {
    /// The party's seat count.
    pub fn seat_count(&self) -> usize {
        self.party.seat_count()
    }
    /// The fork-ballot quorum threshold.
    pub fn quorum(&self) -> u64 {
        self.party.quorum()
    }
    /// The party's total focus spent so far.
    pub fn focus_spent(&self) -> u64 {
        self.party.focus_spent()
    }
    /// The number of committed party turns (seated moves + resolved forks).
    pub fn turns(&self) -> usize {
        self.turns
    }
    /// The last resolved fork's label, if any.
    pub fn last_fork(&self) -> Option<&str> {
        self.last_fork.as_deref()
    }

    /// Whether seat `idx` has landed its role move (its role cell is marked on the shared ledger).
    fn seat_acted(&self, idx: usize) -> bool {
        if idx >= self.party.seat_count() {
            return false;
        }
        let l = self.party.layout();
        // The cell each role acts on (its role-target in the shared layout).
        let cell = match self.party.seat(idx).role() {
            Role::Tank => l.front,
            Role::Scout => l.lock,
            Role::Mage => l.ward,
            Role::Healer => l.rally,
        };
        self.party.read_field(cell, ROLE_SLOT) != 0
    }
}

/// **The party offering** — a stateless factory over the party substrate. Each
/// [`open`](Offering::open) musters a fresh canonical four-seat party.
pub struct PartyOffering;

impl PartyOffering {
    /// A fresh party offering.
    pub fn new() -> Self {
        PartyOffering
    }

    /// Fold a real [`ActOutcome`] into an [`Outcome`], counting a committed turn.
    fn fold_act(s: &mut PartySession, outcome: ActOutcome) -> Outcome {
        match outcome {
            ActOutcome::Committed { receipt } => {
                s.turns += 1;
                Outcome::Landed {
                    receipt: TurnReceipt {
                        turn_hash: receipt,
                        ..Default::default()
                    },
                    ended: false,
                }
            }
            ActOutcome::Refused { reason } => Outcome::Refused(reason),
        }
    }

    fn do_act(&self, s: &mut PartySession, idx: usize) -> Outcome {
        if idx >= s.party.seat_count() {
            return Outcome::Refused(format!("no seat #{idx} in the roster"));
        }
        let outcome = s.party.act_in_role(idx);
        Self::fold_act(s, outcome)
    }

    fn do_misplay(&self, s: &mut PartySession, idx: usize) -> Outcome {
        if idx >= s.party.seat_count() {
            return Outcome::Refused(format!("no seat #{idx} in the roster"));
        }
        // A move the seat holds NO cap for (a cross-role forge) — a real executor refusal.
        let wrong = if s.party.seat(idx).role() == Role::Tank {
            PartyMove::CastWard
        } else {
            PartyMove::GuardFront
        };
        let outcome = s.party.act(idx, wrong);
        Self::fold_act(s, outcome)
    }
}

impl Default for PartyOffering {
    fn default() -> Self {
        PartyOffering::new()
    }
}

impl Offering for PartyOffering {
    type Session = PartySession;

    fn open(&self, _cfg: SessionConfig) -> Result<PartySession, OfferingError> {
        Ok(PartySession {
            party: Party::muster(),
            turns: 0,
            last_fork: None,
        })
    }

    fn actions(&self, s: &PartySession) -> Vec<Action> {
        let mut out = Vec::new();
        for (i, seat) in s.party.seats().iter().enumerate() {
            out.push(Action::new(
                format!("{} acts ({})", seat.name(), seat.role().name()),
                TURN_ACT,
                i as i64,
                !s.seat_acted(i),
            ));
        }
        for (i, (label, _)) in fork_options().into_iter().enumerate() {
            out.push(Action::new(
                format!("Fork: {label}"),
                TURN_FORK,
                i as i64,
                true,
            ));
        }
        out
    }

    fn advance(&self, s: &mut PartySession, input: Action, _actor: DreggIdentity) -> Outcome {
        let idx = input.arg.max(0) as usize;
        match input.turn.as_str() {
            TURN_ACT => self.do_act(s, idx),
            TURN_MISPLAY => self.do_misplay(s, idx),
            TURN_FORK => Outcome::Refused(
                "a fork needs a collective decision — open it with advance_collective".into(),
            ),
            other => Outcome::Refused(format!("unknown party affordance: {other}")),
        }
    }

    /// **The collective path** — resolve a fork the crowd decided. Opens a real [`PartyFork`], casts
    /// a quorum of the seats' OWN signed ballots for the winning option, and resolves the certified
    /// shared move into the party world (a real committed turn). A non-fork turn delegates to the
    /// single-actor [`advance`] attributed to the decision's carrier (the trait default).
    fn advance_collective(
        &self,
        s: &mut PartySession,
        input: Action,
        decision: CollectiveDecision,
    ) -> Outcome {
        if input.turn != TURN_FORK {
            return self.advance(s, input, decision.carrier);
        }
        let options = fork_options();
        let opt = (decision.tally.winner.max(0) as usize).min(options.len().saturating_sub(1));

        let mut fork = match s.party.open_fork("The passage forks", options) {
            Ok(f) => f,
            Err(e) => return Outcome::Refused(format!("the fork could not open: {e}")),
        };
        // Cast a quorum of the seats' genuine custody-signed ballots for the crowd's winner.
        let quorum = s.party.quorum() as usize;
        let seats = s.party.seat_count();
        for seat in 0..quorum.min(seats) {
            let ballot = s.party.sign_ballot(&fork, seat, opt);
            if let Err(e) = fork.cast(&ballot) {
                return Outcome::Refused(format!("a party ballot was refused: {e}"));
            }
        }
        match fork.resolve_into(&mut s.party) {
            Ok(res) => {
                s.turns += 1;
                s.last_fork = Some(res.label.clone());
                Outcome::Landed {
                    receipt: TurnReceipt {
                        turn_hash: res.receipt,
                        ..Default::default()
                    },
                    ended: false,
                }
            }
            Err(e) => Outcome::Refused(format!("the fork did not resolve: {e}")),
        }
    }

    /// Re-verify the party world is intact — every seat + shared cell is a real cell in the ONE
    /// shared ledger.
    fn verify(&self, s: &PartySession) -> VerifyReport {
        for seat in s.party.seats() {
            if s.party.world().ledger().get(&seat.cell()).is_none() {
                return VerifyReport::broken(
                    s.turns,
                    format!("seat `{}` has no cell in the shared ledger", seat.name()),
                );
            }
        }
        VerifyReport::ok(s.turns)
    }

    fn render(&self, s: &PartySession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();

        children.push(section(
            "Party",
            "muted",
            vec![text(format!(
                "{} seats · quorum {} · focus {}/{} · turns {}",
                s.seat_count(),
                s.quorum(),
                s.focus_spent(),
                FOCUS_BUDGET,
                s.turns,
            ))],
        ));

        // The roster — a Table of seats with role + an acted pill (read off the shared ledger).
        let mut rows: Vec<ViewNode> = vec![row(vec![text("Seat"), text("Role"), text("Acted")])];
        for (i, seat) in s.party.seats().iter().enumerate() {
            let acted = s.seat_acted(i);
            rows.push(row(vec![
                text(seat.name()),
                pill(seat.role().name(), "accent"),
                pill(
                    if acted { "acted" } else { "ready" },
                    if acted { "good" } else { "muted" },
                ),
            ]));
        }
        children.push(section("Roster", "accent", vec![ViewNode::Table(rows)]));

        // The fork ballot + seat actions as a Section{Menu}.
        let acts = action_menu(self.actions(s));
        if !acts.is_empty() {
            children.push(section("Actions", "accent", vec![menu(acts)]));
        }

        if let Some(fork) = s.last_fork() {
            children.push(section(
                "Resolved fork",
                "genuine",
                vec![text(format!("the party took: {fork}"))],
            ));
        }

        children.push(section(
            "Verified turns",
            "genuine",
            vec![text(s.turns.to_string())],
        ));

        Surface(section(
            "DreggNet Party — a seated roster + a fork ballot",
            "accent",
            children,
        ))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}
