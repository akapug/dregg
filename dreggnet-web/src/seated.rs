//! # `SeatedTug` — the seat-claiming adapter that makes multiway-tug PLAYABLE BY WEB USERS.
//!
//! [`dregg_multiway_tug::TugOffering`] identifies its two seats by fixed canonical strings
//! (`"multiway-tug:seat-A"` / `"…seat-B"`). A frontend user's [`DreggIdentity`] is a *derived* key
//! (the web's `blake3(user)` hex, the bot's `UserCipherclerk` pubkey) — never one of those strings —
//! so a browser user could open and watch a tug round but every play would be refused as
//! "actor holds no seat".
//!
//! This adapter is the seam, and it changes NOTHING in `dregg-multiway-tug`: it wraps the offering,
//! **claims a seat for the first two distinct identities that act** (seat A, then seat B), and
//! rewrites the actor to the canonical seat identity before delegating. A third identity is a
//! spectator (refused, nothing commits). `render_for` maps a viewer's identity to their claimed seat,
//! so the hidden-hand fog reaches the right browser: your cards, their commitment.
//!
//! (`dregg-automatafl`'s [`dregg_automatafl::AutomataflOffering`] claims seats natively, so it needs
//! no adapter — it is registered directly.)

use dregg_multiway_tug::{Player, TugOffering, TugSession};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

/// The multiway-tug offering with **web-claimable seats**.
pub struct SeatedTug {
    inner: TugOffering,
}

impl SeatedTug {
    /// A fresh seated tug offering.
    pub fn new() -> Self {
        SeatedTug { inner: TugOffering }
    }
}

impl Default for SeatedTug {
    fn default() -> Self {
        SeatedTug::new()
    }
}

/// A live tug round plus its seat claims (which frontend identity holds seat A / seat B).
pub struct SeatedTugSession {
    inner: TugSession,
    seats: [Option<DreggIdentity>; 2],
}

impl SeatedTugSession {
    /// The seat `who` holds, if they have claimed one.
    pub fn seat_of(&self, who: &DreggIdentity) -> Option<Player> {
        for p in [Player::A, Player::B] {
            if self.seats[p.idx()].as_ref() == Some(who) {
                return Some(p);
            }
        }
        None
    }

    /// The seat `who` holds, CLAIMING the first free one (A, then B) if they hold none. `None` when
    /// both seats are held by other identities (a spectator).
    fn claim(&mut self, who: &DreggIdentity) -> Option<Player> {
        if let Some(p) = self.seat_of(who) {
            return Some(p);
        }
        for p in [Player::A, Player::B] {
            if self.seats[p.idx()].is_none() {
                self.seats[p.idx()] = Some(who.clone());
                return Some(p);
            }
        }
        None
    }

    /// The seat a not-yet-seated viewer would CLAIM on their first act (first free seat, A then
    /// B), or `None` if both seats are already held (a true spectator).
    fn claimable_seat(&self) -> Option<Player> {
        [Player::A, Player::B]
            .into_iter()
            .find(|p| self.seats[p.idx()].is_none())
    }

    /// The live tug round (read-only).
    pub fn inner(&self) -> &TugSession {
        &self.inner
    }
}

impl Offering for SeatedTug {
    type Session = SeatedTugSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(SeatedTugSession {
            inner: self.inner.open(cfg)?,
            seats: [None, None],
        })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        self.inner.actions(&session.inner)
    }

    /// Claim a seat for `actor` (first-come: A, then B), then resolve the move on the REAL executor
    /// as that seat. A third identity is a spectator — refused, nothing commits.
    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        let Some(seat) = session.claim(&actor) else {
            return Outcome::Refused("both seats are taken — you are a spectator".to_string());
        };
        self.inner
            .advance(&mut session.inner, input, TugOffering::seat_identity(seat))
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        self.inner.verify(&session.inner)
    }

    fn render(&self, session: &Self::Session) -> Surface {
        self.inner.render(&session.inner)
    }

    /// The per-viewer surface — a claimed seat sees its OWN hand; anyone else sees the public fog.
    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        match session.seat_of(viewer) {
            Some(seat) => self
                .inner
                .render_for(&session.inner, &TugOffering::seat_identity(seat)),
            // A not-yet-seated viewer gets the OPENING-CLAIM surface for the seat they will claim
            // the instant they act (public fog + that seat's action menu) — so a fresh web visitor
            // has real controls to make the first move. Only a true spectator (both seats already
            // held) falls back to the viewer-blind public render.
            None => match session.claimable_seat() {
                Some(seat) => session.inner.surface_claim(seat),
                None => self.inner.render(&session.inner),
            },
        }
    }

    fn price(&self, input: &Action) -> RunCost {
        self.inner.price(input)
    }
}
