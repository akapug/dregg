//! The interactive **powerbox** (CapDesk) — the trusted designation flow.
//!
//! An ocap system has no ambient authority: a confined app-cell holds exactly the
//! capabilities in its c-list and *cannot name a peer or a resource it was never
//! granted*. So how does a user hand a freshly-launched app the authority to touch
//! one specific file / peer / cell — without that app getting the power to enumerate
//! or reach anything else? The **powerbox** (CapDesk / the "open file dialog as the
//! grant ceremony"): the app *requests* a capability it lacks; the **trusted UI**
//! (here the cockpit, the system's own principal — NOT the app) presents a picker of
//! the things the USER actually holds; the user **designates** one + the rights to
//! confer; and the trusted UI **mints a fresh, attenuated capability into the app's
//! c-list via a real grant turn**, handing back exactly that one designated cap. The
//! app never sees the namespace; it gets precisely what the user pointed at, narrowed.
//!
//! This is the user-facing flow over machinery this workspace already PROVES — it
//! reinvents none of it:
//!
//! - **The trusted UI holds NO ambient authority of its own.** The powerbox can only
//!   grant from the cockpit principal's OWN held caps — exactly the
//!   `starbridge_web_surface::delegate` thesis ("the delegate callback is the
//!   powerbox; holds no ambient authority"). [`Powerbox::present`] filters the picker
//!   to the principal's live c-list ([`dregg_cell::CapabilitySet::iter`]); a target
//!   the user does not hold simply *is not in the picker*.
//! - **You cannot grant what you do not hold** — the proven `mint_needs_held_factory`
//!   (`metatheory/Dregg2/Spec/Authority.lean`: "minting needs a held factory cap; the
//!   powerbox is not ambient"). The picker IS that fact made visible, and the real
//!   executor is the backstop: an over-grant from a principal that holds nothing is
//!   REJECTED by [`World::commit_turn`] (the same gate `world::over_grant_is_rejected`
//!   exercises), never by us.
//! - **The grant is strictly attenuating** — the conferred rights are `≤` the held
//!   rights (the proven `gen_conferral_is_attenuation`: a conferral's rights are `≤`
//!   the holder's). [`Powerbox::grant`] runs the GENUINE
//!   [`dregg_cell::is_attenuation`] (`granted ⊆ held`) before it ever builds a turn,
//!   so a request to confer MORE than the user holds is denied in-band (the anti-ghost
//!   tooth), and the executor's no-amplification rule is the second gate.
//! - **The mint is a real verified turn** — [`Powerbox::grant`] builds a real
//!   [`dregg_turn::Effect::GrantCapability`] from the principal to the app-cell and
//!   commits it through the embedded [`World`], so the conferral leaves the
//!   executor's own [`TurnReceipt`]. There is NO parallel grant path: the powerbox is
//!   the *designation UI*, the executor is the *authority*.
//!
//! gpui-free and `cargo test`-able: this is the pure flow model (like
//! [`crate::web_cells`] / [`crate::landing`]); the cockpit's POWERBOX tab renders
//! exactly these rows, so the `cargo test` that asserts the grant is real + attenuated
//! + held-bounded proves the flow without a GPU.

use dregg_cell::{is_attenuation, AuthRequired, CapabilityRef, CellId};
use dregg_turn::action::Effect;
use dregg_turn::turn::TurnReceipt;

use crate::reflect;
use crate::world::{CommitOutcome, World};

/// **A capability REQUEST from a confined app-cell.**
///
/// The app declares the *kind of thing* it needs to reach (a target cell) and the
/// authority it would like to confer — but it holds NO power to obtain it; it can
/// only *ask*. The powerbox + the user decide whether, and at what attenuation, to
/// satisfy the request. (The app does not even get to see whether the user holds the
/// target — only the trusted UI sees the namespace.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapabilityRequest {
    /// The app-cell making the request — the grantee a satisfied request mints a cap
    /// INTO. It is a real cell in the live ledger (a confined surface / app-as-cell).
    pub app_cell: CellId,
    /// A human reason the app gives ("needs to read your documents folder", "wants to
    /// message this peer") — shown in the trusted UI so the user designates knowingly.
    pub reason: String,
    /// The authority the app would *like* over whatever it is granted. The powerbox
    /// treats this as a CEILING REQUEST, never a command: the user may confer this or
    /// LESS, and the conferral can never exceed what the user holds (non-amp).
    pub desired_rights: AuthRequired,
}

impl CapabilityRequest {
    /// A request from `app_cell` for `desired_rights`, with a human `reason`.
    pub fn new(app_cell: CellId, reason: impl Into<String>, desired_rights: AuthRequired) -> Self {
        CapabilityRequest {
            app_cell,
            reason: reason.into(),
            desired_rights,
        }
    }
}

/// **One row in the powerbox picker — a target the USER actually holds.**
///
/// Built ONLY from the cockpit principal's live c-list
/// ([`dregg_cell::CapabilitySet::iter`]): a `GrantableTarget` exists iff the principal
/// holds a capability reaching `target`. This IS `mint_needs_held_factory` made
/// visible — a thing the user cannot reach never appears, so the user can only ever
/// designate from their own authority. `held_rights` is the authority the principal
/// holds over the target (the ceiling any conferral attenuates from).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrantableTarget {
    /// The cell the user holds a capability reaching — a candidate to hand the app.
    pub target: CellId,
    /// The principal's own slot holding the cap (the held-authority witness; the
    /// grant cites a fresh slot in the APP's c-list, but this proves the user holds it).
    pub held_slot: u32,
    /// The authority the principal holds over `target` — the CEILING. Any conferral is
    /// `≤` this by the real [`is_attenuation`]; the user cannot grant more than this.
    pub held_rights: AuthRequired,
    /// A short-hex display of the target id (the trusted-UI label — drawn from the
    /// ledger id, never an app-supplied name).
    pub label: String,
}

/// The outcome of a powerbox designation — either the trusted UI minted the cap (a
/// real verified turn) or it was DENIED (an amplification refusal, or the executor's
/// own guarantee firing). Both are first-class; the denial is the no-amplification
/// property visible.
#[derive(Debug)]
pub enum PowerboxOutcome {
    /// The powerbox MINTED a fresh attenuated cap into the app-cell's c-list via a
    /// real grant turn. Carries the executor's own [`TurnReceipt`] and the exact
    /// [`GrantedCap`] the app received (so the UI shows what was conferred, and a test
    /// asserts it is `⊆` the user's authority).
    Granted {
        receipt: TurnReceipt,
        conferred: GrantedCap,
    },
    /// The designation was DENIED — no cap was minted, the app got nothing. `reason`
    /// is the trusted-UI/executor explanation (an over-grant attempt, a no-such-target,
    /// or the executor's no-amplification gate firing).
    Denied { reason: String },
}

impl PowerboxOutcome {
    pub fn is_granted(&self) -> bool {
        matches!(self, PowerboxOutcome::Granted { .. })
    }

    /// The conferred cap, if the designation was granted.
    pub fn conferred(&self) -> Option<&GrantedCap> {
        match self {
            PowerboxOutcome::Granted { conferred, .. } => Some(conferred),
            PowerboxOutcome::Denied { .. } => None,
        }
    }
}

/// **The exact capability the app received** — the fresh, attenuated cap the grant
/// turn installed into the app-cell's c-list. The app gets PRECISELY this: one
/// designated target, narrowed to the conferred rights. It carries no view of the
/// namespace, no other target, nothing the user did not point at.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrantedCap {
    /// The app-cell the cap was minted into (the grantee).
    pub app_cell: CellId,
    /// The single target the cap reaches — exactly the one the user designated.
    pub target: CellId,
    /// The conferred authority — `≤` the user's held authority over the target (the
    /// real [`is_attenuation`] guaranteed it before the turn was built).
    pub conferred_rights: AuthRequired,
    /// The slot in the APP-cell's c-list the cap landed at.
    pub slot: u32,
}

/// **THE INTERACTIVE POWERBOX — the trusted designation surface.**
///
/// Built fresh from the live [`World`] + the cockpit principal (the system's own
/// identity). It holds NO authority of its own: every grant it can offer is sourced
/// from the principal's live c-list, so the powerbox is a *pure projection* of the
/// user's own authority into a designation UI. The cockpit renders exactly its rows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Powerbox {
    /// The cockpit's own principal — the USER identity the powerbox grants FROM. (The
    /// app never sees this; it only ever sees the one cap it is handed.)
    pub principal: CellId,
    /// The app-cell whose request the powerbox is mediating (the grantee).
    pub app_cell: CellId,
    /// The app's human-readable reason for the request (shown to the user).
    pub reason: String,
    /// The authority the app *asked* for (the ceiling request — the user may confer
    /// this or less).
    pub desired_rights: AuthRequired,
    /// **The picker** — every target the principal actually holds a cap reaching, the
    /// only things the user can designate. Filtered from the principal's live c-list:
    /// `mint_needs_held_factory` made visible.
    pub grantable: Vec<GrantableTarget>,
}

impl Powerbox {
    /// **Present the powerbox for an app's request.** Build the picker of GRANTABLE
    /// targets — every cell the cockpit `principal` actually holds a capability
    /// reaching, read from its LIVE c-list ([`dregg_cell::CapabilitySet::iter`]).
    ///
    /// A target the principal does not hold simply does not appear: the powerbox can
    /// offer ONLY the user's own authority (`mint_needs_held_factory` — the powerbox
    /// is not ambient). The app's `desired_rights` is carried as a ceiling request; it
    /// does not widen anything.
    pub fn present(world: &World, principal: CellId, request: &CapabilityRequest) -> Self {
        let grantable = grantable_targets(world, &principal);
        Powerbox {
            principal,
            app_cell: request.app_cell,
            reason: request.reason.clone(),
            desired_rights: request.desired_rights.clone(),
            grantable,
        }
    }

    /// Is `target` a thing the principal can actually grant (it is in the picker)?
    /// The structural precondition `mint_needs_held_factory` checks: a designation of
    /// a non-held target is refused before any turn.
    pub fn can_grant(&self, target: &CellId) -> Option<&GrantableTarget> {
        self.grantable.iter().find(|g| &g.target == target)
    }

    /// The widest authority the user may confer over `target` — its held rights (the
    /// conferral ceiling), or `None` if the user does not hold the target at all.
    pub fn ceiling_for(&self, target: &CellId) -> Option<&AuthRequired> {
        self.can_grant(target).map(|g| &g.held_rights)
    }

    /// **The user DESIGNATES `target` at `confer_rights` → MINT a fresh attenuated cap
    /// into the app-cell via a real grant turn.** This is the powerbox's whole point:
    /// the trusted UI hands the app exactly one designated, attenuated capability.
    ///
    /// The two safety gates, both REAL, both in-band:
    ///   1. **Held + non-amplifying (the powerbox's own pre-check):** the principal
    ///      must hold a cap reaching `target` (`mint_needs_held_factory`), and
    ///      `confer_rights` must be `⊆` the held rights — the GENUINE
    ///      [`is_attenuation`] (`gen_conferral_is_attenuation`: a conferral's rights
    ///      are `≤` the holder's). A designation of a non-held target, or a request to
    ///      confer MORE than the user holds, is [`PowerboxOutcome::Denied`] here,
    ///      before any turn is built (the anti-ghost tooth).
    ///   2. **The verified executor (the backstop):** the mint is a real
    ///      [`Effect::GrantCapability`] from `principal` to `app_cell`, committed
    ///      through [`World::commit_turn`]. The executor re-checks no-amplification
    ///      (its own `mint_needs_held_factory` gate); a turn that would amplify is
    ///      REJECTED, surfaced as [`PowerboxOutcome::Denied`] — never by us.
    ///
    /// On success the app's c-list gains EXACTLY one cap: `target`, narrowed to
    /// `confer_rights`. The receipt is the executor's own.
    pub fn grant(
        world: &mut World,
        principal: CellId,
        app_cell: CellId,
        target: CellId,
        confer_rights: AuthRequired,
    ) -> PowerboxOutcome {
        // (1a) mint_needs_held_factory: the principal must actually HOLD a cap
        //      reaching `target`. The picker is built from exactly this; re-check it
        //      at grant time so a stale designation can't slip a non-held target.
        let held = match held_cap_reaching(world, &principal, &target) {
            Some(h) => h,
            None => {
                return PowerboxOutcome::Denied {
                    reason: format!(
                        "the powerbox holds no authority reaching {} — it cannot grant what the user does not hold (mint_needs_held_factory)",
                        reflect::short_hex(&target.0)
                    ),
                };
            }
        };

        // (1b) gen_conferral_is_attenuation: the conferred rights must be ⊆ the held
        //      rights. The GENUINE is_attenuation gate (granted ⊆ held). A request to
        //      confer MORE than the user holds is refused IN-BAND (anti-ghost), before
        //      any turn — the powerbox never amplifies.
        if !is_attenuation(&held.permissions, &confer_rights) {
            return PowerboxOutcome::Denied {
                reason: format!(
                    "conferring {:?} would AMPLIFY the user's {:?} authority over {} — the powerbox is attenuation-only (gen_conferral_is_attenuation)",
                    confer_rights,
                    held.permissions,
                    reflect::short_hex(&target.0)
                ),
            };
        }

        // (2) THE REAL MINT: a genuine Effect::GrantCapability from the principal to
        //     the app-cell, attenuated to confer_rights, into a fresh slot in the
        //     APP's c-list. The executor is the authority; we only designate.
        let slot = next_free_slot(world, &app_cell);
        let effect = Effect::GrantCapability {
            from: principal,
            to: app_cell,
            cap: CapabilityRef {
                target,
                slot,
                permissions: confer_rights.clone(),
                breadstuff: None,
                expires_at: None,
                allowed_effects: None,
                stored_epoch: None,
            },
        };
        let turn = world.turn(principal, vec![effect]);
        match world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => PowerboxOutcome::Granted {
                receipt,
                conferred: GrantedCap {
                    app_cell,
                    target,
                    conferred_rights: confer_rights,
                    slot,
                },
            },
            // The executor's OWN no-amplification / authority gate fired — surfaced,
            // never hidden. The user's designation conferred NOTHING.
            CommitOutcome::Rejected { reason, .. } => PowerboxOutcome::Denied { reason },
        }
    }

    /// Every line of real text the powerbox renders, flattened — used by tests to
    /// assert the trusted UI speaks real text about the app's request + the picker of
    /// the user's own grantable targets (the exact gpui tree content).
    pub fn all_text(&self) -> Vec<String> {
        let mut out = Vec::new();
        out.push(format!(
            "POWERBOX — app {} requests a capability it lacks",
            reflect::short_hex(&self.app_cell.0)
        ));
        out.push(format!("reason: {}", self.reason));
        out.push(format!(
            "granting principal (you): {} · app asked for {:?}",
            reflect::short_hex(&self.principal.0),
            self.desired_rights
        ));
        out.push(format!(
            "designate a target you hold ({} grantable — you cannot grant what you don't hold):",
            self.grantable.len()
        ));
        for g in &self.grantable {
            out.push(format!(
                "· {} (you hold {:?} at slot {}) → grant attenuated",
                g.label, g.held_rights, g.held_slot
            ));
        }
        if self.grantable.is_empty() {
            out.push(
                "(you hold no grantable targets — the powerbox can confer nothing, by construction)"
                    .to_string(),
            );
        }
        out
    }
}

// ── the model-building helpers (pure; each names the real cap primitive) ──

/// Build the picker: every distinct target the `principal` holds a cap reaching, read
/// from its LIVE c-list. The structural realization of `mint_needs_held_factory` — a
/// target the principal does not hold is simply absent.
fn grantable_targets(world: &World, principal: &CellId) -> Vec<GrantableTarget> {
    let mut out: Vec<GrantableTarget> = Vec::new();
    let Some(cell) = world.ledger().get(principal) else {
        return out;
    };
    for cap in cell.capabilities.iter() {
        // A principal would never hand an app a cap reaching the principal's own self
        // (a self-grant is meaningless designation); skip it so the picker shows real
        // grantable peers/resources.
        if cap.target == *principal {
            continue;
        }
        // One row per distinct target; if the user holds several caps to the same
        // target, surface the WIDEST (the broadest ceiling the user could confer).
        match out.iter_mut().find(|g| g.target == cap.target) {
            Some(existing) => {
                if is_attenuation(&cap.permissions, &existing.held_rights) {
                    // existing ⊆ cap → cap is wider; promote the ceiling to cap.
                    existing.held_rights = cap.permissions.clone();
                    existing.held_slot = cap.slot;
                }
            }
            None => out.push(GrantableTarget {
                target: cap.target,
                held_slot: cap.slot,
                held_rights: cap.permissions.clone(),
                label: format!("dregg://{}", reflect::short_hex(&cap.target.0)),
            }),
        }
    }
    out
}

/// The principal's held capability reaching `target` (the WIDEST, if several), or
/// `None` if the principal holds none — the `mint_needs_held_factory` precondition,
/// re-checked at grant time so the grant cannot outrun the picker.
fn held_cap_reaching(world: &World, principal: &CellId, target: &CellId) -> Option<CapabilityRef> {
    let cell = world.ledger().get(principal)?;
    let mut widest: Option<CapabilityRef> = None;
    for cap in cell.capabilities.iter() {
        if &cap.target == target {
            match &widest {
                Some(w) if is_attenuation(&cap.permissions, &w.permissions) => {}
                _ => widest = Some(cap.clone()),
            }
        }
    }
    widest
}

/// The next free slot in `app_cell`'s c-list to mint the granted cap into (one past
/// the highest occupied slot, so a fresh grant never collides with an existing cap).
/// If the app does not exist yet, slot 0 is the natural first slot (the executor
/// rejects a grant to a missing cell anyway — that path surfaces as a Denied).
fn next_free_slot(world: &World, app_cell: &CellId) -> u32 {
    match world.ledger().get(app_cell) {
        Some(cell) => cell
            .capabilities
            .iter()
            .map(|c| c.slot)
            .max()
            .map(|m| m + 1)
            .unwrap_or(0),
        None => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::World;

    /// A demo world tailored to the powerbox flow: a USER principal that already holds
    /// caps to two resources (a `docs` cell + a `peer` cell), and a fresh confined APP
    /// cell that holds NOTHING. The grant ceilings differ (Either over docs, Signature
    /// over peer) so the attenuation lattice is a real witness, not a coincidence.
    ///
    /// Returns `(world, principal, app, docs, peer)`.
    fn powerbox_world() -> (World, CellId, CellId, CellId, CellId) {
        use crate::world::make_open_cell;

        let mut w = World::new();
        // The two resources the user holds authority over.
        let docs = w.genesis_cell(0xD0, 0);
        let peer = w.genesis_cell(0xBE, 0);
        // The confined app-cell — holds no caps (a freshly-launched app-as-cell).
        let app = w.genesis_cell(0xA9, 0);

        // The USER principal, built DIRECTLY holding two real caps at DISTINCT rights:
        // full (None) over `docs` and narrowed (Signature) over `peer`. These are the
        // user's genuine held authorities (the c-list the executor checks against); the
        // distinct ceilings make the attenuation lattice a real witness. `grant` takes
        // the rights directly, so no test-only mutator is needed — the principal simply
        // IS a cell holding exactly these caps, installed via the genesis path.
        let mut principal_cell = make_open_cell(0x55, 0);
        principal_cell
            .capabilities
            .grant(docs, AuthRequired::None)
            .expect("fresh c-list slot for docs");
        principal_cell
            .capabilities
            .grant(peer, AuthRequired::Signature)
            .expect("fresh c-list slot for peer");
        let principal = w.genesis_install(principal_cell);

        (w, principal, app, docs, peer)
    }

    #[test]
    fn the_picker_shows_only_targets_the_user_actually_holds() {
        // mint_needs_held_factory, made visible: the picker contains EXACTLY the
        // targets the principal holds a cap reaching (docs + peer), and nothing else.
        // A confined app that holds nothing would present an EMPTY powerbox.
        let (world, principal, app, docs, peer) = powerbox_world();
        let request = CapabilityRequest::new(app, "needs to read your documents", AuthRequired::Either);
        let pb = Powerbox::present(&world, principal, &request);

        let targets: Vec<CellId> = pb.grantable.iter().map(|g| g.target).collect();
        assert!(targets.contains(&docs), "the user holds docs → it is grantable");
        assert!(targets.contains(&peer), "the user holds peer → it is grantable");
        assert_eq!(pb.grantable.len(), 2, "exactly the two held targets, nothing the user doesn't hold");

        // The ceilings are the user's REAL held rights: full (None) over docs, narrowed
        // (Signature) over peer — the picker reflects the user's own authority, never
        // amplifies it.
        assert_eq!(pb.ceiling_for(&docs), Some(&AuthRequired::None));
        assert_eq!(pb.ceiling_for(&peer), Some(&AuthRequired::Signature));

        // A target the user does NOT hold is not grantable (cannot be designated).
        let unheld = world.ledger().iter().map(|(id, _)| *id).find(|id| {
            *id != docs && *id != peer && *id != principal && *id != app
        });
        if let Some(unheld) = unheld {
            assert!(pb.can_grant(&unheld).is_none(), "an unheld target is not in the picker");
        }
    }

    #[test]
    fn a_confined_app_with_no_held_caps_presents_an_empty_powerbox() {
        // The structural floor: a principal that holds NOTHING can grant nothing — the
        // powerbox is empty, by construction (mint_needs_held_factory). The app gets a
        // picker it cannot designate from, never a capability.
        let (world, _principal, app, _docs, _peer) = powerbox_world();
        let request = CapabilityRequest::new(app, "wants authority", AuthRequired::None);
        // `app` itself holds no caps — present the powerbox AS the app (a principal
        // with an empty c-list).
        let pb = Powerbox::present(&world, app, &request);
        assert!(pb.grantable.is_empty(), "an empty-c-list principal has nothing to grant");
        assert!(pb.all_text().iter().any(|l| l.contains("can confer nothing")));
    }

    #[test]
    fn designating_a_held_target_mints_a_real_attenuated_cap_into_the_app() {
        // THE FLOW: the user designates `docs` (which they hold at None) and confers a
        // narrower Signature cap → the powerbox mints a REAL grant turn into the app's
        // c-list. The app, which held nothing, now holds exactly ONE cap: docs at
        // Signature. Nothing else.
        let (mut world, principal, app, docs, _peer) = powerbox_world();
        assert!(
            !world.ledger().get(&app).unwrap().capabilities.has_access(&docs),
            "precondition: the app does NOT reach docs before the grant"
        );
        let receipts_before = world.receipts().len();

        let outcome = Powerbox::grant(&mut world, principal, app, docs, AuthRequired::Signature);
        let conferred = outcome
            .conferred()
            .expect("designating a held target with an attenuated right grants")
            .clone();

        // The app received EXACTLY the designated, attenuated cap — one target, narrowed.
        assert_eq!(conferred.app_cell, app);
        assert_eq!(conferred.target, docs);
        assert_eq!(conferred.conferred_rights, AuthRequired::Signature);

        // It is a REAL verified turn: the executor's own receipt landed on the chain.
        assert!(outcome.is_granted());
        assert_eq!(world.receipts().len(), receipts_before + 1, "the grant added a real receipt");

        // The app's LIVE c-list now reaches docs (the cap was minted in by the executor).
        let app_cell = world.ledger().get(&app).unwrap();
        assert!(app_cell.capabilities.has_access(&docs), "the app now reaches docs via the granted cap");
        // …and the granted cap carries the ATTENUATED rights, not the user's wider ones.
        let granted = app_cell
            .capabilities
            .iter()
            .find(|c| c.target == docs)
            .expect("the granted cap is in the app's c-list");
        assert_eq!(
            granted.permissions,
            AuthRequired::Signature,
            "the app holds the ATTENUATED right, never the user's wider authority (no amplification)"
        );
    }

    #[test]
    fn the_app_cannot_obtain_a_target_the_user_does_not_hold() {
        // The keystone: designating a target the principal does NOT hold is denied
        // before any turn — the powerbox cannot grant what the user does not hold
        // (mint_needs_held_factory). The app gets nothing.
        let (mut world, principal, app, _docs, _peer) = powerbox_world();
        // A fresh cell the principal holds NO cap reaching.
        let unheld = world.genesis_cell(0x77, 0);
        let receipts_before = world.receipts().len();

        let outcome = Powerbox::grant(&mut world, principal, app, unheld, AuthRequired::Signature);
        assert!(!outcome.is_granted(), "an unheld target cannot be designated");
        match outcome {
            PowerboxOutcome::Denied { reason } => {
                assert!(
                    reason.contains("mint_needs_held_factory") || reason.contains("does not hold"),
                    "the denial cites the held-authority requirement, got: {reason}"
                );
            }
            PowerboxOutcome::Granted { .. } => panic!("must be denied"),
        }
        // No turn ran; the app got nothing.
        assert_eq!(world.receipts().len(), receipts_before, "a denied designation runs no turn");
        assert!(
            !world.ledger().get(&app).unwrap().capabilities.has_access(&unheld),
            "the app does not reach the unheld target"
        );
    }

    #[test]
    fn the_powerbox_refuses_to_amplify_beyond_what_the_user_holds() {
        // gen_conferral_is_attenuation, in-band: the user holds only Signature over
        // `peer`; designating peer at the WIDER None (full authority) would amplify —
        // refused before any turn, the anti-ghost tooth. The app gets nothing.
        let (mut world, principal, app, _docs, peer) = powerbox_world();
        let receipts_before = world.receipts().len();

        // The user holds Signature over peer; confer None (wider) → amplification.
        let outcome = Powerbox::grant(&mut world, principal, app, peer, AuthRequired::None);
        assert!(!outcome.is_granted(), "conferring more than the user holds must be refused");
        match outcome {
            PowerboxOutcome::Denied { reason } => assert!(
                reason.contains("AMPLIFY") || reason.contains("attenuation"),
                "the denial cites amplification, got: {reason}"
            ),
            PowerboxOutcome::Granted { .. } => panic!("must be denied"),
        }
        assert_eq!(world.receipts().len(), receipts_before, "an amplifying designation runs no turn");

        // But conferring AT or BELOW the held ceiling (Signature) is fine — the same
        // target, the legitimate (non-amplifying) grant succeeds.
        let ok = Powerbox::grant(&mut world, principal, app, peer, AuthRequired::Signature);
        assert!(ok.is_granted(), "conferring ⊆ the held authority is a legitimate grant");
    }

    #[test]
    fn the_executor_is_the_backstop_for_a_principal_holding_nothing() {
        // Even if a UI bug let a designation through, the EXECUTOR is the second gate:
        // a grant FROM a principal that holds no cap reaching the target is rejected by
        // the real executor (its own mint_needs_held_factory / no-amplification rule),
        // exactly as `world::over_grant_is_rejected_by_the_real_executor`. We exercise
        // the executor path directly: a principal with an empty c-list cannot grant.
        let mut world = World::new();
        let empty_principal = world.genesis_cell(0x01, 0);
        let app = world.genesis_cell(0x02, 0);
        let target = world.genesis_cell(0x03, 0);

        // The powerbox's own pre-check denies this (empty picker) …
        let outcome = Powerbox::grant(&mut world, empty_principal, app, target, AuthRequired::Signature);
        assert!(!outcome.is_granted(), "a principal holding nothing grants nothing");

        // … and the raw executor agrees: a hand-built grant from the empty principal is
        // rejected (the backstop), so even bypassing the powerbox cannot amplify.
        let raw = world.turn(
            empty_principal,
            vec![crate::world::grant_capability(empty_principal, app, target, 0)],
        );
        assert!(
            !world.commit_turn(raw).is_committed(),
            "the executor rejects a grant from a principal that holds no reaching cap"
        );
    }
}
