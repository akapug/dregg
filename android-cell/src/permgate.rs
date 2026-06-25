//! **Cap-gate the PERMISSION.** The confined Android app's runtime-permission model reforged
//! from an ambient "allow X to access Y?" dialog into a **visible cap-badge set** plus a
//! **receipted hand-over turn** — `GRAPHIDEOS.md §1` (the permission-model row) made real, in
//! the same shape as the proven [`crate::intentgate`] / [`crate::contentgate`] /
//! [`crate::organgate`] gates and the cockpit's [`powerbox`](../../starbridge-v2/src/powerbox.rs)
//! grant ceremony.
//!
//! # What Android does (the ambient mechanism deos replaces)
//!
//! Stock Android's runtime-permission model: an app declares `<uses-permission>` in its
//! manifest, then — for a *dangerous* permission — calls `requestPermissions(…)`, which raises
//! a system **dialog** ("Allow Maps to access this device's location?"). The user taps Allow /
//! Deny; the framework records a per-UID grant; the app later calls `checkSelfPermission`. A
//! *normal* permission (e.g. `INTERNET`) is granted **automatically at install**, no dialog. The
//! held set is **hidden in Settings** — a user inspecting an app sees a tree of toggles, not the
//! authority on the app's face. This is ambient: the grant is a UID-scoped flag, the dialog is a
//! modal interruption, and the standing authority is invisible until you go looking.
//!
//! # What graphideOS does (the cap-badge reforge)
//!
//! `GRAPHIDEOS.md §1`: *"**visible capabilities** — no dialogs; a cell's held caps render as
//! cap-badges on its card (lit = held, dim = ungranted, never hidden); a grant is a hand-over
//! sheet, itself a turn."* This module is that, in the same shape as the sibling gates:
//!
//! 1. **Authority is a visible badge set, never hidden in Settings.** [`PermBox::badges`]
//!    renders the WHOLE permission roster as a [`CapBadgeSet`]: each [`CapBadge`] is
//!    [`BadgeState::Lit`] (held) or [`BadgeState::Dim`] (not held), with a [`BadgeReason`]
//!    naming *why* — never hidden, never a toggle tree. The card shows its authority on its face.
//! 2. **An ungranted cap is simply absent — no ambient escalation.** A permission the app's
//!    manifest never declared has NO cap template ([`crate::appfactory`]), so it can never be
//!    held: its badge is [`BadgeReason::NotDeclared`] (dim, forever), and a hand-over of it is
//!    [`PermDecision::RefusedNotDeclared`]. Faithful to AOSP: you cannot grant a runtime
//!    permission the app did not declare.
//! 3. **A normal permission lights at install; a dangerous one waits for the hand-over.**
//!    Faithful AOSP protection levels ([`AndroidPermission::protection_level`]): a `Normal`
//!    permission (`INTERNET`) is held the moment the cell is minted ([`BadgeReason::HeldAtInstall`]);
//!    a `Dangerous`/`Signature` permission is declared-but-dim ([`BadgeReason::DeclaredNotGranted`])
//!    until the ceremony lights it ([`BadgeReason::HeldByGrant`]).
//! 4. **The grant is a receipted hand-over turn — the dialog, reforged.** [`PermBox::grant`]
//!    replaces `requestPermissions`'s modal dialog with a **powerbox-style hand-over**: a
//!    granting principal (the user/system, holding the device authority) confers the permission
//!    to the app-cell, and — exactly the powerbox's `mint_needs_held_factory` tooth — **it can
//!    only hand over an authority it actually holds** ([`PermDecision::RefusedNotHeldByGranter`]).
//!    Every decision leaves a content-addressed [`PermReceipt`], so the app's authority changes
//!    are auditable end to end exactly like the intent / content / service receipts. A
//!    [`PermBox::revoke`] (the Settings-revoke reforge) dims a runtime-granted badge again,
//!    receipted.
//!
//! # The depth (honest, like the sibling gates')
//!
//! This is the **authority-and-visibility** layer: the badge set is the faithful projection of
//! an app's held permissions, and the hand-over is the receipted cap transfer that replaces the
//! dialog. The remaining frontier — binding a grant to the cockpit's *real* [`World`] grant turn
//! (the cockpit powerbox already mints a verified [`Effect::GrantCapability`]; the device-side
//! wiring routes a dangerous-permission hand-over through that same executor so the permission
//! cap lands in the android-cell's c-list with a kernel [`TurnReceipt`]), and the in-runtime
//! `checkSelfPermission` interposition so the confined app's own permission checks read this
//! badge set rather than the framework's — are the same not-yet-claimed depth the sibling gates
//! name. What IS real today: the protection-level-faithful badge derivation + the declared /
//! held-by-granter teeth + the receipted hand-over + revoke, testable on any node with no device.
//!
//! [`World`]: ../../starbridge-v2/src/world.rs
//! [`Effect::GrantCapability`]: dregg_turn::action::Effect
//! [`TurnReceipt`]: dregg_turn::turn::TurnReceipt

use std::collections::BTreeSet;

use dregg_firmament::CellId;

use crate::appfactory::{AndroidManifest, AndroidPermission, ProtectionLevel};

/// Whether a permission's cap-badge is **lit** (the authority is held) or **dim** (not held) —
/// the visible-capabilities core: `GRAPHIDEOS.md §1`'s "lit = held, dim = ungranted, never
/// hidden". There is no third "hidden" state: every recognised permission is always *shown*,
/// the only question is lit vs dim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BadgeState {
    /// The app holds this authority — the badge is lit.
    Lit,
    /// The app does not hold this authority — the badge is dim (never hidden).
    Dim,
}

impl BadgeState {
    /// The glyph the cockpit renders (a lit ● vs a dim ○) — the one-glance authority read.
    pub fn glyph(&self) -> char {
        match self {
            BadgeState::Lit => '●',
            BadgeState::Dim => '○',
        }
    }

    pub fn is_lit(&self) -> bool {
        matches!(self, BadgeState::Lit)
    }
}

/// **Why a badge is lit or dim** — the faithful audit reason, never hidden. This is the
/// load-bearing distinction the AOSP Settings tree obscures: a dim badge can be *declared but
/// not yet granted* (a pending hand-over) or *never declared* (un-grantable, no ambient
/// escalation), and a lit badge can be *held at install* (a normal permission) or *handed over*
/// (a dangerous permission's receipted grant).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BadgeReason {
    /// Lit: a `Normal` permission auto-granted at install (declaring it sufficed; no dialog).
    HeldAtInstall,
    /// Lit: a `Dangerous`/`Signature` permission lit by a receipted hand-over ([`PermBox::grant`]).
    HeldByGrant,
    /// Dim: declared in the manifest but NOT yet handed over — a pending grant (the badge the
    /// user can light via the ceremony).
    DeclaredNotGranted,
    /// Dim: NOT declared in the manifest — there is no cap template for it, so it can never be
    /// held. The no-ambient-escalation property, made visible (forever dim).
    NotDeclared,
}

impl BadgeReason {
    /// The badge state this reason implies (lit for the two held reasons, dim otherwise).
    pub fn state(&self) -> BadgeState {
        match self {
            BadgeReason::HeldAtInstall | BadgeReason::HeldByGrant => BadgeState::Lit,
            BadgeReason::DeclaredNotGranted | BadgeReason::NotDeclared => BadgeState::Dim,
        }
    }

    fn label(&self) -> &'static str {
        match self {
            BadgeReason::HeldAtInstall => "held at install (normal permission)",
            BadgeReason::HeldByGrant => "held by hand-over",
            BadgeReason::DeclaredNotGranted => "declared, awaiting hand-over",
            BadgeReason::NotDeclared => "not declared (un-grantable, no ambient escalation)",
        }
    }
}

/// **One cap-badge — a permission shown on the android-cell's card, lit or dim.** The visible
/// unit `GRAPHIDEOS.md §1` describes; the cockpit renders a row of these on the app's card. It
/// carries the permission, its faithful AOSP [`ProtectionLevel`], the [`BadgeState`], and the
/// [`BadgeReason`] (the never-hidden "why").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapBadge {
    /// The permission this badge represents.
    pub permission: AndroidPermission,
    /// The faithful AOSP protection level (normal → install, dangerous/signature → hand-over).
    pub level: ProtectionLevel,
    /// Lit (held) or dim (not held).
    pub state: BadgeState,
    /// Why — the never-hidden audit reason.
    pub reason: BadgeReason,
}

impl CapBadge {
    /// A one-line status for the cockpit/audit: the glyph, the AOSP permission name, and why.
    pub fn status_line(&self) -> String {
        format!(
            "{} {} — {}",
            self.state.glyph(),
            self.permission.android_name(),
            self.reason.label()
        )
    }
}

/// **The cap-badge set rendered on an android-cell's card** — the WHOLE permission roster, each
/// lit or dim, never a hidden toggle tree. `GRAPHIDEOS.md §1`'s visible capabilities, made a
/// value. The roster is the standard permissions ([`AndroidPermission::all_standard`]) unioned
/// with any custom permissions the app declared, so a declared `Other(_)` permission is shown
/// too (and a never-declared standard permission is shown dim — the authority the app does NOT
/// hold is as visible as the authority it does).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapBadgeSet {
    /// The android-cell whose authority this badge set renders.
    pub cell: CellId,
    /// The badges, one per recognised permission, sorted by permission (a stable render order).
    pub badges: Vec<CapBadge>,
}

impl CapBadgeSet {
    /// The lit badges — the authorities the app actually holds.
    pub fn held(&self) -> impl Iterator<Item = &CapBadge> {
        self.badges.iter().filter(|b| b.state.is_lit())
    }

    /// The dim badges — the authorities the app does NOT hold (declared-pending or undeclared).
    pub fn unheld(&self) -> impl Iterator<Item = &CapBadge> {
        self.badges.iter().filter(|b| !b.state.is_lit())
    }

    /// Every badge line, flattened — the cockpit row text + the test assertion surface.
    pub fn all_text(&self) -> Vec<String> {
        self.badges.iter().map(CapBadge::status_line).collect()
    }
}

/// The outcomes a permission hand-over (or revoke) can reach — the permission-side analogue of
/// [`crate::organgate::ServiceDecision`], faithful to AOSP's runtime-permission model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PermDecision {
    /// The hand-over committed: a `Dangerous`/`Signature` permission the granter held was
    /// conferred to the app-cell, lighting its badge. The receipted replacement for the dialog.
    Granted {
        permission: AndroidPermission,
        app_cell: CellId,
    },
    /// A runtime-granted permission was revoked (the Settings-revoke reforge): the badge dims.
    Revoked {
        permission: AndroidPermission,
        app_cell: CellId,
    },
    /// A no-op hand-over: a `Normal` permission is ALREADY held at install (auto-granted) — no
    /// ceremony is needed, the badge is already lit.
    AlreadyHeldAtInstall { permission: AndroidPermission },
    /// REFUSED: the app's manifest never declared this permission — there is no cap template, so
    /// it can never be held (no ambient escalation; AOSP refuses to grant an undeclared
    /// permission too).
    RefusedNotDeclared { permission: AndroidPermission },
    /// REFUSED: the granting principal does not hold this authority to confer it — the
    /// powerbox's `mint_needs_held_factory`: you cannot hand over what you do not hold.
    RefusedNotHeldByGranter { permission: AndroidPermission },
    /// A no-op revoke: the permission was not runtime-granted (it was install-held or already
    /// dim), so there is nothing to revoke (a `Normal` permission cannot be runtime-revoked).
    NothingToRevoke { permission: AndroidPermission },
}

impl PermDecision {
    pub fn granted(&self) -> bool {
        matches!(self, PermDecision::Granted { .. })
    }
    pub fn revoked(&self) -> bool {
        matches!(self, PermDecision::Revoked { .. })
    }
    pub fn refused_not_declared(&self) -> bool {
        matches!(self, PermDecision::RefusedNotDeclared { .. })
    }
    pub fn refused_not_held_by_granter(&self) -> bool {
        matches!(self, PermDecision::RefusedNotHeldByGranter { .. })
    }
    pub fn already_held_at_install(&self) -> bool {
        matches!(self, PermDecision::AlreadyHeldAtInstall { .. })
    }

    fn tag(&self) -> &'static str {
        match self {
            PermDecision::Granted { .. } => "granted",
            PermDecision::Revoked { .. } => "revoked",
            PermDecision::AlreadyHeldAtInstall { .. } => "already-held-at-install",
            PermDecision::RefusedNotDeclared { .. } => "refused-not-declared",
            PermDecision::RefusedNotHeldByGranter { .. } => "refused-not-held-by-granter",
            PermDecision::NothingToRevoke { .. } => "nothing-to-revoke",
        }
    }

    fn permission(&self) -> &AndroidPermission {
        match self {
            PermDecision::Granted { permission, .. }
            | PermDecision::Revoked { permission, .. }
            | PermDecision::AlreadyHeldAtInstall { permission }
            | PermDecision::RefusedNotDeclared { permission }
            | PermDecision::RefusedNotHeldByGranter { permission }
            | PermDecision::NothingToRevoke { permission } => permission,
        }
    }
}

/// **The receipt left by a permission hand-over (or revoke).** Every decision produces one, so
/// the android-cell's authority changes are auditable end to end exactly like the intent /
/// content / service receipts — the receipted cap transfer that replaces AOSP's silent per-UID
/// grant flag. Content-addressed:
/// `decision_digest = blake3(principal ‖ app_cell ‖ permission ‖ outcome)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PermReceipt {
    /// The granting principal (the user/system that held the device authority).
    pub principal: CellId,
    /// The android-cell the hand-over targeted (the grantee).
    pub app_cell: CellId,
    /// The decision reached.
    pub decision: PermDecision,
    /// `blake3(…)[..32]` — the content-addressed witness a verifier reconstructs.
    pub decision_digest: [u8; 32],
}

impl PermReceipt {
    fn digest(principal: CellId, app_cell: CellId, decision: &PermDecision) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"graphideos-perm-handover-v1");
        h.update(principal.as_bytes());
        h.update(app_cell.as_bytes());
        h.update(decision.permission().android_name().as_bytes());
        h.update(b"\x00");
        h.update(decision.tag().as_bytes());
        *h.finalize().as_bytes()
    }

    /// A one-line audit truth for the cockpit status line — which outcome, named exactly.
    pub fn status_line(&self) -> String {
        let perm = self.decision.permission().android_name();
        match &self.decision {
            PermDecision::Granted { .. } => format!(
                "android-perm: ✔ {perm} HANDED OVER to the app as a receipted cap transfer — the badge lights (no runtime dialog)"
            ),
            PermDecision::Revoked { .. } => format!(
                "android-perm: ↩ {perm} REVOKED — the runtime grant is withdrawn, the badge dims (the Settings-revoke reforge)"
            ),
            PermDecision::AlreadyHeldAtInstall { .. } => format!(
                "android-perm: ● {perm} already held at install (a normal permission) — no hand-over needed"
            ),
            PermDecision::RefusedNotDeclared { .. } => format!(
                "android-perm: ✖ {perm} REFUSED — the app never declared it; there is no cap to hold (no ambient escalation)"
            ),
            PermDecision::RefusedNotHeldByGranter { .. } => format!(
                "android-perm: ✖ {perm} REFUSED — the granting principal does not hold this authority (you cannot hand over what you do not hold)"
            ),
            PermDecision::NothingToRevoke { .. } => format!(
                "android-perm: ◦ {perm} not runtime-granted — nothing to revoke"
            ),
        }
    }
}

/// **THE PERMISSION HAND-OVER SURFACE for one android-cell** — the trusted, powerbox-style
/// surface that renders the app's cap-badges AND mediates a receipted hand-over (the deos form
/// of the runtime-permission dialog). Holds the app's manifest (the declared set — what is even
/// grantable), the granting principal + the authorities it holds (the powerbox's "you can only
/// grant what you hold"), and the set of permissions runtime-granted so far. Holds NO ambient
/// authority: a hand-over the principal cannot back is refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PermBox {
    /// The android-cell this surface speaks for (the grantee).
    app_cell: CellId,
    /// The app's manifest — the declared permissions are the ONLY grantable ones.
    manifest: AndroidManifest,
    /// The granting principal (the user/system identity the hand-over grants FROM).
    principal: CellId,
    /// The authorities the principal actually holds and can confer (the powerbox ceiling: a
    /// hand-over of a permission not in here is `RefusedNotHeldByGranter`).
    principal_holds: BTreeSet<AndroidPermission>,
    /// The `Dangerous`/`Signature` permissions runtime-granted so far (the handed-over set). A
    /// `Normal` permission is never in here — it is held at install, not via the ceremony.
    granted: BTreeSet<AndroidPermission>,
}

impl PermBox {
    /// Build a permission hand-over surface for `app_cell` (born from `manifest`), granting from
    /// `principal` which holds `principal_holds`. No permission is runtime-granted yet — the
    /// dangerous badges start dim, the normal badges start lit (held at install).
    pub fn new(
        app_cell: CellId,
        manifest: AndroidManifest,
        principal: CellId,
        principal_holds: impl IntoIterator<Item = AndroidPermission>,
    ) -> Self {
        PermBox {
            app_cell,
            manifest,
            principal,
            principal_holds: principal_holds.into_iter().collect(),
            granted: BTreeSet::new(),
        }
    }

    /// The android-cell this surface speaks for.
    pub fn app_cell(&self) -> CellId {
        self.app_cell
    }

    /// Is this permission's badge currently LIT (the app holds the authority)? A `Normal`
    /// declared permission is always lit (held at install); a `Dangerous`/`Signature` declared
    /// permission is lit iff it was handed over; an undeclared permission is never lit.
    pub fn holds(&self, permission: &AndroidPermission) -> bool {
        self.manifest.declares(permission)
            && (permission.protection_level().held_at_install()
                || self.granted.contains(permission))
    }

    /// The [`BadgeReason`] for one permission — the faithful lit/dim "why".
    fn reason_for(&self, permission: &AndroidPermission) -> BadgeReason {
        if !self.manifest.declares(permission) {
            BadgeReason::NotDeclared
        } else if permission.protection_level().held_at_install() {
            BadgeReason::HeldAtInstall
        } else if self.granted.contains(permission) {
            BadgeReason::HeldByGrant
        } else {
            BadgeReason::DeclaredNotGranted
        }
    }

    fn badge_for(&self, permission: &AndroidPermission) -> CapBadge {
        let reason = self.reason_for(permission);
        CapBadge {
            permission: permission.clone(),
            level: permission.protection_level(),
            state: reason.state(),
            reason,
        }
    }

    /// **RENDER THE CAP-BADGE SET** — the WHOLE roster (standard permissions ∪ the app's
    /// declared custom permissions), each lit or dim. The visible-capabilities surface
    /// `GRAPHIDEOS.md §1` describes; the cockpit renders these as a row on the app's card.
    pub fn badges(&self) -> CapBadgeSet {
        let mut roster: BTreeSet<AndroidPermission> =
            AndroidPermission::all_standard().into_iter().collect();
        roster.extend(self.manifest.uses_permissions.iter().cloned());
        let badges = roster.iter().map(|p| self.badge_for(p)).collect();
        CapBadgeSet {
            cell: self.app_cell,
            badges,
        }
    }

    /// **THE HAND-OVER CEREMONY — grant `permission` to the app (the dialog, reforged).** The
    /// receipted cap transfer that replaces `requestPermissions`'s modal dialog. Faithful AOSP
    /// + powerbox teeth, fail-closed:
    ///
    /// 1. **Declared, or absent** — the manifest must declare `permission`; otherwise there is
    ///    no cap template ([`crate::appfactory`]) and it can never be held:
    ///    [`PermDecision::RefusedNotDeclared`] (no ambient escalation).
    /// 2. **Normal is already held** — a `Normal` permission was auto-granted at install; the
    ///    hand-over is a no-op [`PermDecision::AlreadyHeldAtInstall`] (the badge is already lit).
    /// 3. **The granter must hold it** — for a `Dangerous`/`Signature` permission, the principal
    ///    must hold the authority to confer it; otherwise [`PermDecision::RefusedNotHeldByGranter`]
    ///    (the powerbox's `mint_needs_held_factory`: you cannot hand over what you do not hold).
    ///
    /// On success the permission joins the runtime-granted set (its badge lights), and the
    /// decision leaves a [`PermReceipt`].
    pub fn grant(&mut self, permission: AndroidPermission) -> PermReceipt {
        let decision = if !self.manifest.declares(&permission) {
            PermDecision::RefusedNotDeclared { permission }
        } else if permission.protection_level().held_at_install() {
            PermDecision::AlreadyHeldAtInstall { permission }
        } else if !self.principal_holds.contains(&permission) {
            PermDecision::RefusedNotHeldByGranter { permission }
        } else {
            self.granted.insert(permission.clone());
            PermDecision::Granted {
                permission,
                app_cell: self.app_cell,
            }
        };
        self.receipt(decision)
    }

    /// **REVOKE a runtime-granted permission (the Settings-revoke reforge).** Withdraw a
    /// previously handed-over `Dangerous`/`Signature` permission — the badge dims again,
    /// receipted. A permission that was not runtime-granted (a `Normal` install-held one, or one
    /// already dim) is [`PermDecision::NothingToRevoke`]: AOSP cannot runtime-revoke a normal
    /// permission either.
    pub fn revoke(&mut self, permission: AndroidPermission) -> PermReceipt {
        let decision = if self.granted.remove(&permission) {
            PermDecision::Revoked {
                permission,
                app_cell: self.app_cell,
            }
        } else {
            PermDecision::NothingToRevoke { permission }
        };
        self.receipt(decision)
    }

    fn receipt(&self, decision: PermDecision) -> PermReceipt {
        let decision_digest = PermReceipt::digest(self.principal, self.app_cell, &decision);
        PermReceipt {
            principal: self.principal,
            app_cell: self.app_cell,
            decision,
            decision_digest,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::cell_seed;

    /// A maps app declaring INTERNET (normal) + ACCESS_FINE_LOCATION (dangerous), and a granting
    /// principal that holds the location authority. Returns `(permbox, app, principal)`.
    fn maps_permbox() -> (PermBox, CellId, CellId) {
        let app = cell_seed(0x51);
        let principal = cell_seed(0x01);
        let manifest = AndroidManifest::new(
            "com.example.maps",
            [
                AndroidPermission::Internet,
                AndroidPermission::AccessFineLocation,
            ],
        );
        let pb = PermBox::new(
            app,
            manifest,
            principal,
            [AndroidPermission::AccessFineLocation],
        );
        (pb, app, principal)
    }

    /// **THE VISIBLE-CAPABILITIES TEST: a normal declared permission lights at install; a
    /// dangerous declared one is dim (pending); an undeclared one is dim forever — never
    /// hidden.**
    #[test]
    fn badges_render_lit_dim_with_faithful_reasons() {
        let (pb, app, _principal) = maps_permbox();
        let set = pb.badges();
        assert_eq!(set.cell, app);

        let badge = |p: &AndroidPermission| {
            set.badges
                .iter()
                .find(|b| &b.permission == p)
                .unwrap_or_else(|| panic!("badge for {} is in the roster", p.android_name()))
        };

        // INTERNET (normal, declared) → lit, held at install.
        let net = badge(&AndroidPermission::Internet);
        assert_eq!(net.state, BadgeState::Lit);
        assert_eq!(net.reason, BadgeReason::HeldAtInstall);

        // ACCESS_FINE_LOCATION (dangerous, declared, not yet granted) → dim, pending.
        let loc = badge(&AndroidPermission::AccessFineLocation);
        assert_eq!(loc.state, BadgeState::Dim);
        assert_eq!(loc.reason, BadgeReason::DeclaredNotGranted);

        // CAMERA (dangerous, NOT declared) → dim, un-grantable (no ambient escalation).
        let cam = badge(&AndroidPermission::Camera);
        assert_eq!(cam.state, BadgeState::Dim);
        assert_eq!(cam.reason, BadgeReason::NotDeclared);

        // The whole standard roster is shown (nothing hidden).
        assert_eq!(set.badges.len(), AndroidPermission::all_standard().len());
        assert!(set.all_text().iter().any(|l| l.contains("INTERNET")));
    }

    /// **THE HAND-OVER TEST: granting a declared dangerous permission the principal holds lights
    /// the badge and leaves a receipt — the dialog, reforged into a receipted cap transfer.**
    #[test]
    fn hand_over_lights_a_dangerous_badge_and_receipts() {
        let (mut pb, app, principal) = maps_permbox();
        assert!(!pb.holds(&AndroidPermission::AccessFineLocation), "dim before");

        let receipt = pb.grant(AndroidPermission::AccessFineLocation);
        assert!(receipt.decision.granted());
        assert_eq!(receipt.principal, principal);
        assert_eq!(receipt.app_cell, app);
        assert!(receipt.status_line().contains("HANDED OVER"));
        assert_eq!(
            receipt.decision_digest,
            PermReceipt::digest(principal, app, &receipt.decision)
        );

        // The badge is now LIT, by hand-over.
        assert!(pb.holds(&AndroidPermission::AccessFineLocation));
        let loc = pb
            .badges()
            .badges
            .into_iter()
            .find(|b| b.permission == AndroidPermission::AccessFineLocation)
            .unwrap();
        assert_eq!(loc.state, BadgeState::Lit);
        assert_eq!(loc.reason, BadgeReason::HeldByGrant);
    }

    /// **THE NO-AMBIENT-ESCALATION TEST: a hand-over of a permission the app never declared is
    /// refused — there is no cap to hold (faithful AOSP: cannot grant an undeclared permission).**
    #[test]
    fn hand_over_of_an_undeclared_permission_is_refused() {
        let (mut pb, _app, _principal) = maps_permbox();
        // The maps app never declared CAMERA.
        let receipt = pb.grant(AndroidPermission::Camera);
        assert!(receipt.decision.refused_not_declared());
        assert!(!pb.holds(&AndroidPermission::Camera));
        assert!(receipt.status_line().contains("no ambient escalation"));
    }

    /// **THE POWERBOX TOOTH: a hand-over of a declared dangerous permission the GRANTER does not
    /// hold is refused — you cannot hand over what you do not hold (mint_needs_held_factory).**
    #[test]
    fn hand_over_the_granter_cannot_back_is_refused() {
        let app = cell_seed(0x52);
        let principal = cell_seed(0x01);
        // The app declares CAMERA, but the principal holds NO camera authority.
        let manifest = AndroidManifest::new("com.example.cam", [AndroidPermission::Camera]);
        let mut pb = PermBox::new(app, manifest, principal, []); // principal holds nothing

        let receipt = pb.grant(AndroidPermission::Camera);
        assert!(receipt.decision.refused_not_held_by_granter());
        assert!(!pb.holds(&AndroidPermission::Camera));
        assert!(
            receipt
                .status_line()
                .contains("cannot hand over what you do not hold")
        );
    }

    /// A normal permission is already held at install — the hand-over is a no-op (no dialog ever
    /// existed for a normal permission in AOSP either).
    #[test]
    fn hand_over_of_a_normal_permission_is_a_no_op() {
        let (mut pb, _app, _principal) = maps_permbox();
        assert!(pb.holds(&AndroidPermission::Internet), "lit at install");
        let receipt = pb.grant(AndroidPermission::Internet);
        assert!(receipt.decision.already_held_at_install());
        // Still lit, and NOT in the runtime-granted set (it is install-held).
        assert!(pb.holds(&AndroidPermission::Internet));
        assert!(!pb.granted.contains(&AndroidPermission::Internet));
    }

    /// **REVOKE (the Settings-revoke reforge): a runtime-granted badge dims again, receipted; a
    /// normal install-held permission cannot be runtime-revoked (nothing to revoke).**
    #[test]
    fn revoke_dims_a_runtime_grant_but_not_an_install_grant() {
        let (mut pb, _app, _principal) = maps_permbox();
        pb.grant(AndroidPermission::AccessFineLocation);
        assert!(pb.holds(&AndroidPermission::AccessFineLocation));

        // Revoke the runtime grant → dim again, receipted.
        let r = pb.revoke(AndroidPermission::AccessFineLocation);
        assert!(r.decision.revoked());
        assert!(!pb.holds(&AndroidPermission::AccessFineLocation));
        assert!(r.status_line().contains("REVOKED"));

        // A normal install-held permission has nothing to runtime-revoke.
        let r2 = pb.revoke(AndroidPermission::Internet);
        assert!(matches!(r2.decision, PermDecision::NothingToRevoke { .. }));
        assert!(pb.holds(&AndroidPermission::Internet), "still install-held");
    }

    /// A declared custom (`Other`) permission appears in the roster and fails closed to
    /// dangerous (declared-but-dim until an explicit hand-over).
    #[test]
    fn a_declared_custom_permission_is_shown_and_fails_closed() {
        let app = cell_seed(0x53);
        let principal = cell_seed(0x01);
        let custom = AndroidPermission::Other("com.example.SPECIAL".into());
        let manifest = AndroidManifest::new("com.example.app", [custom.clone()]);
        let pb = PermBox::new(app, manifest, principal, [custom.clone()]);

        let badge = pb
            .badges()
            .badges
            .into_iter()
            .find(|b| b.permission == custom)
            .expect("the declared custom permission is shown in the roster");
        assert_eq!(badge.level, ProtectionLevel::Dangerous, "custom fails closed");
        assert_eq!(badge.state, BadgeState::Dim, "dim until handed over");
        assert_eq!(badge.reason, BadgeReason::DeclaredNotGranted);
    }
}
