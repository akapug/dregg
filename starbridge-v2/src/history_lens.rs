//! # The HISTORY / UNDO lens — per-cell reversibility, welded.
//!
//! The cockpit's `MoldableLens::History` was an honest `weld_pending` placeholder
//! that said it would light up the moment the reversibility weld landed. That weld
//! landed (`dregg_turn::reversible`, M-REV-0 / `docs/deos/FIRST-CLASS-REVERSIBILITY.md`).
//! This lights it up — the per-cell, lens-shaped view of the same reversibility the
//! cockpit's REPLAY tab time-travels for the WHOLE image.
//!
//! For the focused cell it computes, off the REAL organ over the LIVE ledger, the
//! **reversibility map**: each kind of change to this cell, classified by
//! `Effect::invert` into the three honest tiers —
//!
//! - **Clean** — the inverse is a single forward effect (a reverse Transfer, a
//!   grant's revoke, a seal's unseal); reverses anywhere.
//! - **Contextual** — the inverse needs the pre-image (a SetField's old value),
//!   held by the producing history; reverses against it.
//! - **Committed** — irreversible BY DESIGN, with its typed reason (a spend's
//!   consumed nullifier, a burn's destroyed value, the monotone nonce ratchet, a
//!   revocation, a terminal lifecycle, a one-way attenuation) — the
//!   RCCS-with-committed-actions boundary, not a gap.
//!
//! Plus the cell's CURRENT lifecycle posture (a terminal cell already sits past an
//! irreversible boundary), read off its live state. The classification is computed
//! by the actual `Effect::invert(ledger)` — nothing is fabricated. gpui-free +
//! fully tested; renders through the existing generic body widget.

use dregg_cell::{Cell, CellId, CellLifecycle, DeathReason};
use dregg_turn::Inversion;

use crate::presentable::{
    Presentable, Presentation, PresentationBody, PresentationKind, PresentCtx,
};
use crate::reflect::{self, Field, Inspectable, ObjectKind};
use crate::world::{
    burn, destroy, grant_capability, revoke_capability, seal, set_field, transfer, World,
};

/// The per-cell reversibility view.
pub struct CellReversibility {
    /// Which cell this is the undo-history of.
    pub id: CellId,
    /// A clone of the live cell (its lifecycle posture is read off this).
    pub cell: Cell,
    /// The current block height (the destroy/lifecycle anchor for classification).
    pub height: u64,
}

impl CellReversibility {
    /// Wrap the live cell `id` if it is present in the world's ledger.
    pub fn from_world(world: &World, id: CellId) -> Option<Self> {
        world.ledger().get(&id).map(|c| CellReversibility {
            id,
            cell: c.clone(),
            height: world.height(),
        })
    }
}

/// One row of the reversibility map: a kind of change to the cell + its tier.
struct ReversibilityRow {
    /// The forward change's legible name.
    change: &'static str,
    /// The tier label ("reversible (clean)" / "reversible (contextual)" /
    /// "irreversible — <reason>").
    tier: String,
    /// True iff Clean or Contextual.
    reversible: bool,
}

/// Classify the representative forward effects on `target` against the live ledger
/// via the REAL `Effect::invert`. Returns the reversibility map rows.
fn reversibility_map(target: CellId, height: u64, world: &World) -> Vec<ReversibilityRow> {
    // A second cell for the two-party effects (transfer/grant) — a fixed derived
    // id; the classification depends on the EFFECT KIND + ledger, not this id.
    let other = CellId::derive_raw(&[0xEE; 32], &[0u8; 32]);
    let fe = dregg_cell::field_from_u64(0);
    let pre = world.ledger();

    let cases: Vec<(&'static str, dregg_turn::Effect)> = vec![
        ("Transfer (value out)", transfer(target, other, 1)),
        ("SetField (a state slot)", set_field(target, 0, fe)),
        ("CellSeal (freeze)", seal(target, "lens")),
        ("GrantCapability (delegate)", grant_capability(target, other, target, 0)),
        ("Burn (destroy value)", burn(target, 1)),
        ("RevokeCapability (retract)", revoke_capability(target, 0)),
        ("CellDestroy (terminal)", destroy(target, height, DeathReason::Voluntary)),
    ];

    cases
        .into_iter()
        .map(|(change, effect)| {
            let inv = effect.invert(pre);
            let (tier, reversible) = match &inv {
                Inversion::Clean(_) => ("reversible (clean — a single forward effect)".to_string(), true),
                Inversion::Contextual(_) => (
                    "reversible (contextual — needs the held pre-image)".to_string(),
                    true,
                ),
                Inversion::Committed(reason) => {
                    (format!("irreversible — {}", reason.label()), false)
                }
            };
            ReversibilityRow {
                change,
                tier,
                reversible,
            }
        })
        .collect()
}

/// The cell's current lifecycle posture, in reversibility terms.
fn lifecycle_posture(lifecycle: &CellLifecycle) -> (&'static str, &'static str) {
    match lifecycle {
        CellLifecycle::Live => (
            "Live",
            "active — its reversible-tier changes can be un-turned (modulo the monotone nonce)",
        ),
        CellLifecycle::Sealed { .. } => (
            "Sealed",
            "sealed — reversible via unseal (the seal↔unseal pair is clean)",
        ),
        CellLifecycle::Migrated { .. } => (
            "Migrated",
            "migrated — past a terminal lifecycle boundary; no un-turn restores it here",
        ),
        CellLifecycle::Destroyed { .. } => (
            "Destroyed",
            "destroyed — past an irreversible terminal boundary; no un-turn restores it",
        ),
        CellLifecycle::Archived { .. } => (
            "Archived",
            "archived — past a terminal lifecycle boundary; no un-turn restores it",
        ),
    }
}

impl Presentable for CellReversibility {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Cell
    }

    /// The reversibility classification needs the LIVE ledger for `Effect::invert`
    /// — read through `ctx.world` (the read-only live world every `present` takes),
    /// the same way the Affordances face reads the live ledger to divide its caps.
    fn present(&self, ctx: &PresentCtx) -> Vec<Presentation> {
        let world = ctx.world;
        let rows = reversibility_map(self.id, self.height, world);
        let reversible = rows.iter().filter(|r| r.reversible).count();
        let committed = rows.len() - reversible;
        let (posture, posture_prose) = lifecycle_posture(&self.cell.lifecycle);
        let short = reflect::short_hex(self.id.as_bytes());

        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor.
        let insp = Inspectable {
            kind: ObjectKind::Cell,
            title: "REVERSIBILITY — the rewind/undo posture of this cell".to_string(),
            subtitle: format!(
                "cell {short} · {posture} · {reversible} reversible / {committed} committed change-kinds"
            ),
            fields: vec![
                Field::id("cell", *self.id.as_bytes()),
                Field::text("lens", "history / undo".to_string()),
                Field::boolean("available", true),
                Field::text("lifecycle", posture.to_string()),
                Field::text("reversible_kinds", reversible.to_string()),
                Field::text("committed_kinds", committed.to_string()),
            ],
        };
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Undo Posture".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) DomainVisual (Fields) — the per-change reversibility map, computed by
        //     the REAL Effect::invert over the live ledger.
        let mut map_fields: Vec<Field> = Vec::new();
        for row in &rows {
            map_fields.push(Field::text(row.change.to_string(), row.tier.clone()));
        }
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Reversibility Map".to_string(),
            search_text: format!(
                "reversibility map undo {}",
                rows.iter().map(|r| r.change).collect::<Vec<_>>().join(" ")
            ),
            body: PresentationBody::Fields(Inspectable {
                kind: ObjectKind::Cell,
                title: "WHAT REVERSING EACH CHANGE ENTAILS".to_string(),
                subtitle: "classified by Effect::invert against the live ledger".to_string(),
                fields: map_fields,
            }),
        });

        // (3) Invariant (Prose) — the un-turn model + this cell's posture.
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "The Un-Turn".to_string(),
            search_text: "un-turn reversibility modulo nonce committed boundary rccs".to_string(),
            body: PresentationBody::Prose(un_turn_prose(posture, posture_prose, reversible, committed)),
        });

        out
    }
}

/// The un-turn explanation, with this cell's lifecycle posture.
fn un_turn_prose(
    posture: &str,
    posture_prose: &str,
    reversible: usize,
    committed: usize,
) -> String {
    let mut s = String::new();
    s.push_str("THE UN-TURN — reversal is itself a cap-gated forward turn, not a bypass.\n\n");
    s.push_str(&format!(
        "This cell is {posture}: {posture_prose}.\n\n"
    ));
    s.push_str(&format!(
        "Of the representative changes to this cell, {reversible} are reversible (clean or \
         contextual) and {committed} are committed (irreversible by design).\n\n"
    ));
    s.push_str(
        "A reversible change un-turns to the SAME verified state MODULO the monotone nonce: \
         value, fields, and caps are restored exactly, but the per-turn freshness ratchet \
         advances (re-applying the inverse is a fresh forward turn). A ratchet that ran \
         backward would re-admit a stale turn — so the equality is value/state, not raw root.\n\n",
    );
    s.push_str(
        "The committed boundary — a consumed nullifier (spend), destroyed value (burn), the \
         nonce ratchet, a revocation, a terminal lifecycle, a one-way attenuation — is \
         irreversible BY DESIGN (RCCS with committed actions). Restoring authority means a \
         fresh forward grant, not an un-turn. (The cockpit's REPLAY tab time-travels the whole \
         image; this is the same reversibility, lens-shaped per cell.)",
    );
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::presentable::PresentCtx;

    fn live_world() -> (World, CellId) {
        let mut w = World::new();
        let id = w.genesis_cell(0x31, 1_000);
        (w, id)
    }

    #[test]
    fn lights_up_with_a_real_reversibility_map() {
        let (w, id) = live_world();
        let view = CellReversibility::from_world(&w, id).expect("cell present");
        let set = view.present(&PresentCtx::new(&w, id));
        // Floor + map + un-turn.
        assert_eq!(set.len(), 3);
        let floor = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .expect("floor");
        if let PresentationBody::Fields(i) = &floor.body {
            assert!(i.fields.iter().any(|f| f.key == "available"));
            assert!(i.fields.iter().any(|f| f.key == "reversible_kinds"));
        } else {
            panic!("floor is Fields");
        }
    }

    #[test]
    fn the_map_classifies_via_the_real_organ() {
        let (w, id) = live_world();
        let rows = reversibility_map(id, w.height(), &w);
        // Transfer is clean-reversible; Burn / RevokeCapability / CellDestroy are
        // committed — the real Effect::invert taxonomy, not a transcription.
        let transfer = rows.iter().find(|r| r.change.starts_with("Transfer")).unwrap();
        assert!(transfer.reversible, "transfer reverses (clean)");
        let burn = rows.iter().find(|r| r.change.starts_with("Burn")).unwrap();
        assert!(!burn.reversible, "burn is committed");
        assert!(burn.tier.contains("burned"));
        let setfield = rows.iter().find(|r| r.change.starts_with("SetField")).unwrap();
        assert!(setfield.reversible && setfield.tier.contains("contextual"));
        let destroy = rows.iter().find(|r| r.change.starts_with("CellDestroy")).unwrap();
        assert!(!destroy.reversible && destroy.tier.contains("terminal"));
    }

    #[test]
    fn a_live_cell_reports_an_active_posture() {
        let (w, id) = live_world();
        let view = CellReversibility::from_world(&w, id).unwrap();
        let (posture, _) = lifecycle_posture(&view.cell.lifecycle);
        assert_eq!(posture, "Live");
        let prose = un_turn_prose("Live", "active", 4, 3);
        assert!(prose.contains("MODULO the monotone nonce"));
        assert!(prose.contains("RCCS with committed actions"));
    }

    #[test]
    fn the_object_kind_is_cell() {
        let (w, id) = live_world();
        let view = CellReversibility::from_world(&w, id).unwrap();
        // The History lens is a per-cell view (a cell-kind object), and `present`
        // is the world-aware path (the Presentable trait method is not the live one).
        assert_eq!(view.object_kind(), ObjectKind::Cell);
        let _ctx = PresentCtx::new(&w, id);
    }
}
