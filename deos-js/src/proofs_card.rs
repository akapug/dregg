//! **THE PROOFS CARD** — the cockpit's PROOFS surface (the proof-attach + STARK
//! verification-status board), reborn as a deos-js card.
//!
//! Today the cockpit's proofs surface is hardcoded Rust gpui: its UI is *compiled code*
//! (`Cockpit::proofs_panel`). This module makes it a **deos-js card** — a `view-tree`
//! ([`crate::card_editor::ViewTree`], the same `{kind, props, children}` shape
//! [`deos-view`] renders) generated from a verification-status survey of the live World's
//! committed turns:
//!
//!   - a **summary row** of [`ViewTree::Pill`] badges (how many turns are
//!     verified-by-construction / executor-signed / STARK-attached), and
//!   - one [`ViewTree::Section`] per committed turn (most-recent-first), titled
//!     `h{height} · {receipt}`, tinted by the turn's verification tier, carrying its
//!     one-line proof summary + (when present) the honest "→ next" upgrade route.
//!
//! The proofs surface is **read-only** (it never mints a multi-second STARK inside a paint
//! — the honest stance the panel doc names), so the card carries no affordance buttons; it
//! is a pure projection of the live verification posture. The card is gpui-free DATA, so it
//! renders identically through `deos-view`'s native (gpui) and web (HTML) backends, and it
//! is reshapeable from within (the [`crate::card_editor::CardEditor`] patch route the mode
//! cards share).
//!
//! The starbridge-v2 side (`dock::card_surface::ModeCard::Proofs`) builds the
//! [`ProofCardRow`] list from `starbridge_v2::proofs::ProofBoard` and calls
//! [`proofs_view`]; this crate stays gpui-free + `cargo test`-able.

use crate::card_editor::{PillProps, SectionProps, TextProps, ViewTree};

/// One committed turn's verification posture, as the card reads it — the renderer-agnostic
/// shape the cockpit lifts from `starbridge_v2::proofs::ProofEntry`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofCardRow {
    /// The turn's local chain height.
    pub height: u64,
    /// The turn's receipt hash, short-form (the provenance-chain link).
    pub receipt_short: String,
    /// The verification tier's operator-legible label (`verified-by-construction`/…).
    pub tier_label: String,
    /// The styling accent for this tier (`good` STARK / `accent` signed / `muted` by-construction).
    pub tag: String,
    /// The one-line proof summary (tier · attach · pre→post).
    pub summary: String,
    /// The honest route to the next-stronger tier, or `None` at the top.
    pub route: Option<String>,
}

/// **Generate the proofs view-tree** from a verification survey: a title, a summary pill
/// row, then one section per committed turn. The pure function the cockpit's
/// `ModeCard::Proofs` calls (the surface IS this data).
pub fn proofs_view(
    by_construction: usize,
    signed: usize,
    stark_attached: usize,
    rows: &[ProofCardRow],
) -> ViewTree {
    let mut top: Vec<ViewTree> = Vec::new();
    // Warm headline first (the newcomer reassurance), the count second.
    top.push(text(&format!(
        "Everything here was checked — {} change(s) recorded.",
        rows.len()
    )));

    // The summary badge row — the three honest tiers as pills, in plain words.
    top.push(ViewTree::Row {
        children: vec![
            pill(&format!("{by_construction} checked as it ran"), "muted"),
            pill(&format!("{signed} signed"), "accent"),
            pill(&format!("{stark_attached} independently proven"), "good"),
        ],
    });

    if rows.is_empty() {
        top.push(text("Nothing has happened yet — go make the first change."));
        return ViewTree::VStack { children: top };
    }

    // One section per turn: a friendly tier word + the honest upgrade route up front; the
    // receipt hash + the dense one-line summary tucked into an `adept` "under the hood" drawer
    // (DROPPED in the clean newcomer view, REVEALED for an adept — one card, two projections).
    for row in rows {
        let mut body: Vec<ViewTree> = vec![pill(friendly_tier(&row.tier_label), &row.tag)];
        if let Some(route) = &row.route {
            body.push(text(&format!("Want it even stronger? {route}.")));
        }
        body.push(section_adept(
            "under the hood",
            &row.tag,
            vec![
                text(&format!("receipt {}", row.receipt_short)),
                text(&row.summary),
            ],
        ));
        top.push(section(&format!("Change #{}", row.height), &row.tag, body));
    }

    ViewTree::VStack { children: top }
}

/// Map a verification-tier label into plain, newcomer-legible words (the default face never
/// says "by-construction" / "STARK"). The styling-accent `tag` carries the tier's color.
fn friendly_tier(tier_label: &str) -> &'static str {
    let t = tier_label.to_ascii_lowercase();
    if t.contains("stark") {
        "independently proven"
    } else if t.contains("sign") {
        "signed by the machine that ran it"
    } else {
        "checked as it ran"
    }
}

fn text(s: &str) -> ViewTree {
    ViewTree::Text {
        props: TextProps {
            text: s.to_string(),
        },
    }
}

fn pill(text: &str, tag: &str) -> ViewTree {
    ViewTree::Pill {
        props: PillProps {
            text: text.to_string(),
            tag: tag.to_string(),
        },
    }
}

fn section(title: &str, tag: &str, children: Vec<ViewTree>) -> ViewTree {
    ViewTree::Section {
        props: SectionProps {
            title: title.to_string(),
            tag: tag.to_string(),
            adept: false,
        },
        children,
    }
}

/// An **adept-only** section — the "see the bones" drawer (`disclose(Simple)` drops it, the
/// adept projection reveals it).
fn section_adept(title: &str, tag: &str, children: Vec<ViewTree>) -> ViewTree {
    ViewTree::Section {
        props: SectionProps {
            title: title.to_string(),
            tag: tag.to_string(),
            adept: true,
        },
        children,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(h: u64, tier: &str, tag: &str, route: Option<&str>) -> ProofCardRow {
        ProofCardRow {
            height: h,
            receipt_short: format!("rh{h}"),
            tier_label: tier.into(),
            tag: tag.into(),
            summary: format!("h{h} · {tier} · attached"),
            route: route.map(|s| s.to_string()),
        }
    }

    #[test]
    fn empty_board_renders_a_calm_placeholder() {
        let tree = proofs_view(0, 0, 0, &[]);
        assert!(
            tree.walk()
                .iter()
                .any(|n| n.label() == Some("Nothing has happened yet — go make the first change.")),
            "an empty proofs board shows the warm, jargon-free placeholder"
        );
        // Even empty it carries the three summary pills.
        assert_eq!(
            tree.walk()
                .iter()
                .filter(|n| matches!(n, ViewTree::Pill { .. }))
                .count(),
            3,
            "the summary pill row is always present"
        );
    }

    #[test]
    fn each_turn_becomes_a_friendly_section_with_its_route() {
        let rows = [
            row(2, "STARK-attached", "good", None),
            row(
                1,
                "verified-by-construction",
                "muted",
                Some("attach a signature"),
            ),
        ];
        let tree = proofs_view(1, 0, 1, &rows);
        // One section per turn, titled by a friendly step number (no raw receipt in the title).
        assert!(tree.walk().iter().any(|n| n.label() == Some("Change #2")));
        assert!(tree.walk().iter().any(|n| n.label() == Some("Change #1")));
        // The upgrade route surfaces honestly for the lower tier, in warm words.
        assert!(
            tree.walk()
                .iter()
                .any(|n| n.label() == Some("Want it even stronger? attach a signature.")),
            "the honest upgrade route is shown warmly"
        );
        // The headline counts the changes in plain words.
        assert!(tree
            .walk()
            .iter()
            .any(|n| n.label() == Some("Everything here was checked — 2 change(s) recorded.")));
    }

    /// The raw receipt + dense summary live in an `adept` drawer — so the simple projection
    /// (what `disclose(Simple)` and the card mount paint) hides them, an adept reveals them.
    #[test]
    fn the_receipt_and_dense_summary_are_adept_only() {
        let rows = [row(2, "STARK-attached", "good", None)];
        let tree = proofs_view(1, 0, 1, &rows);
        // The "under the hood" drawer is an adept-marked section carrying the receipt + summary.
        let drawer = tree
            .walk()
            .into_iter()
            .find_map(|n| match n {
                ViewTree::Section { props, children } if props.title == "under the hood" => {
                    Some((props.adept, children))
                }
                _ => None,
            })
            .expect("the under-the-hood drawer is present");
        assert!(
            drawer.0,
            "the drawer is adept-only (hidden in the simple view)"
        );
        assert!(
            drawer.1.iter().any(|c| c.label() == Some("receipt rh2")),
            "the raw receipt lives inside the adept drawer, not the friendly title"
        );
    }
}
