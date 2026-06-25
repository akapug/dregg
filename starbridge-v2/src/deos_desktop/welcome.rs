//! **The WELCOME moment** — the warm front door of the deos desktop.
//!
//! The desktop has two faces and they are the same image (see `docs/deos/AOL-WONDER.md`):
//! the dense power-instrument an adept lives in, and the calm room a newcomer wakes up
//! in. This module owns the calm half's first breath — the small greeting card a
//! stranger meets on a fresh image, before any window is open. It greets in a plain,
//! jargon-free sentence drawn from the LIVE world (its real cell count, its real height),
//! and offers a tiny set of inviting doors. No comprehension is required to read it;
//! reading it *is* the comprehension arriving.
//!
//! ## The clobber-safe split (mirrors `spotter`)
//!
//! This module owns the pure, gpui-free DATA MODEL ([`WelcomeAction`], [`WelcomeTile`],
//! [`welcome_tiles`]) and the unit-testable [`greeting`] sentence. The desktop View
//! (`DeosDesktop`) owns the overlay rendering and the `cx.listener` click wiring that
//! dispatches a chosen [`WelcomeAction`]. Keeping the model gpui-free means it compiles
//! and tests without a renderer.

/// What a welcome door dispatches when a newcomer pokes it. Each maps to a real
/// gesture the desktop already performs — there is no second, beginner-only machinery:
/// the welcome simply *names the first move* in warm words.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WelcomeAction {
    /// Dismiss the card and just look around the room of glowing cell-icons. The
    /// gentlest door: it does nothing but get out of the way.
    LookAround,
    /// Open the Spotter — the "type anything and jump" entry.
    FindAnything,
    /// Open a fresh document to start writing (every keystroke a receipted patch).
    WriteSomething,
    /// Open the World Explorer — the map of everything (cells · receipts · the Σ=0).
    SeeTheWorld,
}

/// One inviting door on the welcome card. `step` is a tiny font-safe digit badge (a
/// calm 1-2-3-4 a five-year-old can follow), `title` the warm headline, `blurb` the
/// one plain sentence under it, and `action` the gesture the door opens.
pub struct WelcomeTile {
    pub step: &'static str,
    pub title: &'static str,
    pub blurb: &'static str,
    pub action: WelcomeAction,
}

/// The four doors of the warm front room, in the order a newcomer best meets them:
/// look, find, make, survey. Each is a real desktop gesture wearing a warm name.
pub fn welcome_tiles() -> Vec<WelcomeTile> {
    vec![
        WelcomeTile {
            step: "1",
            title: "Look around",
            blurb: "Poke the glowing cells. Hover one, click it — it tells you what it is.",
            action: WelcomeAction::LookAround,
        },
        WelcomeTile {
            step: "2",
            title: "Find anything",
            blurb: "Type a word and jump straight to it — a cell, an action, a place.",
            action: WelcomeAction::FindAnything,
        },
        WelcomeTile {
            step: "3",
            title: "Write something",
            blurb: "Open a fresh page and start typing. Every keystroke is kept, forever.",
            action: WelcomeAction::WriteSomething,
        },
        WelcomeTile {
            step: "4",
            title: "See the whole world",
            blurb: "Open the map of everything — every cell, every receipt, balance summing to zero.",
            action: WelcomeAction::SeeTheWorld,
        },
    ]
}

/// A warm, jargon-free greeting that names the live image's real shape. It reads the
/// world's true `cells` count and `height` (how many turns of history it carries) so
/// the welcome is never a static splash — it greets you with the actual living thing.
/// The words never say "cell", "capability", "turn", or "receipt"; a stranger
/// understands the room without a manual.
pub fn greeting(cells: usize, height: u64) -> String {
    let things = if cells == 1 { "thing" } else { "things" };
    let turns = if height == 1 { "change" } else { "changes" };
    format!(
        "You're looking at a living image — {cells} {things} in it, {height} {turns} \
         of history, all real. This isn't a picture of a computer; it is one. Click \
         anything to see what it is. Nothing you click can break it — go ahead."
    )
}

/// The closing reassurance under the doors — the calm "you can leave whenever" note
/// that keeps the welcome a warm invitation, never a wizard you must complete.
pub const WELCOME_FOOTER: &str =
    "You can close this whenever you like — the room is always waiting.";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn greeting_names_the_live_shape() {
        let g = greeting(7, 3);
        assert!(g.contains('7'), "the greeting names the real cell count");
        assert!(
            g.contains('3'),
            "the greeting names the real history height"
        );
        // The four load-bearing jargon words never appear in the default face (HIG §3).
        for jargon in ["capability", "receipt", "nullifier", "REJECT"] {
            assert!(
                !g.contains(jargon),
                "the welcome must speak human, not compiler — found {jargon:?}"
            );
        }
    }

    #[test]
    fn greeting_pluralizes_gently() {
        assert!(greeting(1, 1).contains("1 thing in it"));
        assert!(greeting(1, 1).contains("1 change of history"));
        assert!(greeting(2, 2).contains("2 things in it"));
        assert!(greeting(2, 2).contains("2 changes of history"));
    }

    #[test]
    fn four_doors_in_warm_order() {
        let tiles = welcome_tiles();
        assert_eq!(tiles.len(), 4, "look · find · make · survey");
        let actions: Vec<WelcomeAction> = tiles.iter().map(|t| t.action).collect();
        assert_eq!(
            actions,
            vec![
                WelcomeAction::LookAround,
                WelcomeAction::FindAnything,
                WelcomeAction::WriteSomething,
                WelcomeAction::SeeTheWorld,
            ]
        );
        // Steps are font-safe digit badges (no tofu in the headline bake).
        for t in &tiles {
            assert!(t.step.chars().all(|c| c.is_ascii_digit()));
            assert!(!t.title.is_empty() && !t.blurb.is_empty());
        }
    }
}
