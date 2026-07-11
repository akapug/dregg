//! # shared-draft — the SHARED DUNGEON DRAFT + the bounded structured EDIT model.
//!
//! The data heart of COLLECTIVE CO-AUTHORING. A crowd quorum-votes structured edits to ONE shared
//! dungeon draft that grows over time and stays playable. This crate holds the two nouns and the
//! one disposition:
//!
//! * A [`Draft`] — a structured, server-held value (rooms / exits / items / objective) that
//!   [`Draft::render`]s to a `.dungeon` source string. It starts minimal ([`Draft::seed`]: a start
//!   room + an obtainable objective) and is PLAYABLE at any point — the rendered source parses
//!   through [`attested_dm::parse_dungeon`] into a real `GameWorld` over the existing `/game` path.
//! * An [`Edit`] — one of a small CLOSED set of typed proposals: [`Edit::AddRoom`],
//!   [`Edit::AddExit`], [`Edit::PlaceItem`], [`Edit::SetObjective`]. An edit is a *typed proposal*,
//!   not prose. The fields are already sanitized ids/words (the HTTP surface sanitizes on the way
//!   in), so the RENDER is always syntactically valid `.dungeon` — which makes the only way an edit
//!   can fail a SEMANTIC one, caught by the validator.
//! * [`Draft::dispose`] — THE VALIDATOR DISPOSES. It applies the edit to a fresh draft, renders it,
//!   and re-parses through [`attested_dm::parse_dungeon`] (the fail-closed validator). A well-typed
//!   edit that would break the world — a dangling exit, an unreachable objective, an unplaced win
//!   item — is [`Disposition::Refused`] and the caller keeps the old draft (rollback). A sound edit
//!   is [`Disposition::Applied`] with the grown draft + its rendered source. The crowd proposes;
//!   the validator disposes.
//!
//! Because the renderer guarantees syntactic validity, every [`Disposition::Refused`] with
//! [`DisposeStage::Validate`] is a genuine SEMANTIC refusal from `parse_dungeon` — the same
//! fail-closed gate `/game/author` runs. Nothing here is a hand-rolled re-check.

/// One node of the shared draft — a room, mirroring the `.dungeon` `room` block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DraftRoom {
    /// The room id (a single sanitized word).
    pub id: String,
    /// The display name.
    pub name: String,
    /// The prose description (may be empty).
    pub description: String,
    /// The items placed in this room, in insertion order.
    pub items: Vec<String>,
    /// The exits out of this room, in insertion order.
    pub exits: Vec<DraftExit>,
}

/// A directed exit out of a room, mirroring an `exit <dir> -> <to> [requires <gate>]` line.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DraftExit {
    /// The direction word (`north`, `down`, …).
    pub dir: String,
    /// The destination room id.
    pub to: String,
    /// An optional gate — the exit is barred until it is satisfied.
    pub gate: Option<EditGate>,
}

/// A bounded gate on an exit — an item held, or a flag raised. Mirrors `attested_dm::Gate`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EditGate {
    /// Barred until the item is held.
    Item(String),
    /// Barred until the flag reaches `>= value`.
    Flag(String, i64),
}

/// **One bounded, structured edit to the shared draft.** A CLOSED set — NOT free-form DSL text.
/// Each variant carries already-sanitized fields (single-word ids; the display name and
/// description are the only free text, and both are sanitized on render).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Edit {
    /// Add a new room `id` named `name`, with `description`.
    AddRoom {
        id: String,
        name: String,
        description: String,
    },
    /// Add an exit `dir` from room `from` to room `to`, optionally gated.
    AddExit {
        from: String,
        dir: String,
        to: String,
        gate: Option<EditGate>,
    },
    /// Place `item` in room `room`.
    PlaceItem { room: String, item: String },
    /// Retarget the win objective to: reach `room` holding `holding`.
    SetObjective { room: String, holding: String },
}

impl Edit {
    /// The stable edit-kind tag (for the ballot slate + the history JSON).
    pub fn kind(&self) -> &'static str {
        match self {
            Edit::AddRoom { .. } => "AddRoom",
            Edit::AddExit { .. } => "AddExit",
            Edit::PlaceItem { .. } => "PlaceItem",
            Edit::SetObjective { .. } => "SetObjective",
        }
    }

    /// A one-line human-legible summary — the ballot option label + the history line.
    pub fn summary(&self) -> String {
        match self {
            Edit::AddRoom { id, name, .. } => format!("AddRoom {id} \u{201c}{name}\u{201d}"),
            Edit::AddExit {
                from,
                dir,
                to,
                gate,
            } => {
                let g = match gate {
                    None => String::new(),
                    Some(EditGate::Item(i)) => format!(" (requires item {i})"),
                    Some(EditGate::Flag(f, v)) => format!(" (requires flag {f} \u{2265} {v})"),
                };
                format!("AddExit {from} \u{2014}{dir}\u{2192} {to}{g}")
            }
            Edit::PlaceItem { room, item } => format!("PlaceItem {item} in {room}"),
            Edit::SetObjective { room, holding } => {
                format!("SetObjective reach {room} holding {holding}")
            }
        }
    }
}

/// The disposition stage a refusal occurred at.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DisposeStage {
    /// The edit could not be applied structurally (e.g. an exit from a room not in the draft).
    Apply,
    /// The applied draft failed the fail-closed validator (`parse_dungeon`) — the SEMANTIC gate:
    /// a dangling exit, an unreachable objective, an unplaced win item, …
    Validate,
}

impl DisposeStage {
    /// The lower-case tag for JSON.
    pub fn tag(self) -> &'static str {
        match self {
            DisposeStage::Apply => "apply",
            DisposeStage::Validate => "validate",
        }
    }
}

/// **The validator's verdict on a certified edit.** Either the edit is sound and the draft grows
/// ([`Disposition::Applied`]), or it is refused and the caller keeps the old draft
/// ([`Disposition::Refused`]).
#[derive(Clone, Debug)]
pub enum Disposition {
    /// The edit is sound: the grown draft + its rendered `.dungeon` source (which
    /// `attested_dm::parse_dungeon` accepted — so it PLAYS).
    Applied { draft: Draft, source: String },
    /// The edit was refused (and rolled back). Carries the stage and a legible reason.
    Refused { stage: DisposeStage, reason: String },
}

/// **The shared dungeon draft** — a structured value the crowd co-authors. Renders to `.dungeon`
/// source; grows by applying [`Edit`]s; stays playable (the rendered source parses).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Draft {
    /// The flavour name (the `.dungeon` `name:` line).
    pub name: String,
    /// The opening room id.
    pub start: String,
    /// The objective room id (`objective: reach <room> …`).
    pub objective_room: String,
    /// The win item (`… holding <item>`).
    pub objective_holding: String,
    /// The rooms, in insertion order (the start room is first in [`Draft::seed`]).
    pub rooms: Vec<DraftRoom>,
}

impl Draft {
    /// **The minimal seed draft** — a single start room holding the win item, so it is PLAYABLE
    /// (and trivially winnable) the instant it exists. The crowd grows it outward from here.
    pub fn seed() -> Draft {
        Draft {
            name: "The Commons Draft".to_string(),
            start: "threshold".to_string(),
            objective_room: "threshold".to_string(),
            objective_holding: "spark".to_string(),
            rooms: vec![DraftRoom {
                id: "threshold".to_string(),
                name: "The Threshold".to_string(),
                description: "A bare round chamber of pale stone where the co-authored dungeon \
                              begins. The crowd grows it outward from here, one certified edit at \
                              a time."
                    .to_string(),
                items: vec!["spark".to_string()],
                exits: vec![],
            }],
        }
    }

    /// The room with this id, if present.
    pub fn room(&self, id: &str) -> Option<&DraftRoom> {
        self.rooms.iter().find(|r| r.id == id)
    }

    /// Whether a room with this id exists in the draft.
    pub fn has_room(&self, id: &str) -> bool {
        self.rooms.iter().any(|r| r.id == id)
    }

    /// **Render the draft to `.dungeon` source.** The output is always syntactically valid (this
    /// crate controls the grammar), so any `parse_dungeon` failure over it is purely SEMANTIC.
    pub fn render(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("name: {}\n", sanitize_line(&self.name)));
        out.push_str(&format!("start: {}\n", self.start));
        out.push_str(&format!(
            "objective: reach {} holding {}\n",
            self.objective_room, self.objective_holding
        ));
        for room in &self.rooms {
            out.push('\n');
            out.push_str(&format!(
                "room {} \"{}\"\n",
                room.id,
                sanitize_name(&room.name)
            ));
            let desc = sanitize_line(&room.description);
            if !desc.is_empty() {
                // The `desc:` prefix keeps a description whose first word might collide with a body
                // keyword (`items:`, `exit`, …) from being misparsed — it is always description.
                out.push_str(&format!("  desc: {desc}\n"));
            }
            if !room.items.is_empty() {
                out.push_str(&format!("  items: {}\n", room.items.join(", ")));
            }
            for e in &room.exits {
                let gate = match &e.gate {
                    None => String::new(),
                    Some(EditGate::Item(i)) => format!(" requires item {i}"),
                    Some(EditGate::Flag(f, v)) => format!(" requires flag {f} >= {v}"),
                };
                out.push_str(&format!("  exit {} -> {}{}\n", e.dir, e.to, gate));
            }
        }
        out
    }

    /// **Apply an edit structurally, returning a fresh grown draft** (leaving `self` untouched, so
    /// a refusal is a no-op rollback). A structural precondition failure (an exit from a room not
    /// in the draft; a duplicate room id) is an `Err(reason)` — surfaced by [`Draft::dispose`] as a
    /// [`DisposeStage::Apply`] refusal. Everything else is left to the validator.
    pub fn apply(&self, edit: &Edit) -> Result<Draft, String> {
        let mut next = self.clone();
        match edit {
            Edit::AddRoom {
                id,
                name,
                description,
            } => {
                if next.has_room(id) {
                    return Err(format!("a room `{id}` already exists in the draft"));
                }
                next.rooms.push(DraftRoom {
                    id: id.clone(),
                    name: if name.trim().is_empty() {
                        id.clone()
                    } else {
                        name.clone()
                    },
                    description: description.clone(),
                    items: vec![],
                    exits: vec![],
                });
            }
            Edit::AddExit {
                from,
                dir,
                to,
                gate,
            } => {
                let room = next
                    .rooms
                    .iter_mut()
                    .find(|r| &r.id == from)
                    .ok_or_else(|| format!("no room `{from}` in the draft to add an exit from"))?;
                // A same-direction exit is replaced (last write wins), matching the DSL's per-dir
                // exit map — so re-proposing `north` retargets it rather than duplicating.
                room.exits.retain(|e| e.dir != *dir);
                room.exits.push(DraftExit {
                    dir: dir.clone(),
                    to: to.clone(),
                    gate: gate.clone(),
                });
            }
            Edit::PlaceItem { room, item } => {
                let r = next
                    .rooms
                    .iter_mut()
                    .find(|r| &r.id == room)
                    .ok_or_else(|| format!("no room `{room}` in the draft to place an item in"))?;
                if !r.items.iter().any(|i| i == item) {
                    r.items.push(item.clone());
                }
            }
            Edit::SetObjective { room, holding } => {
                // No structural precondition — the validator decides whether the room is reachable
                // and the item obtainable. (That is the whole point: a voted-for unreachable
                // objective is refused by parse_dungeon, not pre-screened here.)
                next.objective_room = room.clone();
                next.objective_holding = holding.clone();
            }
        }
        Ok(next)
    }

    /// **THE VALIDATOR DISPOSES.** Apply the edit to a fresh draft, render it, and re-parse through
    /// [`attested_dm::parse_dungeon`] — the fail-closed validator. Sound ⇒ [`Disposition::Applied`]
    /// with the grown draft + source; broken (dangling exit, unreachable objective, unplaced item,
    /// …) ⇒ [`Disposition::Refused`] and the caller keeps the old draft. The crowd proposed; the
    /// validator disposed.
    pub fn dispose(&self, edit: &Edit) -> Disposition {
        let next = match self.apply(edit) {
            Ok(d) => d,
            Err(reason) => {
                return Disposition::Refused {
                    stage: DisposeStage::Apply,
                    reason,
                }
            }
        };
        let source = next.render();
        match attested_dm::parse_dungeon(&source) {
            Ok(_world) => Disposition::Applied {
                draft: next,
                source,
            },
            Err(e) => Disposition::Refused {
                stage: DisposeStage::Validate,
                reason: e.to_string(),
            },
        }
    }

    /// A convenience: does the current draft parse (is it playable right now)? True for the seed
    /// and after every applied edit (the invariant `dispose` preserves).
    pub fn plays(&self) -> bool {
        attested_dm::parse_dungeon(&self.render()).is_ok()
    }
}

/// Sanitize a single line of free text (a name / description) for embedding in `.dungeon` source:
/// collapse newlines, drop comment starters (`#`, `//`) so they cannot truncate the line, and trim.
fn sanitize_line(s: &str) -> String {
    let mut out = s.replace(['\n', '\r', '\t'], " ").replace("//", " ");
    out = out.replace('#', " ");
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Sanitize a display name for a `"quoted"` slot: like [`sanitize_line`] but also drop the quote.
fn sanitize_name(s: &str) -> String {
    sanitize_line(s).replace('"', "")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seed_plays() {
        let d = Draft::seed();
        assert!(d.plays(), "the seed draft must parse + validate (playable)");
    }

    #[test]
    fn add_room_grows_and_still_plays() {
        let d = Draft::seed();
        let before = d.rooms.len();
        let edit = Edit::AddRoom {
            id: "hall".into(),
            name: "The Hall".into(),
            description: "A long echoing hall.".into(),
        };
        match d.dispose(&edit) {
            Disposition::Applied { draft, source } => {
                assert_eq!(draft.rooms.len(), before + 1, "the draft grew by one room");
                assert!(
                    source.contains("room hall"),
                    "the source names the new room"
                );
                assert!(draft.plays(), "the grown draft still plays");
            }
            Disposition::Refused { reason, .. } => panic!("a sound AddRoom was refused: {reason}"),
        }
    }

    #[test]
    fn add_exit_to_nonexistent_room_is_refused_by_validator() {
        // NON-VACUOUS: a well-typed AddExit (from a REAL room `threshold`) to a room that does not
        // exist renders valid syntax but is a DANGLING exit — the validator refuses it.
        let d = Draft::seed();
        let edit = Edit::AddExit {
            from: "threshold".into(),
            dir: "west".into(),
            to: "nowhere".into(),
            gate: None,
        };
        match d.dispose(&edit) {
            Disposition::Refused { stage, reason } => {
                assert_eq!(stage, DisposeStage::Validate, "refused by the VALIDATOR");
                assert!(
                    reason.contains("nowhere") || reason.contains("unknown room"),
                    "the refusal names the dangling target: {reason}"
                );
            }
            Disposition::Applied { .. } => panic!("a dangling exit must be refused, not applied"),
        }
        // Rollback: the original draft is untouched (dispose took &self).
        assert_eq!(d.rooms[0].exits.len(), 0, "the draft was not mutated");
    }

    #[test]
    fn set_objective_to_unplaced_item_is_refused() {
        let d = Draft::seed();
        let edit = Edit::SetObjective {
            room: "threshold".into(),
            holding: "phantom".into(),
        };
        match d.dispose(&edit) {
            Disposition::Refused { stage, reason } => {
                assert_eq!(stage, DisposeStage::Validate);
                assert!(
                    reason.contains("phantom"),
                    "names the unplaced item: {reason}"
                );
            }
            Disposition::Applied { .. } => panic!("an unwinnable objective must be refused"),
        }
    }

    #[test]
    fn add_room_then_exit_then_move_is_reachable() {
        let d = Draft::seed();
        let d = match d.dispose(&Edit::AddRoom {
            id: "hall".into(),
            name: "The Hall".into(),
            description: "A long echoing hall.".into(),
        }) {
            Disposition::Applied { draft, .. } => draft,
            Disposition::Refused { reason, .. } => panic!("AddRoom refused: {reason}"),
        };
        let d = match d.dispose(&Edit::AddExit {
            from: "threshold".into(),
            dir: "north".into(),
            to: "hall".into(),
            gate: None,
        }) {
            Disposition::Applied { draft, source } => {
                assert!(source.contains("exit north -> hall"));
                draft
            }
            Disposition::Refused { reason, .. } => panic!("AddExit refused: {reason}"),
        };
        // The grown draft opens a real GameSession and a move into the new room lands.
        let world = attested_dm::parse_dungeon(&d.render()).expect("grown draft parses");
        let mut session = attested_dm::GameSession::open(world);
        let before = session.world().ledger.len();
        let proposal = attested_dm::Proposal::new(
            "You step north into the hall.".to_string(),
            attested_dm::GameAction::Move("north".to_string()),
        );
        let res = session.play(proposal, "player", "go north");
        assert!(
            matches!(res, attested_dm::PlayResult::Landed { .. }),
            "the voted move into the co-authored room lands"
        );
        assert_eq!(
            session.world().ledger.len(),
            before + 1,
            "the landed move grew the receipt ledger"
        );
        assert!(
            session.verify().is_ok(),
            "the ledger re-verifies as a chain"
        );
    }
}
