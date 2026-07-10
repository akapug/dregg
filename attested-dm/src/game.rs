//! # game — the dungeon-crawler ENGINE: the AI proposes, the world disposes.
//!
//! attested-dm's [`crate::DungeonMaster`] proves a narration is authentic, well-formed,
//! injection-free, cap-bounded, and on-chain. This module is the layer that makes it a
//! *game*: a [`GameWorld`] of rooms / items / gated exits with an [`Objective`], and a
//! deterministic [`resolve_action`] that decides what a move actually does — regardless of
//! how the AI narrates it.
//!
//! ## Prose is not power, at the level of a game move
//!
//! Each turn, the AI dungeon-master (the [`GameBrain`] — the modeled [`ScriptedGm`] here,
//! a real gemma2 in the flagship) does two things: it **narrates** the room + the move
//! vividly, and it **proposes a [`GameAction`]** — a *closed typed* channel: `Move`,
//! `Take`, `Use`, `Examine`, `Attack`. It cannot free-text a world mutation; it can only
//! name one of these moves. Then the **world resolves**:
//!
//! * [`GameAction::Move`] succeeds only through an OPEN exit — a [`Gate`]d exit is REFUSED
//!   ("the door is locked") until its requirement (a held item, or a set flag) is met.
//! * [`GameAction::Take`] succeeds only for an item PRESENT in the current room.
//! * [`GameAction::Use`] needs an item you HOLD, and applies only a rule the world defines
//!   (e.g. use the key on the iron door → the door-unlocked flag sets → the gated exit opens).
//! * [`GameAction::Attack`] resolves by the world's rules — the Warden falls to the sword,
//!   or cuts you down if you lack it.
//!
//! A jailbroken model that narrates *"the iron door swings wide and you stride through"*
//! changes **nothing** if the door is locked: it can only propose `Move`, and the resolver
//! refuses it ([`Outcome::Refused`]) — the world unchanged, **no receipt** (the anti-ghost
//! tooth). The narration is discarded; the state does not move. Only a **legal** move is
//! attested and appended to the chain as ONE verified turn carrying its [`GameBinding`].
//!
//! ## The two teeth, both kept
//!
//! * **The resolver** gates every move by the world's rules (you cannot narrate through a
//!   locked door, take an absent item, or win without the amulet).
//! * **[`crate::DmCaps`]** still gates grants: the DM can only propose `GrantItem` for an
//!   item on its whitelist, so it cannot mint an item the world never placed. The engine's
//!   takeable items are exactly the DM's grantable set — the resolver only ever proposes a
//!   grant for an item actually present, and the cap is the second, independent bound.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    slot_confined, world_binding, DmError, DmMove, DungeonMaster, PromptBinding, Receipt,
    RecordedDm, WorldCell, WorldEffect,
};

// ─────────────────────────────────────────────────────────────────────────────
// The closed typed action channel — the ONLY moves the AI can propose.
// ─────────────────────────────────────────────────────────────────────────────

/// **The closed, typed action a dungeon-master may propose.** This is the whole channel
/// through which the AI can attempt to change the world — it cannot emit free-text state
/// mutations, only *name* one of these moves. The [`resolve_action`] resolver then decides
/// what (if anything) actually happens. Riding the chain via [`GameBinding`], the on-ledger
/// receipt commits to exactly which typed move produced each turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GameAction {
    /// Move toward a destination — named either by a room id or by an exit direction
    /// (`"north"`, `"down"`, …). Succeeds only through an OPEN exit from the current room.
    Move(String),
    /// Take an item from the current room. Succeeds only if the item is PRESENT here.
    Take(String),
    /// Use a held item, optionally on a target (e.g. `Use("rusted_key", Some("iron_door"))`).
    /// Succeeds only if you HOLD the item and the world defines a [`UseRule`] for it here.
    Use(String, Option<String>),
    /// Look at the current room — a pure-narration move (no world-effect), always legal.
    Examine,
    /// Attack a target in the current room. Resolves by the world's [`Hostile`] rules.
    Attack(String),
}

impl GameAction {
    /// A short human-legible label for the action (for playthrough logs).
    pub fn label(&self) -> String {
        match self {
            GameAction::Move(to) => format!("move -> {to}"),
            GameAction::Take(i) => format!("take {i}"),
            GameAction::Use(i, Some(t)) => format!("use {i} on {t}"),
            GameAction::Use(i, None) => format!("use {i}"),
            GameAction::Examine => "examine".to_string(),
            GameAction::Attack(t) => format!("attack {t}"),
        }
    }

    /// Deterministic, tagged, length-prefixed encoding into the chain hash — so a rewritten
    /// action (claiming a different move produced a landed turn) breaks the receipt.
    pub(crate) fn encode_into(&self, h: &mut blake3::Hasher) {
        fn s(h: &mut blake3::Hasher, x: &str) {
            h.update(&(x.len() as u64).to_le_bytes());
            h.update(x.as_bytes());
        }
        match self {
            GameAction::Move(to) => {
                h.update(&[1u8]);
                s(h, to);
            }
            GameAction::Take(i) => {
                h.update(&[2u8]);
                s(h, i);
            }
            GameAction::Use(i, t) => {
                h.update(&[3u8]);
                s(h, i);
                match t {
                    None => {
                        h.update(&[0u8]);
                    }
                    Some(t) => {
                        h.update(&[1u8]);
                        s(h, t);
                    }
                }
            }
            GameAction::Examine => {
                h.update(&[4u8]);
            }
            GameAction::Attack(t) => {
                h.update(&[5u8]);
                s(h, t);
            }
        }
    }
}

/// **The game-move binding a landed turn carries** — the closed typed [`GameAction`] the
/// resolver admitted, and the room it acted in. Bound into the turn's receipt (see
/// [`crate::chain_receipt_id`]) so the chain commits to the sequence of *moves*, not just the
/// prose: a rewritten action or swapped room breaks the link.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GameBinding {
    /// The typed action the resolver admitted this turn.
    pub action: GameAction,
    /// The room id the action was resolved in.
    pub room: String,
}

impl GameBinding {
    /// A binding over an admitted action + the room it resolved in.
    pub fn new(action: GameAction, room: impl Into<String>) -> GameBinding {
        GameBinding {
            action,
            room: room.into(),
        }
    }

    /// Deterministic encoding into the chain hash (room ‖ action).
    pub(crate) fn encode_into(&self, h: &mut blake3::Hasher) {
        h.update(&(self.room.len() as u64).to_le_bytes());
        h.update(self.room.as_bytes());
        self.action.encode_into(h);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The static world — rooms, gated exits, items, use-rules, hostiles, objective.
// ─────────────────────────────────────────────────────────────────────────────

/// **A requirement that blocks an exit until met** — the deterministic lock. A gated exit is
/// REFUSED until its gate is satisfied by the current world state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Gate {
    /// The exit is open only while the player HOLDS `item` (e.g. the lantern lights a dark stair).
    NeedsItem(String),
    /// The exit is open only while world flag `k >= v` (e.g. `door_unlocked >= 1`).
    NeedsFlag(String, i64),
}

impl Gate {
    fn satisfied(&self, world: &WorldCell) -> bool {
        match self {
            Gate::NeedsItem(i) => world.inventory.contains(i),
            Gate::NeedsFlag(k, v) => world.flags.get(k).copied().unwrap_or(0) >= *v,
        }
    }

    fn reason(&self) -> GateReason {
        match self {
            Gate::NeedsItem(i) => GateReason::NeedsItem(i.clone()),
            Gate::NeedsFlag(k, v) => GateReason::NeedsFlag(k.clone(), *v),
        }
    }
}

/// The legible reason a gated exit refused a move.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GateReason {
    /// The exit needs a held item the player lacks.
    NeedsItem(String),
    /// The exit needs a world flag not yet set high enough.
    NeedsFlag(String, i64),
}

impl std::fmt::Display for GateReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GateReason::NeedsItem(i) => write!(f, "it needs the {i}"),
            GateReason::NeedsFlag(k, v) => write!(f, "it stays sealed until {k} >= {v}"),
        }
    }
}

/// An exit from a room — where it leads, and the (optional) [`Gate`] that must be met to pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exit {
    /// The destination room id.
    pub to_room: String,
    /// The requirement that blocks this exit, or `None` for an always-open passage.
    pub gate: Option<Gate>,
}

impl Exit {
    /// An always-open exit to `to_room`.
    pub fn open(to_room: impl Into<String>) -> Exit {
        Exit {
            to_room: to_room.into(),
            gate: None,
        }
    }

    /// An exit to `to_room` blocked by `gate` until it is satisfied.
    pub fn gated(to_room: impl Into<String>, gate: Gate) -> Exit {
        Exit {
            to_room: to_room.into(),
            gate: Some(gate),
        }
    }
}

/// A room in the dungeon — its name, description, gated exits (keyed by direction), and the
/// items initially resting here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Room {
    /// The room's stable id (the value stored in [`WorldCell::scene`]).
    pub id: String,
    /// The room's short name.
    pub name: String,
    /// A vivid description (the world's own account; the AI narrates *around* it).
    pub description: String,
    /// Exits keyed by direction (`"north"`, `"down"`, …), each with its optional gate.
    pub exits: BTreeMap<String, Exit>,
    /// The items initially in this room. An item is "here" until it is taken into inventory.
    pub items: BTreeSet<String>,
}

impl Room {
    /// A room builder.
    pub fn new(
        id: impl Into<String>,
        name: impl Into<String>,
        description: impl Into<String>,
    ) -> Room {
        Room {
            id: id.into(),
            name: name.into(),
            description: description.into(),
            exits: BTreeMap::new(),
            items: BTreeSet::new(),
        }
    }

    /// Add an exit in `dir` and return `self` (builder style).
    pub fn exit(mut self, dir: impl Into<String>, exit: Exit) -> Room {
        self.exits.insert(dir.into(), exit);
        self
    }

    /// Place an item here and return `self` (builder style).
    pub fn item(mut self, item: impl Into<String>) -> Room {
        self.items.insert(item.into());
        self
    }
}

/// **A `Use` interaction the world defines.** When the player uses `item` (optionally on
/// `target`) in `room`, world flag `sets_flag` is set. This is how a key opens a door: the
/// gated exit reads the flag this rule sets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UseRule {
    /// The room this interaction is available in.
    pub room: String,
    /// The (held) item that triggers it.
    pub item: String,
    /// The target it must be used on, or `None` if the item is used bare.
    pub target: Option<String>,
    /// The world flag the interaction sets (name, value).
    pub sets_flag: (String, i64),
    /// The world's account of what the interaction does.
    pub narration: String,
}

/// **A hostile in a room** — resolves [`GameAction::Attack`]. Defeated only if the player
/// holds `defeated_by`; otherwise the attacker is slain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hostile {
    /// The room the hostile guards.
    pub room: String,
    /// The hostile's name (the `Attack` target).
    pub name: String,
    /// The item that lets the player defeat it (e.g. the sword).
    pub defeated_by: String,
    /// The flag set on victory (e.g. `warden_defeated = 1`), which downstream gates read.
    pub victory_flag: (String, i64),
    /// The flag set on the player's death (a lose flag; see [`LoseCondition`]).
    pub death_flag: (String, i64),
    /// The world's account of a victorious strike.
    pub victory_narration: String,
    /// The world's account of the fatal strike (the player dies).
    pub death_narration: String,
}

/// **The win condition** — reach `room` while HOLDING `item`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Objective {
    /// The room the player must reach.
    pub room: String,
    /// The item the player must be holding when they reach it.
    pub holding: String,
}

/// **A lose condition** — the game is LOST once world flag `k >= v` (e.g. `slain >= 1`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoseCondition {
    /// The flag that, once set high enough, ends the game in defeat.
    pub flag: String,
    /// The threshold.
    pub at_least: i64,
    /// A legible description of the defeat.
    pub description: String,
}

/// **The static dungeon** — the rooms, use-rules, hostiles, the starting room, the win
/// objective, and the lose conditions. Pure data; it never mutates. All dynamic state (the
/// current room, the held inventory, the set flags) lives in the [`WorldCell`], so a legal
/// move is exactly a cap-gated, attested, on-chain [`WorldEffect`].
#[derive(Clone, Debug)]
pub struct GameWorld {
    /// The rooms, keyed by id.
    pub rooms: BTreeMap<String, Room>,
    /// The `Use` interactions the world defines.
    pub use_rules: Vec<UseRule>,
    /// The hostiles, keyed by the room they guard.
    pub hostiles: BTreeMap<String, Hostile>,
    /// The starting room id.
    pub start: String,
    /// The win objective.
    pub objective: Objective,
    /// The lose conditions.
    pub lose: Vec<LoseCondition>,
}

impl GameWorld {
    /// A fresh [`WorldCell`] opened at this world's starting room.
    pub fn new_world(&self) -> WorldCell {
        WorldCell::new(self.start.clone())
    }

    /// The room with `id`, if any.
    pub fn room(&self, id: &str) -> Option<&Room> {
        self.rooms.get(id)
    }

    /// The set of takeable items across the whole dungeon — exactly the DM's grantable
    /// whitelist ([`crate::DmCaps::narrator`]), so a `Take` is a cap-permitted grant.
    pub fn all_items(&self) -> BTreeSet<String> {
        self.rooms
            .values()
            .flat_map(|r| r.items.iter().cloned())
            .collect()
    }

    /// The items visible in `room` right now — its initial items minus anything already taken
    /// into the player's inventory. (Each item lives in exactly one room, so a taken item
    /// simply disappears from its origin.)
    pub fn items_here(&self, room: &str, world: &WorldCell) -> BTreeSet<String> {
        match self.rooms.get(room) {
            None => BTreeSet::new(),
            Some(r) => r
                .items
                .iter()
                .filter(|i| !world.inventory.contains(*i))
                .cloned()
                .collect(),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The resolver — the world disposes.
// ─────────────────────────────────────────────────────────────────────────────

/// The game's status after a move.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GameStatus {
    /// The game continues.
    Playing,
    /// The objective is met — the player WON.
    Won,
    /// A lose condition fired — the player LOST.
    Lost,
}

/// A legal, resolved move: the world-effect to apply (if any), the world's narration of what
/// happened, and the game status once the effect lands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resolution {
    /// The single [`WorldEffect`] this move applies (`None` for a pure look).
    pub effect: Option<WorldEffect>,
    /// The world's own account of the outcome (distinct from the AI's flavor narration).
    pub narration: String,
    /// The game status after the effect is applied.
    pub status: GameStatus,
}

/// **Why the world REFUSED a proposed move** — a legible reason. A refused move leaves the
/// world unchanged and lands no receipt (anti-ghost).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GameRefusal {
    /// There is no exit from the current room toward the named destination/direction.
    NoSuchExit { from: String, toward: String },
    /// The exit exists but its gate is not satisfied — the reason names what is missing.
    LockedExit { toward: String, reason: GateReason },
    /// The item is not present in the current room (absent, or already taken).
    ItemNotHere(String),
    /// The player is not holding the item they tried to use.
    NotHolding(String),
    /// The player holds the item but there is no `Use` interaction for it here.
    NothingHappens {
        item: String,
        target: Option<String>,
    },
    /// There is nothing by that name to attack in this room.
    NoSuchTarget(String),
    /// The game is already over — no further moves resolve.
    GameOver(GameStatus),
}

impl std::fmt::Display for GameRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GameRefusal::NoSuchExit { from, toward } => {
                write!(f, "there is no way from the {from} toward {toward}")
            }
            GameRefusal::LockedExit { toward, reason } => {
                write!(f, "the way to {toward} is barred: {reason}")
            }
            GameRefusal::ItemNotHere(i) => write!(f, "there is no {i} here to take"),
            GameRefusal::NotHolding(i) => write!(f, "you are not holding the {i}"),
            GameRefusal::NothingHappens { item, target } => match target {
                Some(t) => write!(f, "using the {item} on the {t} does nothing here"),
                None => write!(f, "using the {item} does nothing here"),
            },
            GameRefusal::NoSuchTarget(t) => write!(f, "there is no {t} here to attack"),
            GameRefusal::GameOver(s) => write!(f, "the game is over ({s:?})"),
        }
    }
}

impl std::error::Error for GameRefusal {}

/// The result of resolving a proposed action against the world.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// The move is legal — apply `Resolution` (one attested, cap-gated, on-chain turn).
    Legal(Resolution),
    /// The move is illegal — REFUSED in-band, world unchanged, no receipt.
    Refused(GameRefusal),
}

/// **THE RESOLVER — the world disposes.** Given the static [`GameWorld`], the current
/// [`WorldCell`] state, and the AI-proposed [`GameAction`], decide *deterministically* what
/// actually happens. No matter how the AI narrates, only what this function returns [`Outcome::Legal`]
/// can change the world; everything else is [`Outcome::Refused`] and leaves no trace.
///
/// The win/lose status is computed from the *post-effect* state (the hypothetical world after
/// the returned effect lands), so a move that steps into the exit holding the amulet reports
/// [`GameStatus::Won`], and a strike that gets you killed reports [`GameStatus::Lost`].
pub fn resolve_action(map: &GameWorld, world: &WorldCell, action: &GameAction) -> Outcome {
    let here = world.scene.clone();
    match action {
        GameAction::Examine => {
            let narration = describe_room(map, &here, world);
            Outcome::Legal(Resolution {
                effect: None,
                narration,
                status: status_after(map, world, None),
            })
        }

        GameAction::Move(dest) => {
            let room = match map.rooms.get(&here) {
                Some(r) => r,
                None => {
                    return Outcome::Refused(GameRefusal::NoSuchExit {
                        from: here,
                        toward: dest.clone(),
                    })
                }
            };
            // Resolve the destination by room id first, then by direction name.
            let exit = room
                .exits
                .values()
                .find(|e| &e.to_room == dest)
                .or_else(|| room.exits.get(dest));
            let exit = match exit {
                Some(e) => e,
                None => {
                    return Outcome::Refused(GameRefusal::NoSuchExit {
                        from: room.name.clone(),
                        toward: dest.clone(),
                    })
                }
            };
            // A GATED exit is refused until its requirement is met — the locked door.
            if let Some(gate) = &exit.gate {
                if !gate.satisfied(world) {
                    let toward = map
                        .rooms
                        .get(&exit.to_room)
                        .map(|r| r.name.clone())
                        .unwrap_or_else(|| exit.to_room.clone());
                    return Outcome::Refused(GameRefusal::LockedExit {
                        toward,
                        reason: gate.reason(),
                    });
                }
            }
            let effect = Some(WorldEffect::AdvanceScene(exit.to_room.clone()));
            let dest_name = map
                .rooms
                .get(&exit.to_room)
                .map(|r| r.name.clone())
                .unwrap_or_else(|| exit.to_room.clone());
            Outcome::Legal(Resolution {
                narration: format!("You pass into the {dest_name}."),
                status: status_after(map, world, effect.as_ref()),
                effect,
            })
        }

        GameAction::Take(item) => {
            if !map.items_here(&here, world).contains(item) {
                return Outcome::Refused(GameRefusal::ItemNotHere(item.clone()));
            }
            let effect = Some(WorldEffect::GrantItem(item.clone()));
            Outcome::Legal(Resolution {
                narration: format!("You take the {item}."),
                status: status_after(map, world, effect.as_ref()),
                effect,
            })
        }

        GameAction::Use(item, target) => {
            if !world.inventory.contains(item) {
                return Outcome::Refused(GameRefusal::NotHolding(item.clone()));
            }
            let rule = map
                .use_rules
                .iter()
                .find(|r| &r.room == &here && &r.item == item && &r.target == target);
            let rule = match rule {
                Some(r) => r,
                None => {
                    return Outcome::Refused(GameRefusal::NothingHappens {
                        item: item.clone(),
                        target: target.clone(),
                    })
                }
            };
            let effect = Some(WorldEffect::SetFlag(
                rule.sets_flag.0.clone(),
                rule.sets_flag.1,
            ));
            Outcome::Legal(Resolution {
                narration: rule.narration.clone(),
                status: status_after(map, world, effect.as_ref()),
                effect,
            })
        }

        GameAction::Attack(target) => {
            let hostile = match map.hostiles.get(&here) {
                Some(h) if &h.name == target => h,
                _ => return Outcome::Refused(GameRefusal::NoSuchTarget(target.clone())),
            };
            // The world's rule: the sword slays the Warden; without it, the Warden slays you.
            if world.inventory.contains(&hostile.defeated_by) {
                let effect = Some(WorldEffect::SetFlag(
                    hostile.victory_flag.0.clone(),
                    hostile.victory_flag.1,
                ));
                Outcome::Legal(Resolution {
                    narration: hostile.victory_narration.clone(),
                    status: status_after(map, world, effect.as_ref()),
                    effect,
                })
            } else {
                // A LOSING move: it lands a turn (the death is receipted), then the game is over.
                let effect = Some(WorldEffect::SetFlag(
                    hostile.death_flag.0.clone(),
                    hostile.death_flag.1,
                ));
                Outcome::Legal(Resolution {
                    narration: hostile.death_narration.clone(),
                    status: status_after(map, world, effect.as_ref()),
                    effect,
                })
            }
        }
    }
}

/// Compute the game status after `effect` would land: the post-state's room + inventory +
/// flags, checked against the lose conditions (first) and then the win objective.
fn status_after(map: &GameWorld, world: &WorldCell, effect: Option<&WorldEffect>) -> GameStatus {
    let mut room = world.scene.clone();
    let mut holds_extra: Option<String> = None;
    let mut flag_over: Option<(String, i64)> = None;
    match effect {
        Some(WorldEffect::AdvanceScene(s)) => room = s.clone(),
        Some(WorldEffect::GrantItem(i)) => holds_extra = Some(i.clone()),
        Some(WorldEffect::SetFlag(k, v)) => flag_over = Some((k.clone(), *v)),
        None => {}
    }
    let flag_val = |k: &str| -> i64 {
        if let Some((fk, fv)) = &flag_over {
            if fk == k {
                return *fv;
            }
        }
        world.flags.get(k).copied().unwrap_or(0)
    };
    let holds = |item: &str| -> bool {
        world.inventory.contains(item) || holds_extra.as_deref() == Some(item)
    };
    // Lose FIRST — death precedes any objective.
    for l in &map.lose {
        if flag_val(&l.flag) >= l.at_least {
            return GameStatus::Lost;
        }
    }
    if room == map.objective.room && holds(&map.objective.holding) {
        return GameStatus::Won;
    }
    GameStatus::Playing
}

/// The world's plain description of a room: its prose, the items visible, and the ways out.
pub fn describe_room(map: &GameWorld, room_id: &str, world: &WorldCell) -> String {
    let room = match map.rooms.get(room_id) {
        Some(r) => r,
        None => return format!("You are nowhere ({room_id})."),
    };
    let mut out = format!("{} — {}", room.name, room.description);
    let items = map.items_here(room_id, world);
    if !items.is_empty() {
        let list: Vec<&str> = items.iter().map(String::as_str).collect();
        out.push_str(&format!(" You see: {}.", list.join(", ")));
    }
    if !room.exits.is_empty() {
        let dirs: Vec<&str> = room.exits.keys().map(String::as_str).collect();
        out.push_str(&format!(" Ways out: {}.", dirs.join(", ")));
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// The AI narrator — it proposes; the world disposes.
// ─────────────────────────────────────────────────────────────────────────────

/// The AI's proposal for a turn: how it narrates the move, and the closed typed action it
/// proposes. The world resolves the action; the narration is bound honestly on-chain but has
/// NO authority over the outcome.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proposal {
    /// The AI's vivid narration (attested injection-free; carries no authority over resolution).
    pub narration: String,
    /// The closed typed action the AI proposes — the only thing that CAN change the world.
    pub action: GameAction,
}

impl Proposal {
    /// A proposal.
    pub fn new(narration: impl Into<String>, action: GameAction) -> Proposal {
        Proposal {
            narration: narration.into(),
            action,
        }
    }
}

/// **How the AI dungeon-master takes a turn** — it reads the room + the player's command and
/// returns a [`Proposal`] (a narration + a proposed [`GameAction`]). The modeled [`ScriptedGm`]
/// parses the command deterministically; the flagship plugs a real gemma2 here (it narrates and
/// emits the typed action as JSON). Whatever the brain, the resolver — not the brain — decides.
pub trait GameBrain {
    /// Narrate + propose a typed action for `command` in `room`. `Err` if the command cannot be
    /// parsed into any move (the DM asks the player to rephrase; nothing lands).
    fn take_turn(&self, room: &Room, world: &WorldCell, command: &str) -> Result<Proposal, String>;
}

/// The modeled dungeon-master brain: it parses a player command into a typed [`GameAction`] and
/// narrates a vivid line around the room. A deterministic stand-in for a real gemma2 (which would
/// narrate + emit the same typed action). Crucially it can ONLY propose one of the closed actions —
/// it has no free-text channel to the world.
#[derive(Clone, Copy, Debug, Default)]
pub struct ScriptedGm;

impl GameBrain for ScriptedGm {
    fn take_turn(
        &self,
        room: &Room,
        _world: &WorldCell,
        command: &str,
    ) -> Result<Proposal, String> {
        let c = command.trim().to_lowercase();
        let words: Vec<&str> = c.split_whitespace().collect();
        let action = parse_command(&words)
            .ok_or_else(|| format!("the dungeon master tilts their head: '{command}?'"))?;
        // A vivid line that reflects the room + the move — the AI's prose (no authority).
        let narration = match &action {
            GameAction::Move(to) => {
                format!(
                    "Torchlight wavering, {name} presses on toward {to}.",
                    name = room.name
                )
            }
            GameAction::Take(i) => format!("A glint in the gloom of the {}: the {i}.", room.name),
            GameAction::Use(i, Some(t)) => format!("With care, you work the {i} against the {t}."),
            GameAction::Use(i, None) => format!("You raise the {i}."),
            GameAction::Examine => format!("You study the {} in the flickering dark.", room.name),
            GameAction::Attack(t) => format!("Steel bared, you throw yourself at the {t}."),
        };
        Ok(Proposal::new(narration, action))
    }
}

/// Parse a lowercased, whitespace-split command into a closed [`GameAction`] (best-effort).
fn parse_command(words: &[&str]) -> Option<GameAction> {
    let head = *words.first()?;
    match head {
        "go" | "move" | "walk" | "head" => words.get(1).map(|d| GameAction::Move(d.to_string())),
        // A bare direction is a move.
        "north" | "south" | "east" | "west" | "up" | "down" => {
            Some(GameAction::Move(head.to_string()))
        }
        "take" | "grab" | "get" | "pick" => {
            // "pick up X" / "take X"
            let item = words.iter().skip(1).find(|w| **w != "up")?;
            Some(GameAction::Take(item.to_string()))
        }
        "use" => {
            let item = words.get(1)?.to_string();
            // "use X on Y"
            let on = words.iter().position(|w| *w == "on");
            let target = on.and_then(|i| words.get(i + 1)).map(|t| t.to_string());
            Some(GameAction::Use(item, target))
        }
        "look" | "examine" | "inspect" | "survey" => Some(GameAction::Examine),
        "attack" | "fight" | "strike" | "kill" => {
            words.get(1).map(|t| GameAction::Attack(t.to_string()))
        }
        _ => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The session — ties the world, the DM (attestation + caps + chain), and the state.
// ─────────────────────────────────────────────────────────────────────────────

/// The outcome of a played turn.
#[derive(Clone, Debug)]
pub enum PlayResult {
    /// A LEGAL move: the resolver admitted it, the narration was attested, and it landed as one
    /// verified turn on the chain. Carries the receipt, the world's narration, and the new status.
    Landed {
        /// The on-chain receipt of the landed turn.
        receipt: Receipt,
        /// The world's account of what happened.
        narration: String,
        /// The game status after the move.
        status: GameStatus,
        /// The action that resolved.
        action: GameAction,
    },
    /// An ILLEGAL move: the resolver refused it — the world is unchanged and NO receipt landed
    /// (the anti-ghost tooth). The reason is legible; the AI's contrary narration had no power.
    Refused(GameRefusal),
    /// The DM refused the turn at a tooth *before* resolution: an input-side slot-escape
    /// (`{{`-bearing command), an over-cap grant, an un-attestable/injecting narration, or a
    /// federation rejection. The world is unchanged and no receipt landed.
    DmRefused(DmError),
    /// The AI could not parse the command into any move (nothing lands; ask the player again).
    Unparsed(String),
}

impl PlayResult {
    /// The landed receipt, if the move landed.
    pub fn receipt(&self) -> Option<Receipt> {
        match self {
            PlayResult::Landed { receipt, .. } => Some(*receipt),
            _ => None,
        }
    }

    /// Whether this move actually changed the world (landed a turn).
    pub fn landed(&self) -> bool {
        matches!(self, PlayResult::Landed { .. })
    }
}

/// **A playable session** — the dungeon [`GameWorld`], the attested + cap-bounded
/// [`DungeonMaster`], the [`GameBrain`] (the AI narrator), and the live [`WorldCell`] state.
///
/// A turn flows: the AI proposes (narration + typed action) → the world **resolves** (the
/// resolver, deterministically) → a legal move is cap-gated + attested + appended to the chain
/// as one verified turn; an illegal move is refused in-band with no receipt. The AI's prose
/// never overrides the resolver.
pub struct GameSession<B: GameBrain = ScriptedGm> {
    map: GameWorld,
    dm: DungeonMaster<RecordedDm>,
    brain: B,
    world: WorldCell,
    status: GameStatus,
}

impl GameSession<ScriptedGm> {
    /// Open a session on `map` with the default modeled brain and a DM whose grantable
    /// whitelist is exactly the dungeon's takeable items (so a `Take` is a cap-permitted grant).
    pub fn open(map: GameWorld) -> GameSession<ScriptedGm> {
        GameSession::with_brain(map, ScriptedGm)
    }
}

impl<B: GameBrain> GameSession<B> {
    /// Open a session on `map` with a custom [`GameBrain`].
    pub fn with_brain(map: GameWorld, brain: B) -> GameSession<B> {
        let dm = DungeonMaster::recorded(crate::DmCaps::narrator(map.all_items()));
        let world = map.new_world();
        GameSession {
            map,
            dm,
            brain,
            world,
            status: GameStatus::Playing,
        }
    }

    /// The live world-cell (current room in `scene`, held items in `inventory`, flags, ledger).
    pub fn world(&self) -> &WorldCell {
        &self.world
    }

    /// The static dungeon.
    pub fn map(&self) -> &GameWorld {
        &self.map
    }

    /// The current game status.
    pub fn status(&self) -> GameStatus {
        self.status
    }

    /// The attested + cap-bounded dungeon-master.
    pub fn dm(&self) -> &DungeonMaster<RecordedDm> {
        &self.dm
    }

    /// The current room.
    pub fn current_room(&self) -> Option<&Room> {
        self.map.rooms.get(&self.world.scene)
    }

    /// The world's description of the current room.
    pub fn look(&self) -> String {
        describe_room(&self.map, &self.world.scene, &self.world)
    }

    /// **Play one turn from a player's free-text command.** The AI (brain) parses + narrates +
    /// proposes a typed action; the world resolves it; a legal move lands on the chain.
    /// `player_name` labels the turn; `text` is the raw command (slot-confinement applies).
    pub fn command(&mut self, player_name: &str, text: &str) -> PlayResult {
        if self.status != GameStatus::Playing {
            return PlayResult::Refused(GameRefusal::GameOver(self.status));
        }
        let room = match self.current_room() {
            Some(r) => r.clone(),
            None => {
                return PlayResult::Refused(GameRefusal::NoSuchExit {
                    from: self.world.scene.clone(),
                    toward: "anywhere".into(),
                })
            }
        };
        let proposal = match self.brain.take_turn(&room, &self.world, text) {
            Ok(p) => p,
            Err(msg) => return PlayResult::Unparsed(msg),
        };
        self.play(proposal, player_name, text)
    }

    /// **Play one turn from an explicit [`Proposal`]** (the AI's narration + typed action). This
    /// is the "the AI proposes, the world disposes" seam laid bare — used to drive a specific
    /// action, or to demonstrate a *jailbroken* narrator whose flowery prose the world ignores.
    ///
    /// `player_text` is the player's command bound input-side (slot-confinement + prompt binding);
    /// pass `""` for a DM-driven move with no player field.
    pub fn play(&mut self, proposal: Proposal, player_name: &str, player_text: &str) -> PlayResult {
        if self.status != GameStatus::Playing {
            return PlayResult::Refused(GameRefusal::GameOver(self.status));
        }
        // THE WORLD DISPOSES — resolve the proposed action against the rules, regardless of prose.
        let resolution = match resolve_action(&self.map, &self.world, &proposal.action) {
            Outcome::Legal(r) => r,
            Outcome::Refused(reason) => return PlayResult::Refused(reason),
        };
        let room_id = self.world.scene.clone();
        // The player's command is bound input-side (the same slot-confinement tooth): a
        // `{{`-bearing command is refused before anything lands.
        let prompt_binding = if player_text.is_empty() {
            None
        } else {
            if !slot_confined(player_text) {
                return PlayResult::DmRefused(DmError::SlotEscape);
            }
            Some(PromptBinding::new(
                self.dm.template().template_hash(),
                world_binding(&room_id),
                player_text.to_string(),
            ))
        };
        // Land ONE verified turn: the AI's narration attested (injection-free), the resolver's
        // effect cap-gated + applied, and the closed typed move bound into the receipt.
        let binding = GameBinding::new(proposal.action.clone(), room_id);
        let mv = DmMove {
            narration: proposal.narration.clone(),
            effect: resolution.effect.clone(),
        };
        match self
            .dm
            .narrate_game_move(&mut self.world, mv, prompt_binding, binding)
        {
            Ok(receipt) => {
                let _ = player_name;
                self.status = resolution.status;
                PlayResult::Landed {
                    receipt,
                    narration: resolution.narration,
                    status: resolution.status,
                    action: proposal.action,
                }
            }
            Err(e) => PlayResult::DmRefused(e),
        }
    }

    /// Re-verify the whole session ledger as a hash chain (every landed move authentic +
    /// on-chain + un-forged). The one gate a stranger runs to trust the playthrough.
    pub fn verify(&self) -> Result<(), crate::LedgerBreak> {
        self.world.verify_ledger(self.dm.config())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE SUNKEN VAULT — a complete, hand-authored dungeon with a real critical path.
// ─────────────────────────────────────────────────────────────────────────────

/// **THE SUNKEN VAULT** — a complete, solvable ten-room dungeon.
///
/// The tide has broken open an old drowned vault. To escape with its heart you must, in
/// forced order:
///
/// 1. take the **lantern** in the antechamber — the stair down is pitch dark and impassable
///    without a light (a [`Gate::NeedsItem`] `lantern`);
/// 2. descend the dark stair to the cistern and take the **rusted key**;
/// 3. carry the key to the vestry and **use it on the iron door** — that sets the
///    `door_unlocked` flag, opening the gated exit to the armory;
/// 4. take the **sword** in the armory — the Warden in the next hall will cut down anyone
///    who attacks it unarmed;
/// 5. enter the Warden's hall and **attack the Warden** (with the sword: it falls, setting
///    `warden_defeated`; without it: you die — the game is LOST);
/// 6. take the **amulet** in the treasury beyond the fallen Warden;
/// 7. carry the amulet up to the **sunken gate** — reach it HOLDING the amulet to WIN.
///
/// Every gate forces exploration order: no lantern → no descent; no key → no armory; no sword
/// → death at the Warden; no amulet → no win even standing at the gate. The `pool_grotto` is
/// an optional side room (atmosphere + a takeable pearl) off the critical path.
pub fn sunken_vault() -> GameWorld {
    let rooms = vec![
        Room::new(
            "shore",
            "Tide-Worn Shore",
            "Cold surf hisses over black rock; a cracked archway leads into the cliff.",
        )
        .exit("north", Exit::open("antechamber")),
        Room::new(
            "antechamber",
            "Salt Antechamber",
            "A dim vaulted room, walls furred with salt. A lantern hangs by the stairwell.",
        )
        .item("lantern")
        .exit("south", Exit::open("shore"))
        .exit("east", Exit::open("pool_grotto"))
        // The stair down is pitch dark — impassable without a light.
        .exit(
            "down",
            Exit::gated("dark_stair", Gate::NeedsItem("lantern".into())),
        ),
        Room::new(
            "pool_grotto",
            "Pool Grotto",
            "A still tidal pool mirrors the ceiling; a pale pearl rests on its rim.",
        )
        .item("pearl")
        .exit("west", Exit::open("antechamber")),
        Room::new(
            "dark_stair",
            "Dark Stair",
            "Lantern-light gutters against wet stone as the steps wind down.",
        )
        .exit("up", Exit::open("antechamber"))
        .exit("down", Exit::open("cistern")),
        Room::new(
            "cistern",
            "Flooded Cistern",
            "Knee-deep black water. A rusted key lies caught in a drain grate.",
        )
        .item("rusted_key")
        .exit("up", Exit::open("dark_stair"))
        .exit("north", Exit::open("vestry")),
        Room::new(
            "vestry",
            "Drowned Vestry",
            "Rotted pews face a great iron door, its lock thick with rust.",
        )
        .exit("south", Exit::open("cistern"))
        // The iron door is locked until the rusted key turns it (sets door_unlocked).
        .exit(
            "east",
            Exit::gated("armory", Gate::NeedsFlag("door_unlocked".into(), 1)),
        ),
        Room::new(
            "armory",
            "Rusted Armory",
            "Racks of ruined weapons — but one blade still holds an edge: a sword.",
        )
        .item("sword")
        .exit("west", Exit::open("vestry"))
        .exit("north", Exit::open("warden_hall")),
        Room::new(
            "warden_hall",
            "Warden's Hall",
            "A drowned knight in barnacled plate stirs — the Warden, guarding the way east.",
        )
        .exit("south", Exit::open("armory"))
        // Sealed until the Warden is defeated.
        .exit(
            "east",
            Exit::gated("treasury", Gate::NeedsFlag("warden_defeated".into(), 1)),
        ),
        Room::new(
            "treasury",
            "Sunken Treasury",
            "Silt-choked coffers, and upon a coral plinth: the Drowned Amulet.",
        )
        .item("amulet")
        .exit("west", Exit::open("warden_hall"))
        .exit("up", Exit::open("sunken_gate")),
        Room::new(
            "sunken_gate",
            "Sunken Gate",
            "A shaft of grey daylight through a broken portcullis — the way out.",
        )
        .exit("down", Exit::open("treasury")),
    ];

    let mut room_map = BTreeMap::new();
    for r in rooms {
        room_map.insert(r.id.clone(), r);
    }

    let use_rules = vec![UseRule {
        room: "vestry".into(),
        item: "rusted_key".into(),
        target: Some("iron_door".into()),
        sets_flag: ("door_unlocked".into(), 1),
        narration: "The rusted key grinds, and the iron door's lock gives with a groan.".into(),
    }];

    let mut hostiles = BTreeMap::new();
    hostiles.insert(
        "warden_hall".to_string(),
        Hostile {
            room: "warden_hall".into(),
            name: "warden".into(),
            defeated_by: "sword".into(),
            victory_flag: ("warden_defeated".into(), 1),
            death_flag: ("slain".into(), 1),
            victory_narration: "Your sword finds the gap in the barnacled plate; the Warden crashes down and moves no more.".into(),
            death_narration: "Bare-handed, you are no match — the Warden's blade takes you, and the vault keeps another bone.".into(),
        },
    );

    GameWorld {
        rooms: room_map,
        use_rules,
        hostiles,
        start: "shore".into(),
        objective: Objective {
            room: "sunken_gate".into(),
            holding: "amulet".into(),
        },
        lose: vec![LoseCondition {
            flag: "slain".into(),
            at_least: 1,
            description: "slain by the Warden".into(),
        }],
    }
}

#[cfg(test)]
mod tests;
