//! # The typed component schema — what an author declares.
//!
//! A [`Schema`] is an ordered list of typed [`Component`]s. Each component carries an
//! [`Archetype`] naming which cell-program tooth it compiles to (the ISA in
//! `cell/src/program/types.rs`). The author never writes a `StateConstraint`, a slot
//! index, or a heap key — they declare INTENT ("hp is a stat bounded 0..=20", "gold is
//! a monotone resource"), and the allocator ([`crate::layout`]) + emitter
//! ([`crate::emit`]) lower it to a verified layout + program.

/// Where a component's field lives in the cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Placement {
    /// One of the 16 fixed register slots (`0..STATE_SLOTS`). The static / cross-field
    /// vocabulary (`FieldGte`/`FieldLte`/`WriteOnce`/`Monotonic`/`FieldLteOther`)
    /// indexes registers by `u8`.
    Register,
    /// A heap key (`>= STATE_SLOTS`) in the cell's `fields_map`. The collection lane —
    /// `HeapField` lifts a `HeapAtom` over an unbounded heap key.
    Heap,
}

/// The typed archetype of a component — the intent that fixes which tooth it compiles
/// to. Each variant is one archetype in the keystone (docs/GAME-STRATEGY.md Phase 2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Archetype {
    /// A bounded stat: `min <= field <= max` on every admitted move. Lowers to
    /// `FieldGte { min } + FieldLte { max }`. (hp in `0..=20`, floor in `1..=99`.)
    Stat { min: u64, max: u64 },
    /// A monotone resource: the field never decreases. Lowers to `Monotonic`.
    /// (gold, score, xp — a value only accrued.)
    Resource,
    /// A write-once identity: the field freezes after its first nonzero write. Lowers
    /// to `WriteOnce`. (owner key, character id — set at genesis, immutable after.)
    Identity,
    /// A cross-field invariant: `self <= other + delta` on every admitted move. Lowers
    /// to `FieldLteOther { other, delta }`. `other` names another REGISTER component.
    /// (shield `<= hp` is `Invariant { other: "hp", delta: 0 }`.)
    Invariant { other: String, delta: i64 },
    /// A heap-keyed monotone collection counter: an unbounded, only-growing count on a
    /// heap key. Lowers to `HeapField { HeapAtom::Monotonic }`. (items collected — the
    /// >16-field lane that spills off the registers.)
    Collection,
}

impl Archetype {
    /// Which cell region this archetype's field occupies.
    pub fn placement(&self) -> Placement {
        match self {
            Archetype::Collection => Placement::Heap,
            _ => Placement::Register,
        }
    }
}

/// One declared component: a name + its archetype.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Component {
    pub name: String,
    pub archetype: Archetype,
}

/// A game's declared state schema: a name + an ordered list of typed components.
///
/// Built fluently; the order is the deterministic allocation order (register slots
/// assigned `0, 1, 2, …` in declaration order, heap keys `STATE_SLOTS, …`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Schema {
    pub name: String,
    pub components: Vec<Component>,
}

impl Schema {
    /// Start a new schema named `name` (the name drives the deterministic world-cell
    /// identity, exactly as a spween `scene_id` does).
    pub fn new(name: impl Into<String>) -> Self {
        Schema {
            name: name.into(),
            components: Vec::new(),
        }
    }

    fn push(mut self, name: impl Into<String>, archetype: Archetype) -> Self {
        self.components.push(Component {
            name: name.into(),
            archetype,
        });
        self
    }

    /// Declare a bounded stat `min <= name <= max`.
    pub fn stat(self, name: impl Into<String>, min: u64, max: u64) -> Self {
        self.push(name, Archetype::Stat { min, max })
    }

    /// Declare a monotone resource (never decreases).
    pub fn resource(self, name: impl Into<String>) -> Self {
        self.push(name, Archetype::Resource)
    }

    /// Declare a write-once identity.
    pub fn identity(self, name: impl Into<String>) -> Self {
        self.push(name, Archetype::Identity)
    }

    /// Declare a cross-field invariant `name <= other + delta`.
    pub fn invariant(self, name: impl Into<String>, other: impl Into<String>, delta: i64) -> Self {
        self.push(
            name,
            Archetype::Invariant {
                other: other.into(),
                delta,
            },
        )
    }

    /// Declare a heap-keyed monotone collection counter.
    pub fn collection(self, name: impl Into<String>) -> Self {
        self.push(name, Archetype::Collection)
    }

    /// Look up a component by name.
    pub fn get(&self, name: &str) -> Option<&Component> {
        self.components.iter().find(|c| c.name == name)
    }
}
