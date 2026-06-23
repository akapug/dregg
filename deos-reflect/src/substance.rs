//! The four substances + the uniform reflective view of a cell.
//!
//! Every cell carries FOUR substances (DREGG-CALCULUS): **value** (balance/nonce),
//! **authority** (the c-list of capabilities), **state** (the field slots + program),
//! and **evidence** (lifecycle/delegation/commit height). [`reflect_cell`] projects
//! them into a uniform [`Inspectable`] — a flat tree of typed [`Field`]s any view
//! renders the same way. Ported from starbridge-v2's gpui-free `reflect.rs`, rebased
//! off the cockpit `World` onto a bare [`dregg_cell::Cell`].
//!
//! Reflection is ATTESTED, not omniscient: state fields are read through
//! [`dregg_cell::state::CellState::get_field_public`], so a `Committed` field surfaces
//! its COMMITMENT, never the cleartext — the redaction the substance itself enforces.

use dregg_cell::state::PublicFieldView;
use dregg_cell::{Cell, CellId};

/// A typed value in a reflected object's field list. A view renders each variant
/// distinctly (an id navigates; a `CapEdge` draws a graph edge; a `Committed` slot
/// shows a redaction badge, not a value).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FieldValue {
    Text(String),
    /// A signed balance (issuer wells carry −supply — render distinctly).
    Balance(i64),
    Count(u64),
    Bool(bool),
    /// A 32-byte hex id that navigates to another object.
    Id([u8; 32]),
    /// A 32-byte hash (receipt/turn/state-commit) — provenance, navigable.
    Hash([u8; 32]),
    /// A capability edge (this object → target), the ocap-graph primitive.
    CapEdge {
        target: [u8; 32],
        slot: u32,
    },
    /// A REVEALED (public) field slot's raw contents.
    FieldSlot {
        index: usize,
        hex: String,
    },
    /// A COMMITTED field slot: the holder disclosed only the commitment hash, never
    /// the value. The attested-read redaction made visible.
    CommittedSlot {
        index: usize,
        commitment: [u8; 32],
    },
}

/// One labeled field of a reflected object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    pub key: String,
    pub value: FieldValue,
}

impl Field {
    pub fn text(key: impl Into<String>, v: impl Into<String>) -> Self {
        Field {
            key: key.into(),
            value: FieldValue::Text(v.into()),
        }
    }
    pub fn balance(key: impl Into<String>, v: i64) -> Self {
        Field {
            key: key.into(),
            value: FieldValue::Balance(v),
        }
    }
    pub fn count(key: impl Into<String>, v: u64) -> Self {
        Field {
            key: key.into(),
            value: FieldValue::Count(v),
        }
    }
    pub fn boolean(key: impl Into<String>, v: bool) -> Self {
        Field {
            key: key.into(),
            value: FieldValue::Bool(v),
        }
    }
    pub fn id(key: impl Into<String>, v: [u8; 32]) -> Self {
        Field {
            key: key.into(),
            value: FieldValue::Id(v),
        }
    }
    pub fn hash(key: impl Into<String>, v: [u8; 32]) -> Self {
        Field {
            key: key.into(),
            value: FieldValue::Hash(v),
        }
    }
}

/// What kind of dregg object this is (drives the view's icon/affordances).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjectKind {
    Cell,
    Capability,
    Receipt,
    Image,
}

/// The uniform reflective view of ANY dregg object. Every view consumes this; no view
/// knows the concrete protocol type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Inspectable {
    pub kind: ObjectKind,
    pub title: String,
    pub subtitle: String,
    pub fields: Vec<Field>,
}

/// **Project a cell into the uniform reflective object** — all four substances.
///
/// State slots are read through `get_field_public`, so a `Committed` slot surfaces a
/// [`FieldValue::CommittedSlot`] (the commitment, redacted), NOT the value. This is
/// the attested read: the reflector cannot show what the substance withholds.
pub fn reflect_cell(id: &CellId, cell: &Cell) -> Inspectable {
    let has_program = !matches!(cell.program, dregg_cell::CellProgram::None);
    let mut fields = vec![
        // value
        Field::balance("balance", cell.state.balance()),
        Field::count("nonce", cell.state.nonce()),
        // identity
        Field::id("id", *id.as_bytes()),
        Field::id("public_key", *cell.public_key()),
        Field::id("token_id", *cell.token_id()),
        // authority
        Field::count("capabilities", cell.capabilities.len() as u64),
        Field::boolean("has_delegate", cell.delegate.is_some()),
        // state
        Field::boolean("has_program", has_program),
        Field::text("mode", format!("{:?}", cell.mode)),
        // evidence
        Field::text("lifecycle", lifecycle_label(cell)),
        Field::count("delegation_epoch", cell.state.delegation_epoch()),
        Field::count("committed_height", cell.state.committed_height()),
    ];
    if let Some(d) = &cell.delegate {
        fields.push(Field::id("delegate", *d.as_bytes()));
    }
    // authority — one CapEdge per held capability (the ocap-graph primitive).
    for cap in cell.capabilities.iter() {
        fields.push(Field {
            key: format!("cap[{}]", cap.slot),
            value: FieldValue::CapEdge {
                target: *cap.target.as_bytes(),
                slot: cap.slot,
            },
        });
    }
    // state — the field slots, read PUBLICLY (attested redaction). Only non-trivial
    // slots are surfaced to keep the view legible.
    for i in 0..dregg_cell::state::STATE_SLOTS {
        match cell.state.get_field_public(i) {
            Some(PublicFieldView::Revealed(fe)) if fe.iter().any(|b| *b != 0) => {
                fields.push(Field {
                    key: format!("state[{i}]"),
                    value: FieldValue::FieldSlot {
                        index: i,
                        hex: hex_encode(&fe),
                    },
                });
            }
            Some(PublicFieldView::Committed(commitment)) => {
                fields.push(Field {
                    key: format!("state[{i}]"),
                    value: FieldValue::CommittedSlot {
                        index: i,
                        commitment,
                    },
                });
            }
            _ => {}
        }
    }
    Inspectable {
        kind: ObjectKind::Cell,
        title: format!("Cell {}", short_hex(id.as_bytes())),
        subtitle: format!(
            "{} computrons · {} caps · {}",
            cell.state.balance(),
            cell.capabilities.len(),
            lifecycle_label(cell),
        ),
        fields,
    }
}

/// A short operator-legible lifecycle label.
pub fn lifecycle_label(cell: &Cell) -> String {
    match &cell.lifecycle {
        dregg_cell::CellLifecycle::Live => "live".into(),
        dregg_cell::CellLifecycle::Sealed { .. } => "sealed".into(),
        dregg_cell::CellLifecycle::Migrated { .. } => "migrated".into(),
        other => format!("{other:?}").to_lowercase(),
    }
}

/// Abbreviate a 32-byte id to `aabbcc…wwxx` for legible display.
pub fn short_hex(bytes: &[u8]) -> String {
    let h = hex_encode(bytes);
    if h.len() <= 12 {
        h
    } else {
        format!("{}…{}", &h[..6], &h[h.len() - 4..])
    }
}

/// Lowercase hex of a byte slice (no external `hex` dep — keep the substrate lean).
pub fn hex_encode(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push(char::from_digit((b >> 4) as u32, 16).unwrap());
        s.push(char::from_digit((b & 0xf) as u32, 16).unwrap());
    }
    s
}
