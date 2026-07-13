//! # The verified allocator (translation-validation style).
//!
//! An UNTRUSTED allocator ([`allocate`]) assigns each component a [`Slot`]; a CHECKED
//! obligation ([`Layout::legal`], surfaced through [`CheckedLayout::new`]) verifies the
//! output before anything downstream may read it. This mirrors the LANDED
//! `metatheory/Dregg2/Circuit/Emit/RotatedLayout.lean` discipline:
//!
//! * `RotatedLayout` there ≈ [`Layout`] here — the layout as data.
//! * `RotatedLayout.occupied` ≈ [`Layout::occupied`] — every column an instance uses.
//! * `structure Legal { disjoint : occupied.Nodup; inBounds : ∀ c ∈ occupied, c < n }`
//!   ≈ [`Layout::legal`]'s Nodup + in-bounds check.
//! * `theorem rotated178_legal : Legal rotated178 := by native_decide` (an ill-aligned
//!   layout is UNCONSTRUCTABLE) ≈ [`CheckedLayout`]: the only way to obtain one is to
//!   pass the Legal check, so an overlapping / out-of-bounds layout is a CONSTRUCTION
//!   ERROR, not a runtime panic.
//!
//! The Rust check is the imported PATTERN; the deeper Lean-PROVEN `Legal` obligation
//! over this allocator is the named follow-up (docs/GAME-STRATEGY.md Phase 2).

use crate::schema::{Archetype, Placement, Schema};

/// The number of fixed register slots a cell carries. Register keys are `0..STATE_SLOTS`;
/// heap keys are `>= STATE_SLOTS` (mirrors `dregg_cell::state::STATE_SLOTS`, re-exported
/// by spween-dregg).
pub const STATE_SLOTS: u8 = spween_dregg::STATE_SLOTS as u8;

/// Where a component's field is placed in the cell — a fixed register or a heap key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slot {
    /// Register slot `index` (`< STATE_SLOTS`).
    Register(u8),
    /// Heap key `key` (`>= STATE_SLOTS`) in the cell's `fields_map`.
    Heap(u64),
}

impl Slot {
    /// The single occupied "column" this slot uses — the domain element for the
    /// disjointness obligation. Register `r` occupies column `r` (`0..STATE_SLOTS`);
    /// heap key `k` occupies column `k` (`>= STATE_SLOTS`). The two spaces cannot alias
    /// (registers `< STATE_SLOTS <=` heap keys), so a single `u64` column space is a
    /// faithful disjointness domain.
    pub fn column(&self) -> u64 {
        match self {
            Slot::Register(r) => *r as u64,
            Slot::Heap(k) => *k,
        }
    }
}

/// One component's placement: its name, archetype, and assigned slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Assignment {
    pub component: String,
    pub archetype: Archetype,
    pub slot: Slot,
}

/// A raw (untrusted) layout — the allocator's output, before the Legal check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub assignments: Vec<Assignment>,
    /// The register-space width (`STATE_SLOTS`); a register slot is in-bounds iff
    /// `< num_registers`, a heap key iff `>= num_registers`.
    pub num_registers: u8,
}

/// Why a [`Layout`] is not [`Legal`](Layout::legal) — the disjointness / in-bounds
/// violations `CheckedLayout::new` refuses to construct past.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LegalError {
    /// Two components write the same column — the `disjoint : occupied.Nodup`
    /// obligation. THE invariant that was a comment in the 14-file emit.
    Overlap { column: u64, a: String, b: String },
    /// A register slot is `>= num_registers` — out of the register file.
    RegisterOutOfBounds {
        component: String,
        slot: u8,
        num_registers: u8,
    },
    /// A "heap" key is `< num_registers` — it aliases the register file (a heap key
    /// must be `>= STATE_SLOTS`).
    HeapAliasesRegisters {
        component: String,
        key: u64,
        num_registers: u8,
    },
}

impl core::fmt::Display for LegalError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LegalError::Overlap { column, a, b } => write!(
                f,
                "layout is not disjoint: `{a}` and `{b}` both write column {column}"
            ),
            LegalError::RegisterOutOfBounds {
                component,
                slot,
                num_registers,
            } => write!(
                f,
                "`{component}` register slot {slot} is out of bounds (num_registers = {num_registers})"
            ),
            LegalError::HeapAliasesRegisters {
                component,
                key,
                num_registers,
            } => write!(
                f,
                "`{component}` heap key {key} aliases the register file (must be >= {num_registers})"
            ),
        }
    }
}

impl std::error::Error for LegalError {}

impl Layout {
    /// Every column this layout occupies — the domain of the disjointness obligation
    /// (`RotatedLayout.occupied`).
    pub fn occupied(&self) -> Vec<u64> {
        self.assignments.iter().map(|a| a.slot.column()).collect()
    }

    /// **THE LEGALITY OBLIGATION** — decidable, mirroring `RotatedLayout`'s
    /// `Legal { disjoint, inBounds }`:
    ///
    /// * `disjoint` — `occupied` has no duplicate column (Nodup);
    /// * `inBounds` — every register slot is `< num_registers`, every heap key is
    ///   `>= num_registers`.
    ///
    /// [`CheckedLayout::new`] runs this; an illegal layout cannot become a
    /// `CheckedLayout`, so nothing downstream ever reads an ill-aligned layout.
    pub fn legal(&self) -> Result<(), LegalError> {
        // disjoint : occupied.Nodup
        for i in 0..self.assignments.len() {
            for j in (i + 1)..self.assignments.len() {
                let ci = self.assignments[i].slot.column();
                let cj = self.assignments[j].slot.column();
                if ci == cj {
                    return Err(LegalError::Overlap {
                        column: ci,
                        a: self.assignments[i].component.clone(),
                        b: self.assignments[j].component.clone(),
                    });
                }
            }
        }
        // inBounds : register < num_registers ; heap >= num_registers
        for a in &self.assignments {
            match a.slot {
                Slot::Register(r) => {
                    if r >= self.num_registers {
                        return Err(LegalError::RegisterOutOfBounds {
                            component: a.component.clone(),
                            slot: r,
                            num_registers: self.num_registers,
                        });
                    }
                }
                Slot::Heap(k) => {
                    if k < self.num_registers as u64 {
                        return Err(LegalError::HeapAliasesRegisters {
                            component: a.component.clone(),
                            key: k,
                            num_registers: self.num_registers,
                        });
                    }
                }
            }
        }
        Ok(())
    }
}

/// A layout that has PASSED the Legal check — the ONLY kind [`crate::emit`] and
/// [`crate::game`] read from. Constructing one is the sole gate; an illegal layout is a
/// construction error, exactly as an ill-aligned `RotatedLayout` is unconstructable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedLayout {
    layout: Layout,
}

impl CheckedLayout {
    /// The one gate: verify [`Layout::legal`], then wrap. Fails (never panics) on an
    /// overlapping / out-of-bounds layout.
    pub fn new(layout: Layout) -> Result<Self, LegalError> {
        layout.legal()?;
        Ok(CheckedLayout { layout })
    }

    /// The checked assignments.
    pub fn assignments(&self) -> &[Assignment] {
        &self.layout.assignments
    }

    /// The register-space width.
    pub fn num_registers(&self) -> u8 {
        self.layout.num_registers
    }

    /// Resolve a component name to its slot.
    pub fn resolve(&self, component: &str) -> Option<Slot> {
        self.layout
            .assignments
            .iter()
            .find(|a| a.component == component)
            .map(|a| a.slot)
    }
}

/// Why the allocator could not produce a layout at all (before the Legal check).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LayoutError {
    /// More register-placed components than the register file holds — a real
    /// allocation failure (the register-bound archetypes do not spill to the heap).
    OutOfRegisters { needed: usize, available: u8 },
    /// An `Invariant` names an `other` component that is not declared.
    UnknownInvariantTarget { component: String, other: String },
    /// An `Invariant` names an `other` component that is not register-placed
    /// (`FieldLteOther` indexes registers, so the referenced field must be a register).
    InvariantTargetNotRegister { component: String, other: String },
    /// Two components share a name — resolution would be ambiguous.
    DuplicateComponent { name: String },
}

impl core::fmt::Display for LayoutError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LayoutError::OutOfRegisters { needed, available } => write!(
                f,
                "schema needs {needed} register slots but the cell has {available}"
            ),
            LayoutError::UnknownInvariantTarget { component, other } => write!(
                f,
                "invariant `{component}` references undeclared field `{other}`"
            ),
            LayoutError::InvariantTargetNotRegister { component, other } => write!(
                f,
                "invariant `{component}` references non-register field `{other}` (FieldLteOther indexes registers)"
            ),
            LayoutError::DuplicateComponent { name } => {
                write!(f, "component `{name}` is declared more than once")
            }
        }
    }
}

impl std::error::Error for LayoutError {}

/// **The (untrusted) allocator.** Assign register slots `0, 1, 2, …` in declaration
/// order to register-placed components and heap keys `STATE_SLOTS, …` to collections.
/// Fails on register exhaustion or a malformed invariant reference. The OUTPUT is then
/// handed to [`CheckedLayout::new`] (translation validation: untrusted search, checked
/// output).
pub fn allocate(schema: &Schema) -> Result<Layout, LayoutError> {
    // No duplicate names (resolution must be unambiguous).
    for (i, c) in schema.components.iter().enumerate() {
        if schema.components[..i].iter().any(|d| d.name == c.name) {
            return Err(LayoutError::DuplicateComponent {
                name: c.name.clone(),
            });
        }
    }

    // Total register demand (register-placed archetypes do not spill to the heap).
    let register_total = schema
        .components
        .iter()
        .filter(|c| c.archetype.placement() == Placement::Register)
        .count();
    if register_total > STATE_SLOTS as usize {
        return Err(LayoutError::OutOfRegisters {
            needed: register_total,
            available: STATE_SLOTS,
        });
    }

    let mut assignments = Vec::with_capacity(schema.components.len());
    let mut next_reg: u8 = 0;
    let mut next_heap: u64 = STATE_SLOTS as u64;

    for c in &schema.components {
        let slot = match c.archetype.placement() {
            Placement::Register => {
                let s = Slot::Register(next_reg);
                next_reg += 1;
                s
            }
            Placement::Heap => {
                let s = Slot::Heap(next_heap);
                next_heap += 1;
                s
            }
        };
        assignments.push(Assignment {
            component: c.name.clone(),
            archetype: c.archetype.clone(),
            slot,
        });
    }

    // Validate invariant references now that every placement is known.
    for a in &assignments {
        if let Archetype::Invariant { other, .. } = &a.archetype {
            match assignments.iter().find(|b| &b.component == other) {
                None => {
                    return Err(LayoutError::UnknownInvariantTarget {
                        component: a.component.clone(),
                        other: other.clone(),
                    });
                }
                Some(b) if !matches!(b.slot, Slot::Register(_)) => {
                    return Err(LayoutError::InvariantTargetNotRegister {
                        component: a.component.clone(),
                        other: other.clone(),
                    });
                }
                Some(_) => {}
            }
        }
    }

    Ok(Layout {
        assignments,
        num_registers: STATE_SLOTS,
    })
}

/// Allocate + Legal-check in one step: the trusted path from a [`Schema`] to a
/// [`CheckedLayout`].
pub fn allocate_checked(schema: &Schema) -> Result<CheckedLayout, LayoutError> {
    let layout = allocate(schema)?;
    // The allocator produces disjoint, in-bounds layouts by construction; the Legal
    // check re-validates its output (translation validation). A Legal failure here is
    // an allocator bug, surfaced as a construction error rather than trusted away.
    CheckedLayout::new(layout).map_err(|e| {
        // Fold a Legal failure into an allocation failure for the one-step path.
        match e {
            LegalError::Overlap { a, .. } => LayoutError::DuplicateComponent { name: a },
            LegalError::RegisterOutOfBounds { .. } => LayoutError::OutOfRegisters {
                needed: schema.components.len(),
                available: STATE_SLOTS,
            },
            LegalError::HeapAliasesRegisters { component, .. } => {
                LayoutError::DuplicateComponent { name: component }
            }
        }
    })
}
