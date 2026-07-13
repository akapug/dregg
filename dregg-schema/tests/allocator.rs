//! The verified-allocator teeth: the Legal obligation bites NON-VACUOUSLY (a
//! conflicting / out-of-bounds layout FAILS to construct), and the allocator refuses an
//! over-capacity or malformed schema.

use dregg_schema::{
    Archetype, Assignment, CheckedLayout, Layout, LayoutError, LegalError, STATE_SLOTS, Schema,
    Slot, allocate, descent_schema,
};

#[test]
fn descent_allocates_to_a_legal_disjoint_layout() {
    let schema = descent_schema();
    let layout = allocate(&schema).expect("descent allocates");
    // The allocator's output passes the Legal check (disjoint + in-bounds).
    layout.legal().expect("allocated layout is Legal");

    // Deterministic register order, collection spilled to the heap.
    let checked = CheckedLayout::new(layout).expect("checked");
    assert_eq!(checked.resolve("hp"), Some(Slot::Register(0)));
    assert_eq!(checked.resolve("floor"), Some(Slot::Register(1)));
    assert_eq!(checked.resolve("gold"), Some(Slot::Register(2)));
    assert_eq!(checked.resolve("owner"), Some(Slot::Register(3)));
    assert_eq!(checked.resolve("shield"), Some(Slot::Register(4)));
    assert_eq!(
        checked.resolve("items"),
        Some(Slot::Heap(STATE_SLOTS as u64))
    );
}

#[test]
fn conflicting_declaration_fails_to_construct() {
    // A hand-built layout where two components write the SAME register column — the
    // disjointness (Nodup) obligation must refuse it. This is the non-vacuity witness:
    // the Legal check is load-bearing, not always-true.
    let bad = Layout {
        assignments: vec![
            Assignment {
                component: "hp".into(),
                archetype: Archetype::Stat { min: 0, max: 20 },
                slot: Slot::Register(3),
            },
            Assignment {
                component: "gold".into(),
                archetype: Archetype::Resource,
                slot: Slot::Register(3), // <-- collides with hp
            },
        ],
        num_registers: STATE_SLOTS,
    };
    match CheckedLayout::new(bad) {
        Err(LegalError::Overlap { column, .. }) => assert_eq!(column, 3),
        other => panic!("expected Overlap, got {other:?}"),
    }
}

#[test]
fn out_of_bounds_register_fails_to_construct() {
    let bad = Layout {
        assignments: vec![Assignment {
            component: "hp".into(),
            archetype: Archetype::Stat { min: 0, max: 20 },
            slot: Slot::Register(STATE_SLOTS + 4), // beyond the register file
        }],
        num_registers: STATE_SLOTS,
    };
    assert!(matches!(
        CheckedLayout::new(bad),
        Err(LegalError::RegisterOutOfBounds { .. })
    ));
}

#[test]
fn heap_key_aliasing_registers_fails_to_construct() {
    let bad = Layout {
        assignments: vec![Assignment {
            component: "items".into(),
            archetype: Archetype::Collection,
            slot: Slot::Heap(5), // < STATE_SLOTS: aliases the register file
        }],
        num_registers: STATE_SLOTS,
    };
    assert!(matches!(
        CheckedLayout::new(bad),
        Err(LegalError::HeapAliasesRegisters { .. })
    ));
}

#[test]
fn over_capacity_schema_fails_to_allocate() {
    // 17 register-bound stats: one more than the 16-slot register file. The
    // register-bound archetypes do NOT spill to the heap, so this is a real allocation
    // failure (not a silent overflow).
    let mut schema = Schema::new("too-big");
    for i in 0..(STATE_SLOTS as usize + 1) {
        schema = schema.stat(format!("s{i}"), 0, 100);
    }
    match allocate(&schema) {
        Err(LayoutError::OutOfRegisters { needed, available }) => {
            assert_eq!(needed, STATE_SLOTS as usize + 1);
            assert_eq!(available, STATE_SLOTS);
        }
        other => panic!("expected OutOfRegisters, got {other:?}"),
    }
}

#[test]
fn many_collections_spill_to_the_heap() {
    // Collections are heap-placed, so a schema with many of them allocates fine (they
    // do not consume the register file).
    let mut schema = Schema::new("hoarder").stat("hp", 0, 20);
    for i in 0..40 {
        schema = schema.collection(format!("bag{i}"));
    }
    let layout = allocate(&schema).expect("collections spill to heap");
    layout.legal().expect("legal");
    let checked = CheckedLayout::new(layout).unwrap();
    assert_eq!(checked.resolve("hp"), Some(Slot::Register(0)));
    assert_eq!(
        checked.resolve("bag0"),
        Some(Slot::Heap(STATE_SLOTS as u64))
    );
    assert_eq!(
        checked.resolve("bag39"),
        Some(Slot::Heap(STATE_SLOTS as u64 + 39))
    );
}

#[test]
fn malformed_invariant_reference_fails_to_allocate() {
    // References an undeclared field.
    let schema = Schema::new("bad-inv")
        .stat("hp", 0, 20)
        .invariant("shield", "nope", 0);
    assert!(matches!(
        allocate(&schema),
        Err(LayoutError::UnknownInvariantTarget { .. })
    ));

    // References a heap (collection) field — FieldLteOther indexes registers only.
    let schema2 = Schema::new("bad-inv2")
        .collection("bag")
        .invariant("shield", "bag", 0);
    assert!(matches!(
        allocate(&schema2),
        Err(LayoutError::InvariantTargetNotRegister { .. })
    ));
}

#[test]
fn duplicate_component_fails_to_allocate() {
    let schema = Schema::new("dup").stat("hp", 0, 20).resource("hp");
    assert!(matches!(
        allocate(&schema),
        Err(LayoutError::DuplicateComponent { .. })
    ));
}
