//! # MEASUREMENT ONLY — what would dropping the legacy 1-felt Merkle–Damgard chain buy?
//!
//! SUBSTRATE NOTE (say it out loud): this file AUTHORS NO AIR. Every constraint it handles was
//! emitted by the Lean rotation/wide emitters and read back out of the deployed staged registry
//! TSV. The variant built here is a purely MECHANICAL DELETION + COLUMN COMPACTION of an
//! already-Lean-emitted descriptor: drop a set of chip lookups, drop the columns that no surviving
//! constraint reads, renumber. No gate, no lookup tuple, no `air_accepts` predicate is written by
//! hand. This descriptor is NOT a deployment candidate and never touches a registry, an FP, or a
//! VK — it exists to produce a NUMBER.
//!
//! ## What is being sized
//!
//! The deployed WIDE rotated transfer (`transferVmDescriptor2R24` in
//! `circuit/descriptors/rotation-wide-registry-staged.tsv`, `trace_width = 2664`) carries 254
//! poseidon2-chip lookups. Classified by how many of the 16 input slots are genuine columns:
//!
//! | input arity | count | what it is |
//! |---|---|---|
//! | 4  | 133 | the legacy 1-felt Merkle–Damgard absorption chain |
//! | 11 | 116 | the 8-felt wide commitment chain |
//! | 9  | 2   | the two wide-chain terminators |
//! | 2  | 3   | `hash2` joins hanging off the 1-felt chain |
//!
//! ## THE CRITICAL STRUCTURAL FINDING (see `legacy_chain_is_load_bearing_at_head`)
//!
//! The 133 arity-4 sites are NOT a retired parallel structure. The producer/consumer graph over
//! the 254 chip lookups is:
//!
//! ```text
//!   arity-4 -> arity-4  : 127 edges   (the 1-felt chain, ~133 links)
//!   arity-4 -> arity-2  :   3 edges   (hash2 joins; one output lands on PI 45)
//!   arity-4 -> arity-11 :  16 edges   (= 2 sites x 8 lanes: THE SEED OF THE WIDE CHAIN)
//!   arity-11 -> arity-11: 912 edges   (the 8-felt chain proper)
//!   arity-11 -> arity-9 :  16 edges   (the two terminators)
//! ```
//!
//! The LAST TWO arity-4 sites (chain indices 131 and 132) publish all EIGHT of their permutation
//! lanes, and those sixteen columns are exactly `inputs[0..8]` of the two arity-11 lookups that
//! open the BEFORE and AFTER 8-felt commitment chains. In other words: **the faithful 8-felt
//! commitment is ROOTED IN the 1-felt chain's terminal permutation state.** Additionally a
//! legacy-chain digest column is bound to PI 8 (`pi_binding last col 88 -> pi 8`).
//!
//! So the framing "the 133 sites survive only because a Lean soundness keystone is typed to walk
//! them" is FALSE at HEAD for this descriptor. They are a data dependency of the published commit.
//! Deleting them does not remove an over-proof; it un-roots the 8-felt commit (its first 16 input
//! felts become free). The variant below therefore measures an **UPPER BOUND** on any
//! chain-removal win: a SOUND refactor must re-absorb the limbs the 1-felt chain eats into
//! arity-11 sites, buying back only the difference.
//!
//! Run (release; debug prove times are lies):
//! ```text
//! CARGO_TARGET_DIR=/tmp/nf-check cargo test -p dregg-circuit --release \
//!   --test legacy_chain_drop_measurement -- --nocapture
//! ```

use std::collections::HashSet;
use std::time::Instant;

use dregg_circuit::CellState;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, LookupSpec, MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::Effect;
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, generate_rotated_effect_vm_descriptor_and_trace_wide,
    transfer_caveat_manifest,
};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint};
use dregg_turn::rotation_witness as rw;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};

const KEY: &str = "transferVmDescriptor2R24";
/// The poseidon2-chip table wire id in the wide rotated descriptors.
const TID_P2: usize = 1;
/// `[arity, in0..in15, out0..out7]`.
const CHIP_TUPLE_LEN: usize = 25;
const CHIP_IN0: usize = 1;
const CHIP_OUT0: usize = 17;

// ---------------------------------------------------------------------------
// descriptor plumbing
// ---------------------------------------------------------------------------

fn deployed_json() -> &'static str {
    WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(KEY) {
                it.nth(1)
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{KEY} not in WIDE_REGISTRY_STAGED_TSV"))
}

fn expr_vars(e: &LeanExpr, acc: &mut HashSet<usize>) {
    match e {
        LeanExpr::Var(v) => {
            acc.insert(*v);
        }
        LeanExpr::Const(_) => {}
        LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => {
            expr_vars(a, acc);
            expr_vars(b, acc);
        }
    }
}

/// Every column any constraint in `cs` READS (or binds to a PI).
fn live_cols(cs: &[VmConstraint2]) -> HashSet<usize> {
    let mut live = HashSet::new();
    for k in cs {
        match k {
            VmConstraint2::Lookup(l) => {
                for e in &l.tuple {
                    expr_vars(e, &mut live);
                }
            }
            VmConstraint2::Base(b) => match b {
                VmConstraint::Gate(e) => expr_vars(e, &mut live),
                VmConstraint::Boundary { body, .. } => expr_vars(body, &mut live),
                VmConstraint::Transition { hi, lo } => {
                    live.insert(*hi);
                    live.insert(*lo);
                }
                VmConstraint::PiBinding { col, .. } => {
                    live.insert(*col);
                }
            },
            other => panic!("this measurement only handles gate/transition/pi/lookup: {other:?}"),
        }
    }
    live
}

/// Number of genuine `Var` slots among the 16 chip input positions (the "input arity").
fn chip_input_arity(l: &LookupSpec) -> Option<usize> {
    if l.table != TID_P2 || l.tuple.len() != CHIP_TUPLE_LEN {
        return None;
    }
    Some(
        l.tuple[CHIP_IN0..CHIP_OUT0]
            .iter()
            .filter(|e| matches!(e, LeanExpr::Var(_)))
            .count(),
    )
}

fn is_legacy_1felt_site(k: &VmConstraint2) -> bool {
    matches!(k, VmConstraint2::Lookup(l) if chip_input_arity(l) == Some(4))
}

fn remap_expr(e: &LeanExpr, m: &[Option<usize>]) -> LeanExpr {
    match e {
        LeanExpr::Var(v) => LeanExpr::Var(m[*v].expect("live column remapped")),
        LeanExpr::Const(c) => LeanExpr::Const(*c),
        LeanExpr::Add(a, b) => LeanExpr::add(remap_expr(a, m), remap_expr(b, m)),
        LeanExpr::Mul(a, b) => LeanExpr::mul(remap_expr(a, m), remap_expr(b, m)),
    }
}

fn remap_constraint(k: &VmConstraint2, m: &[Option<usize>]) -> VmConstraint2 {
    match k {
        VmConstraint2::Lookup(l) => VmConstraint2::Lookup(LookupSpec {
            table: l.table,
            tuple: l.tuple.iter().map(|e| remap_expr(e, m)).collect(),
        }),
        VmConstraint2::Base(VmConstraint::Gate(e)) => {
            VmConstraint2::Base(VmConstraint::Gate(remap_expr(e, m)))
        }
        VmConstraint2::Base(VmConstraint::Boundary { row, body }) => {
            VmConstraint2::Base(VmConstraint::Boundary {
                row: *row,
                body: remap_expr(body, m),
            })
        }
        VmConstraint2::Base(VmConstraint::Transition { hi, lo }) => {
            VmConstraint2::Base(VmConstraint::Transition {
                hi: m[*hi].expect("live"),
                lo: m[*lo].expect("live"),
            })
        }
        VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) => {
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: *row,
                col: m[*col].expect("live"),
                pi_index: *pi_index,
            })
        }
        other => panic!("unhandled constraint kind: {other:?}"),
    }
}

/// The chain-dropped variant + the column keep-mask (old index -> kept?).
///
/// Only the columns that go dead *because of the drop* are removed; columns already unread in the
/// deployed descriptor are RETAINED, so the measured width delta is attributable to the chain
/// alone and not to incidental dead-column garbage collection.
fn drop_legacy_chain(desc: &EffectVmDescriptor2) -> (EffectVmDescriptor2, Vec<bool>) {
    let base_live = live_cols(&desc.constraints);
    let kept: Vec<VmConstraint2> = desc
        .constraints
        .iter()
        .filter(|k| !is_legacy_1felt_site(k))
        .cloned()
        .collect();
    let new_live = live_cols(&kept);

    let keep_mask: Vec<bool> = (0..desc.trace_width)
        .map(|c| !base_live.contains(&c) || new_live.contains(&c))
        .collect();
    let mut map: Vec<Option<usize>> = vec![None; desc.trace_width];
    let mut n = 0usize;
    for (c, k) in keep_mask.iter().enumerate() {
        if *k {
            map[c] = Some(n);
            n += 1;
        }
    }

    let mut tables = desc.tables.clone();
    // The main table's declared arity shrinks by the same count as the dropped columns below it.
    let dropped_below_arity = (0..tables[0].arity.min(desc.trace_width))
        .filter(|c| !keep_mask[*c])
        .count();
    tables[0].arity -= dropped_below_arity;

    let variant = EffectVmDescriptor2 {
        name: format!("{}-CHAINDROP-MEASUREMENT-ONLY", desc.name),
        trace_width: n,
        public_input_count: desc.public_input_count,
        tables,
        constraints: kept.iter().map(|k| remap_constraint(k, &map)).collect(),
        hash_sites: vec![],
        ranges: vec![],
    };
    (variant, keep_mask)
}

fn project_trace(trace: &[Vec<BabyBear>], keep_mask: &[bool]) -> Vec<Vec<BabyBear>> {
    trace
        .iter()
        .map(|row| {
            row.iter()
                .enumerate()
                .filter(|(c, _)| keep_mask.get(*c).copied().unwrap_or(false))
                .map(|(_, v)| *v)
                .collect()
        })
        .collect()
}

// ---------------------------------------------------------------------------
// the honest transfer witness (same shape the pad-invariance decider uses)
// ---------------------------------------------------------------------------

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// The honest wide transfer, minted through the PRODUCTION dispatcher
/// (`generate_rotated_effect_vm_descriptor_and_trace_wide` — the call
/// `mint_rotated_participant_leg` makes for a transfer), so the descriptor, trace, PI vector and
/// witnesses are exactly the deployed set: 68 PIs = 66 producer + 2 spliced membership claim PIs.
fn honest_wide_transfer() -> (
    EffectVmDescriptor2,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
    Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
    MemBoundaryWitness,
) {
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance);
    let after_cell = producer_cell(before_balance - amount as i64);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let produce = |cell: &Cell| {
        rw::produce(
            cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let bridge =
        |w: &rw::RotationWitness| RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).unwrap();
    let before_w = produce(&before_cell);
    let after_w = produce(&after_cell);
    // The producer-honest membership-teeth pair (the 2 teeth columns pair 1:1 with the 2 claim PIs).
    let membership_teeth = (BabyBear::new(0xA11CE), BabyBear::new(0xF00D));
    let (desc, trace, dpis, map_heaps, mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &transfer_caveat_manifest(),
        None,
        None,
        None,
        Some(membership_teeth),
    )
    .expect("the deployed wide transfer leg mints");
    (desc, trace, dpis, map_heaps, mb)
}

// ---------------------------------------------------------------------------
// (1) THE STRUCTURAL FINDING — pinned, so a future emit change cannot silently
//     change the answer this measurement was taken under.
// ---------------------------------------------------------------------------

#[test]
fn legacy_chain_is_load_bearing_at_head() {
    let desc = parse_vm_descriptor2(deployed_json()).expect("deployed wide transfer parses");
    assert_eq!(desc.trace_width, 2664, "deployed wide transfer width");

    let mut hist = std::collections::BTreeMap::<usize, usize>::new();
    for k in &desc.constraints {
        if let VmConstraint2::Lookup(l) = k {
            if let Some(a) = chip_input_arity(l) {
                *hist.entry(a).or_default() += 1;
            }
        }
    }
    println!("chip-lookup input-arity histogram at HEAD: {hist:?}");
    assert_eq!(hist.get(&4), Some(&133), "133 legacy 1-felt sites");
    assert_eq!(hist.get(&11), Some(&116), "116 wide 8-felt sites");
    assert_eq!(hist.get(&9), Some(&2), "2 wide terminators");
    assert_eq!(hist.get(&2), Some(&3), "3 hash2 joins");

    // Which columns does each arity-4 site PRODUCE?
    let mut legacy_out: HashSet<usize> = HashSet::new();
    for k in &desc.constraints {
        if let VmConstraint2::Lookup(l) = k {
            if chip_input_arity(l) == Some(4) {
                for e in &l.tuple[CHIP_OUT0..] {
                    expr_vars(e, &mut legacy_out);
                }
            }
        }
    }

    // Do any arity-11 (8-felt wide chain) sites READ a legacy output?
    let mut wide_sites_seeded_by_legacy = 0usize;
    let mut seeded_lanes = 0usize;
    for k in &desc.constraints {
        if let VmConstraint2::Lookup(l) = k {
            if chip_input_arity(l) == Some(11) {
                let hits = l.tuple[CHIP_IN0..CHIP_OUT0]
                    .iter()
                    .filter(|e| matches!(e, LeanExpr::Var(v) if legacy_out.contains(v)))
                    .count();
                if hits > 0 {
                    wide_sites_seeded_by_legacy += 1;
                    seeded_lanes += hits;
                }
            }
        }
    }
    println!(
        "arity-11 wide-commit sites SEEDED by legacy-chain output: {wide_sites_seeded_by_legacy} \
         (across {seeded_lanes} input lanes)"
    );
    assert_eq!(
        (wide_sites_seeded_by_legacy, seeded_lanes),
        (2, 16),
        "THE FINDING: the BEFORE and AFTER 8-felt commitment chains each open on all EIGHT \
         permutation lanes of a legacy 1-felt site. The published 8-felt commit is ROOTED IN the \
         1-felt chain — the 133 sites are a DATA DEPENDENCY, not an over-proof residue."
    );

    // And a legacy digest is directly PUBLISHED.
    let published: Vec<usize> = desc
        .constraints
        .iter()
        .filter_map(|k| match k {
            VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. })
                if legacy_out.contains(col) =>
            {
                Some(*pi_index)
            }
            _ => None,
        })
        .collect();
    println!("PI indices bound directly to a legacy-chain output column: {published:?}");
    assert!(
        !published.is_empty(),
        "a legacy-chain digest is bound to a public input"
    );
}

// ---------------------------------------------------------------------------
// (2) THE MEASUREMENT
// ---------------------------------------------------------------------------

fn breakdown(
    label: &str,
    proof: &p3_batch_stark::BatchProof<dregg_circuit::plonky3_prover::DreggStarkConfig>,
) -> (usize, usize, usize) {
    let total = postcard::to_allocvec(proof).expect("postcard").len();
    let opened = postcard::to_allocvec(&proof.opened_values).unwrap().len();
    let opening = postcard::to_allocvec(&proof.opening_proof).unwrap().len();
    let commitments = postcard::to_allocvec(&proof.commitments).unwrap().len();
    let lookups = postcard::to_allocvec(&proof.global_lookup_data)
        .unwrap()
        .len();
    println!(
        "[{label}] proof {total} B | commitments {commitments} B | opened_values {opened} B | \
         opening_proof {opening} B | lookup_data {lookups} B | degree_bits {:?}",
        proof.degree_bits
    );
    for (i, inst) in proof.opened_values.instances.iter().enumerate() {
        println!(
            "[{label}]   instance {i}: log2(h)={} main_cols={} perm_cols(ext)={} quotient_chunks={}",
            proof.degree_bits.get(i).copied().unwrap_or(0),
            inst.base_opened_values.trace_local.len(),
            inst.permutation_local.len(),
            inst.base_opened_values.quotient_chunks.len(),
        );
    }
    (total, opened, opening)
}

#[test]
fn chain_drop_cost_measurement() {
    const REPS: usize = 3;

    let (deployed, mut trace, pis, heaps, mem) = honest_wide_transfer();
    // The dispatcher resolves the DEPLOYED registry member — pin that, so this measurement can
    // never silently drift onto some other descriptor.
    assert_eq!(deployed.trace_width, 2664, "deployed wide transfer width");
    assert_eq!(deployed.public_input_count, 68, "66 producer + 2 claim PIs");
    assert_eq!(
        deployed.name,
        parse_vm_descriptor2(deployed_json()).unwrap().name
    );
    assert_eq!(pis.len(), deployed.public_input_count);

    // The producer emits rows at the PRE-LANE width (= the main table's declared arity); the
    // prover's `trace_with_chip_lanes` grows them to `trace_width` and fills the chip lane
    // columns. Grow here so the column projection below is indexed in `trace_width` space.
    for row in &mut trace {
        row.resize(deployed.trace_width, BabyBear::ZERO);
    }

    let (variant, keep_mask) = drop_legacy_chain(&deployed);
    let vtrace = project_trace(&trace, &keep_mask);
    assert_eq!(vtrace[0].len(), variant.trace_width);

    println!("=========================================================");
    println!(
        "deployed : name={} width={}",
        deployed.name, deployed.trace_width
    );
    println!(
        "variant  : name={} width={} (dropped {} columns, {} constraints)",
        variant.name,
        variant.trace_width,
        deployed.trace_width - variant.trace_width,
        deployed.constraints.len() - variant.constraints.len(),
    );
    println!("=========================================================");

    let mut run = |label: &str, d: &EffectVmDescriptor2, t: &[Vec<BabyBear>]| {
        let mut prove_ms = Vec::new();
        let mut verify_us = Vec::new();
        let mut bytes = (0usize, 0usize, 0usize);
        for r in 0..REPS {
            let t0 = Instant::now();
            let proof = prove_vm_descriptor2(d, t, &pis, &mem, &heaps)
                .unwrap_or_else(|e| panic!("[{label}] MUST PROVE: {e}"));
            prove_ms.push(t0.elapsed().as_secs_f64() * 1000.0);
            let t1 = Instant::now();
            verify_vm_descriptor2(d, &proof, &pis)
                .unwrap_or_else(|e| panic!("[{label}] MUST VERIFY: {e}"));
            verify_us.push(t1.elapsed().as_secs_f64() * 1000.0);
            if r == 0 {
                bytes = breakdown(label, &proof);
            }
        }
        prove_ms.sort_by(f64::total_cmp);
        verify_us.sort_by(f64::total_cmp);
        println!(
            "[{label}] prove(+selfverify) ms: min {:.1} med {:.1} max {:.1} | verify ms: min {:.2} med {:.2} max {:.2}",
            prove_ms[0],
            prove_ms[REPS / 2],
            prove_ms[REPS - 1],
            verify_us[0],
            verify_us[REPS / 2],
            verify_us[REPS - 1],
        );
        (bytes, prove_ms[0], verify_us[0])
    };

    let (dep_bytes, dep_prove, dep_verify) = run("DEPLOYED", &deployed, &trace);
    let (var_bytes, var_prove, var_verify) = run("CHAINDROP", &variant, &vtrace);

    let pct = |a: f64, b: f64| (b - a) / a * 100.0;
    println!("=========== DELTA (deployed -> chain-dropped) ===========");
    println!(
        "main trace_width : {} -> {}  ({:+}, {:+.1}%)",
        deployed.trace_width,
        variant.trace_width,
        variant.trace_width as i64 - deployed.trace_width as i64,
        pct(deployed.trace_width as f64, variant.trace_width as f64)
    );
    println!(
        "proof bytes      : {} -> {}  ({:+}, {:+.1}%)",
        dep_bytes.0,
        var_bytes.0,
        var_bytes.0 as i64 - dep_bytes.0 as i64,
        pct(dep_bytes.0 as f64, var_bytes.0 as f64)
    );
    println!(
        "  opened_values  : {} -> {}  ({:+.1}%)",
        dep_bytes.1,
        var_bytes.1,
        pct(dep_bytes.1 as f64, var_bytes.1 as f64)
    );
    println!(
        "  opening_proof  : {} -> {}  ({:+.1}%)",
        dep_bytes.2,
        var_bytes.2,
        pct(dep_bytes.2 as f64, var_bytes.2 as f64)
    );
    println!(
        "prover ms (best) : {:.1} -> {:.1}  ({:+.1}%)",
        dep_prove,
        var_prove,
        pct(dep_prove, var_prove)
    );
    println!(
        "verify ms (best) : {:.2} -> {:.2}  ({:+.1}%)",
        dep_verify,
        var_verify,
        pct(dep_verify, var_verify)
    );
    println!("========================================================");
    println!(
        "READ THIS WITH `legacy_chain_is_load_bearing_at_head`: the variant is NOT a sound \
         replacement (the 8-felt commit loses its root), so this delta is the CEILING of any \
         chain-removal campaign, not its yield."
    );
}
