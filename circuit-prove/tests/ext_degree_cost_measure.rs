//! # THE COST SIDE OF THE EXTENSION-DEGREE DECISION — measured, not intuited.
//!
//! ## Why this file exists
//!
//! `docs/reference/FRI-BOTH-WIN-LEVERS.md` §1.2 derives the proven ceiling
//!
//! ```text
//! CEILING = 30.907·d − 12.65 − 2·log₂(T) − 3.5·lb
//! ```
//!
//! so the **security** side of "raise the BabyBear extension degree" is known: +30.91 proven bits per
//! degree. The **cost** side is not. §3.5 of that doc states an *estimate* — *"Estimated 4→8 slowdown
//! ≈ 1.3–1.6× — an estimate, not a measurement"* — and prices it off an extension-multiply microbench
//! plus a qualitative claim that trace LDE + Merkle (base-field, D-independent) dominate at ~70–85%.
//!
//! **This file measures it.** It runs a real `p3-uni-stark` prove — the same engine, the same
//! Poseidon2/Merkle/FRI stack, the same two deployed FRI knob-sets — at extension degree **4, 5, and 8**,
//! and reports wall-clock, verify time, and serialized proof size for each.
//!
//! ## What is REAL here and what is a PROXY — read this before quoting a number
//!
//! * **REAL**: the prover. Every path a deployed prove takes — `Radix2DitParallel` LDE, the
//!   Poseidon2-BabyBear `MerkleTreeMmcs` commit, quotient computation, the `TwoAdicFriPcs` FRI
//!   commit/query phases, the `DuplexChallenger` transcript — is the pinned plonky3 (rev `82cfad73`),
//!   unmodified. Only the `Challenge` type argument moves.
//! * **REAL**: the FRI knob-sets. `LEAF` is `circuit::plonky3_prover::PROD_FRI_*` (lb 3 / q 38);
//!   `WRAP` is the rotated leaf-wrap / apex config (lb 6 / q 19,
//!   `circuit-prove/src/ivc_turn_chain.rs` `ir2_leaf_wrap_config`).
//! * **PROXY**: the AIR. The deployed leaf/apex are multi-table `p3-batch-stark` circuits whose AIRs
//!   are reachable only through `DreggRecursionConfig`, which pins `D = 4` at
//!   `circuit-prove/src/plonky3_recursion_impl.rs:74` (and ~30 sibling sites). Retargeting THOSE to
//!   D=5/8 is the engineering this file is a decision input for — so it cannot be a precondition of
//!   the measurement. Instead this proves a **degree-7 AIR at deployed-shaped height and width**
//!   through the identical single-table engine. It measures how prover wall-clock responds to `D`;
//!   it does not claim to be the deployed leaf's absolute prove time.
//!
//! ## The one thing the D-sweep buys that a microbench cannot
//!
//! An extension-multiply microbench prices the *ingredient*. The end-to-end sweep prices the *dish*:
//! `T(D)/T(4)` **is** the answer to ember's question, and — combined with the microbench in
//! [`ext_mul_microbench`] — it lets the extension-arithmetic **fraction** of prover time be solved for
//! rather than asserted, which is the ceiling on how much degree can ever slow the prover.
//!
//! Run: `cargo test -p dregg-circuit-prove --release --test ext_degree_cost_measure -- --nocapture`

use std::time::{Duration, Instant};

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::{BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{StarkConfig, prove, verify};

// ---------------------------------------------------------------------------
// The AIR — degree 7, deployed-shaped width. Identical at every D.
// ---------------------------------------------------------------------------

/// `PAIRS` columns of `x`, each with a witnessed `x^7`. Width = `2·PAIRS`, constraint degree 7 (the
/// deployed max — the Poseidon2 S-box, `descriptor_ir2.rs:5418-5420`), which is what forces `lb ≥ 3`.
struct Degree7Air<const PAIRS: usize>;

impl<const PAIRS: usize, F: PrimeCharacteristicRing + Sync> BaseAir<F> for Degree7Air<PAIRS> {
    fn width(&self) -> usize {
        2 * PAIRS
    }
    fn num_public_values(&self) -> usize {
        0
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        Some(7)
    }
}

impl<const PAIRS: usize, AB: AirBuilder> Air<AB> for Degree7Air<PAIRS> {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        for i in 0..PAIRS {
            let x: AB::Expr = local[2 * i].into();
            let x7: AB::Expr = local[2 * i + 1].into();
            builder.assert_eq(x.exp_const_u64::<7>(), x7);
        }
    }
}

fn trace<const PAIRS: usize>(log_height: usize) -> RowMajorMatrix<P3BabyBear> {
    let height = 1usize << log_height;
    let mut values = Vec::with_capacity(height * 2 * PAIRS);
    for r in 0..height {
        for c in 0..PAIRS {
            let x = P3BabyBear::new(((r * 2 * PAIRS + c) as u32 % 0x7800_0000).wrapping_add(3));
            values.push(x);
            values.push(x.exp_const_u64::<7>());
        }
    }
    RowMajorMatrix::new(values, 2 * PAIRS)
}

// ---------------------------------------------------------------------------
// The config, instantiated once per extension degree.
//
// Byte-for-byte the deployed shape of `circuit::plonky3_prover` (Poseidon2-16 sponge, truncated
// permutation compressor, `MerkleTreeMmcs<_, _, _, _, 2, 8>`, `DuplexChallenger<_, _, 16, 8>`,
// `Radix2DitParallel` DFT, `TwoAdicFriPcs`) with `EF` as the only free parameter.
// ---------------------------------------------------------------------------

type Perm16 = Poseidon2BabyBear<16>;
type Hash = PaddingFreeSponge<Perm16, 16, 8, 8>;
type Compress = TruncatedPermutation<Perm16, 2, 8, 16>;
type ValMmcs = MerkleTreeMmcs<
    <P3BabyBear as Field>::Packing,
    <P3BabyBear as Field>::Packing,
    Hash,
    Compress,
    2,
    8,
>;
type Chal = DuplexChallenger<P3BabyBear, Perm16, 16, 8>;
type Dft = Radix2DitParallel<P3BabyBear>;

/// Timed repeats per cell; the reported number is the MIN (see the runner).
const REPS: usize = 3;

/// One measured (degree × shape) cell.
#[derive(Debug, Clone, Copy)]
struct Cell {
    ext_degree: usize,
    prove: Duration,
    verify: Duration,
    proof_bytes: usize,
}

/// A deployed FRI knob-set.
#[derive(Debug, Clone, Copy)]
struct Knobs {
    name: &'static str,
    log_blowup: usize,
    num_queries: usize,
    query_pow_bits: usize,
    max_log_arity: usize,
    log_final_poly_len: usize,
    log_height: usize,
}

/// `circuit::plonky3_prover::PROD_FRI_*` — the deployed v1 leaf engine.
const LEAF: Knobs = Knobs {
    name: "LEAF  (lb=3, q=38, pow=16)",
    log_blowup: 3,
    num_queries: 38,
    query_pow_bits: 16,
    max_log_arity: 3,
    log_final_poly_len: 0,
    log_height: 14,
};

/// The rotated leaf-wrap / apex engine (`ir2_leaf_wrap_config`), at the `WRAP_LOG_CEIL = 16`
/// trace-height floor every running fold is padded to (`circuit-prove/src/accumulator.rs:238`).
/// `|D⁽⁰⁾| = 2^22` — the domain the apex, i.e. the artifact a light client verifies, is proven over.
const WRAP: Knobs = Knobs {
    name: "WRAP  (lb=6, q=19, pow=16)",
    log_blowup: 6,
    num_queries: 19,
    query_pow_bits: 16,
    max_log_arity: 3,
    log_final_poly_len: 0,
    log_height: 16,
};

/// The wrap FRI engine two trace-doublings down (`|D⁽⁰⁾| = 2^20`). Exists so the WIDE cell can be
/// measured at the wrap's `lb=6` at all: at `log_height 16 × width 128 × blowup 64` the LDE alone is
/// `2^22 × 128 × 4 B = 2 GB`, which does not fit this box and measures the pager, not the prover.
const WRAP_SHORT: Knobs = Knobs {
    name: "WRAP' (lb=6, q=19, pow=16)",
    log_height: 14,
    ..WRAP
};

/// Generate `run_d<N>(knobs) -> Cell` for each degree. A macro rather than a generic fn because the
/// `StarkConfig` bound stack (`ExtensionMmcs`, `TwoAdicFriPcs`, `BinomiallyExtendable<D>`) does not
/// abstract over the const cleanly, and the point is to instantiate the REAL config, not a wrapper.
macro_rules! degree_runner {
    ($name:ident, $d:expr) => {
        fn $name<const PAIRS: usize>(k: Knobs) -> Cell {
            type EF = BinomialExtensionField<P3BabyBear, $d>;
            type Pcs =
                TwoAdicFriPcs<P3BabyBear, Dft, ValMmcs, ExtensionMmcs<P3BabyBear, EF, ValMmcs>>;
            type Cfg = StarkConfig<Pcs, EF, Chal>;

            let perm16 = default_babybear_poseidon2_16();
            let val_mmcs = ValMmcs::new(
                PaddingFreeSponge::new(perm16.clone()),
                TruncatedPermutation::new(perm16.clone()),
                0,
            );
            let fri_params = FriParameters {
                log_blowup: k.log_blowup,
                log_final_poly_len: k.log_final_poly_len,
                max_log_arity: k.max_log_arity,
                num_queries: k.num_queries,
                commit_proof_of_work_bits: 0,
                query_proof_of_work_bits: k.query_pow_bits,
                mmcs: ExtensionMmcs::<P3BabyBear, EF, _>::new(val_mmcs.clone()),
            };
            let pcs = Pcs::new(Dft::default(), val_mmcs, fri_params);
            let config = Cfg::new(pcs, Chal::new(perm16));

            let air = Degree7Air::<PAIRS>;
            let matrix = trace::<PAIRS>(k.log_height);
            assert_eq!(matrix.height(), 1usize << k.log_height);
            let public: Vec<P3BabyBear> = vec![];

            // One untimed warm prove: pay the Poseidon2 constant tables, the DFT twiddle caches, and
            // the rayon pool spin-up ONCE, so the timed runs measure the prover and not the process.
            let _ = prove(&config, &air, matrix.clone(), &public);

            // ⚑ MIN of `REPS`, not mean. This box is shared (parallel agents, other terminals), and
            // under contention wall-clock noise is strictly ADDITIVE — a scheduled-out sample can only
            // be slower than the true cost, never faster. The mean therefore measures the contention;
            // the min measures the prover. The first draft of this file took one sample per cell and
            // produced a 0.38× "speedup" from raising the extension degree, which is not a result, it
            // is a thermally-throttled d=4 sample. Ratios of noisy singletons are worse than useless:
            // they are confidently wrong in an arbitrary direction.
            let mut prove_time = Duration::MAX;
            let mut verify_time = Duration::MAX;
            let mut proof_bytes = 0usize;
            for _ in 0..REPS {
                let t0 = Instant::now();
                let proof = prove(&config, &air, matrix.clone(), &public);
                prove_time = prove_time.min(t0.elapsed());

                let t1 = Instant::now();
                verify(&config, &air, &proof, &public)
                    .expect("degree-7 AIR must verify at every D");
                verify_time = verify_time.min(t1.elapsed());

                proof_bytes = postcard::to_allocvec(&proof)
                    .expect("proof must serialize")
                    .len();
            }

            Cell {
                ext_degree: $d,
                prove: prove_time,
                verify: verify_time,
                proof_bytes,
            }
        }
    };
}

degree_runner!(run_d4, 4);
degree_runner!(run_d5, 5);
degree_runner!(run_d8, 8);

// ---------------------------------------------------------------------------
// ⚑ THE SWEEP
// ---------------------------------------------------------------------------

/// **The measurement.** Prove the same statement, through the same engine, at D = 4 / 5 / 8, under
/// both deployed FRI knob-sets, and print the table.
///
/// This asserts only what is structurally guaranteed (every degree proves and verifies, and D=5/8 are
/// instantiable at all on the pinned rev — which is itself the load-bearing check that
/// `FRI-BOTH-WIN-LEVERS.md`'s "plonky3 supports BabyBear degree 5 and 8 today" is true of the code and
/// not just of a table). The timings are REPORTED, not gated: a wall-clock assertion in a test suite is
/// a flake, and the decision this feeds is ember's, not CI's.
#[test]
fn ext_degree_prover_cost_sweep() {
    // ⚑ Width is swept, not assumed. Both directions were arguable a priori — width scales the
    // base-field column (LDE + Merkle commit) LINEARLY, which would DILUTE D; but it also scales the
    // opened-values / reduced-opening Horner work, which is EF-valued, which would CONCENTRATE D. So
    // whether width 32 over- or under-states the deployed slowdown is an empirical question, and
    // guessing it is exactly the intuition this file exists to replace. Two widths answer it.
    println!("\n=== EXTENSION-DEGREE PROVER COST — MEASURED ===");
    println!("pinned plonky3 rev 82cfad73 · degree-7 AIR · release");

    fn report<const PAIRS: usize>(k: Knobs) {
        let cells = [run_d4::<PAIRS>(k), run_d5::<PAIRS>(k), run_d8::<PAIRS>(k)];
        let base = cells[0];
        println!(
            "\n{} · trace 2^{} · width {} · |D⁽⁰⁾| = 2^{}",
            k.name,
            k.log_height,
            2 * PAIRS,
            k.log_height + k.log_blowup
        );
        println!(
            "  {:>3} | {:>11} | {:>7} | {:>11} | {:>10} | {:>7}",
            "D", "prove", "vs d=4", "verify", "proof B", "vs d=4"
        );
        for c in cells {
            println!(
                "  {:>3} | {:>9.1?} | {:>6.3}× | {:>9.1?} | {:>10} | {:>6.3}×",
                c.ext_degree,
                c.prove,
                c.prove.as_secs_f64() / base.prove.as_secs_f64(),
                c.verify,
                c.proof_bytes,
                c.proof_bytes as f64 / base.proof_bytes as f64,
            );
        }
    }

    report::<16>(LEAF); // width 32
    report::<64>(LEAF); // width 128 — deployed traces are wide; does the ratio move?
    report::<16>(WRAP); // width 32 — the real apex |D⁽⁰⁾| = 2^22
    report::<16>(WRAP_SHORT); // width 32, |D⁽⁰⁾| = 2^20 — the wide cell's own baseline
    report::<64>(WRAP_SHORT); // width 128 at the wrap's lb — the width question, at lb=6
    println!();
}

// ---------------------------------------------------------------------------
// The ingredient: extension multiply, throughput-bound.
// ---------------------------------------------------------------------------

/// Reproduce `FRI-BOTH-WIN-LEVERS.md` §3.5's microbench on THIS machine, so the end-to-end ratio above
/// can be read against the cost of the ingredient it is made of. The doc reports 3.58 / 4.19 / 10.91
/// ns/mul (1.00× / 1.17× / 3.05×) on aarch64 NEON.
///
/// Independent accumulator chains so the measurement is THROUGHPUT (what a prover's bulk fold work is),
/// not latency (dependency-bound, and nearly flat in D).
#[test]
fn ext_mul_microbench() {
    macro_rules! bench {
        ($d:expr) => {{
            type EF = BinomialExtensionField<P3BabyBear, $d>;
            const LANES: usize = 8;
            const ITERS: usize = 200_000;

            let mut acc: [EF; LANES] =
                core::array::from_fn(|i| EF::from(P3BabyBear::new(i as u32 + 2)));
            let mul: [EF; LANES] =
                core::array::from_fn(|i| EF::from(P3BabyBear::new(i as u32 * 7 + 5)));

            // warm
            for _ in 0..(ITERS / 10) {
                for l in 0..LANES {
                    acc[l] *= mul[l];
                }
            }
            let t0 = Instant::now();
            for _ in 0..ITERS {
                for l in 0..LANES {
                    acc[l] *= mul[l];
                }
            }
            let el = t0.elapsed();
            core::hint::black_box(acc);
            el.as_secs_f64() / ((ITERS * LANES) as f64) * 1e9
        }};
    }

    let n4 = bench!(4);
    let n5 = bench!(5);
    let n8 = bench!(8);

    println!("\n=== EXTENSION MULTIPLY — MEASURED (ns/mul, throughput) ===");
    println!(
        "  {:>3} | {:>10} | {:>7} | {:>18}",
        "D", "ns/mul", "vs d=4", "naive O(d²) says"
    );
    for (d, ns) in [(4usize, n4), (5, n5), (8, n8)] {
        println!(
            "  {:>3} | {:>10.3} | {:>6.3}× | {:>17.3}×",
            d,
            ns,
            ns / n4,
            (d * d) as f64 / 16.0
        );
    }
    println!();
}
