//! GNARK FIXTURE EXPORT for a REAL BN254-native shrink proof — the bridge
//! between [`crate::apex_shrink`] (the Rust side of the wrap) and
//! `chain/gnark/fri_verify_native.go` (the gnark side).
//!
//! [`export_real_shrink_fri_fixture`] takes a real shrink proof (a
//! `BatchStarkProof<DreggOuterConfig>` minted by
//! [`crate::apex_shrink::shrink_apex_to_outer`] over a real `ir2_leaf_wrap`
//! apex) and serializes EVERYTHING the gnark native-hash FRI verifier needs to
//! re-verify the proof's FRI layer against the REAL transcript:
//!
//! 1. **The transcript prefix** — the exact Fiat–Shamir event sequence the
//!    batch-STARK verifier drives BEFORE the FRI commit phase
//!    (`p3_batch_stark::verifier::verify_batch` at the pinned rev `82cfad7`,
//!    mirrored step for step below): instance count, per-instance binding
//!    data, the main/preprocessed/permutation/quotient commitments (native
//!    BN254 digests), public values, LogUp cumulative sums, the sampled
//!    permutation challenges / constraint-folding alpha / zeta, the opened
//!    values (observed inside `TwoAdicFriPcs::verify`), and the FRI
//!    batch-combination alpha. Every sampled value is exported too, so the
//!    gnark circuit can PIN its own transcript against the Rust one
//!    lane-for-lane.
//! 2. **The FRI commit-phase data** — commit roots (one native BN254 element
//!    each), the final polynomial, the query proof-of-work witness, and per
//!    query: the initial reduced opening, the roll-in reduced openings (the
//!    multi-height batch openings folded in as the domain shrinks past each
//!    input height), the per-round sibling evaluations, and the per-round
//!    native Merkle paths.
//!
//! ## Why the export is trustworthy (self-checks, run on every export)
//!
//! - The transcript-prefix mirror is validated by handing a challenger
//!   advanced through the RECORDED events to the REAL `TwoAdicFriPcs::verify`
//!   (via the `Pcs` trait) — the real p3 verifier accepting from that
//!   challenger state means the recorded prefix IS the real transcript prefix
//!   (any divergence shifts every beta/query index and fails the FRI check).
//! - The FRI section is validated by re-running the ENTIRE gnark-side flow
//!   host-side with real p3 components: the real `MultiField32Challenger`
//!   (betas, arity schedule, PoW, query indices), the real `ExtensionMmcs`
//!   commit-phase Merkle verification, the real `TwoAdicFriFolding::fold_row`,
//!   an `open_input` replica for the reduced openings, and the final-poly
//!   check. What the fixture contains is exactly what passed this run.
//!
//! ## HONEST SCOPE
//!
//! The fixture drives the gnark side's FRI CORE over real data: transcript
//! agreement, commit-phase Merkle openings, fold arithmetic, PoW, final poly.
//! The reduced openings (initial + roll-ins) are computed HOST-SIDE from the
//! real opened values and the real alpha and enter the gnark circuit as
//! witnesses. The remaining in-circuit gap for a FULL batch-STARK verify —
//! named residual, tracked in `chain/gnark/fri_verify_native.go` — is:
//! (a) in-circuit verification of the input batch openings (the
//! `open_input` Merkle checks against main/preprocessed/quotient/permutation
//! commitments) and the alpha-combination that produces the reduced openings,
//! (b) per-instance constraint evaluation at zeta and the quotient
//! recomposition check. Neither changes the transcript this fixture pins.

use std::collections::{BTreeMap, HashMap};

use p3_baby_bear::BabyBear;
use p3_bn254::Bn254;
use p3_challenger::{CanObserve, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_circuit_prover::{BatchStarkProof, NUM_PRIMITIVE_TABLES};
use p3_commit::{BatchOpening, BatchOpeningRef, Mmcs, Pcs, PolynomialSpace};
use p3_field::extension::BinomialExtensionField;
use p3_field::{
    BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField, PrimeField32, TwoAdicField,
};
use p3_fri::{FriFoldingStrategy, TwoAdicFriFolding};
use p3_lookup::logup::LogUpGadget;
use p3_lookup::{Kind, LookupProtocol};
use p3_matrix::Dimensions;
use p3_symmetric::{Hash, MerkleCap};
use p3_uni_stark::StarkGenericConfig;
use serde::{Deserialize, Serialize};

use crate::apex_shrink::outer_shrink_prover;
use crate::dregg_outer_config::{
    DreggOuterConfig, OUTER_DIGEST_ELEMS, OUTER_FRI_LOG_BLOWUP, OUTER_FRI_NUM_QUERIES,
    OUTER_FRI_QUERY_POW_BITS, OuterChallengeMmcs, OuterChallenger, OuterCompress, OuterHash,
    OuterValMmcs, dregg_poseidon2_bn254,
};

const D: usize = 4;
type EF = BinomialExtensionField<BabyBear, D>;
type OuterDigest = [Bn254; OUTER_DIGEST_ELEMS];
type OuterCap = MerkleCap<BabyBear, OuterDigest>;
/// The outer PCS, with its challenger pinned so trait-method calls
/// (`natural_domain_for_degree`, `verify`) are unambiguous.
type OuterPcsT = <DreggOuterConfig as StarkGenericConfig>::Pcs;
type OuterDomain = <OuterPcsT as Pcs<EF, OuterChallenger>>::Domain;
/// One PCS round: a commitment plus, per matrix, (domain, [(point, values)]).
type ComRound = (OuterCap, Vec<(OuterDomain, Vec<(EF, Vec<EF>)>)>);

/// The pinned outer domain for a degree (UFCS: the challenger generic on
/// `Pcs` is otherwise free and inference stalls).
fn outer_domain(pcs: &OuterPcsT, degree: usize) -> OuterDomain {
    <OuterPcsT as Pcs<EF, OuterChallenger>>::natural_domain_for_degree(pcs, degree)
}

// ============================================================================
// Fixture schema (mirrored by chain/gnark/apex_shrink_real_fixture_test.go)
// ============================================================================

/// One transcript event of the pre-FRI prefix, replayed by the gnark circuit
/// through its `MultiFieldChallenger` gadget.
///
/// Event boundaries matter ONLY for digests (each `observe_digest` is one
/// native absorb call with its own length tag); BabyBear observes/samples are
/// per-value and may be coalesced freely.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum FixtureEvent {
    /// Observe canonical BabyBear proof values, in order.
    ObserveBb { values: Vec<u32> },
    /// Observe ONE native BN254 digest (one `ObserveBn254Digest` call).
    ObserveDigest { words: Vec<String> },
    /// Sample BabyBear challenges; `values` are the expected canonical
    /// results, asserted in-circuit (transcript pinning).
    SampleBb { values: Vec<u32> },
}

/// FRI shape parameters (must match `create_outer_config`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FixtureFriShape {
    pub log_blowup: usize,
    pub log_final_poly_len: usize,
    pub max_log_arity: usize,
    pub num_queries: usize,
    pub commit_pow_bits: usize,
    pub query_pow_bits: usize,
    pub extra_query_index_bits: usize,
    /// Number of commit-phase rounds (all arity 2).
    pub rounds: usize,
    /// `rounds + log_blowup + log_final_poly_len`.
    pub log_global_max_height: usize,
}

/// One query's FRI opening data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FixtureQuery {
    /// The expected sampled query index (pinned in-circuit).
    pub expected_index: u64,
    /// Reduced opening at `log_global_max_height` (the fold seed).
    pub initial_eval: [u32; 4],
    /// Reduced openings rolled in as the fold passes each input height,
    /// aligned with `roll_in_rounds` (same order).
    pub roll_ins: Vec<[u32; 4]>,
    /// Per commit round: the sibling evaluation (arity 2 ⇒ one per round).
    pub siblings: Vec<[u32; 4]>,
    /// Per commit round: the native Merkle path (bottom-up, one BN254 word
    /// per level; round r has `log_global_max_height - r - 1` levels).
    pub merkle_paths: Vec<Vec<String>>,
}

/// The full gnark fixture for one real shrink proof.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RealShrinkFriFixture {
    pub version: u32,
    pub description: String,
    /// Per-instance `log2(extended trace domain)` of the shrink proof.
    pub degree_bits: Vec<usize>,
    pub fri: FixtureFriShape,
    /// The pre-FRI transcript, `initialise_challenger()` through the FRI
    /// batch-combination alpha sample (inclusive).
    pub prefix_events: Vec<FixtureEvent>,
    /// Commit-phase Merkle roots (native BN254), in round order.
    pub commit_roots: Vec<String>,
    /// Expected betas (pinned in-circuit after each root observe).
    pub expected_betas: Vec<[u32; 4]>,
    /// Final polynomial coefficients (length `2^log_final_poly_len`).
    pub final_poly: Vec<[u32; 4]>,
    /// The query proof-of-work witness.
    pub query_pow_witness: u32,
    /// Rounds AFTER whose fold a reduced opening rolls in (ascending;
    /// identical across queries — the input heights are structural).
    pub roll_in_rounds: Vec<usize>,
    pub queries: Vec<FixtureQuery>,
}

// ============================================================================
// Recording challenger
// ============================================================================

fn bb_u32(v: &BabyBear) -> u32 {
    v.as_canonical_u32()
}

fn bn254_hex(v: &Bn254) -> String {
    format!("0x{:064x}", v.as_canonical_biguint())
}

fn ef_coords(e: &EF) -> [u32; 4] {
    let s = e.as_basis_coefficients_slice();
    [bb_u32(&s[0]), bb_u32(&s[1]), bb_u32(&s[2]), bb_u32(&s[3])]
}

/// Drives a REAL `MultiField32Challenger` while recording every event, so the
/// gnark side can replay the identical transcript.
struct Recorder {
    ch: OuterChallenger,
    events: Vec<FixtureEvent>,
}

impl Recorder {
    fn new(ch: OuterChallenger) -> Self {
        Self {
            ch,
            events: Vec::new(),
        }
    }

    fn obs_bb(&mut self, v: BabyBear) {
        self.ch.observe(v);
        if let Some(FixtureEvent::ObserveBb { values }) = self.events.last_mut() {
            values.push(bb_u32(&v));
        } else {
            self.events.push(FixtureEvent::ObserveBb {
                values: vec![bb_u32(&v)],
            });
        }
    }

    fn obs_bb_slice(&mut self, vs: &[BabyBear]) {
        for v in vs {
            self.obs_bb(*v);
        }
    }

    /// `observe_algebra_element`: the extension element's base coefficients.
    fn obs_ext(&mut self, e: &EF) {
        self.obs_bb_slice(e.as_basis_coefficients_slice());
    }

    /// `BatchTranscript::observe_usize`: the value lifted to the challenge
    /// field (coefficients `[v, 0, 0, 0]`).
    fn obs_usize(&mut self, v: usize) {
        self.obs_ext(&EF::from(BabyBear::from_usize(v)));
    }

    /// Observe a Merkle cap exactly as `MultiField32Challenger` does: one
    /// native digest absorb per cap root. NEVER coalesced (each call has its
    /// own length tag).
    fn obs_cap(&mut self, cap: &OuterCap) {
        for root in cap.roots() {
            self.ch
                .observe(Hash::<BabyBear, Bn254, OUTER_DIGEST_ELEMS>::from(*root));
            self.events.push(FixtureEvent::ObserveDigest {
                words: root.iter().map(bn254_hex).collect(),
            });
        }
    }

    /// `sample_algebra_element::<EF>`: four base samples, recorded as
    /// expected values.
    fn sample_ext(&mut self) -> EF {
        let e: EF = self.ch.sample_algebra_element();
        let c = ef_coords(&e);
        if let Some(FixtureEvent::SampleBb { values }) = self.events.last_mut() {
            values.extend_from_slice(&c);
        } else {
            self.events
                .push(FixtureEvent::SampleBb { values: c.to_vec() });
        }
        e
    }
}

// ============================================================================
// The export
// ============================================================================

fn reverse_bits_len(x: usize, bits: usize) -> usize {
    let mut out = 0usize;
    for i in 0..bits {
        out |= ((x >> i) & 1) << (bits - 1 - i);
    }
    out
}

fn log2_strict(n: usize) -> usize {
    debug_assert!(n.is_power_of_two());
    n.trailing_zeros() as usize
}

/// The verifier-side `open_input` (p3-fri `verifier.rs:524` at rev `82cfad7`),
/// replicated so the per-query reduced openings can be EXPORTED (the real
/// function is private and returns them only transiently). Includes the real
/// input-MMCS batch verification, so a mis-built round structure fails here,
/// not in gnark.
#[allow(clippy::type_complexity)]
fn open_input_replica(
    log_blowup: usize,
    log_global_max_height: usize,
    index: usize,
    input_proof: &[BatchOpening<BabyBear, OuterValMmcs>],
    alpha: EF,
    val_mmcs: &OuterValMmcs,
    coms: &[ComRound],
) -> Result<Vec<(usize, EF)>, String> {
    if input_proof.len() != coms.len() {
        return Err(format!(
            "input proof has {} batches, expected {}",
            input_proof.len(),
            coms.len()
        ));
    }
    // log_height -> (alpha_pow, reduced_opening)
    let mut reduced = BTreeMap::<usize, (EF, EF)>::new();

    for (batch_opening, (batch_commit, mats)) in input_proof.iter().zip(coms.iter()) {
        let batch_heights: Vec<usize> = mats
            .iter()
            .map(|(domain, _)| domain.size() << log_blowup)
            .collect();
        let batch_dims: Vec<Dimensions> = batch_heights
            .iter()
            .map(|&height| Dimensions { width: 0, height })
            .collect();
        let reduced_index = batch_heights
            .iter()
            .max()
            .map(|&h| index >> (log_global_max_height - log2_strict(h)))
            .unwrap_or(0);
        val_mmcs
            .verify_batch(
                batch_commit,
                &batch_dims,
                reduced_index,
                BatchOpeningRef::new(&batch_opening.opened_values, &batch_opening.opening_proof),
            )
            .map_err(|e| format!("input batch opening failed host-side verification: {e:?}"))?;

        for (mat_opening, (mat_domain, mat_points_and_values)) in
            batch_opening.opened_values.iter().zip(mats.iter())
        {
            let log_height = log2_strict(mat_domain.size()) + log_blowup;
            let bits_reduced = log_global_max_height - log_height;
            let rev_reduced_index = reverse_bits_len(index >> bits_reduced, log_height);
            let x = BabyBear::GENERATOR
                * BabyBear::two_adic_generator(log_height).exp_u64(rev_reduced_index as u64);

            let (alpha_pow, ro) = reduced.entry(log_height).or_insert((EF::ONE, EF::ZERO));
            for (z, ps_at_z) in mat_points_and_values {
                let quotient = (*z - EF::from(x)).inverse();
                if mat_opening.len() != ps_at_z.len() {
                    return Err("opened-width mismatch between input proof and round".into());
                }
                for (&p_at_x, &p_at_z) in mat_opening.iter().zip(ps_at_z.iter()) {
                    *ro += *alpha_pow * (p_at_z - EF::from(p_at_x)) * quotient;
                    *alpha_pow *= alpha;
                }
            }
        }
    }

    Ok(reduced
        .into_iter()
        .rev()
        .map(|(lh, (_, ro))| (lh, ro))
        .collect())
}

/// Export the gnark FRI fixture from a REAL shrink proof, self-checking every
/// section against the real p3 verifier components (see the module doc).
pub fn export_real_shrink_fri_fixture(
    proof: &BatchStarkProof<DreggOuterConfig>,
    config: &DreggOuterConfig,
) -> Result<RealShrinkFriFixture, String> {
    if config.is_zk() != 0 {
        return Err("exporter assumes a non-ZK outer config".into());
    }
    if proof.ext_degree != D {
        return Err(format!("expected ext_degree {D}, got {}", proof.ext_degree));
    }
    let p = &proof.proof;
    let n = p.degree_bits.len();
    if p.commitments.random.is_some() {
        return Err("unexpected ZK randomization commitment".into());
    }
    if p.opened_values.instances.len() != n {
        return Err("instance count mismatch between opened values and degree_bits".into());
    }
    if NUM_PRIMITIVE_TABLES + proof.non_primitives.len() != n {
        return Err(format!(
            "instance count {} != {} primitive + {} non-primitive tables",
            n,
            NUM_PRIMITIVE_TABLES,
            proof.non_primitives.len()
        ));
    }

    // Public values in instance order: primitive tables have none, dynamic
    // tables carry theirs in the proof (rebuild_airs_pvs_common's order).
    let mut publics: Vec<Vec<BabyBear>> = vec![Vec::new(); NUM_PRIMITIVE_TABLES];
    publics.extend(proof.non_primitives.iter().map(|e| e.public_values.clone()));

    // Lookup contexts + preprocessed binding, rebuilt exactly as the verifier
    // rebuilds them (public fork API).
    let common = outer_shrink_prover(config)
        .rebuild_verifiable_common::<D>(proof, proof.w_binomial)
        .map_err(|e| format!("rebuild_verifiable_common failed: {e:?}"))?;

    // ---- Phase A: the pre-FRI transcript, mirrored + recorded --------------
    // Mirror of p3_batch_stark::verifier::verify_batch (rev 82cfad7) up to and
    // including the pcs.verify opened-value observes and the FRI alpha sample.
    let mut rec = Recorder::new(config.initialise_challenger());

    // observe_instance_count
    rec.obs_usize(n);
    // per-instance observe_instance_binding(ext_db, base_db, width, n_chunks)
    for i in 0..n {
        let inst = &p.opened_values.instances[i].base_opened_values;
        let ext_db = p.degree_bits[i];
        rec.obs_usize(ext_db);
        rec.obs_usize(ext_db); // base_db == ext_db (is_zk = 0)
        rec.obs_usize(inst.trace_local.len());
        rec.obs_usize(inst.quotient_chunks.len());
    }
    // observe_main: main commitment, then per-instance public values.
    rec.obs_cap(&p.commitments.main);
    for pv in &publics {
        rec.obs_bb_slice(pv);
    }
    // observe_preprocessed: widths (all instances), then the global commitment.
    let preprocessed_widths: Vec<usize> = (0..n)
        .map(|i| {
            common
                .preprocessed
                .as_ref()
                .and_then(|g| g.instances[i].as_ref().map(|m| m.width))
                .unwrap_or(0)
        })
        .collect();
    for &w in &preprocessed_widths {
        rec.obs_usize(w);
    }
    if let Some(global) = &common.preprocessed {
        rec.obs_cap(&global.commitment);
    }
    // sample_perm_challenges: global buses share, locals are fresh.
    let lookup_gadget = LogUpGadget::new();
    let n_ch = lookup_gadget.num_challenges();
    let mut seen_buses: HashMap<String, ()> = HashMap::new();
    for lookups in &common.lookups {
        for ctx in lookups.as_ref() {
            match &ctx.kind {
                Kind::Global(name) => {
                    if seen_buses.insert(name.clone(), ()).is_none() {
                        for _ in 0..n_ch {
                            let _ = rec.sample_ext();
                        }
                    }
                }
                Kind::Local => {
                    for _ in 0..n_ch {
                        let _ = rec.sample_ext();
                    }
                }
            }
        }
    }
    // observe_perm_and_sample_alpha.
    if let Some(perm_commit) = &p.commitments.permutation {
        rec.obs_cap(perm_commit);
        for data in p.global_lookup_data.iter().flatten() {
            rec.obs_ext(&data.cumulative_sum);
        }
    }
    let _alpha_constraints = rec.sample_ext();
    // observe_quotient_commitment; sample zeta.
    rec.obs_cap(&p.commitments.quotient_chunks);
    let zeta = rec.sample_ext();

    // ---- The PCS round structure (verify_batch's coms_to_verify) ----------
    let pcs = config.pcs();
    let ext_doms: Vec<OuterDomain> = p
        .degree_bits
        .iter()
        .map(|&db| outer_domain(pcs, 1usize << db))
        .collect();
    let zeta_nexts: Vec<EF> = ext_doms
        .iter()
        .map(|dom| {
            dom.next_point(zeta)
                .ok_or("next_point unavailable".to_string())
        })
        .collect::<Result<_, _>>()?;

    let mut coms: Vec<ComRound> = Vec::new();
    // Trace round.
    let mut trace_round = Vec::with_capacity(n);
    for i in 0..n {
        let inst = &p.opened_values.instances[i].base_opened_values;
        let mut points = vec![(zeta, inst.trace_local.clone())];
        if let Some(next) = &inst.trace_next {
            points.push((zeta_nexts[i], next.clone()));
        }
        trace_round.push((ext_doms[i], points));
    }
    coms.push((p.commitments.main.clone(), trace_round));
    // Quotient chunks round (natural domains of size 2^ext_db, flattened).
    let mut qc_round = Vec::new();
    for i in 0..n {
        let inst = &p.opened_values.instances[i].base_opened_values;
        for chunk in &inst.quotient_chunks {
            qc_round.push((ext_doms[i], vec![(zeta, chunk.clone())]));
        }
    }
    coms.push((p.commitments.quotient_chunks.clone(), qc_round));
    // Preprocessed round.
    if let Some(global) = &common.preprocessed {
        let mut pre_round = Vec::new();
        for &inst_idx in &global.matrix_to_instance {
            let inst = &p.opened_values.instances[inst_idx].base_opened_values;
            let local = inst
                .preprocessed_local
                .as_ref()
                .ok_or("missing preprocessed_local for a preprocessed instance")?;
            let meta = global.instances[inst_idx]
                .as_ref()
                .ok_or("missing preprocessed metadata")?;
            let pre_domain = outer_domain(pcs, 1usize << meta.degree_bits);
            let mut points = vec![(zeta, local.clone())];
            if let Some(next) = &inst.preprocessed_next {
                points.push((zeta_nexts[inst_idx], next.clone()));
            }
            pre_round.push((pre_domain, points));
        }
        coms.push((global.commitment.clone(), pre_round));
    }
    // Permutation round.
    if let Some(perm_commit) = &p.commitments.permutation {
        let mut perm_round = Vec::new();
        for i in 0..n {
            let inst = &p.opened_values.instances[i];
            if !inst.permutation_local.is_empty() {
                perm_round.push((
                    ext_doms[i],
                    vec![
                        (zeta, inst.permutation_local.clone()),
                        (zeta_nexts[i], inst.permutation_next.clone()),
                    ],
                ));
            }
        }
        coms.push((perm_commit.clone(), perm_round));
    }

    // ---- SELF-CHECK 1: the REAL pcs.verify accepts from the recorded state.
    // This validates every event recorded so far AND the round structure: the
    // pcs re-observes the opened values itself, samples alpha and the whole
    // FRI transcript, and re-checks all Merkle openings + the fold chains.
    {
        let mut ch = rec.ch.clone();
        <OuterPcsT as Pcs<EF, OuterChallenger>>::verify(
            pcs,
            coms.clone(),
            &p.opening_proof,
            &mut ch,
        )
        .map_err(|e| {
            format!(
                "REAL pcs.verify rejected from the mirrored transcript state \
                     (the prefix mirror or round structure diverges from verify_batch): {e:?}"
            )
        })?;
    }

    // pcs.verify's own opened-value observes (two_adic_pcs.rs:687-694), then
    // the FRI batch-combination alpha (verifier.rs:143).
    for (_, round) in &coms {
        for (_, mat) in round {
            for (_, values) in mat {
                for v in values {
                    rec.obs_ext(v);
                }
            }
        }
    }
    let alpha = rec.sample_ext();

    let prefix_events = rec.events;
    let ch0 = rec.ch; // positioned at the FRI commit phase

    // ---- Phase B: the FRI core, exactly as the gnark circuit will run it ---
    let fri = &p.opening_proof;
    let rounds = fri.commit_phase_commits.len();
    if fri.commit_pow_witnesses.len() != rounds {
        return Err("commit PoW witness count mismatch".into());
    }
    if fri.query_proofs.len() != OUTER_FRI_NUM_QUERIES {
        return Err(format!(
            "expected {OUTER_FRI_NUM_QUERIES} query proofs, got {}",
            fri.query_proofs.len()
        ));
    }
    for qp in &fri.query_proofs {
        if qp.commit_phase_openings.len() != rounds {
            return Err("query has wrong number of commit-phase openings".into());
        }
        for step in &qp.commit_phase_openings {
            if step.log_arity != 1 || step.sibling_values.len() != 1 {
                return Err("non-arity-2 commit round (fixture scope is arity 2)".into());
            }
        }
    }
    let log_global_max_height = rounds + OUTER_FRI_LOG_BLOWUP; // log_final_poly_len = 0
    let max_db = *p.degree_bits.iter().max().ok_or("no instances")?;
    if max_db + OUTER_FRI_LOG_BLOWUP != log_global_max_height {
        return Err(format!(
            "round count {rounds} inconsistent with max degree bits {max_db} + blowup {OUTER_FRI_LOG_BLOWUP}"
        ));
    }
    if fri.final_poly.len() != 1 {
        return Err("expected a constant final polynomial (log_final_poly_len = 0)".into());
    }

    // Real MMCSes for host-side re-verification (identical constants to the
    // config's own — dregg_poseidon2_bn254 is deterministic).
    let perm = dregg_poseidon2_bn254();
    let val_mmcs = OuterValMmcs::new(
        OuterHash::new(perm.clone()).map_err(|e| format!("{e:?}"))?,
        OuterCompress::new(perm),
        0,
    );
    let challenge_mmcs = OuterChallengeMmcs::new(val_mmcs.clone());
    let folding: TwoAdicFriFolding<
        Vec<BatchOpening<BabyBear, OuterValMmcs>>,
        <OuterValMmcs as Mmcs<BabyBear>>::Error,
    > = TwoAdicFriFolding(core::marker::PhantomData);

    let mut ch = ch0;
    let mut betas: Vec<EF> = Vec::with_capacity(rounds);
    for comm in &fri.commit_phase_commits {
        ch.observe(comm.clone());
        // commit_proof_of_work_bits = 0: check_witness is a no-op.
        betas.push(ch.sample_algebra_element());
    }
    ch.observe_algebra_slice(&fri.final_poly);
    for _ in 0..rounds {
        ch.observe(BabyBear::ONE); // the arity schedule (log_arity = 1)
    }
    if !ch.check_witness(OUTER_FRI_QUERY_POW_BITS, fri.query_pow_witness) {
        return Err("query PoW witness failed host-side check".into());
    }

    let mut roll_in_rounds: Option<Vec<usize>> = None;
    let mut queries_out: Vec<FixtureQuery> = Vec::with_capacity(fri.query_proofs.len());

    for (qi, qp) in fri.query_proofs.iter().enumerate() {
        let index = ch.sample_bits(log_global_max_height); // extra_query_index_bits = 0
        let ro = open_input_replica(
            OUTER_FRI_LOG_BLOWUP,
            log_global_max_height,
            index,
            &qp.input_proof,
            alpha,
            &val_mmcs,
            &coms,
        )?;
        if ro.first().map(|(lh, _)| *lh) != Some(log_global_max_height) {
            return Err(format!(
                "query {qi}: initial reduced opening not at max height"
            ));
        }
        let initial_eval = ro[0].1;
        let mut ro_iter = ro[1..].iter().peekable();

        let mut folded = initial_eval;
        let mut domain_index = index;
        let mut log_current = log_global_max_height;
        let mut q_roll_rounds: Vec<usize> = Vec::new();
        let mut q_roll_vals: Vec<EF> = Vec::new();
        let mut siblings: Vec<[u32; 4]> = Vec::with_capacity(rounds);
        let mut merkle_paths: Vec<Vec<String>> = Vec::with_capacity(rounds);

        for (r, step) in qp.commit_phase_openings.iter().enumerate() {
            let sib = step.sibling_values[0];
            let bit = domain_index & 1;
            let evals: Vec<EF> = if bit == 0 {
                vec![folded, sib]
            } else {
                vec![sib, folded]
            };
            domain_index >>= 1;
            let log_folded = log_current - 1;

            challenge_mmcs
                .verify_batch(
                    &fri.commit_phase_commits[r],
                    &[Dimensions {
                        width: 2,
                        height: 1 << log_folded,
                    }],
                    domain_index,
                    BatchOpeningRef::new(core::slice::from_ref(&evals), &step.opening_proof),
                )
                .map_err(|e| {
                    format!("query {qi} round {r}: commit-phase Merkle opening failed: {e:?}")
                })?;

            folded = <TwoAdicFriFolding<_, _> as FriFoldingStrategy<BabyBear, EF>>::fold_row(
                &folding,
                domain_index,
                log_folded,
                1,
                betas[r],
                evals.into_iter(),
            );
            log_current = log_folded;

            if let Some((_, v)) = ro_iter.next_if(|(lh, _)| *lh == log_current) {
                folded += betas[r] * betas[r] * *v; // beta^arity = beta^2
                q_roll_rounds.push(r);
                q_roll_vals.push(*v);
            }

            siblings.push(ef_coords(&sib));
            merkle_paths.push(
                step.opening_proof
                    .iter()
                    .map(|d| bn254_hex(&d[0]))
                    .collect(),
            );
        }
        if log_current != OUTER_FRI_LOG_BLOWUP {
            return Err(format!("query {qi}: fold ended at height {log_current}"));
        }
        if ro_iter.next().is_some() {
            return Err(format!("query {qi}: unconsumed reduced openings"));
        }
        // final_poly is a constant: its evaluation at any x is coefficient 0.
        if folded != fri.final_poly[0] {
            return Err(format!(
                "query {qi}: fold chain does not reach the final polynomial \
                 (transcript or reduced-opening replica diverges)"
            ));
        }
        match &roll_in_rounds {
            None => roll_in_rounds = Some(q_roll_rounds.clone()),
            Some(expected) if *expected != q_roll_rounds => {
                return Err("roll-in schedule differs across queries".into());
            }
            _ => {}
        }
        queries_out.push(FixtureQuery {
            expected_index: index as u64,
            initial_eval: ef_coords(&initial_eval),
            roll_ins: q_roll_vals.iter().map(ef_coords).collect(),
            siblings,
            merkle_paths,
        });
    }

    Ok(RealShrinkFriFixture {
        version: 1,
        description: "REAL dregg apex shrink proof (BatchStarkProof<DreggOuterConfig> over a real \
                      ir2_leaf_wrap apex): pre-FRI transcript events + FRI commit-phase data for \
                      chain/gnark VerifyFriNative. Reduced openings computed host-side (see \
                      apex_shrink_gnark_export.rs HONEST SCOPE)."
            .into(),
        degree_bits: p.degree_bits.clone(),
        fri: FixtureFriShape {
            log_blowup: OUTER_FRI_LOG_BLOWUP,
            log_final_poly_len: 0,
            max_log_arity: 1,
            num_queries: OUTER_FRI_NUM_QUERIES,
            commit_pow_bits: 0,
            query_pow_bits: OUTER_FRI_QUERY_POW_BITS,
            extra_query_index_bits: 0,
            rounds,
            log_global_max_height,
        },
        prefix_events,
        commit_roots: fri
            .commit_phase_commits
            .iter()
            .map(|cap| {
                let roots = cap.roots();
                assert_eq!(roots.len(), 1, "cap_height 0 ⇒ single root");
                bn254_hex(&roots[0][0])
            })
            .collect(),
        expected_betas: betas.iter().map(ef_coords).collect(),
        final_poly: fri.final_poly.iter().map(ef_coords).collect(),
        query_pow_witness: bb_u32(&fri.query_pow_witness),
        roll_in_rounds: roll_in_rounds.unwrap_or_default(),
        queries: queries_out,
    })
}
