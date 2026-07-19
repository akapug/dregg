//! First production consumer of the retained resident GPU fold.
//!
//! The path is collective keygen → collective-key unary-row encryption → strict one-time
//! `fhe.rs` wire parse → retained GPU/CPU FoldEngine → party-owned masked threshold boundary.
//! No joint `SecretKey` exists anywhere in this integration test.

use fhegg_fhe::additive::{
    encrypt_collective_order_rows, CollectiveFoldError, CollectiveOrderFoldEngine,
};
use fhegg_fhe::bfv_lean::{fold, BfvLeanError};
use fhegg_fhe::boundary::{MaskedBoundaryParty, MaskedDecryptCoordinator, MaskedDecryptSession};
use fhegg_fhe::gpu_arena::FoldBackend;
use fhegg_fhe::threshold::{
    BfvParams, KeygenCoordinator, KeygenSession, ThresholdParty, MIN_SMUDGE_BITS,
};
use fhegg_fhe::{reference_clear, Order, Side};

fn collective_keygen(
    n: usize,
    params: &BfvParams,
) -> (
    fhegg_fhe::threshold::CollectivePublicKey,
    Vec<ThresholdParty>,
) {
    let session = KeygenSession::from_seed(n, [0x6au8; 32]).expect("public keygen session");
    let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
    let mut parties = Vec::with_capacity(n);
    for party_index in 0..n {
        let (party, contribution) =
            ThresholdParty::join(&session, party_index, params).expect("party-owned key share");
        coordinator
            .accept(contribution)
            .expect("public contribution");
        parties.push(party);
    }
    (
        coordinator.finish().expect("collective public key"),
        parties,
    )
}

fn book() -> Vec<Order> {
    vec![
        Order {
            side: Side::Bid,
            limit: 2,
            qty: 7,
        },
        Order {
            side: Side::Ask,
            limit: 1,
            qty: 3,
        },
        Order {
            side: Side::Bid,
            limit: 6,
            qty: 11,
        },
        Order {
            side: Side::Ask,
            limit: 5,
            qty: 13,
        },
        Order {
            side: Side::Bid,
            limit: 4,
            qty: 17,
        },
        Order {
            side: Side::Ask,
            limit: 3,
            qty: 19,
        },
    ]
}

#[test]
fn collective_rows_fold_with_explicit_backend_and_feed_masked_threshold_boundary() {
    const N: usize = 2;
    const K: usize = 8;

    let params = BfvParams::fold_set();
    let t = params.plaintext_modulus();
    let (collective, threshold_parties) = collective_keygen(N, &params);
    let orders = book();
    let reference = reference_clear(&orders, K);

    let (rows, ingress) =
        encrypt_collective_order_rows(&orders, K, &params, &collective).expect("row ingress");
    assert_eq!(ingress.rows, orders.len());

    // CPU arithmetic is the byte-level oracle for whichever backend the retained engine reports.
    let demand_rows = rows
        .iter()
        .filter(|row| matches!(row.side(), Side::Bid))
        .map(|row| row.ciphertext().clone())
        .collect::<Vec<_>>();
    let supply_rows = rows
        .iter()
        .filter(|row| matches!(row.side(), Side::Ask))
        .map(|row| row.ciphertext().clone())
        .collect::<Vec<_>>();
    let cpu_demand = fold(&demand_rows, t).expect("CPU demand oracle");
    let cpu_supply = fold(&supply_rows, t).expect("CPU supply oracle");

    let engine = CollectiveOrderFoldEngine::new();
    let has_gpu = engine.has_gpu_arena();
    let folded = engine
        .fold_rows(rows.clone(), K, t)
        .expect("retained production fold");
    assert_eq!(folded.d_ct, cpu_demand, "demand differs from CPU fold");
    assert_eq!(folded.s_ct, cpu_supply, "supply differs from CPU fold");
    assert_eq!(folded.timing.n_rows, orders.len());
    assert_eq!(folded.timing.k, K);
    assert_eq!(folded.demand.input_ciphertexts, demand_rows.len());
    assert_eq!(folded.supply.input_ciphertexts, supply_rows.len());
    assert_eq!(folded.demand.ciphertext_bytes, 2 * 3 * 4096 * 8);
    assert_eq!(folded.supply.ciphertext_bytes, 2 * 3 * 4096 * 8);

    for phase in [folded.demand, folded.supply] {
        match phase.backend {
            FoldBackend::GpuResident(plan) => {
                assert!(has_gpu, "GPU backend reported without an arena");
                assert_eq!(phase.plan, Some(plan));
                let capacity = phase.capacity.expect("GPU capacity metadata");
                assert_eq!(capacity.ciphertexts_per_chunk, plan.ciphertexts_per_chunk);
                assert_eq!(capacity.ciphertext_bytes, phase.ciphertext_bytes);
                assert!(capacity.max_storage_bytes >= capacity.ciphertext_bytes);
                assert_eq!(plan.input_ciphertexts, phase.input_ciphertexts);
                assert!(plan.ciphertexts_per_chunk > 0);
                assert!(plan.upload_chunks > 0);
            }
            FoldBackend::CpuNoArena => {
                assert!(
                    !has_gpu,
                    "headless fallback reported despite a retained arena"
                );
                assert_eq!(phase.plan, None);
                assert_eq!(phase.capacity, None);
            }
            FoldBackend::CpuUnsupportedShape => {
                panic!("the pinned three-modulus collective shape is GPU-supported")
            }
        }
    }
    eprintln!(
        "collective fold: rows={} ingress={{encode:{:?}, encrypt:{:?}, strict_wire_parse:{:?}}} demand={{backend:{:?}, capacity:{:?}, plan:{:?}, elapsed:{:?}}} supply={{backend:{:?}, capacity:{:?}, plan:{:?}, elapsed:{:?}}}",
        ingress.rows,
        ingress.encode,
        ingress.encrypt,
        ingress.wire_ingress,
        folded.demand.backend,
        folded.demand.capacity,
        folded.demand.plan,
        folded.demand.elapsed,
        folded.supply.backend,
        folded.supply.capacity,
        folded.supply.plan,
        folded.supply.elapsed,
    );

    // Deterministic policy/headless fallback reports itself and remains byte-identical.
    let cpu_only = CollectiveOrderFoldEngine::cpu_only()
        .fold_rows(rows.clone(), K, t)
        .expect("explicit CPU-only fold");
    assert_eq!(cpu_only.d_ct, folded.d_ct);
    assert_eq!(cpu_only.s_ct, folded.s_ct);
    assert_eq!(cpu_only.demand.backend, FoldBackend::CpuNoArena);
    assert_eq!(cpu_only.supply.backend, FoldBackend::CpuNoArena);
    assert_eq!(cpu_only.demand.capacity, None);
    assert_eq!(cpu_only.demand.plan, None);

    // On a real arena, a shape outside the three-RNS-modulus shader stone takes the labelled CPU path.
    // Headless runs exercise CpuNoArena above and state the unavailable hardware branch explicitly.
    if has_gpu {
        let mut unsupported = rows.clone();
        for row in &mut unsupported {
            let ct = row.ciphertext().clone();
            let mut ct = ct;
            ct.moduli.pop();
            for poly in &mut ct.polys {
                poly.rows.pop();
            }
            *row = fhegg_fhe::additive::CollectiveOrderRow::from_lean(row.side(), ct, K)
                .expect("two-modulus CPU shape");
        }
        let fallback = engine
            .fold_rows(unsupported, K, t)
            .expect("unsupported-shape fallback");
        assert_eq!(fallback.demand.backend, FoldBackend::CpuUnsupportedShape);
        assert_eq!(fallback.supply.backend, FoldBackend::CpuUnsupportedShape);
        assert_eq!(fallback.demand.capacity, None);
        assert_eq!(fallback.demand.plan, None);
    } else {
        eprintln!("no wgpu adapter — unsupported-shape GPU fallback branch SKIPPED explicitly");
    }

    // The declared plaintext budget still bites before either CPU or GPU can silently wrap.
    let mut wrapping = rows.clone();
    let mut bid_indexes = wrapping
        .iter()
        .enumerate()
        .filter(|(_, row)| matches!(row.side(), Side::Bid))
        .map(|(index, _)| index);
    let first_bid = bid_indexes.next().expect("first bid");
    let second_bid = bid_indexes.next().expect("second bid");
    for (index, bound) in [(first_bid, t - 1), (second_bid, 1)] {
        let side = wrapping[index].side();
        let mut ciphertext = wrapping[index].ciphertext().clone();
        ciphertext.plain_bound = bound;
        wrapping[index] = fhegg_fhe::additive::CollectiveOrderRow::from_lean(side, ciphertext, K)
            .expect("shape-preserving bound mutation");
    }
    assert!(matches!(
        CollectiveOrderFoldEngine::cpu_only().fold_rows(wrapping, K, t),
        Err(CollectiveFoldError::Fold(BfvLeanError::WrapRefused {
            bound_sum,
            plaintext_modulus,
        })) if bound_sum >= u128::from(t) && plaintext_modulus == t
    ));

    // A one-row side must hit the same preflight. The lower-level CPU left-fold performs no addition in
    // that case, so this specifically guards the consumer's backend-independent envelope check.
    let mut single_bid = rows
        .iter()
        .find(|row| matches!(row.side(), Side::Bid))
        .expect("bid row")
        .ciphertext()
        .clone();
    single_bid.plain_bound = t;
    let single_bid = fhegg_fhe::additive::CollectiveOrderRow::from_lean(Side::Bid, single_bid, K)
        .expect("single bid shape");
    let single_ask = rows
        .iter()
        .find(|row| matches!(row.side(), Side::Ask))
        .expect("ask row")
        .clone();
    assert!(matches!(
        CollectiveOrderFoldEngine::cpu_only().fold_rows(vec![single_bid, single_ask], K, t),
        Err(CollectiveFoldError::Fold(BfvLeanError::WrapRefused {
            bound_sum,
            plaintext_modulus,
        })) if bound_sum == u128::from(t) && plaintext_modulus == t
    ));

    // Actual consumer handoff: mask the GPU/CPU-produced demand ciphertext, threshold-open only the
    // one-time-padded value, then locally recover mod-t shares. No joint SecretKey is constructed.
    let mask_session =
        MaskedDecryptSession::from_public([0x51u8; 32], N, K, folded.d_ct.clone(), &params)
            .expect("masked boundary accepts folded LeanCiphertext");
    let mut mask_coordinator = MaskedDecryptCoordinator::new(mask_session.clone(), params.clone());
    let mut mask_parties = Vec::with_capacity(N);
    for party_index in 0..N {
        let (mask_party, contribution) =
            MaskedBoundaryParty::prepare(&mask_session, party_index, &params, &collective)
                .expect("party-owned mask");
        mask_coordinator
            .accept(contribution)
            .expect("encrypted public mask contribution");
        mask_parties.push(mask_party);
    }
    let masked = mask_coordinator.finish().expect("masked aggregate");
    let framed_shares = threshold_parties
        .iter()
        .map(|party| {
            party
                .partial_decrypt(masked.ciphertext(), MIN_SMUDGE_BITS)
                .expect("smudged threshold share")
                .to_wire_bytes()
        })
        .collect::<Vec<_>>();
    let opening = masked
        .open_framed(&framed_shares, &params)
        .expect("full n-of-n masked opening");
    let share_rows = mask_parties
        .iter()
        .map(|party| {
            party
                .derive_mod_t_share(&opening)
                .expect("local mod-t share")
        })
        .collect::<Vec<_>>();
    let reconstructed = (0..K)
        .map(|slot| share_rows.iter().map(|row| row[slot]).sum::<u64>() % t)
        .collect::<Vec<_>>();
    let expected_demand = reference
        .demand
        .iter()
        .copied()
        .map(u64::from)
        .collect::<Vec<_>>();
    assert_eq!(reconstructed, expected_demand);
}
