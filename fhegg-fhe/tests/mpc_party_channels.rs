//! Channel-level teeth for the party-owned boolean MPC runtime.

use std::thread;
use std::time::Duration;

use fhegg_fhe::mpc::{crossing_rounds, index_bits, Crossing};
use fhegg_fhe::mpc_party::{
    local_channels, run_party, simulate_public_transcript, trusted_dealer_triples, MaskedOpening,
    PartyArithmeticInput, PartyMpcError, PartyMpcSession, ProtocolPhase,
};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

fn reference_crossing(demand: &[u64], supply: &[u64]) -> Crossing {
    assert_eq!(demand.len(), supply.len());
    let mut best_index = 0usize;
    let mut best_volume = 0u64;
    for (index, (&demand, &supply)) in demand.iter().zip(supply).enumerate() {
        let volume = demand.min(supply);
        if volume > best_volume {
            best_index = index;
            best_volume = volume;
        }
    }
    Crossing {
        p_star: (best_volume != 0).then_some(best_index),
        v_star: best_volume,
    }
}

fn share_mod_t<R: Rng>(values: &[u64], n: usize, modulus: u64, rng: &mut R) -> Vec<Vec<u64>> {
    let mut rows = vec![vec![0u64; values.len()]; n];
    for (bucket, &value) in values.iter().enumerate() {
        let mut sum = 0u64;
        for row in rows.iter_mut().take(n - 1) {
            row[bucket] = rng.gen_range(0..modulus);
            sum = (sum + row[bucket]) % modulus;
        }
        rows[n - 1][bucket] = (value + modulus - sum) % modulus;
    }
    rows
}

fn party_inputs(
    session: &PartyMpcSession,
    demand: &[u64],
    supply: &[u64],
    seed: u64,
) -> Vec<PartyArithmeticInput> {
    // Test-only stand-in for the independently derived MaskedBoundaryParty rows.
    // This helper is not passed to the runtime coordinator or triple dealer.
    let mut upstream_rng = StdRng::seed_from_u64(seed);
    let demand_rows = share_mod_t(
        demand,
        session.n_parties(),
        session.plaintext_modulus(),
        &mut upstream_rng,
    );
    let supply_rows = share_mod_t(
        supply,
        session.n_parties(),
        session.plaintext_modulus(),
        &mut upstream_rng,
    );
    (0..session.n_parties())
        .map(|party| {
            let mut party_rng = StdRng::seed_from_u64(seed ^ (0x1000 + party as u64));
            PartyArithmeticInput::new(
                session,
                party,
                &demand_rows[party],
                &supply_rows[party],
                &mut party_rng,
            )
            .expect("party-local arithmetic input")
        })
        .collect()
}

fn run_case(tag: u8, demand: &[u64], supply: &[u64]) {
    const N: usize = 3;
    const B: usize = 8;
    const T: u64 = 257;

    let session = PartyMpcSession::new([tag; 32], N, demand.len(), B, T, Duration::from_secs(5))
        .expect("valid session");
    let inputs = party_inputs(&session, demand, supply, 0x1a2b_0000 + u64::from(tag));
    let mut dealer_rng = StdRng::seed_from_u64(0xd15c_0000 + u64::from(tag));
    let preprocessing =
        trusted_dealer_triples(&session, &mut dealer_rng).expect("shape-only preprocessing");
    let (coordinator, endpoints) = local_channels(&session);
    let parties = inputs
        .into_iter()
        .zip(preprocessing)
        .zip(endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_party(input, triples, endpoint))
        })
        .collect::<Vec<_>>();

    let run = coordinator
        .coordinate(&session)
        .expect("full party quorum completes");
    for (party, handle) in parties.into_iter().enumerate() {
        let report = handle
            .join()
            .expect("party thread did not panic")
            .expect("party completes");
        assert_eq!(report.party, party);
        assert_eq!(report.and_gates, session.exact_and_gates());
        assert_eq!(report.peer_input_messages_sent, 2 * demand.len() * N);
        assert_eq!(report.peer_input_messages_received, 2 * demand.len() * N);
    }

    assert_eq!(run.crossing, reference_crossing(demand, supply));
    assert!(run.transcript.is_reveal_only(&session));
    let w = session.ingress_bits();
    let expected_depth = 2 * (w - 1) + (N - 1) * (w + 1) + crossing_rounds(demand.len(), B);
    assert_eq!(run.transcript.modeled_batched_rounds, expected_depth);
    assert_eq!(
        run.transcript.scalar_opening_rounds,
        session.exact_and_gates()
    );
    assert_eq!(
        run.transcript.revealed_pstar.len(),
        index_bits(demand.len())
    );

    // The public-transcript simulator receives only the public result and shape.
    let mut simulator_rng = StdRng::seed_from_u64(0x51_0000 + u64::from(tag));
    let simulated = simulate_public_transcript(&run.crossing, &session, &mut simulator_rng)
        .expect("valid public result simulates");
    assert!(simulated.is_reveal_only(&session));
    assert_eq!(simulated.revealed_pstar, run.transcript.revealed_pstar);
    assert_eq!(simulated.revealed_vstar, run.transcript.revealed_vstar);
    assert_eq!(simulated.masked.len(), run.transcript.masked.len());

    // Strict transcript teeth: extra masked/output fields and non-canonical bits
    // cannot be relabelled as a reveal-only transcript.
    let mut extra_masked = run.transcript.clone();
    extra_masked.masked.push(MaskedOpening {
        gate: session.exact_and_gates(),
        d: 0,
        e: 0,
    });
    assert!(!extra_masked.is_reveal_only(&session));

    let mut extra_output = run.transcript.clone();
    extra_output.revealed_vstar.push(0);
    assert!(!extra_output.is_reveal_only(&session));

    let mut noncanonical = run.transcript.clone();
    noncanonical.masked[0].d = 2;
    assert!(!noncanonical.is_reveal_only(&session));

    let mut hidden_message = run.transcript.clone();
    hidden_message.gate_share_messages += 1;
    assert!(!hidden_message.is_reveal_only(&session));
}

#[test]
fn channel_runtime_matches_balanced_reference_for_odd_non_power_and_ties() {
    // K=1/no-clear, then odd/non-power-of-two sizes and a power-of-two control.
    // K=5 and K=9 deliberately contain volume plateaus: the lowest maximizer wins.
    run_case(1, &[0], &[91]);
    run_case(2, &[10, 7, 2], &[1, 7, 10]);
    run_case(3, &[9, 7, 7, 2, 1], &[1, 7, 7, 8, 9]);
    run_case(4, &[20, 18, 14, 11, 9, 4, 1], &[1, 4, 9, 11, 14, 18, 20]);
    run_case(
        5,
        &[31, 29, 24, 18, 13, 9, 4, 2],
        &[2, 5, 9, 13, 18, 24, 29, 31],
    );
    run_case(
        6,
        &[40, 35, 30, 22, 22, 12, 8, 3, 1],
        &[1, 5, 9, 22, 22, 26, 31, 35, 40],
    );
}

#[test]
fn coordinator_refuses_n_minus_one_and_releases_waiting_parties() {
    const N: usize = 3;
    let session = PartyMpcSession::new([0x77; 32], N, 3, 4, 17, Duration::from_millis(100))
        .expect("valid session");
    let mut inputs = party_inputs(&session, &[9, 6, 1], &[1, 6, 9], 0x7711);
    let mut dealer_rng = StdRng::seed_from_u64(0xdead_beef);
    let mut preprocessing =
        trusted_dealer_triples(&session, &mut dealer_rng).expect("shape-only preprocessing");
    let (coordinator, mut endpoints) = local_channels(&session);

    // Deliberately withhold party 2 while retaining its peer receiver until the
    // coordinator's deadline. The two live parties cannot complete input ingress
    // and therefore submit zero gate messages.
    inputs.pop();
    preprocessing.pop();
    let missing_endpoint = endpoints.pop().expect("party 2 endpoint");
    let parties = inputs
        .into_iter()
        .zip(preprocessing)
        .zip(endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_party(input, triples, endpoint))
        })
        .collect::<Vec<_>>();

    let error = coordinator
        .coordinate(&session)
        .expect_err("n-1 must never reconstruct or advance");
    assert_eq!(
        error,
        PartyMpcError::QuorumTimeout {
            phase: ProtocolPhase::BeaverGate(0),
            have: 0,
            need: N,
        }
    );
    drop(missing_endpoint);

    // Live parties are still awaiting the missing peer's ingress shares; their
    // bounded peer deadline makes them refuse/exit rather than hang forever.
    for handle in parties {
        assert!(handle.join().expect("waiting party did not panic").is_err());
    }
}

#[test]
fn invalid_shapes_and_cross_session_messages_fail_closed() {
    assert!(matches!(
        PartyMpcSession::new([0; 32], 1, 3, 8, 257, Duration::from_secs(1)),
        Err(PartyMpcError::InvalidParameters(_))
    ));
    assert!(matches!(
        PartyMpcSession::new([0; 32], 3, 0, 8, 257, Duration::from_secs(1)),
        Err(PartyMpcError::InvalidParameters(_))
    ));
    assert!(matches!(
        PartyMpcSession::new([0; 32], 3, 3, 0, 257, Duration::from_secs(1)),
        Err(PartyMpcError::InvalidParameters(_))
    ));
    assert!(matches!(
        PartyMpcSession::new([0; 32], 3, 3, 8, 255, Duration::from_secs(1)),
        Err(PartyMpcError::InvalidParameters(_))
    ));

    let session_a = PartyMpcSession::new([0xa1; 32], 3, 3, 4, 17, Duration::from_millis(250))
        .expect("valid session A");
    let session_b = PartyMpcSession::new([0xb2; 32], 3, 3, 4, 17, Duration::from_millis(250))
        .expect("valid session B");
    let mut dealer_rng = StdRng::seed_from_u64(0x51de);
    assert!(matches!(
        PartyArithmeticInput::new(&session_a, 0, &[3, 2], &[1, 2], &mut dealer_rng),
        Err(PartyMpcError::ShapeMismatch)
    ));
    assert!(matches!(
        PartyArithmeticInput::new(&session_a, 0, &[17, 2, 1], &[1, 2, 3], &mut dealer_rng),
        Err(PartyMpcError::ValueOverflow { .. })
    ));
    assert!(matches!(
        simulate_public_transcript(
            &Crossing {
                p_star: None,
                v_star: 1,
            },
            &session_a,
            &mut dealer_rng,
        ),
        Err(PartyMpcError::InvalidOutput)
    ));
    assert!(matches!(
        simulate_public_transcript(
            &Crossing {
                p_star: Some(0),
                v_star: 0,
            },
            &session_a,
            &mut dealer_rng,
        ),
        Err(PartyMpcError::InvalidOutput)
    ));

    let inputs = party_inputs(&session_a, &[9, 6, 1], &[1, 6, 9], 0xa1a1);
    let preprocessing =
        trusted_dealer_triples(&session_a, &mut dealer_rng).expect("session-A triples");
    let (coordinator, endpoints) = local_channels(&session_b);
    let parties = inputs
        .into_iter()
        .zip(preprocessing)
        .zip(endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_party(input, triples, endpoint))
        })
        .collect::<Vec<_>>();
    assert_eq!(
        coordinator
            .coordinate(&session_b)
            .expect_err("session-A shares must not enter session B"),
        PartyMpcError::SessionMismatch
    );
    for handle in parties {
        assert!(handle
            .join()
            .expect("cross-session party did not panic")
            .is_err());
    }

    // The nonce alone is not the session identity: a same-nonce modulus/shape
    // mutation with the same gate count is bound and rejected too.
    let session_shape_mutation =
        PartyMpcSession::new([0xa1; 32], 3, 3, 4, 19, Duration::from_millis(250))
            .expect("same-nonce mutated session");
    let inputs = party_inputs(&session_a, &[9, 6, 1], &[1, 6, 9], 0xa1a2);
    let preprocessing =
        trusted_dealer_triples(&session_a, &mut dealer_rng).expect("session-A triples again");
    let (coordinator, endpoints) = local_channels(&session_shape_mutation);
    let parties = inputs
        .into_iter()
        .zip(preprocessing)
        .zip(endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_party(input, triples, endpoint))
        })
        .collect::<Vec<_>>();
    assert_eq!(
        coordinator
            .coordinate(&session_shape_mutation)
            .expect_err("same nonce cannot hide a public-shape mutation"),
        PartyMpcError::SessionMismatch
    );
    for handle in parties {
        assert!(handle
            .join()
            .expect("shape-mutated party did not panic")
            .is_err());
    }
}
