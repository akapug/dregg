//! Party-owned threshold decrypt composed with the masked BFV→MPC boundary.
//!
//! Party threads retain both opaque `ThresholdParty` state and their plaintext
//! one-time-pad row. The coordinator receives only framed public-key messages,
//! framed `Enc(r_i)` contributions, and framed smudged decrypt shares. Locally
//! derived mod-t rows leave on a distinct channel standing in for MPC ingress.
//! This is a custody/API tooth, not authenticated transport or malicious security.

use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use fhe::bfv::{Ciphertext, Encoding, Plaintext, PublicKey};
use fhe_traits::{DeserializeParametrized, FheEncoder, FheEncrypter, Serialize as FheSerialize};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::boundary::{
    a2b_mod_t, triples_needed_boundary, BoundaryError, EncryptedMaskContribution,
    MaskedBoundaryParty, MaskedDecryptCoordinator, MaskedDecryptSession, MaskedOpening,
};
use fhegg_fhe::mpc::{open_int, Transcript, TriplePool};
use fhegg_fhe::mpc_party::{
    local_channels as mpc_channels, run_party as run_mpc_party, trusted_dealer_triples,
    PartyArithmeticInput, PartyMpcSession,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, DecryptShare, KeygenCoordinator, KeygenSession,
    PublicKeyContribution, ThresholdParty, MIN_SMUDGE_BITS,
};
use rand::rngs::StdRng;
use rand::SeedableRng;

enum PartyCommand {
    PrepareMask {
        session: MaskedDecryptSession,
        public_key_bytes: Vec<u8>,
    },
    Decrypt(LeanCiphertext),
    Derive(MaskedOpening),
    Stop,
}

#[test]
fn party_masks_and_threshold_shares_compose_without_a_joint_secret_key() {
    const N: usize = 2;
    const K: usize = 4;
    const B: usize = 16;

    let params = BfvParams::fold_set();
    let keygen_session = KeygenSession::random(N).expect("keygen session");
    let public_seed = keygen_session.crp_seed();

    let (keygen_tx, keygen_rx) = mpsc::channel::<Vec<u8>>();
    let (mask_tx, mask_rx) = mpsc::channel::<Vec<u8>>();
    let (decrypt_tx, decrypt_rx) = mpsc::channel::<Vec<u8>>();
    // This receiver represents the MPC ingress, not the masked-opening coordinator.
    let (mpc_tx, mpc_rx) = mpsc::channel::<(usize, Vec<u64>)>();

    let mut commands = Vec::with_capacity(N);
    let mut party_threads = Vec::with_capacity(N);
    for party_index in 0..N {
        let (command_tx, command_rx) = mpsc::channel::<PartyCommand>();
        commands.push(command_tx);
        let keygen_tx = keygen_tx.clone();
        let mask_tx = mask_tx.clone();
        let decrypt_tx = decrypt_tx.clone();
        let mpc_tx = mpc_tx.clone();
        party_threads.push(thread::spawn(move || {
            let params = BfvParams::fold_set();
            let keygen_session =
                KeygenSession::from_seed(N, public_seed).expect("public keygen session");
            let (threshold_party, keygen_contribution) =
                ThresholdParty::join(&keygen_session, party_index, &params)
                    .expect("party-owned threshold key share");
            keygen_tx
                .send(keygen_contribution.to_wire_bytes())
                .expect("public keygen contribution");

            let mut mask_state: Option<MaskedBoundaryParty> = None;
            while let Ok(command) = command_rx.recv() {
                match command {
                    PartyCommand::PrepareMask {
                        session,
                        public_key_bytes,
                    } => {
                        let pk = PublicKey::from_bytes(&public_key_bytes, params.arc())
                            .expect("public collective key parses");
                        let collective = CollectivePublicKey { pk };
                        let (state, contribution) = MaskedBoundaryParty::prepare(
                            &session,
                            party_index,
                            &params,
                            &collective,
                        )
                        .expect("party samples and retains mask");
                        mask_state = Some(state);
                        mask_tx
                            .send(contribution.to_wire_bytes())
                            .expect("encrypted-mask contribution");
                    }
                    PartyCommand::Decrypt(ciphertext) => {
                        let share = threshold_party
                            .partial_decrypt(&ciphertext, MIN_SMUDGE_BITS)
                            .expect("Lean-pinned smudged decrypt share");
                        decrypt_tx
                            .send(share.to_wire_bytes())
                            .expect("framed decrypt share");
                    }
                    PartyCommand::Derive(opening) => {
                        let state = mask_state.as_ref().expect("mask prepared first");
                        let row = state
                            .derive_mod_t_share(&opening)
                            .expect("local mod-t share derivation");
                        mpc_tx
                            .send((party_index, row))
                            .expect("local row enters MPC ingress");
                    }
                    PartyCommand::Stop => break,
                }
            }
        }));
    }
    drop(keygen_tx);
    drop(mask_tx);
    drop(decrypt_tx);
    drop(mpc_tx);

    // Public-only collective keygen. No joint SecretKey is constructed or nameable here.
    let mut keygen = KeygenCoordinator::new(keygen_session.clone(), params.clone());
    for _ in 0..N {
        let wire = keygen_rx.recv().expect("keygen contribution");
        keygen
            .accept(PublicKeyContribution::from_wire_bytes(&wire).expect("strict keygen wire"))
            .expect("unique in-session keygen contribution");
    }
    let collective = keygen.finish().expect("full public-key quorum");

    // Encrypt a known aggregate under the collective key; the known vector is
    // the external oracle, not a decryption through a conveniently assembled SK.
    let message = [0u64, 7, 65_535, 1_234];
    let mut slots = vec![0u64; params.degree()];
    slots[..K].copy_from_slice(&message);
    let plaintext =
        Plaintext::try_encode(&slots, Encoding::simd(), params.arc()).expect("SIMD encode");
    let mut crypto_rng = rand_09::rng();
    let target_ct: Ciphertext = collective
        .pk
        .try_encrypt(&plaintext, &mut crypto_rng)
        .expect("collective encrypt");
    let target = LeanCiphertext::from_fhe_bytes(
        &target_ct.to_bytes(),
        params.moduli(),
        params.degree(),
        65_535,
    )
    .expect("strict target parse");
    let session =
        MaskedDecryptSession::random(N, K, target.clone(), &params).expect("mask session");

    // Each party receives only public session/key material, retains r_i, and
    // returns only the framed encryption of r_i.
    let public_key_bytes = collective.pk.to_bytes();
    for command in &commands {
        command
            .send(PartyCommand::PrepareMask {
                session: session.clone(),
                public_key_bytes: public_key_bytes.clone(),
            })
            .expect("mask request");
    }
    let mut mask_messages = (0..N)
        .map(|_| {
            let wire = mask_rx.recv().expect("encrypted mask");
            EncryptedMaskContribution::from_wire_bytes(&wire, &params)
                .expect("strict encrypted-mask wire")
        })
        .collect::<Vec<_>>();
    mask_messages.sort_by_key(EncryptedMaskContribution::party);

    let mut mask_coordinator = MaskedDecryptCoordinator::new(session.clone(), params.clone());
    // Session mutation parses structurally but is not accepted into this round.
    let mut wrong_session_wire = mask_messages[0].to_wire_bytes();
    wrong_session_wire[32] ^= 1; // nonce starts after magic + party/n/k u64 fields
    let wrong_session = EncryptedMaskContribution::from_wire_bytes(&wrong_session_wire, &params)
        .expect("mutated public session remains structurally valid");
    assert_eq!(
        mask_coordinator.accept(wrong_session),
        Err(BoundaryError::SessionMismatch)
    );
    mask_coordinator
        .accept(mask_messages[0].clone())
        .expect("party 0 mask");
    assert_eq!(
        mask_coordinator.accept(mask_messages[0].clone()),
        Err(BoundaryError::DuplicateParty { party: 0 })
    );
    mask_coordinator
        .accept(mask_messages[1].clone())
        .expect("party 1 mask");
    let masked = mask_coordinator
        .finish()
        .expect("target plus full encrypted-mask quorum");

    // The coordinator asks each threshold party for a share over the exact
    // masked ciphertext and handles only its public framing.
    for command in &commands {
        command
            .send(PartyCommand::Decrypt(masked.ciphertext().clone()))
            .expect("masked decrypt request");
    }
    let mut decrypt_wires = (0..N)
        .map(|_| decrypt_rx.recv().expect("framed decrypt share"))
        .collect::<Vec<_>>();
    decrypt_wires.sort_by_key(|wire| {
        DecryptShare::from_wire_bytes(wire, &params)
            .expect("strict decrypt wire")
            .party()
    });
    assert_eq!(
        masked.open_framed(&decrypt_wires[..N - 1], &params),
        Err(BoundaryError::QuorumTooSmall {
            have: N - 1,
            need: N,
        })
    );

    // A valid share over a different ciphertext cannot be spliced into the round.
    commands[1]
        .send(PartyCommand::Decrypt(target.clone()))
        .expect("mismatch control request");
    let mismatch_wire = decrypt_rx.recv().expect("mismatch control share");
    assert_eq!(
        masked.open_framed(&[decrypt_wires[0].clone(), mismatch_wire], &params),
        Err(BoundaryError::SessionMismatch)
    );

    // Equality among the submitted shares is not enough: a complete quorum for
    // another ciphertext must still be rejected by the session target binding.
    for command in &commands {
        command
            .send(PartyCommand::Decrypt(target.clone()))
            .expect("wrong-target quorum request");
    }
    let wrong_target_wires = (0..N)
        .map(|_| decrypt_rx.recv().expect("wrong-target decrypt share"))
        .collect::<Vec<_>>();
    assert_eq!(
        masked.open_framed(&wrong_target_wires, &params),
        Err(BoundaryError::SessionMismatch),
        "a self-consistent quorum for another ciphertext must not open this session"
    );

    let opening = masked
        .open_framed(&decrypt_wires, &params)
        .expect("full exact-ciphertext threshold quorum opens only padded y");
    assert_eq!(opening.values().len(), K);

    // Each party locally turns (public y, private r_i) into its mod-t row.
    // The test driver gathers those rows only as the stand-in for MPC ingress.
    for command in &commands {
        command
            .send(PartyCommand::Derive(opening.clone()))
            .expect("public opening broadcast");
    }
    let mut party_rows = (0..N)
        .map(|_| mpc_rx.recv().expect("party's local MPC input row"))
        .collect::<Vec<_>>();
    party_rows.sort_by_key(|(party, _)| *party);

    let t = params.plaintext_modulus();
    let mut bool_rng = StdRng::seed_from_u64(0xB0_A2_B0_0D);
    let mut triples = TriplePool::generate(triples_needed_boundary(K, B, t, N), N, &mut bool_rng);
    let mut transcript = Transcript::default();
    for slot in 0..K {
        let sigma = party_rows
            .iter()
            .map(|(_, row)| row[slot])
            .collect::<Vec<_>>();
        assert_eq!(
            sigma.iter().fold(0u64, |acc, &share| (acc + share) % t),
            message[slot],
            "mod-t parity at slot {slot}"
        );
        let boolean = a2b_mod_t(&sigma, t, B, &mut triples, &mut transcript, &mut bool_rng);
        assert_eq!(
            open_int(&boolean),
            message[slot],
            "a2b parity at slot {slot}"
        );
    }

    // Actual party-thread MPC ingress: each constructor receives only one
    // MaskedBoundaryParty-derived row, peer-distributes its boolean shares, and
    // runs distributed A2B/mod-t reduction. Reusing the same aggregate for both
    // curves makes the expected crossing the lowest index of its maximum.
    let mpc_session = PartyMpcSession::new([0x4d; 32], N, K, B, t, Duration::from_secs(3))
        .expect("boundary-compatible MPC session");
    let mpc_inputs = party_rows
        .iter()
        .map(|(party, row)| {
            let mut party_rng = StdRng::seed_from_u64(0x4d50_4300 + *party as u64);
            PartyArithmeticInput::new(&mpc_session, *party, row, row, &mut party_rng)
                .expect("one party's local boundary rows enter MPC")
        })
        .collect::<Vec<_>>();
    let mut triple_rng = StdRng::seed_from_u64(0x4d50_4354);
    let mpc_triples = trusted_dealer_triples(&mpc_session, &mut triple_rng)
        .expect("shape-only triple preprocessing");
    let (mpc_coordinator, mpc_endpoints) = mpc_channels(&mpc_session);
    let mpc_parties = mpc_inputs
        .into_iter()
        .zip(mpc_triples)
        .zip(mpc_endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_mpc_party(input, triples, endpoint))
        })
        .collect::<Vec<_>>();
    let distributed = mpc_coordinator
        .coordinate(&mpc_session)
        .expect("full boundary-to-MPC party quorum");
    assert_eq!(distributed.crossing.p_star, Some(2));
    assert_eq!(distributed.crossing.v_star, 65_535);
    assert!(distributed.transcript.is_reveal_only(&mpc_session));
    for party in mpc_parties {
        party
            .join()
            .expect("MPC party thread exits")
            .expect("MPC party completes");
    }

    for command in commands {
        command.send(PartyCommand::Stop).expect("stop party");
    }
    for party in party_threads {
        party.join().expect("party thread exits");
    }
}
