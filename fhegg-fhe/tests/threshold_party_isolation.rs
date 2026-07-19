//! Process-shaped no-viewer custody tooth.
//!
//! Each party thread constructs and retains its own opaque `ThresholdParty`. The coordinator sees
//! only framed public-key contributions and framed smudged decrypt shares (`Vec<u8>`), exactly the
//! objects an external transport would carry. This proves the Rust API no longer requires one
//! caller to receive every secret `KeyShare`; it does NOT provide transport authentication,
//! persistent secret storage, malicious-share verification, or crash recovery.

use std::sync::mpsc;
use std::thread;

use fhe::bfv::{Encoding, Plaintext};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::threshold::{
    combine, BfvParams, DecryptShare, KeygenCoordinator, KeygenSession, PublicKeyContribution,
    ThresholdError, ThresholdParty, MIN_SMUDGE_BITS,
};

enum PartyCommand {
    Decrypt(LeanCiphertext),
    Stop,
}

#[test]
fn coordinator_only_handles_public_messages_across_party_channels() {
    const N: usize = 2;

    let params = BfvParams::fold_set();
    let session = KeygenSession::random(N).expect("session");
    let public_session_seed = session.crp_seed();
    let (contribution_tx, contribution_rx) = mpsc::channel::<Vec<u8>>();
    let (decrypt_tx, decrypt_rx) = mpsc::channel::<Vec<u8>>();

    let mut commands = Vec::with_capacity(N);
    let mut parties = Vec::with_capacity(N);
    for party_index in 0..N {
        let (command_tx, command_rx) = mpsc::channel::<PartyCommand>();
        commands.push(command_tx);
        let contribution_tx = contribution_tx.clone();
        let decrypt_tx = decrypt_tx.clone();
        parties.push(thread::spawn(move || {
            // Reconstruct only PUBLIC session/parameter state in this party's custody domain.
            let params = BfvParams::fold_set();
            let session = KeygenSession::from_seed(N, public_session_seed).expect("wire session");
            let (party, contribution) =
                ThresholdParty::join(&session, party_index, &params).expect("party keygen");
            contribution_tx
                .send(contribution.to_wire_bytes())
                .expect("public contribution channel");

            while let Ok(command) = command_rx.recv() {
                match command {
                    PartyCommand::Decrypt(ct) => {
                        let share = party
                            .partial_decrypt(&ct, MIN_SMUDGE_BITS)
                            .expect("Lean-pinned smudged share");
                        decrypt_tx
                            .send(share.to_wire_bytes())
                            .expect("public decrypt-share channel");
                    }
                    PartyCommand::Stop => break,
                }
            }
        }));
    }
    drop(contribution_tx);
    drop(decrypt_tx);

    // The coordinator accepts only parsed PUBLIC messages. Secret KeyShare is private to the
    // threshold module and is not nameable or returnable through this integration-test API.
    let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
    for _ in 0..N {
        let wire = contribution_rx.recv().expect("party contribution");
        let contribution = PublicKeyContribution::from_wire_bytes(&wire).expect("wire parses");
        assert_eq!(contribution.session(), &session);
        coordinator
            .accept(contribution)
            .expect("contribution accepted");
    }
    let collective = coordinator.finish().expect("full n-of-n public key");

    let mut message = vec![0u64; params.degree()];
    message[..4].copy_from_slice(&[7, 19, 23, 41]);
    let plaintext =
        Plaintext::try_encode(&message, Encoding::simd(), params.arc()).expect("plaintext encode");
    let mut rng = rand_09::rng();
    let ciphertext = collective
        .pk
        .try_encrypt(&plaintext, &mut rng)
        .expect("collective-key encrypt");
    let ciphertext = LeanCiphertext::from_fhe_bytes(
        &ciphertext.to_bytes(),
        params.moduli(),
        params.degree(),
        41,
    )
    .expect("wire ciphertext parse");

    for command in &commands {
        command
            .send(PartyCommand::Decrypt(ciphertext.clone()))
            .expect("decrypt request");
    }
    let mut shares = Vec::with_capacity(N);
    for _ in 0..N {
        shares.push(
            DecryptShare::from_wire_bytes(
                &decrypt_rx.recv().expect("decrypt-share response"),
                &params,
            )
            .expect("decrypt-share wire parses"),
        );
    }
    shares.sort_by_key(DecryptShare::party);

    assert_eq!(
        combine(&shares[..N - 1], &params),
        Err(ThresholdError::QuorumTooSmall {
            have: N - 1,
            need: N,
        }),
        "n-of-n refusal survives the process-shaped API"
    );
    let decoded = combine(&shares, &params).expect("full n-of-n combine");
    assert_eq!(&decoded[..4], &message[..4]);

    for command in commands {
        command.send(PartyCommand::Stop).expect("stop party");
    }
    for party in parties {
        party.join().expect("party thread exits");
    }
}
