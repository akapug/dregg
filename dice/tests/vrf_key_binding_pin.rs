//! CHARACTERIZATION PIN (fic-crypto lane) — an ACTIVE key-binding gap in the bare
//! `ServerVrf` / `EvidenceKind::LbVrf` verifier. Passes TODAY because the system is
//! broken; flip the assertion to `== 1` when the binding is added (see TESTQALOG
//! 2026-07-17 fic-crypto).
//!
//! Claim under test (dice/src/lib.rs security table row 4): "VRF one-output-per-input
//! — Closed by ServerVrf ... the LB-VRF output is the *unique* value for (key,input)".
//! And source.rs:331-336: "a per-event key committed in the request ... the verifier
//! checks the proof under the key the request committed to and the server cannot swap keys."
//! And dungeon-on-dregg/src/lib.rs:87 / combat.rs:75: the "non-grindable `ServerVrf`".
//!
//! The break: `ServerVrf::seed()` reads the public key FROM THE EVIDENCE and never
//! binds it to `req` (unlike `Hybrid::seed`, which checks a genesis-committed key-chain
//! Merkle membership). So an adversarial server GRINDS the outcome: mint many one-time
//! keys, eval each over the SAME event id, and present whichever (pk, output, proof)
//! yields the seed it wants. Every one VERIFIES. Uniqueness is per-(pk,x); with pk free,
//! the server picks x's output. ACTIVE: `attested_dm::game::verify_seed` (the light-client
//! trust surface) routes `EvidenceKind::LbVrf` into this verifier, and attested-dm ships a
//! live `SessionRandomness::LbVrf` producer. This is the grinding the game must prevent.

use dregg_dice::{RandomnessRequest, RandomnessSource, ServerVrf};
use std::collections::HashSet;

fn req() -> RandomnessRequest {
    RandomnessRequest {
        game_binding: b"game/epoch-7".to_vec(),
        seq: 42,
        pre_state_root: [0x11; 32],
        action_hash: [0x22; 32],
        event_kind: "combat/hit".to_string(),
        draw_count: 1,
    }
}

#[test]
fn server_vrf_output_is_grindable_because_pk_is_unbound() {
    let r = req();
    let mut seeds = HashSet::new();

    // The "server" tries many DIFFERENT one-time key epochs on the SAME request.
    for k in 0u8..32 {
        let source = ServerVrf::from_key_seed(&[k; 32]);
        let ev = source.try_evidence(&r).expect("honest eval");

        // The verifier ACCEPTS every one of them — pk is taken from the evidence and
        // never checked against the request.
        let seed = ServerVrf::seed(&r, &ev)
            .expect("a fully self-consistent (pk,output,proof) verifies for ANY key");
        seeds.insert(*seed.as_bytes());
    }

    // If pk were bound to the request, at most one key epoch would verify and the
    // server would have no choice of seed. Instead we got a whole menu:
    assert!(
        seeds.len() > 1,
        "expected many verifying seeds (grindable); got {}",
        seeds.len()
    );
    eprintln!(
        "GRIND: {} distinct verifying seeds for ONE event id — the server picks the outcome",
        seeds.len()
    );
}
