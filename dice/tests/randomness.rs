//! Non-vacuous verification tests for dregg-dice.
//!
//! These exercise the load-bearing properties: deterministic stream
//! reproduction, grinding detection (a changed `draw_count` diverges), skipped/
//! extra-index detection, an unbiased + reject-free bounded mapping, and the
//! CommitReveal round-trip incl. tamper rejection. The trust-level caveat
//! (selective abort is NOT prevented by CommitReveal) is asserted structurally
//! below.

use dregg_dice::{
    CommitReveal, Deterministic, DrawError, DrawStream, EventId, EvidenceKind, Hybrid, MockBeacon,
    RandomnessEvidence, RandomnessRequest, RandomnessSource, Seed, ServerVrf, VerifyError,
};

fn sample_request(draw_count: u32) -> RandomnessRequest {
    RandomnessRequest {
        game_binding: b"game/epoch-7".to_vec(),
        seq: 42,
        pre_state_root: [0x11; 32],
        action_hash: [0x22; 32],
        event_kind: "combat/hit".to_string(),
        draw_count,
    }
}

// ── Draw stream: a verifier reproduces the full stream from (seed, index). ──

#[test]
fn draw_stream_is_deterministic_and_reproducible() {
    let seed = Seed::from_bytes([0x5a; 32]);
    let a = DrawStream::new(seed, 8);
    let b = DrawStream::new(seed, 8); // an independent "verifier" reconstruction

    for i in 0..8 {
        assert_eq!(
            a.draw(i).unwrap(),
            b.draw(i).unwrap(),
            "same (seed,index) must yield the same draw"
        );
    }
    // Different indices produce different draws (stream is not constant).
    assert_ne!(a.draw(0).unwrap(), a.draw(1).unwrap());
    // A different seed produces a different stream.
    let other = DrawStream::new(Seed::from_bytes([0x5b; 32]), 8);
    assert_ne!(a.draw(0).unwrap(), other.draw(0).unwrap());
}

// ── Grinding detection: a changed draw_count changes the EventId, so the
//    evidence produced for the original count fails verification. ──

#[test]
fn changed_draw_count_changes_event_id() {
    let base = sample_request(3);
    let mut grinded = base.clone();
    grinded.draw_count = 4;
    assert_ne!(
        base.event_id().as_bytes(),
        grinded.event_id().as_bytes(),
        "draw_count is bound into the EventId"
    );
    // The same holds for event_kind (subsystem domain separation).
    let mut other_kind = base.clone();
    other_kind.event_kind = "loot".to_string();
    assert_ne!(base.event_id().as_bytes(), other_kind.event_id().as_bytes());
}

#[test]
fn grinding_draw_count_fails_verification() {
    // Server produces honest evidence for a 3-draw event.
    let req = sample_request(3);
    let src = CommitReveal {
        server_reveal: [0xaa; 32],
        player_contribution: [0xbb; 32],
    };
    let ev = src.evidence(&req);

    // Honest verification succeeds.
    let seed = CommitReveal::seed(&req, &ev).expect("honest evidence verifies");

    // An attacker re-presents the SAME evidence against a request with a
    // different draw_count (hoping to consume a different, favorable stream).
    // The EventId moves → the re-derived seed moves → the transcript no longer
    // matches → detected.
    let mut grinded_req = req.clone();
    grinded_req.draw_count = 5;
    assert_eq!(
        CommitReveal::seed(&grinded_req, &ev),
        Err(VerifyError::TranscriptMismatch),
        "grinding draw_count must be detected"
    );

    // Sanity: the honest seed does reproduce the committed transcript.
    let stream = DrawStream::new(seed, req.draw_count);
    assert_eq!(
        stream.transcript_commitment(),
        ev.draw_transcript_commitment
    );
}

// ── Skipped/extra index is detectable. ──

#[test]
fn out_of_range_index_is_rejected() {
    let stream = DrawStream::new(Seed::from_bytes([1; 32]), 3);
    assert!(stream.draw(0).is_ok());
    assert!(stream.draw(2).is_ok());
    assert_eq!(
        stream.draw(3),
        Err(DrawError::IndexOutOfRange {
            index: 3,
            draw_count: 3
        }),
        "index == draw_count is out of range"
    );
}

#[test]
fn extra_or_skipped_draw_changes_transcript() {
    let seed = Seed::from_bytes([7; 32]);
    let three = DrawStream::new(seed, 3).transcript_commitment();
    let four = DrawStream::new(seed, 4).transcript_commitment(); // one extra draw
    let two = DrawStream::new(seed, 2).transcript_commitment(); // one skipped draw
    assert_ne!(three, four, "an extra draw changes the transcript");
    assert_ne!(three, two, "a skipped draw changes the transcript");
}

// ── Bounded mapping: unbiased + reject-free + deterministic. ──

#[test]
fn bounded_mapping_is_deterministic() {
    let seed = Seed::from_bytes([0x99; 32]);
    let s1 = DrawStream::new(seed, 100);
    let s2 = DrawStream::new(seed, 100);
    for i in 0..100 {
        assert_eq!(
            s1.draw_bounded(i, 20).unwrap(),
            s2.draw_bounded(i, 20).unwrap()
        );
        // Range respected.
        assert!(s1.draw_bounded(i, 20).unwrap() < 20);
        // Die convenience is 1-based.
        let d = s1.draw_die(i, 6).unwrap();
        assert!((1..=6).contains(&d));
    }
    assert_eq!(s1.draw_bounded(0, 0), Err(DrawError::ZeroBound));
}

#[test]
fn bounded_mapping_is_unbiased_and_reject_free() {
    // Roll a d6 sixty thousand times via distinct indices. The wide
    // multiply-and-shift mapping consumes EXACTLY ONE raw draw per index (no
    // rejection loop), so the number of draws is a public constant `n` — this is
    // what lets draw_count be bound up front. Verify the outputs are near-uniform.
    const N: u32 = 60_000;
    const SIDES: u64 = 6;
    let stream = DrawStream::new(Seed::from_bytes([0x42; 32]), N);

    let mut buckets = [0u64; SIDES as usize];
    for i in 0..N {
        // draw_die is 1..=6; index into 0..6.
        let face = stream.draw_die(i, SIDES).unwrap();
        assert!((1..=SIDES).contains(&face));
        buckets[(face - 1) as usize] += 1;
    }

    // Every face appears (reject-free coverage) and total is exactly N (one draw
    // consumed per index — no draw was discarded).
    let total: u64 = buckets.iter().sum();
    assert_eq!(
        total, N as u64,
        "exactly one outcome per draw — reject-free"
    );
    assert!(buckets.iter().all(|&c| c > 0), "every face must appear");

    // Chi-square goodness-of-fit against uniform. Expected = N/6 = 10000 per face.
    // df = 5; the 0.1% critical value is ~20.5, 0.01% is ~25.7. The stream is
    // deterministic (fixed seed), so this is a stable, non-flaky assertion; a
    // biased mapping (e.g. `x % 6`) would inflate this well past the threshold.
    let expected = N as f64 / SIDES as f64;
    let chi2: f64 = buckets
        .iter()
        .map(|&c| {
            let d = c as f64 - expected;
            d * d / expected
        })
        .sum();
    assert!(
        chi2 < 20.5,
        "d6 distribution not uniform enough: chi2 = {chi2:.3} (buckets = {buckets:?})"
    );

    // Each bucket within 5% of expected — a coarse eyeball backstop.
    for &c in &buckets {
        let dev = (c as f64 - expected).abs() / expected;
        assert!(dev < 0.05, "bucket deviates {:.3} from uniform", dev);
    }
}

// ── CommitReveal round-trip + tamper rejection. ──

#[test]
fn commit_reveal_round_trip() {
    let req = sample_request(4);
    let src = CommitReveal {
        server_reveal: [0xc0; 32],
        player_contribution: [0x0d; 32],
    };
    let ev = src.evidence(&req);

    // Evidence carries the published commitment (server committed before reveal).
    match &ev.source {
        EvidenceKind::CommitReveal {
            server_commitment,
            server_reveal,
            ..
        } => {
            assert_eq!(*server_commitment, CommitReveal::commit(server_reveal));
        }
        _ => panic!("wrong evidence kind"),
    }

    // produce → verify → seed round-trips, and the seed reproduces the draws.
    let seed = CommitReveal::seed(&req, &ev).expect("round-trip verifies");
    let stream = DrawStream::new(seed, req.draw_count);
    assert_eq!(
        stream.transcript_commitment(),
        ev.draw_transcript_commitment
    );
}

#[test]
fn tampered_reveal_fails_commitment() {
    let req = sample_request(2);
    let src = CommitReveal {
        server_reveal: [0x01; 32],
        player_contribution: [0x02; 32],
    };
    let mut ev = src.evidence(&req);

    // Attacker swaps in a different reveal (to bias the seed) but leaves the
    // published commitment. The reveal no longer opens the commitment → rejected
    // before the seed is even used.
    if let EvidenceKind::CommitReveal { server_reveal, .. } = &mut ev.source {
        *server_reveal = [0xff; 32];
    }
    assert_eq!(
        CommitReveal::seed(&req, &ev),
        Err(VerifyError::CommitmentMismatch),
        "a tampered reveal must fail commitment verification"
    );
}

#[test]
fn tampered_player_contribution_fails_transcript() {
    // The player's contribution is not behind a commitment, but it feeds the
    // seed, so changing it moves the transcript → detected there.
    let req = sample_request(2);
    let src = CommitReveal {
        server_reveal: [0x01; 32],
        player_contribution: [0x02; 32],
    };
    let mut ev = src.evidence(&req);
    if let EvidenceKind::CommitReveal {
        player_contribution,
        ..
    } = &mut ev.source
    {
        *player_contribution = [0x03; 32];
    }
    assert_eq!(
        CommitReveal::seed(&req, &ev),
        Err(VerifyError::TranscriptMismatch)
    );
}

/// TRUST-LEVEL NOTE (asserted structurally): CommitReveal prevents unilateral
/// *choice* but NOT selective *abort*. There is no protocol step here by which a
/// party is *forced* to reveal — `CommitReveal::seed` verifies evidence that
/// already contains the reveal. A dishonest last-revealer who dislikes the
/// outcome simply never produces the evidence, and the transition never lands.
/// This test documents that gap: we can compute the outcome from a would-be
/// reveal *before* committing to landing it, which is exactly the abort lever.
/// Closing it needs timeout finalization (a follow-up), NOT anything in this crate.
#[test]
fn commit_reveal_selective_abort_is_not_prevented() {
    let req = sample_request(1);
    let unfavorable_hunt = |reveal: [u8; 32]| -> u64 {
        let src = CommitReveal {
            server_reveal: reveal,
            player_contribution: [0x00; 32],
        };
        let ev = src.evidence(&req);
        let seed = CommitReveal::seed(&req, &ev).unwrap();
        DrawStream::new(seed, 1).draw_die(0, 20).unwrap()
    };
    // The server can evaluate the outcome for its (already chosen) reveal BEFORE
    // deciding to publish the evidence at all. Nothing in the verifier forces
    // publication — that is the selective-abort gap, by construction.
    let outcome = unfavorable_hunt([0x77; 32]);
    assert!((1..=20).contains(&outcome));
    // (No cryptographic control here prevents "see result, then decline to land".)
}

// ── Deterministic + MockBeacon round-trips, and the VRF/Hybrid stubs. ──

#[test]
fn deterministic_source_round_trip() {
    let req = sample_request(3);
    let src = Deterministic {
        context: [0x33; 32],
    };
    let ev = src.evidence(&req);
    let seed = Deterministic::seed(&req, &ev).expect("verifies");
    assert_eq!(
        DrawStream::new(seed, req.draw_count).transcript_commitment(),
        ev.draw_transcript_commitment
    );
    // Cross-source verifier rejects a foreign evidence kind.
    assert_eq!(
        CommitReveal::seed(&req, &ev),
        Err(VerifyError::SourceMismatch)
    );
}

#[test]
fn mock_beacon_round_trip() {
    let req = sample_request(2);
    let src = MockBeacon {
        beacon_id: b"drand/quicknet".to_vec(),
        round: 9_000_001,
        output: [0xbe; 32],
    };
    let ev = src.evidence(&req);
    let seed = MockBeacon::seed(&req, &ev).expect("verifies");
    assert_eq!(
        DrawStream::new(seed, req.draw_count).transcript_commitment(),
        ev.draw_transcript_commitment
    );
    // A different beacon output → different seed → different transcript.
    let mut tampered = ev.clone();
    if let EvidenceKind::Beacon { output, .. } = &mut tampered.source {
        *output = [0xbf; 32];
    }
    assert_eq!(
        MockBeacon::seed(&req, &tampered),
        Err(VerifyError::TranscriptMismatch)
    );
}

#[test]
fn vrf_and_hybrid_stubs_fail_closed() {
    let req = sample_request(1);
    let dummy = RandomnessEvidence {
        derivation_version: dregg_dice::DERIVATION_VERSION,
        source: EvidenceKind::Vrf {
            public_key: vec![1, 2, 3],
            output: [0; 32],
            proof: vec![],
        },
        draw_transcript_commitment: [0; 32],
    };
    assert!(matches!(
        ServerVrf::seed(&req, &dummy),
        Err(VerifyError::BackendUnavailable(_))
    ));
    assert!(matches!(
        Hybrid::seed(&req, &dummy),
        Err(VerifyError::BackendUnavailable(_))
    ));
}

// ── EventId domain separation + serde. ──

#[test]
fn event_id_derive_matches_request() {
    let req = sample_request(3);
    let direct = EventId::derive(
        &req.game_binding,
        req.seq,
        &req.pre_state_root,
        &req.action_hash,
        &req.event_kind,
        req.draw_count,
    );
    assert_eq!(direct.as_bytes(), req.event_id().as_bytes());
}

#[test]
fn request_commitment_changes_with_any_bound_field() {
    let base = sample_request(3).commitment();
    let mut r = sample_request(3);
    r.seq = 43;
    assert_ne!(base, r.commitment());
    let mut r2 = sample_request(3);
    r2.action_hash = [0x23; 32];
    assert_ne!(base, r2.commitment());
}

#[test]
fn evidence_serde_round_trip() {
    let req = sample_request(2);
    let ev = CommitReveal {
        server_reveal: [9; 32],
        player_contribution: [8; 32],
    }
    .evidence(&req);
    let json = serde_json::to_string(&ev).unwrap();
    let back: RandomnessEvidence = serde_json::from_str(&json).unwrap();
    assert_eq!(ev, back);
    // The deserialized evidence still verifies.
    assert!(CommitReveal::seed(&req, &back).is_ok());
}
