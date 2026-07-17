//! **SESSION LIFECYCLE, DRIVEN — the host-layer cap/TTL/eviction policy in both polarities.**
//!
//! The structural G2 fix (`docs/EXCELLENCE-BACKLOG-2026-07-16.md`): unbounded session growth and
//! zero throttling lived twice (web + bot) because session management was reimplemented per
//! surface; here it lives ONCE in [`OfferingHost`] and these tests drive every gate on the real
//! dungeon substrate with a deterministic [`ManualClock`]:
//!
//! * CAPACITY: opening past the cap LRU-evicts the coldest PERSISTED session — which then
//!   RESUMES on its next touch with state intact — and REFUSES (typed) when nothing is evictable;
//! * PER-ACTOR QUOTA: an opener at its limit is refused (typed), other openers unaffected, and
//!   the `Signed` / `Asserted` quota lanes are disjoint namespaces;
//! * OPEN RATE: a too-fast second mint is refused with an honest retry-after; time passing admits;
//! * TTL SWEEP: an idle persisted session is evicted + resumes on touch; an idle UNpersisted one
//!   is retained unless the policy names the loss (`evict_unpersisted`) — both polarities;
//! * REPLAY SAFETY across evict/resume AND across a full restart: a signed envelope consumed
//!   before eviction stays consumed after resume (the floor survived — persisted, never wiped),
//!   while a fresh higher-counter envelope lands;
//! * NONE-POLICY: the default policy is byte-identical unbounded behavior.

use dreggnet_offerings::dungeon::{DungeonOffering, TURN_CHOOSE};
use dreggnet_offerings::resume::InMemoryResumeStore;
use dreggnet_offerings::signed::TurnSigner;
use dreggnet_offerings::{
    Action, Attribution, DreggIdentity, HostError, ManualClock, OfferingHost, PolicyRefusal,
    SessionId, SessionPolicy, SignedError,
};
use dungeon_on_dregg::{KP_CLAIM_RED, KP_PRESS_ON};

fn choose(arg: usize) -> Action {
    Action::new("move", TURN_CHOOSE, arg as i64, true)
}

fn asserted(label: &str) -> Attribution {
    Attribution::Asserted {
        label: label.to_string(),
    }
}

/// A dungeon host with `policy` armed on `clock`, optionally over a durable store.
fn policied_host(
    policy: SessionPolicy,
    clock: &ManualClock,
    store: Option<&InMemoryResumeStore>,
) -> OfferingHost {
    let mut host = OfferingHost::new().with_policy(policy, clock.clone());
    if let Some(s) = store {
        host = host.with_resume_store(Box::new(s.clone()));
    }
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    host
}

/// Land one real dungeon turn on `(dungeon, id)` attributed to `actor`.
fn land_turn(host: &mut OfferingHost, id: &SessionId, actor: &str) {
    let out = host
        .advance(
            "dungeon",
            id,
            choose(KP_PRESS_ON),
            DreggIdentity(actor.to_string()),
        )
        .expect("session is live");
    assert!(out.landed(), "the move landed a real receipt");
}

/// **CAPACITY + LRU + LAZY RESUME.** At the 2-session cap, a third open EVICTS the coldest
/// persisted session (LRU by last touch, driven on a manual clock); the evicted session is no
/// longer live — and then RESUMES transparently on its next touch, to its identical committed
/// state (turn count + commitment equal, non-vacuously ≠ genesis).
#[test]
fn capacity_evicts_the_coldest_persisted_session_which_resumes_on_touch() {
    let clock = ManualClock::new(1_000);
    let store = InMemoryResumeStore::new();
    let policy = SessionPolicy {
        max_sessions_per_offering: Some(2),
        ..SessionPolicy::default()
    };
    let mut host = policied_host(policy, &clock, Some(&store));

    // t=1000: open A and land a real turn (the state the resume must bring back).
    let a = SessionId::new("cap-a");
    assert!(host.ensure_open_as("dungeon", &a, None).expect("A opens"));
    land_turn(&mut host, &a, "alice");
    let a_commit = host.commitment("dungeon", &a).expect("A commits");
    let a_genesis_differs = {
        // Non-vacuity witness: a fresh identically-seeded session at genesis commits differently.
        let mut probe = OfferingHost::new();
        probe.register("dungeon", "probe", DungeonOffering::new());
        let g = SessionId::new("cap-a");
        probe.ensure_open("dungeon", &g).expect("genesis opens");
        probe.commitment("dungeon", &g).expect("genesis commits") != a_commit
    };
    assert!(
        a_genesis_differs,
        "A's played state provably differs from genesis"
    );

    // t=1010: open B. t=1020: touch A (render), so B is now the coldest.
    clock.set(1_010);
    let b = SessionId::new("cap-b");
    assert!(host.ensure_open_as("dungeon", &b, None).expect("B opens"));
    clock.set(1_020);
    assert!(host.render("dungeon", &a).is_some(), "A touched (hot)");

    // t=1030: opening C at the cap evicts the COLDEST (B) — not the recently-touched A.
    clock.set(1_030);
    let c = SessionId::new("cap-c");
    assert!(host.ensure_open_as("dungeon", &c, None).expect("C opens"));
    assert!(host.is_open("dungeon", &a), "hot A survived");
    assert!(!host.is_open("dungeon", &b), "coldest B was evicted");
    assert!(host.is_open("dungeon", &c), "C is live");

    // B's next touch RESUMES it from the store — state intact (it was at genesis; drive it to
    // prove the lane, then evict A and resume A to check a PLAYED state comes back).
    assert_eq!(
        host.ensure_open_as("dungeon", &b, None).expect("B resumes"),
        false,
        "a resume is not a fresh mint"
    );
    assert!(host.is_open("dungeon", &b), "B is live again");
    // Resuming B at the cap evicted the then-coldest (A, untouched since t=1020 vs C at 1030).
    assert!(
        !host.is_open("dungeon", &a),
        "A was the coldest and gave way"
    );

    // A's next touch resumes A's PLAYED state: same turn count, same commitment.
    clock.set(1_040);
    assert!(!host.ensure_open_as("dungeon", &a, None).expect("A resumes"));
    let report = host.verify("dungeon", &a).expect("A re-verifies");
    assert!(report.verified);
    assert_eq!(
        report.turns, 2,
        "genesis + the landed turn survived eviction"
    );
    assert_eq!(
        host.commitment("dungeon", &a).expect("A commits"),
        a_commit,
        "the resumed session is in the IDENTICAL committed state"
    );
}

/// **CAPACITY REFUSES when nothing is evictable** — no store, no lossy opt-in: the cap holds
/// with a typed [`PolicyRefusal::Capacity`], and the sessions already live are untouched.
#[test]
fn capacity_refuses_when_nothing_is_evictable() {
    let clock = ManualClock::new(0);
    let policy = SessionPolicy {
        max_sessions_per_offering: Some(1),
        ..SessionPolicy::default()
    };
    let mut host = policied_host(policy, &clock, None);

    let a = SessionId::new("only");
    assert!(host.ensure_open_as("dungeon", &a, None).expect("A opens"));
    let refused = host.ensure_open_as("dungeon", &SessionId::new("over"), None);
    assert!(
        matches!(
            refused,
            Err(HostError::Policy(PolicyRefusal::Capacity { ref key, limit: 1 })) if key == "dungeon"
        ),
        "the over-cap open is refused by NAME: {refused:?}"
    );
    assert!(
        host.is_open("dungeon", &a),
        "the live session was not sacrificed"
    );
    // The refused id was never opened.
    assert!(!host.is_open("dungeon", &SessionId::new("over")));
    // A re-touch of the LIVE session is not an open — never gated.
    assert!(!host.ensure_open_as("dungeon", &a, None).expect("touch ok"));
}

/// **PER-ACTOR QUOTA, both polarities + the trust-boundary namespacing.** An opener at its
/// fresh-mint limit is refused (typed, naming the quota); a different opener is unaffected; and
/// the `Signed` vs `Asserted` quota lanes are DISJOINT even over the same identity string (a
/// forgeable label can never spend a signed key's quota). Eviction frees the quota slot.
#[test]
fn per_actor_quota_refuses_at_limit_and_namespaces_signed_vs_asserted() {
    let clock = ManualClock::new(0);
    let store = InMemoryResumeStore::new();
    let policy = SessionPolicy {
        max_opens_per_actor: Some(1),
        idle_ttl_secs: Some(10),
        ..SessionPolicy::default()
    };
    let mut host = policied_host(policy, &clock, Some(&store));

    let signer = TurnSigner::from_seed([7u8; 32]);
    let signed = Attribution::Signed {
        pubkey_hex: signer.pubkey_hex().to_string(),
    };
    // The FORGEABLE twin: an asserted label carrying the same string as the signed pubkey.
    let label_twin = asserted(signer.pubkey_hex());

    // The signed opener mints one session — at its quota.
    let s1 = host
        .open_as("dungeon", Some(&signed))
        .expect("first mint lands");
    let refused = host.open_as("dungeon", Some(&signed));
    assert!(
        matches!(
            refused,
            Err(HostError::Policy(PolicyRefusal::ActorQuota {
                limit: 1,
                ..
            }))
        ),
        "the signed opener at its limit is refused by NAME: {refused:?}"
    );

    // The asserted twin (same string, forgeable lane) is a DIFFERENT quota bucket — admitted.
    let a1 = host
        .open_as("dungeon", Some(&label_twin))
        .expect("the asserted lane has its own quota");
    // ... and now the asserted twin is itself at limit.
    assert!(matches!(
        host.open_as("dungeon", Some(&label_twin)),
        Err(HostError::Policy(PolicyRefusal::ActorQuota { .. }))
    ));

    // A third, unrelated opener is unaffected.
    let bob = asserted("bob");
    host.open_as("dungeon", Some(&bob))
        .expect("bob is not gated by others' quotas");

    // EVICTION FREES THE SLOT: idle out the signed opener's session; its quota slot returns.
    clock.set(100);
    let report = host.sweep(100);
    assert!(
        report.evicted.iter().any(|(_, id)| *id == s1),
        "the idle session was evicted: {report:?}"
    );
    host.open_as("dungeon", Some(&signed))
        .expect("the freed quota slot admits a new mint");
    let _ = a1;
}

/// **OPEN RATE.** A second mint inside the interval is refused with an honest retry-after;
/// once the clock passes the interval the same opener is admitted; another opener never waits.
#[test]
fn open_rate_limits_a_burst_and_admits_after_the_interval() {
    let clock = ManualClock::new(50);
    let policy = SessionPolicy {
        min_open_interval_secs: Some(10),
        ..SessionPolicy::default()
    };
    let mut host = policied_host(policy, &clock, None);
    let alice = asserted("alice");

    host.open_as("dungeon", Some(&alice)).expect("first mint");
    clock.set(55);
    let refused = host.open_as("dungeon", Some(&alice));
    assert!(
        matches!(
            refused,
            Err(HostError::Policy(PolicyRefusal::OpenRate {
                retry_after_secs: 5
            }))
        ),
        "a too-fast mint is refused with the honest retry-after: {refused:?}"
    );
    // Another opener is on their own rate lane.
    host.open_as("dungeon", Some(&asserted("bob")))
        .expect("bob's first mint is not gated by alice's burst");
    // Time passing admits alice again.
    clock.set(60);
    host.open_as("dungeon", Some(&alice))
        .expect("the interval elapsed — admitted");
}

/// **TTL SWEEP, both polarities.** An idle PERSISTED session is evicted (and resumes on touch,
/// state intact); a hot one survives; an idle UNPERSISTED session is RETAINED (reported) unless
/// the policy opts into the loss by name — under `evict_unpersisted` it is genuinely gone and a
/// re-open is a fresh genesis.
#[test]
fn ttl_sweep_evicts_idle_persisted_sessions_and_retains_unpersisted_unless_opted_in() {
    // ── persisted: evict + lazy resume ──
    let clock = ManualClock::new(0);
    let store = InMemoryResumeStore::new();
    let policy = SessionPolicy {
        idle_ttl_secs: Some(100),
        ..SessionPolicy::default()
    };
    let mut host = policied_host(policy.clone(), &clock, Some(&store));

    let idle = SessionId::new("ttl-idle");
    let hot = SessionId::new("ttl-hot");
    host.ensure_open_as("dungeon", &idle, None)
        .expect("idle opens");
    land_turn(&mut host, &idle, "alice");
    let idle_commit = host.commitment("dungeon", &idle).expect("commits");
    host.ensure_open_as("dungeon", &hot, None)
        .expect("hot opens");

    clock.set(90);
    assert!(
        host.render("dungeon", &hot).is_some(),
        "hot touched at t=90"
    );
    clock.set(150); // idle is 150s idle (> 100); hot is 60s idle.
    let report = host.sweep(150);
    assert_eq!(
        report.evicted,
        vec![("dungeon".to_string(), idle.clone())],
        "exactly the idle-past-TTL session was evicted"
    );
    assert!(!host.is_open("dungeon", &idle));
    assert!(host.is_open("dungeon", &hot), "the hot session survived");

    // The evicted session RESUMES on touch — identical committed state.
    assert!(
        !host
            .ensure_open_as("dungeon", &idle, None)
            .expect("resumes")
    );
    assert_eq!(
        host.commitment("dungeon", &idle).expect("commits"),
        idle_commit,
        "the resumed session is in the identical committed state"
    );

    // ── unpersisted: retained by default, evicted (lossily) only under the named opt-in ──
    let clock2 = ManualClock::new(0);
    let mut bare = policied_host(policy, &clock2, None);
    let s = SessionId::new("bare");
    bare.ensure_open_as("dungeon", &s, None).expect("opens");
    land_turn(&mut bare, &s, "alice");
    clock2.set(1_000);
    let report = bare.sweep(1_000);
    assert!(
        report.evicted.is_empty(),
        "no store, no opt-in: nothing evicted"
    );
    assert_eq!(
        report.retained_unpersisted,
        vec![("dungeon".to_string(), s.clone())],
        "the idle unpersisted session is RETAINED and honestly reported"
    );
    assert!(
        bare.is_open("dungeon", &s),
        "still live — its state was not lost"
    );

    let clock3 = ManualClock::new(0);
    let lossy_policy = SessionPolicy {
        idle_ttl_secs: Some(100),
        evict_unpersisted: true,
        ..SessionPolicy::default()
    };
    let mut lossy = policied_host(lossy_policy, &clock3, None);
    let s = SessionId::new("lossy");
    lossy.ensure_open_as("dungeon", &s, None).expect("opens");
    land_turn(&mut lossy, &s, "alice");
    let played_turns = lossy.verify("dungeon", &s).expect("live").turns;
    assert_eq!(played_turns, 2);
    clock3.set(1_000);
    let report = lossy.sweep(1_000);
    assert_eq!(report.evicted.len(), 1, "the named opt-in evicts lossily");
    assert!(!lossy.is_open("dungeon", &s));
    // A re-open under the same id is a FRESH genesis — the loss is real (and was named).
    assert!(
        lossy
            .ensure_open_as("dungeon", &s, None)
            .expect("re-opens fresh")
    );
    assert_eq!(
        lossy.verify("dungeon", &s).expect("live").turns,
        1,
        "genesis only — the played state did not silently survive a LOSSY eviction"
    );
}

/// **REPLAY SAFETY across evict/resume.** A signed envelope consumed before eviction is STILL
/// refused after the session is evicted and lazily resumed (the counter floor survived — it was
/// persisted, never wiped with the in-memory bookkeeping); a fresh higher-counter envelope lands.
#[test]
fn a_signed_envelope_cannot_replay_across_evict_and_resume() {
    let clock = ManualClock::new(0);
    let store = InMemoryResumeStore::new();
    let policy = SessionPolicy {
        idle_ttl_secs: Some(10),
        ..SessionPolicy::default()
    };
    let mut host = policied_host(policy, &clock, Some(&store));
    let signer = TurnSigner::from_seed([9u8; 32]);

    let id = SessionId::new("replay");
    host.ensure_open_as("dungeon", &id, None).expect("opens");

    // Counter 0 consumed by a real signed landed turn; keep the envelope (the capture).
    let captured = signer.sign("dungeon", &id, 0, choose(KP_PRESS_ON));
    assert!(
        host.advance_signed("dungeon", &id, captured.clone())
            .expect("the genuine signed move lands")
            .landed()
    );

    // Idle out + evict.
    clock.set(100);
    let report = host.sweep(100);
    assert_eq!(report.evicted.len(), 1, "the idle session was evicted");
    assert!(!host.is_open("dungeon", &id));

    // The REPLAY: the captured envelope against the evicted session. advance_signed lazily
    // RESUMES the session — and the resumed floor still refuses the burnt counter.
    let replay = host.advance_signed("dungeon", &id, captured);
    assert!(
        matches!(
            replay,
            Err(HostError::Signature(SignedError::StaleCounter {
                presented: 0,
                expected: 1
            }))
        ),
        "the captured envelope is refused AFTER evict+resume — the floor survived: {replay:?}"
    );
    assert!(
        host.is_open("dungeon", &id),
        "the lazy resume itself landed"
    );
    assert_eq!(
        host.verify("dungeon", &id).expect("live").turns,
        2,
        "genesis + the ONE original signed turn — the replay committed nothing"
    );

    // A fresh, higher-counter envelope lands (the lane is alive, not bricked).
    let fresh = signer.sign("dungeon", &id, 1, choose(KP_CLAIM_RED));
    assert!(
        host.advance_signed("dungeon", &id, fresh)
            .expect("the fresh envelope lands")
            .landed()
    );
    assert_eq!(
        host.signed_counter("dungeon", &id, signer.pubkey_hex()),
        Some(1)
    );
}

/// **REPLAY SAFETY across a full RESTART.** The consumed floor is written through to the store
/// beside the move-log, so a brand-new host booting `resume_all` over the same store refuses the
/// captured pre-restart envelope — the restart is not a counter reset.
#[test]
fn a_signed_envelope_cannot_replay_across_a_restart() {
    let store = InMemoryResumeStore::new();
    let signer = TurnSigner::from_seed([11u8; 32]);
    let id;
    let captured;
    {
        let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
        host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
        id = host.open("dungeon").expect("opens");
        captured = signer.sign("dungeon", &id, 0, choose(KP_PRESS_ON));
        assert!(
            host.advance_signed("dungeon", &id, captured.clone())
                .expect("lands")
                .landed()
        );
    } // the process "dies" — every in-memory ledger is gone

    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let resumed = host.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "the session boot-resumed");

    let replay = host.advance_signed("dungeon", &id, captured);
    assert!(
        matches!(
            replay,
            Err(HostError::Signature(SignedError::StaleCounter { .. }))
        ),
        "the pre-restart envelope is refused — the floor was persisted, not reset: {replay:?}"
    );
    // The signer continues at the next counter.
    assert!(
        host.advance_signed(
            "dungeon",
            &id,
            signer.sign("dungeon", &id, 1, choose(KP_CLAIM_RED))
        )
        .expect("lands")
        .landed()
    );
}

/// **NONE-POLICY = today's unbounded behavior.** A host with the default (all-`None`) policy —
/// and a host with NO policy call at all — admits any number of opens, sweeps nothing, and
/// `ensure_open` keeps its exact open-then-exists contract.
#[test]
fn the_default_policy_is_byte_identical_unbounded() {
    let clock = ManualClock::new(0);
    for mut host in [policied_host(SessionPolicy::default(), &clock, None), {
        let mut h = OfferingHost::new();
        h.register("dungeon", "The Warden's Keep", DungeonOffering::new());
        h
    }] {
        let alice = asserted("alice");
        // Many rapid opens by one actor: no cap, no rate, no quota.
        for i in 0..8 {
            let id = SessionId::new(format!("free-{i}"));
            assert!(
                host.ensure_open_as("dungeon", &id, Some(&alice))
                    .expect("unbounded open lands")
            );
            assert!(!host.ensure_open_as("dungeon", &id, Some(&alice)).unwrap());
        }
        assert_eq!(host.session_ids("dungeon").len(), 8);
        // Sweeping at any time evicts nothing.
        assert!(host.sweep(u64::MAX).is_empty());
        assert_eq!(host.session_ids("dungeon").len(), 8);
    }
}
