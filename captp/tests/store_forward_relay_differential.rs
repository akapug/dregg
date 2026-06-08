//! CapTP STORE-AND-FORWARD MESSAGE-RELAY ACCOUNTING ⟷ LEAN DIFFERENTIAL.
//!
//! `Dregg2/Exec/CapTPStoreForward.lean`'s §5-§8 proved the relay SECURITY shape (delay-permutes,
//! drop-shrinks, no-read, no-forge) over a flat `List Box`. But the object the captp crate SHIPS
//! and runs — `store_forward.rs::MessageRelay` — is a DoS-bounded ACCOUNTING machine:
//! per-destination FIFO `VecDeque`s, a `total_messages` counter, and `enqueue` REJECTIONS
//! (`InvalidTtl` on ttl=0, `StorageFull` at total cap, `QueueFull` at per-destination depth cap).
//! That accounting state machine was the dark-mirror gap. The new
//! `Dregg2/Exec/CapTPStoreForward.lean::Mr` section closes it with a faithful, total mirror
//! (`enqueue`/`drain`/`expire`) and proves, by `decide`:
//!
//!   * `relayDifferentialCorpus_observable` — the per-step `(field1, total_stored, field3)`
//!     observable column for a `mk depth=2 total=3` relay over enqueue (FIFO + 3 rejection
//!     arms) → drain (FIFO + total decrement) → expire (TTL drop + total decrement). `field1`
//!     is the ok-bit for enqueue / the count for drain+expire; `field3` is `pending_count` for
//!     enqueue+drain / `active_destinations` for expire.
//!   * `relayDifferentialCorpus_drain_fifo` — drain returns messages OLDEST-FIRST `[10, 11]`.
//!
//! This test drives the REAL `MessageRelay` over the IDENTICAL program and asserts the SAME
//! observables. A drift on EITHER side fails:
//!   * change the Rust accounting (drop a cap check, mis-decrement total, drain LIFO, forget to
//!     remove an empty queue) → the runtime triples diverge from the Lean-proved column → FAIL;
//!   * change the Lean model → its `decide` trips at Lean build AND the rows here no longer
//!     match → re-exposing the Rust drift.

use dregg_captp::store_forward::{MessageRelay, MessagePriority, QueuedMessage, RelayError};
use dregg_captp::FederationId;

fn dest(n: u8) -> FederationId {
    FederationId([n; 32])
}

/// A queued message labelled `label` (we don't read the label back here — the FIFO order test
/// below reads `causal_sequence`), queued at `queued_at` with `ttl_blocks`.
fn qmsg(d: FederationId, label: u64, queued_at: u64, ttl: u64) -> QueuedMessage {
    QueuedMessage {
        destination: d,
        encrypted_payload: vec![],
        sender_ephemeral_pk: [0u8; 32],
        causal_sequence: label,
        queued_at,
        ttl_blocks: ttl,
        priority: MessagePriority::Normal,
    }
}

/// THE ACCOUNTING TOOTH: replay `relayDifferentialCorpus` against the REAL relay and assert the
/// `(field1, total_stored, field3)` triple at each step equals the Lean-proved column.
#[test]
fn relay_accounting_matches_lean_corpus() {
    // Lean `mk 2 3`: max_queue_depth = 2, max_total_messages = 3.
    let mut relay = MessageRelay::new(2, 3);
    let d0 = dest(0);
    let d1 = dest(1);

    // The Lean-proved observable column (`relayDifferentialCorpus_observable`).
    let expected: Vec<(u64, u64, u64)> = vec![
        (1, 1, 1), // enq d0 ttl5: ok, total 1, pending(d0) 1
        (1, 2, 2), // enq d0 ttl5: ok, total 2, pending(d0) 2 (FIFO)
        (0, 2, 2), // enq d0 ttl5: REJECT depth cap, total 2, pending(d0) 2
        (1, 3, 1), // enq d1 ttl3: ok, total 3, pending(d1) 1
        (0, 3, 1), // enq d1 ttl3: REJECT total cap, total 3, pending(d1) 1
        (0, 3, 2), // enq d0 ttl0: REJECT InvalidTtl, total 3, pending(d0) still 2
        (2, 1, 0), // drain d0: 2 msgs, total 1, pending(d0) 0
        (1, 0, 0), // expire @100: d1 (qa 0, ttl 3) drops; expired 1, total 0, active 0
    ];
    let mut got: Vec<(u64, u64, u64)> = Vec::new();

    // .enq d0 label10 qa0 ttl5  → ok
    let ok = relay.enqueue(qmsg(d0, 10, 0, 5)).is_ok();
    got.push((ok as u64, relay.total_stored() as u64, relay.pending_count(&d0) as u64));

    // .enq d0 label11 qa0 ttl5  → ok
    let ok = relay.enqueue(qmsg(d0, 11, 0, 5)).is_ok();
    got.push((ok as u64, relay.total_stored() as u64, relay.pending_count(&d0) as u64));

    // .enq d0 label12 qa0 ttl5  → REJECT (QueueFull, depth 2)
    let verdict = relay.enqueue(qmsg(d0, 12, 0, 5));
    assert!(matches!(verdict, Err(RelayError::QueueFull { .. })), "depth cap reject");
    got.push((verdict.is_ok() as u64, relay.total_stored() as u64, relay.pending_count(&d0) as u64));

    // .enq d1 label20 qa0 ttl3  → ok (total now 3 = cap)
    let ok = relay.enqueue(qmsg(d1, 20, 0, 3)).is_ok();
    got.push((ok as u64, relay.total_stored() as u64, relay.pending_count(&d1) as u64));

    // .enq d1 label21 qa0 ttl3  → REJECT (StorageFull, total cap 3)
    let verdict = relay.enqueue(qmsg(d1, 21, 0, 3));
    assert!(matches!(verdict, Err(RelayError::StorageFull { .. })), "total cap reject");
    got.push((verdict.is_ok() as u64, relay.total_stored() as u64, relay.pending_count(&d1) as u64));

    // .enq d0 label13 qa0 ttl0  → REJECT (InvalidTtl)
    let verdict = relay.enqueue(qmsg(d0, 13, 0, 0));
    assert!(matches!(verdict, Err(RelayError::InvalidTtl)), "ttl=0 reject");
    got.push((verdict.is_ok() as u64, relay.total_stored() as u64, relay.pending_count(&d0) as u64));

    // .drn d0  → 2 msgs (FIFO), total 1
    let drained = relay.drain(&d0);
    let labels: Vec<u64> = drained.iter().map(|m| m.causal_sequence).collect();
    assert_eq!(labels, vec![10, 11], "drain is FIFO oldest-first");
    got.push((drained.len() as u64, relay.total_stored() as u64, relay.pending_count(&d0) as u64));

    // .exp 100  → d1 msg (qa 0, ttl 3 ⇒ 100-0 ≥ 3) expires; total 0, active destinations 0
    let expired = relay.expire(100);
    got.push((expired as u64, relay.total_stored() as u64, relay.active_destinations() as u64));

    assert_eq!(
        got, expected,
        "REAL MessageRelay accounting drifted from the Lean-proved \
         `relayDifferentialCorpus_observable`"
    );
}

/// FIFO-drain + clear tooth in isolation — Lean `drain_clears`.
#[test]
fn drain_is_fifo_and_clears() {
    let mut relay = MessageRelay::new(8, 8);
    let d = dest(7);
    relay.enqueue(qmsg(d, 1, 0, 9)).unwrap();
    relay.enqueue(qmsg(d, 2, 0, 9)).unwrap();
    relay.enqueue(qmsg(d, 3, 0, 9)).unwrap();

    let drained = relay.drain(&d);
    let labels: Vec<u64> = drained.iter().map(|m| m.causal_sequence).collect();
    assert_eq!(labels, vec![1, 2, 3], "FIFO insertion order");
    assert_eq!(relay.pending_count(&d), 0, "drain clears the queue");
    assert_eq!(relay.total_stored(), 0, "total decremented by drained count");

    // a re-drain delivers nothing.
    assert!(relay.drain(&d).is_empty());
}

/// Expire-by-TTL tooth — Lean `expire`/`expired_box_gone` + the total accounting.
#[test]
fn expire_drops_stale_and_keeps_fresh() {
    let mut relay = MessageRelay::new(8, 8);
    let d = dest(5);
    relay.enqueue(qmsg(d, 1, 0, 3)).unwrap();   // expires at height 3
    relay.enqueue(qmsg(d, 2, 0, 100)).unwrap(); // long-lived

    // at height 50: msg 1 (0+3 ≤ 50) drops; msg 2 survives.
    let expired = relay.expire(50);
    assert_eq!(expired, 1, "exactly the stale message expired");
    assert_eq!(relay.total_stored(), 1, "total decremented by expired count");
    let survivors: Vec<u64> = relay.drain(&d).iter().map(|m| m.causal_sequence).collect();
    assert_eq!(survivors, vec![2], "only the fresh message survives");
}
