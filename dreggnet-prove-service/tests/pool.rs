//! FAST: the bounded worker-pool mechanics — driven with a controllable stub
//! backend (no fold), so the pool's guarantees (bounded concurrency, non-blocking
//! enqueue, a depth cap that DROPS rather than blocks, status transitions,
//! metrics) are gated in the normal suite. The real minutes-to-hours fold is the
//! `--ignored` lane in `match_fold.rs`.

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use dreggnet_prove_service::{JobId, JobStatus, ProveService};

/// A backend the test can hold inside and release on command — so we can observe
/// jobs mid-fold (Proving, in_flight) deterministically.
struct Gate {
    started: AtomicUsize,
    open: std::sync::Mutex<bool>,
    cv: std::sync::Condvar,
}

impl Gate {
    fn new() -> Arc<Gate> {
        Arc::new(Gate {
            started: AtomicUsize::new(0),
            open: std::sync::Mutex::new(false),
            cv: std::sync::Condvar::new(),
        })
    }
    fn release(&self) {
        *self.open.lock().unwrap() = true;
        self.cv.notify_all();
    }
    fn wait_started(&self, n: usize) {
        let deadline = Instant::now() + Duration::from_secs(5);
        while self.started.load(Ordering::SeqCst) < n {
            assert!(
                Instant::now() < deadline,
                "workers never reached {n} started"
            );
            std::thread::sleep(Duration::from_millis(2));
        }
    }
}

/// Backend that blocks in the fold until the gate opens, then doubles the input.
fn gated_backend(gate: Arc<Gate>) -> dreggnet_prove_service::Backend<u64, u64> {
    Arc::new(move |x: u64| {
        gate.started.fetch_add(1, Ordering::SeqCst);
        let mut open = gate.open.lock().unwrap();
        while !*open {
            open = gate.cv.wait(open).unwrap();
        }
        Ok(x * 2)
    })
}

#[test]
fn enqueue_returns_a_jobid_immediately_and_wait_delivers_the_output() {
    let svc = ProveService::<u64, u64>::spawn_with(Arc::new(|x: u64| Ok(x + 1)), 2, 8);
    let id = svc.enqueue(41).expect("accepted");
    assert_eq!(svc.wait(id), Ok(42));
    assert_eq!(svc.metrics().completed, 1);
    assert_eq!(svc.metrics().enqueued, 1);
}

#[test]
fn n_workers_fold_concurrently_and_enqueue_never_blocks_while_busy() {
    let gate = Gate::new();
    let svc = ProveService::<u64, u64>::spawn_with(gated_backend(gate.clone()), 3, 16);

    // Fill all three workers.
    let ids: Vec<JobId> = (0..3).map(|i| svc.enqueue(i).expect("accepted")).collect();
    gate.wait_started(3); // all three are folding AT ONCE => real N-way concurrency

    let m = svc.metrics();
    assert_eq!(m.in_flight, 3, "three folds run in parallel");
    for id in &ids {
        assert!(
            matches!(svc.status(*id), JobStatus::Proving),
            "a busy worker's job reads Proving"
        );
    }

    // A further enqueue must return IMMEDIATELY (the play path is never blocked),
    // even with every worker busy — the job just queues.
    let t0 = Instant::now();
    let extra = svc.enqueue(100).expect("queued while workers busy");
    assert!(
        t0.elapsed() < Duration::from_millis(200),
        "enqueue blocked for {:?} — it must be off the caller's path",
        t0.elapsed()
    );
    assert!(matches!(
        svc.status(extra),
        JobStatus::Queued | JobStatus::Proving
    ));

    gate.release();
    for id in ids {
        assert_eq!(svc.wait(id).map(|v| v % 2), Ok(0));
    }
    assert_eq!(svc.wait(extra), Ok(200));
    assert_eq!(svc.metrics().completed, 4);
    assert_eq!(svc.metrics().in_flight, 0);
}

#[test]
fn a_full_queue_drops_rather_than_blocks() {
    let gate = Gate::new();
    // 1 worker, depth 2 => 1 in-fold + 2 buffered = capacity 3, the 4th drops.
    let svc = ProveService::<u64, u64>::spawn_with(gated_backend(gate.clone()), 1, 2);

    let j1 = svc.enqueue(1).expect("accepted");
    gate.wait_started(1); // the sole worker is now blocked in the fold (buffer empty)

    let j2 = svc.enqueue(2).expect("buffered");
    let j3 = svc.enqueue(3).expect("buffered"); // buffer now full (depth 2)

    let t0 = Instant::now();
    let dropped = svc.enqueue(4);
    assert!(
        dropped.is_none(),
        "the 4th job is DROPPED on the full queue"
    );
    assert!(
        t0.elapsed() < Duration::from_millis(200),
        "a full-queue enqueue must return fast (drop, not block): {:?}",
        t0.elapsed()
    );
    assert_eq!(svc.metrics().dropped, 1);

    gate.release();
    assert_eq!(svc.wait(j1), Ok(2));
    assert_eq!(svc.wait(j2), Ok(4));
    assert_eq!(svc.wait(j3), Ok(6));
    let m = svc.metrics();
    assert_eq!(m.completed, 3);
    assert_eq!(m.dropped, 1);
    assert_eq!(m.enqueued, 3, "only the accepted jobs count as enqueued");
}

#[test]
fn a_failing_fold_settles_failed_and_counts() {
    let svc = ProveService::<u64, u64>::spawn_with(
        Arc::new(|x: u64| {
            if x == 0 {
                Err("refused: forged match".into())
            } else {
                Ok(x)
            }
        }),
        2,
        8,
    );
    let bad = svc.enqueue(0).expect("accepted");
    let good = svc.enqueue(7).expect("accepted");
    assert_eq!(svc.wait(bad), Err("refused: forged match".into()));
    assert_eq!(svc.wait(good), Ok(7));
    assert!(matches!(svc.status(bad), JobStatus::Failed(_)));
    let m = svc.metrics();
    assert_eq!(m.failed, 1);
    assert_eq!(m.completed, 1);
}

#[test]
fn an_unknown_jobid_reads_unknown() {
    let svc = ProveService::<u64, u64>::spawn_with(Arc::new(|x: u64| Ok(x)), 1, 4);
    assert!(matches!(svc.status(JobId(999_999)), JobStatus::Unknown));
    assert_eq!(svc.wait(JobId(999_999)), Err("unknown job 999999".into()));
}

#[test]
fn env_knobs_default_when_unset() {
    // spawn() reads DREGG_MATCH_PROVE_WORKERS / _QUEUE_DEPTH; with them unset the
    // documented defaults apply.
    let svc = ProveService::<u64, u64>::spawn(Arc::new(|x: u64| Ok(x)));
    assert_eq!(svc.workers(), dreggnet_prove_service::DEFAULT_WORKERS);
    assert_eq!(
        svc.queue_depth(),
        dreggnet_prove_service::DEFAULT_QUEUE_DEPTH
    );
    let id = svc.enqueue(5).expect("accepted");
    assert_eq!(svc.wait(id), Ok(5));
}
