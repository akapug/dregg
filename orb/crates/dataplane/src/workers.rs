//! The multi-worker supervisor (`--workers N`).
//!
//! The proven serve is a process-global singleton: one Lean runtime, one serve
//! thread per process (see `serve`). Many IO shards feed that one thread, so a
//! single process's request throughput is capped by one core's worth of serve
//! latency. The share-nothing way past that ceiling is more *processes*: N
//! independent copies of this binary, each with its own runtime and serve thread,
//! all bound to the one port with `SO_REUSEPORT`. The kernel then load-balances
//! incoming connections across them — on Linux and the BSDs it hash-distributes
//! across every `SO_REUSEPORT` socket, including across processes, so throughput
//! scales ~Nx. (Darwin only *permits* the duplicate bind; it does not
//! cross-distribute, so there the operator needs a front load balancer.)
//!
//! This is a pure shell change with zero proof impact: every worker runs the same
//! `drorb_serve`, byte-for-byte, exactly as the single-process path does. The
//! parent never boots a runtime — it only spawns, supervises, and tears down the
//! workers. `--workers 1` (the default) skips this module entirely.

use std::process::{Child, Command};
use std::sync::atomic::Ordering;
use std::time::Duration;

/// POSIX `SIGTERM`; the supervisor treats it the same as `SIGINT`.
const SIGTERM: i32 = 15;

/// The parent argv to hand each worker: the original arguments with the
/// `--workers`/`-w` flag (and its count) removed, so a worker re-enters `main`
/// on the ordinary single-process path.
fn worker_args() -> Vec<String> {
    let mut out = Vec::new();
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--workers" | "-w" => {
                let _ = it.next(); // drop the count argument too
            }
            _ => out.push(a),
        }
    }
    out
}

/// Become the multi-worker supervisor: spawn `n` worker processes sharing the
/// one `SO_REUSEPORT` port, then supervise them until a shutdown signal. Reaps
/// and respawns a worker that dies. Never returns — it `exit`s the process on
/// shutdown.
pub fn supervise(n: usize) {
    // A shutdown signal (SIGINT or SIGTERM) sets the shared flag; the loop below
    // observes it and tears the workers down.
    // SAFETY: `on_sigint` only stores into an atomic — async-signal-safe.
    unsafe {
        crate::signal(crate::SIGINT, crate::on_sigint as *const () as usize);
        crate::signal(SIGTERM, crate::on_sigint as *const () as usize);
    }

    let exe = std::env::current_exe().unwrap_or_else(|e| {
        eprintln!("dataplane: --workers cannot find own executable: {e}");
        std::process::exit(1);
    });
    let child_args = worker_args();
    let spawn_one = || -> std::io::Result<Child> {
        Command::new(&exe)
            .args(&child_args)
            // Mark the child so it runs the single-process serve path, not the
            // supervisor, however DRORB_WORKERS/--workers was passed through.
            .env("DRORB_WORKER", "1")
            .spawn()
    };

    let mut children: Vec<Child> = Vec::with_capacity(n);
    for i in 0..n {
        match spawn_one() {
            Ok(c) => children.push(c),
            Err(e) => eprintln!("dataplane: worker {i} spawn failed: {e}"),
        }
    }
    if children.is_empty() {
        eprintln!("dataplane: --workers spawned no workers; nothing to serve");
        std::process::exit(1);
    }
    eprintln!(
        "dataplane: supervising {} workers behind the shared SO_REUSEPORT port \
         (each its own proven runtime; SIGINT to stop)",
        children.len()
    );

    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            for c in children.iter_mut() {
                let _ = c.kill();
            }
            for c in children.iter_mut() {
                let _ = c.wait();
            }
            eprintln!("dataplane: all workers stopped");
            std::process::exit(0);
        }
        // Reap and respawn any worker that exited on its own (a crash, not a
        // supervised shutdown). The loop's sleep bounds respawn attempts.
        for slot in children.iter_mut() {
            match slot.try_wait() {
                Ok(Some(status)) => {
                    if crate::SHUTDOWN.load(Ordering::SeqCst) {
                        continue;
                    }
                    eprintln!("dataplane: a worker exited ({status}); respawning");
                    match spawn_one() {
                        Ok(c) => *slot = c,
                        Err(e) => eprintln!("dataplane: worker respawn failed: {e}"),
                    }
                }
                Ok(None) => {}
                Err(e) => eprintln!("dataplane: worker wait error: {e}"),
            }
        }
        std::thread::sleep(Duration::from_millis(200));
    }
}
