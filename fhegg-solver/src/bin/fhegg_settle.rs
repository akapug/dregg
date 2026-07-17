//! # `fhegg_settle` — the versioned wire settle as a thin JSON CLI
//!
//! ```text
//! echo '<WireBook-json>'                    | fhegg_settle          # settle
//! echo '{"book":…,"settlement":…}'          | fhegg_settle verify   # check
//! ```
//!
//! The CLI twin of `fhegg_solver::wire` (and of the SDK surface
//! `dregg_sdk::fhegg`). Two modes, both strict:
//!
//! * **settle** (no args): read a [`WireBook`] on stdin (versioned; exact
//!   on-grid integer prices; unknown fields refused), run [`wire::settle`]
//!   (validate → lower → fold + crossing + conserving allocation → invariant
//!   gate), then RE-VERIFY the just-produced settlement from scratch via
//!   [`Settlement::verify`] before emitting it — settle and verify are BOTH
//!   exercised on every run, so the emitted JSON never skips the self-check.
//!   Output: the [`Settlement`] JSON on stdout. Exit 0 iff settled + verified.
//! * **verify** (`fhegg_settle verify`): read `{"book": <WireBook>,
//!   "settlement": <Settlement>}` on stdin and run the untrusted-solver check a
//!   consumer gates on: [`Settlement::verify`] re-derives everything and
//!   refuses ANY deviation. Output: `{"ok":true}` on stdout and exit 0, or the
//!   named divergence on stderr and exit 1.
//!
//! Honest scope (same as the wire module): PLAINTEXT, demo-scale, no FHE, no
//! privacy. The verify mode's authority is re-derivation by the same
//! deterministic rule — it catches a tampered/buggy PRODUCER, not a bug in the
//! rule itself. The STARK-verified clearing path (Cert-F) is
//! `circuit-prove/src/cert_f_air.rs`, not this binary.

use std::io::Read;

use fhegg_solver::wire::{self, Settlement, WireBook};

use serde::Deserialize;

/// stdin payload for `fhegg_settle verify`.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct VerifyIn {
    book: WireBook,
    settlement: Settlement,
}

fn read_stdin() -> String {
    let mut buf = String::new();
    if std::io::stdin().read_to_string(&mut buf).is_err() {
        eprintln!("fhegg_settle: failed to read stdin");
        std::process::exit(2);
    }
    buf
}

fn main() {
    let mode = std::env::args().nth(1);
    match mode.as_deref() {
        None => {
            // settle: book in → settle → self-verify → settlement out.
            let buf = read_stdin();
            let book = match WireBook::from_json(&buf) {
                Ok(b) => b,
                Err(e) => {
                    eprintln!("fhegg_settle: refused book: {e}");
                    std::process::exit(1);
                }
            };
            let settlement = match wire::settle(&book) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("fhegg_settle: refused: {e}");
                    std::process::exit(1);
                }
            };
            // The self-check: the emitted settlement must survive the same
            // verify a consumer would run. Never skipped.
            if let Err(e) = settlement.verify(&book) {
                eprintln!("fhegg_settle: internal: emitted settlement failed self-verify: {e}");
                std::process::exit(1);
            }
            println!("{}", settlement.to_json());
        }
        Some("verify") => {
            // verify: {book, settlement} in → accept/refuse with named field.
            let buf = read_stdin();
            let v: VerifyIn = match serde_json::from_str(&buf) {
                Ok(v) => v,
                Err(e) => {
                    eprintln!("fhegg_settle verify: bad input JSON: {e}");
                    std::process::exit(2);
                }
            };
            match v.settlement.verify(&v.book) {
                Ok(()) => println!("{{\"ok\":true}}"),
                Err(e) => {
                    eprintln!("fhegg_settle verify: REFUSED: {e}");
                    std::process::exit(1);
                }
            }
        }
        Some(other) => {
            eprintln!(
                "fhegg_settle: unknown mode '{other}' (usage: fhegg_settle [verify] < input.json)"
            );
            std::process::exit(2);
        }
    }
}
