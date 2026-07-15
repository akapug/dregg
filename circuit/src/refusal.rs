//! **`refusal`** — the shared REFUSAL DISCRIMINATOR for adversarial tests.
//!
//! # Why this module exists
//!
//! The dominant anti-pattern in this tree's adversarial suite was:
//!
//! ```ignore
//! match std::panic::catch_unwind(|| prove(&desc, &forged_rows, ..)) {
//!     Err(_) => {}                              // a panic — "refused"
//!     Ok(res) => assert!(res.is_err(), "tooth OPEN"),
//! }
//! ```
//!
//! **Any** panic and **any** `Err` both count as "the forgery was refused". That tooth cannot
//! distinguish *"the constraint system rejected the forgery"* from *"the process crashed"* — so a
//! stray `.unwrap()` or a producer-side `debug_assert!` in **trace assembly** keeps it green while
//! proving nothing about the constraint system.
//!
//! This is not hypothetical. At the commit that introduced this module,
//! `descriptor_ir2::tests::ir2_forged_map_opening_refuses` reported `ok` because
//! `descriptor_ir2.rs:5195`'s `debug_assert_eq!(end, root, "old path must authenticate against
//! root8")` — a **witness-assembly sanity check**, not a constraint — panicked first. The prover
//! was never asked to refuse anything. The `Err(_) => {}` arm swallowed it.
//!
//! # What a refusal actually looks like
//!
//! There are exactly **two** honest refusal mechanisms on the `prove_vm_descriptor2*` path, and
//! they are reached under different conditions:
//!
//! 1. **A typed `Err`** — the pre-flight in-trace replay (gated on `check: true`, i.e. the public
//!    [`crate::descriptor_ir2::prove_vm_descriptor2`] entry) eagerly refuses a bad witness
//!    fail-closed and returns `Err(String)`. In a release build this is also what the batch
//!    self-verify surfaces. **This is the mechanism to prefer, and [`must_refuse`] requires it.**
//!
//! 2. **The p3 batch prover's DOCUMENTED unsat panic** — the adversarial teeth that call
//!    `prove_vm_descriptor2_inner` DIRECTLY with `check: false` bypass the replay, so the forged
//!    witness reaches `p3_batch_stark::prove_batch`. That function runs two `#[cfg(debug_assertions)]`
//!    checks which **panic** rather than return:
//!
//!    * `batch-stark/src/check_constraints.rs:133` — `panic!("constraints not satisfied on row
//!      {row_index}: failed constraints = {rendered}")`
//!    * `lookup/src/debug_util.rs:82` (via `MultiSet::assert_empty`, called by `check_lookups`) —
//!      `panic!("Lookup mismatch ({label}): tuple {:?} has net multiplicity {:?} ...")`
//!
//!    Under `cargo test` (a debug build) these fire *before* the prover could return anything, so
//!    for a `check: false` site the panic genuinely **is** the refusal. [`must_refuse_or_unsat_panic`]
//!    accepts it — but **only** it, matched by message against [`P3_UNSAT_PANIC_MARKERS`]. Any other
//!    panic (a trace-assembly `debug_assert`, a stray `unwrap`, an index OOB, an OOM) is a **test
//!    failure**, because it is not a refusal — it is a crash wearing a refusal's clothes.
//!
//! Note what is deliberately **not** in the marker list: `check_constraints.rs:54/62`'s
//! `assert_eq!` on trace heights, and `debug_util.rs:243`'s `"only two-row windows are supported"`.
//! Those are **shape/deploy faults**, not unsat verdicts. A tooth that "passes" because the trace
//! was the wrong height has not witnessed a refusal, so those panics red the test.
//!
//! # Placement
//!
//! This is test-support code living in a production crate's `src/`, which deserves a justification:
//!
//! * `dregg-circuit-prove` depends on `dregg-circuit` as a **normal** `[dependencies]` entry, so one
//!   `pub mod` here is reachable from both crates' unit tests (`#[cfg(test)]` in `src/`) **and**
//!   their integration tests (`tests/`, which link the crate as an external rlib and therefore
//!   cannot see a `#[cfg(test)]` module). No other single placement covers all four.
//! * It is deliberately **not** behind a Cargo feature. A feature that arms test-only code is
//!   exactly the `test-stubs` leak this tree already has (CRATE-EXCELLENCE-PLAN §1.3: feature
//!   unification armed `StubVerifier` inside the production node binary). Features unify; `pub mod`
//!   does not.
//! * The soundness surface is nil in the strict sense: this module has no accept path. Every
//!   function here either returns a refusal reason or panics. It can only make a test **stricter**,
//!   never more permissive, so shipping it in a production build arms nothing.

use std::any::Any;
use std::panic::{AssertUnwindSafe, catch_unwind};

/// The p3 batch prover's two DOCUMENTED unsatisfiable-witness panics, verified by reading
/// Plonky3 @ `82cfad73cd734d37a0d51953094f970c531817ec`:
///
/// * `batch-stark/src/check_constraints.rs:133` — an AIR constraint is violated on some row.
/// * `lookup/src/debug_util.rs:82` — a lookup/permutation bus does not balance.
///
/// Both are `#[cfg(debug_assertions)]`-gated inside `prove_batch`, so they are live under
/// `cargo test` and absent under `--release`. A panic matching neither marker is **not** a
/// refusal.
pub const P3_UNSAT_PANIC_MARKERS: [&str; 2] =
    ["constraints not satisfied on row", "Lookup mismatch"];

/// How a call under test refused. Returned by [`must_refuse_or_unsat_panic`] so a caller can
/// match on the reason once `LeafError`/`Ir2VerifyError` land (CRATE-EXCELLENCE-PLAN Move 5) —
/// today the `Err` payload is still a `String` on most boundaries.
#[derive(Debug)]
pub enum Refusal<E> {
    /// The call returned `Err` — the replay/verify refused fail-closed. The preferred shape.
    Err(E),
    /// The p3 debug prover panicked with one of [`P3_UNSAT_PANIC_MARKERS`]. Carries the full
    /// panic message so a caller can assert *which* constraint or bus caught the forgery.
    UnsatPanic(String),
}

impl<E> Refusal<E> {
    /// The refusal rendered as text, for a caller that wants to assert on the reason uniformly
    /// across both mechanisms.
    pub fn reason(&self) -> String
    where
        E: std::fmt::Debug,
    {
        match self {
            Refusal::Err(e) => format!("{e:?}"),
            Refusal::UnsatPanic(m) => m.clone(),
        }
    }
}

/// The full outcome of a call under test, including ACCEPTANCE. Returned by [`classify`].
///
/// Needed by teeth whose real soundness boundary is one layer **down**: under `--release`, a
/// `check: false` prove emits an unverified proof, so "the prover returned `Ok`" is not yet a
/// failure — the CONSUMER's verify is what must reject. Such a tooth must be able to take the
/// accepted proof and go check it, rather than fail on the spot.
#[derive(Debug)]
pub enum Outcome<T, E> {
    /// The call RETURNED `Ok`. **Not** necessarily a hole — see the type docs — but the caller
    /// now owes an assertion against the next boundary down.
    Accepted(T),
    /// Refused fail-closed with a typed/stringly error.
    Err(E),
    /// Refused by the p3 debug prover's DOCUMENTED unsat panic ([`P3_UNSAT_PANIC_MARKERS`]).
    UnsatPanic(String),
}

/// **`classify`** — run `f` and discriminate its outcome three ways, REDDING on any panic that is
/// not the p3 prover's documented unsat verdict.
///
/// This is the primitive [`must_refuse_or_unsat_panic`] is built from. Reach for `classify`
/// directly only when acceptance at this layer is legitimately not a failure (see [`Outcome`]);
/// otherwise prefer the `must_*` wrappers, which cannot forget to assert.
#[track_caller]
pub fn classify<T, E, F>(what: &str, f: F) -> Outcome<T, E>
where
    F: FnOnce() -> Result<T, E>,
{
    match catch_quietly(f) {
        Err(p) => {
            let msg = panic_message(&*p);
            if P3_UNSAT_PANIC_MARKERS.iter().any(|m| msg.contains(m)) {
                Outcome::UnsatPanic(msg)
            } else {
                panic!(
                    "{what}: the call panicked, but NOT with the p3 debug prover's documented \
                     unsat panic — so this is NOT a refusal, it is a crash:\n  {msg}\n\
                     Expected the panic to contain one of {P3_UNSAT_PANIC_MARKERS:?} \
                     (batch-stark/src/check_constraints.rs:133 or lookup/src/debug_util.rs:82). \
                     A trace-assembly debug_assert, a stray unwrap, or a trace-shape assert_eq! \
                     means the prover was never asked to refuse the forgery."
                )
            }
        }
        Ok(Ok(v)) => Outcome::Accepted(v),
        Ok(Err(e)) => Outcome::Err(e),
    }
}

/// Extract a panic payload as text. `panic!("literal")` yields `&'static str`; a formatted
/// `panic!("{x}")` and `assert*!` yield `String`.
fn panic_message(payload: &(dyn Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else if let Some(s) = payload.downcast_ref::<&'static str>() {
        (*s).to_string()
    } else {
        "<non-string panic payload>".to_string()
    }
}

/// Run `f`, silencing the default panic hook for its duration so an *expected* unsat panic does
/// not spray a backtrace across passing test output. The hook is restored before returning.
fn catch_quietly<T>(f: impl FnOnce() -> T) -> Result<T, Box<dyn Any + Send>> {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = catch_unwind(AssertUnwindSafe(f));
    std::panic::set_hook(prev);
    r
}

/// **`must_refuse`** — require that `f` refuses by returning `Err`, and hand back the error so the
/// caller can assert *why*.
///
/// This is the default, and the shape every site should reach for. It is strictly stronger than the
/// idiom it replaces:
///
/// * `f` **panicked** → this test **FAILS**. A panic is not a refusal. This is the whole point: a
///   stray `unwrap` in trace assembly now reds the suite instead of silently satisfying the tooth.
/// * `f` returned `Ok` → this test **FAILS**: the forgery was ACCEPTED, the tooth is OPEN.
/// * `f` returned `Err(e)` → returns `e`.
///
/// `what` names the forgery under test and is quoted in every failure message, so a red says which
/// tooth broke without a backtrace.
///
/// Use [`must_refuse_or_unsat_panic`] **only** for a site that calls `prove_vm_descriptor2_inner`
/// with `check: false`, where the p3 debug prover's panic is genuinely the mechanism.
#[track_caller]
pub fn must_refuse<T, E, F>(what: &str, f: F) -> E
where
    F: FnOnce() -> Result<T, E>,
{
    match catch_quietly(f) {
        Err(p) => panic!(
            "{what}: expected a fail-closed Err refusal, but the call PANICKED: {}\n\
             A panic is NOT a refusal — this tooth cannot tell 'rejected the forgery' from \
             'crashed'. If the p3 debug prover's documented unsat panic is genuinely the \
             mechanism here (a `check: false` prove_vm_descriptor2_inner site), use \
             `must_refuse_or_unsat_panic`. Otherwise this is a real bug in the path under test.",
            panic_message(&*p)
        ),
        Ok(Ok(_)) => panic!("{what}: the forgery was ACCEPTED — this tooth is OPEN."),
        Ok(Err(e)) => e,
    }
}

/// **`must_refuse_or_unsat_panic`** — require that `f` refuses either by returning `Err` **or** by
/// the p3 debug prover's DOCUMENTED unsat panic ([`P3_UNSAT_PANIC_MARKERS`]).
///
/// Reserved for sites that bypass the pre-flight replay (`prove_vm_descriptor2_inner` with
/// `check: false`), where a forged witness reaches `prove_batch` and the debug-gated constraint /
/// lookup check panics before anything can be returned. There, the panic **is** the refusal.
///
/// It is still a discriminator, not a shrug:
///
/// * panic **matching** a marker → `Refusal::UnsatPanic(msg)`.
/// * panic **not** matching → this test **FAILS**. A trace-assembly `debug_assert`, a stray
///   `unwrap`, a height-mismatch `assert_eq!` — none of those are the constraint system refusing.
/// * `Ok(Ok(_))` → this test **FAILS**: forgery accepted, tooth OPEN.
/// * `Ok(Err(e))` → `Refusal::Err(e)`.
#[track_caller]
pub fn must_refuse_or_unsat_panic<T, E, F>(what: &str, f: F) -> Refusal<E>
where
    F: FnOnce() -> Result<T, E>,
{
    match classify(what, f) {
        Outcome::UnsatPanic(m) => Refusal::UnsatPanic(m),
        Outcome::Err(e) => Refusal::Err(e),
        Outcome::Accepted(_) => panic!("{what}: the forgery was ACCEPTED — this tooth is OPEN."),
    }
}

/// **`must_panic_containing`** — require that `f` panics with a SPECIFIC, named message.
///
/// For the narrow case where a panic is genuinely the documented mechanism but it is **not** the
/// p3 prover's unsat verdict — e.g. a producer-side `debug_assert!` in trace assembly that refuses
/// to build a trace for a forged witness. Such a check is a real refusal, but it is a **different
/// tooth** from the in-circuit one, and it is compiled out under `--release`. Naming it forces the
/// distinction to stay visible instead of being laundered by an `Err(_) => {}` arm.
///
/// Any other panic, or no panic at all, is a test failure. Returns the panic message.
#[track_caller]
pub fn must_panic_containing<T, F>(what: &str, expected: &str, f: F) -> String
where
    F: FnOnce() -> T,
{
    match catch_quietly(f) {
        Err(p) => {
            let msg = panic_message(&*p);
            assert!(
                msg.contains(expected),
                "{what}: panicked, but not with the expected message.\n  expected to contain: \
                 {expected}\n  got: {msg}"
            );
            msg
        }
        Ok(_) => panic!("{what}: expected a panic containing {expected:?}, but the call RETURNED."),
    }
}

/// **`must_accept`** — the honest pole. Require that `f` ACCEPTS, so the paired negative is not
/// vacuous.
///
/// CRATE-EXCELLENCE-PLAN §S1 requires every forgery tooth to re-assert the honest pole first:
/// a tooth that rejects the forgery *and also* rejects the honest witness has proved nothing —
/// it might reject everything. Panics carry the underlying error/panic text.
#[track_caller]
pub fn must_accept<T, E: std::fmt::Debug, F>(what: &str, f: F) -> T
where
    F: FnOnce() -> Result<T, E>,
{
    match catch_quietly(f) {
        Err(p) => panic!(
            "{what}: the HONEST witness PANICKED: {}\n\
             The honest pole must be accepted — otherwise the paired forgery test is vacuous \
             (it would 'reject' everything).",
            panic_message(&*p)
        ),
        Ok(Err(e)) => panic!(
            "{what}: the HONEST witness was REJECTED: {e:?}\n\
             The honest pole must be accepted — otherwise the paired forgery test is vacuous \
             (it would 'reject' everything)."
        ),
        Ok(Ok(v)) => v,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn must_refuse_returns_the_error_for_a_fail_closed_reject() {
        let e = must_refuse("probe", || Err::<(), _>("replay refused: forged opening"));
        assert_eq!(e, "replay refused: forged opening");
    }

    #[test]
    #[should_panic(expected = "the forgery was ACCEPTED")]
    fn must_refuse_reds_when_the_forgery_is_accepted() {
        must_refuse("probe", || Ok::<_, String>(()));
    }

    /// THE POINT OF THE WHOLE MODULE: a stray panic in trace assembly used to satisfy the tooth.
    /// It must now RED.
    #[test]
    #[should_panic(expected = "expected a fail-closed Err refusal, but the call PANICKED")]
    fn must_refuse_reds_on_a_stray_trace_assembly_panic() {
        must_refuse("probe", || -> Result<(), String> {
            panic!("old path must authenticate against root8")
        });
    }

    #[test]
    fn unsat_panic_variant_accepts_the_documented_constraint_panic() {
        let r = must_refuse_or_unsat_panic("probe", || -> Result<(), String> {
            panic!("constraints not satisfied on row 3: failed constraints = [..]")
        });
        assert!(matches!(r, Refusal::UnsatPanic(ref m) if m.contains("row 3")));
    }

    #[test]
    fn unsat_panic_variant_accepts_the_documented_lookup_panic() {
        let r = must_refuse_or_unsat_panic("probe", || -> Result<(), String> {
            panic!("Lookup mismatch (global lookup 'ir2_chip'): tuple [..] has net multiplicity 1")
        });
        assert!(matches!(r, Refusal::UnsatPanic(_)));
    }

    /// The discriminator's real teeth: even the panic-tolerant variant must REJECT a panic that is
    /// not the prover's unsat verdict.
    #[test]
    #[should_panic(expected = "NOT with the p3 debug prover's documented unsat panic")]
    fn unsat_panic_variant_reds_on_a_stray_assembly_panic() {
        must_refuse_or_unsat_panic("probe", || -> Result<(), String> {
            panic!("old path must authenticate against root8")
        });
    }

    /// A trace-SHAPE assert is a deploy fault, not an unsat verdict — it must not be laundered
    /// into a refusal.
    #[test]
    #[should_panic(expected = "NOT with the p3 debug prover's documented unsat panic")]
    fn unsat_panic_variant_reds_on_a_trace_shape_assert() {
        must_refuse_or_unsat_panic("probe", || -> Result<(), String> {
            panic!(
                "debug constraint check requires permutation trace height (4) to match main trace height (8)"
            )
        });
    }

    #[test]
    #[should_panic(expected = "a stray unwrap")]
    fn unsat_panic_variant_reds_on_a_stray_unwrap() {
        must_refuse_or_unsat_panic("probe", || -> Result<(), String> {
            None::<()>.expect("a stray unwrap in trace assembly");
            Ok(())
        });
    }

    #[test]
    fn must_accept_passes_the_honest_pole_through() {
        assert_eq!(must_accept("honest", || Ok::<_, String>(7u8)), 7);
    }

    #[test]
    #[should_panic(expected = "the HONEST witness was REJECTED")]
    fn must_accept_reds_when_the_honest_pole_is_rejected() {
        must_accept("honest", || Err::<(), _>("nope".to_string()));
    }
}
