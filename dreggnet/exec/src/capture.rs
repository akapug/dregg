//! **The exec → logs capture wire.** Where a workload's output is produced (the
//! compute-tier run, [`crate::run_workload`]), this module writes the real result
//! lines into a [`dreggnet_logs::LogSink`], keyed by the resource id + the owner
//! subject. That is what makes `dregg-cloud logs <resource>` show a tenant their
//! app's actual output instead of cached step metadata
//! (`docs/CLOUD-PROVIDER-READINESS.md`, the LOG blocker).
//!
//! ## What gets captured at this rung
//!
//! polyana's provider wire owns the child process's raw stdout fd (it speaks the
//! newline-JSON protocol over it), so the **tenant-visible output** of a run is
//! the entrypoint's returned values ([`crate::Output::values`]) — the program's
//! real result lines — and any failure is the [`crate::ExecError`] message. We
//! capture values as `stdout` records and an error as a `stderr` record. This is
//! honest: these are the workload's genuine output, not metadata.
//!
//! The deeper raw-stdout interleave (a `print()` mid-run, distinct from the
//! returned value) rides the polyana guest wire and is a **named seam** for the
//! integration pass — it lands the moment the provider surfaces a side-channel
//! line stream. The deploy/build path (`dregg-deploy`) already has true child
//! stdout/stderr (`git clone`, the build command) and is the richest near-term
//! capture site — also a named seam owned by that lane.
//!
//! ## Cap-scoping
//!
//! Capture records the `owner` (the lease's lessee — the `dga1_` cap-account
//! subject). The sink fixes one owner per resource, and every read is cap-scoped
//! to that owner ([`dreggnet_logs::LogSink::tail`] et al.), so a tenant sees only
//! their own logs.

use dreggnet_logs::{LogError, LogLine, LogSink, Stream};

use crate::Output;

/// Capture a finished run's [`Output`] into `sink` under `resource_id` / `owner`.
///
/// Each returned value becomes a `stdout` line. Returns the stored records (in
/// order) so a caller can surface what was captured. A capture failure is an
/// I/O/scope error from the sink, not a run failure — the run already happened.
pub fn capture_output(
    sink: &LogSink,
    resource_id: &str,
    owner: &str,
    out: &Output,
) -> Result<Vec<LogLine>, LogError> {
    let mut stored = Vec::with_capacity(out.values.len());
    for v in &out.values {
        stored.push(sink.append(resource_id, owner, Stream::Stdout, v)?);
    }
    Ok(stored)
}

/// Capture a run failure into `sink` as a single `stderr` line.
pub fn capture_error(
    sink: &LogSink,
    resource_id: &str,
    owner: &str,
    message: &str,
) -> Result<LogLine, LogError> {
    sink.append(resource_id, owner, Stream::Stderr, message)
}

/// Capture an arbitrary already-produced output line (stdout or stderr) — the
/// general wire the deploy/server/agent capture seams call with their own child
/// process lines once they are wired.
pub fn capture_line(
    sink: &LogSink,
    resource_id: &str,
    owner: &str,
    stream: Stream,
    line: &str,
) -> Result<LogLine, LogError> {
    sink.append(resource_id, owner, stream, line)
}

/// Run a workload through the compute tier AND capture its output into `sink`,
/// keyed by `resource_id` / `owner`. The one-call capture wire for the run path:
/// the result lines (or the error) land in the tenant log as a side effect, and
/// the run's [`Output`]/[`crate::ExecError`] is returned unchanged.
#[cfg(feature = "polyana")]
pub fn run_workload_captured(
    lang: &str,
    source: &str,
    cap_tier: crate::CapTier,
    resource_id: &str,
    owner: &str,
    sink: &LogSink,
) -> Result<Output, crate::ExecError> {
    match crate::run_workload_with_input(lang, source, cap_tier, &[]) {
        Ok(out) => {
            // A capture I/O error must not mask a successful run; surface it as a
            // best-effort stderr note and return the real output.
            let _ = capture_output(sink, resource_id, owner, &out);
            Ok(out)
        }
        Err(e) => {
            let _ = capture_error(sink, resource_id, owner, &e.to_string());
            Err(e)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE: &str = "dregg:aaaa0000aaaa0000";
    const BOB: &str = "dregg:bbbb1111bbbb1111";

    fn sink() -> (tempfile::TempDir, LogSink) {
        let dir = tempfile::tempdir().unwrap();
        let sink = LogSink::open(dir.path()).unwrap();
        (dir, sink)
    }

    #[test]
    fn capture_output_records_each_value_as_a_stdout_line() {
        let (_d, sink) = sink();
        let out = Output {
            values: vec!["42".into(), "hello".into()],
            enforcement: "WasmSandbox".into(),
        };
        let stored = capture_output(&sink, "wl_x", ALICE, &out).unwrap();
        assert_eq!(stored.len(), 2);

        let tailed = sink.tail("wl_x", 0, ALICE).unwrap();
        assert_eq!(
            tailed.iter().map(|l| l.line.as_str()).collect::<Vec<_>>(),
            vec!["42", "hello"]
        );
        assert!(tailed.iter().all(|l| l.stream == Stream::Stdout));
    }

    #[test]
    fn capture_error_records_a_stderr_line() {
        let (_d, sink) = sink();
        capture_error(&sink, "wl_y", ALICE, "workload call failed: boom").unwrap();
        let tailed = sink.tail("wl_y", 0, ALICE).unwrap();
        assert_eq!(tailed.len(), 1);
        assert_eq!(tailed[0].stream, Stream::Stderr);
        assert!(tailed[0].line.contains("boom"));
    }

    #[test]
    fn captured_output_is_cap_scoped_to_the_owner() {
        let (_d, sink) = sink();
        let out = Output {
            values: vec!["secret".into()],
            enforcement: "None".into(),
        };
        capture_output(&sink, "wl_z", ALICE, &out).unwrap();
        // Another tenant cannot read it.
        assert!(sink.tail("wl_z", 0, BOB).is_err());
        assert_eq!(sink.tail("wl_z", 0, ALICE).unwrap().len(), 1);
    }

    // The real compute tier → capture round trip (default-on `polyana` feature):
    // a wat workload returns a value, and that value lands in the tenant log.
    #[cfg(feature = "polyana")]
    #[test]
    fn run_workload_captured_lands_the_real_output() {
        // A core-module wat that exports `run` returning the constant 7.
        let source = r#"(module (func (export "run") (result i32) i32.const 7))"#;
        let (_d, sink) = sink();
        let out = run_workload_captured(
            "wat",
            source,
            crate::CapTier::Sandboxed,
            "wl_run",
            ALICE,
            &sink,
        )
        .expect("the wat workload runs");
        assert!(!out.values.is_empty());

        let tailed = sink.tail("wl_run", 0, ALICE).unwrap();
        assert_eq!(tailed.len(), out.values.len());
        assert_eq!(tailed[0].line, out.values[0]);
        assert_eq!(tailed[0].stream, Stream::Stdout);
    }
}
