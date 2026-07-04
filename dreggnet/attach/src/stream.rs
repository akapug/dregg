//! The **SSE wire**: the session's reason→act→observe transcript as a
//! `text/event-stream` body the browser consumes with `EventSource`.
//!
//! The page opens `GET /api/session/<id>/stream`; the server writes one frame per
//! step as the transcript replays, so each tool-call, its cap-gate verdict
//! (✓ admitted / ✗ refused), and the running budget draw-down land in the browser
//! live. For a completed (recorded) session the frames replay the *signed*
//! transcript; the genuinely-incremental "stream each step as it runs" is the
//! reviewed-go live backend — the frame SHAPE + the `EventSource` wiring are real.
//!
//! Frames:
//! - `event: meta`  — the goal · model · budget · caps (the session header).
//! - `event: step`  — one [`TranscriptStep`] (the reason→act→observe line).
//! - `event: done`  — the final budget bound + the receipt/refusal tallies.

use serde::Serialize;

use crate::session::AgentSession;
use crate::transcript::{TranscriptStep, transcript_of};

/// The opening `meta` frame payload — the session header.
#[derive(Clone, Debug, Serialize)]
pub struct MetaEvent {
    /// The session id.
    pub id: String,
    /// The natural-language goal.
    pub goal: String,
    /// The model/brain that drove it.
    pub model: String,
    /// The budget ceiling.
    pub budget: i64,
    /// The asset the budget is denominated in.
    pub asset: String,
    /// The granted cap bundle (display form).
    pub caps: Vec<String>,
}

/// The closing `done` frame payload — the final bound + tallies.
#[derive(Clone, Debug, Serialize)]
pub struct DoneEvent {
    /// The budget ceiling.
    pub budget: i64,
    /// Total consumed.
    pub consumed: i64,
    /// Un-drawn headroom (the could-have bound).
    pub headroom: i64,
    /// Admitted (receipted) actions.
    pub admitted: u64,
    /// Cap-refused actions (outside the bundle).
    pub cap_refused: u64,
    /// Budget-refused actions (over the ceiling).
    pub budget_refused: u64,
    /// The sealed receipt count.
    pub receipts: usize,
}

/// Encode one SSE frame: `event: <name>\ndata: <json>\n\n`. `data` is single-line
/// JSON (serde_json emits no newlines), so the frame is one well-formed event.
pub fn sse_frame(event: &str, data_json: &str) -> String {
    format!("event: {event}\ndata: {data_json}\n\n")
}

/// The whole `text/event-stream` body for a session: the `meta` frame, one `step`
/// frame per transcript step, then the `done` frame.
pub fn transcript_stream(session: &AgentSession) -> String {
    let mut out = String::new();

    let meta = MetaEvent {
        id: session.id.clone(),
        goal: session.goal().to_string(),
        model: session.run.model.clone(),
        budget: session.budget(),
        asset: session.run.run.asset.clone(),
        caps: session.caps().to_vec(),
    };
    out.push_str(&sse_frame(
        "meta",
        &serde_json::to_string(&meta).unwrap_or_default(),
    ));

    let steps: Vec<TranscriptStep> = transcript_of(session);
    for s in &steps {
        out.push_str(&sse_frame(
            "step",
            &serde_json::to_string(s).unwrap_or_default(),
        ));
    }

    let done = DoneEvent {
        budget: session.budget(),
        consumed: session.consumed(),
        headroom: session.headroom(),
        admitted: session.run.run.admitted,
        cap_refused: session.cap_refused(),
        budget_refused: session.budget_refused(),
        receipts: session.receipts(),
    };
    out.push_str(&sse_frame(
        "done",
        &serde_json::to_string(&done).unwrap_or_default(),
    ));

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::{DemoDriver, SessionDriver};
    use crate::session::GoalRequest;

    fn driven() -> AgentSession {
        let req = GoalRequest::new("run the tests and verify the deploy", 50)
            .with_service("run_tests")
            .with_service("verify_deploy")
            .with_cell("/goal");
        DemoDriver::seeded([8u8; 32]).drive(&req, "dregg:demo0001demo0001", "sess_s")
    }

    // ── the stream is well-formed: meta … steps … done ─────────────────────────
    #[test]
    fn the_stream_is_well_formed() {
        let session = driven();
        let body = transcript_stream(&session);
        assert!(body.contains("event: meta\ndata: "));
        assert!(body.contains("event: done\ndata: "));
        // One step frame per transcript step.
        let step_frames = body.matches("event: step\ndata: ").count();
        assert_eq!(step_frames, transcript_of(&session).len());
        // Every frame ends with the blank-line terminator.
        for frame in body.split("\n\n").filter(|f| !f.trim().is_empty()) {
            assert!(frame.starts_with("event: "));
            assert!(frame.contains("\ndata: "));
        }
    }

    // ── the meta + done payloads carry the real session facts ──────────────────
    #[test]
    fn the_frames_carry_the_real_facts() {
        let session = driven();
        let body = transcript_stream(&session);
        // The goal + a granted cap appear in the meta frame.
        assert!(body.contains("run the tests and verify the deploy"));
        assert!(body.contains("invoke:run_tests"));
        // The done frame's consumed+headroom is the bound.
        let done_line = body
            .lines()
            .skip_while(|l| *l != "event: done")
            .nth(1)
            .expect("a done data line");
        let data = done_line.strip_prefix("data: ").unwrap();
        let v: serde_json::Value = serde_json::from_str(data).unwrap();
        assert_eq!(
            v["consumed"].as_i64().unwrap() + v["headroom"].as_i64().unwrap(),
            v["budget"].as_i64().unwrap()
        );
        assert!(v["cap_refused"].as_u64().unwrap() >= 1, "the ✗ teeth tally");
    }
}
