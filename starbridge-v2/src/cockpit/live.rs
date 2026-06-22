//! The LIVE NODE pump: draining the remote SSE receipt stream off gpui's async executor.

use super::*;

impl Cockpit {
    /// Drain the LIVE NODE's SSE receipt stream into the feed (called once per
    /// render). Each streamed receipt is ingested into `live_feed` (deduped by
    /// chain index); if any were NEW, we `cx.notify()` so the cockpit re-renders
    /// promptly — that is the per-receipt live update REPLACING the static
    /// snapshot. When a receipt stream is connected we ALSO schedule a follow-up
    /// frame (a short deferral) so a continuously-streaming node keeps the loop
    /// turning even between input events. No-op when no node is connected.
    pub(crate) fn drain_live_stream(&mut self, cx: &mut Context<Self>) {
        let Some(stream) = &self.live_stream else {
            return;
        };
        let records = stream.drain();
        if records.is_empty() {
            return;
        }
        let new = self.live_feed.ingest_records(records);
        if new > 0 {
            // The ReceiptInspector advances live — notify to re-render.
            cx.notify();
        }
    }

    /// Whether a LIVE NODE receipt stream is connected (so the post-paint pump in
    /// `main::run_window` should keep turning). `false` for the pure embedded image
    /// (no `--node`), which stops the pump immediately.
    pub fn has_live_stream(&self) -> bool {
        self.live_stream.is_some()
    }

    /// **The LIVE PUMP tick — drain the node's SSE stream off gpui's async
    /// executor.**
    ///
    /// `drain_live_stream` runs at the top of `render`, but gpui only re-renders on
    /// `cx.notify()` or input — so a receipt a remote node streams while the UI is
    /// idle would sit unconsumed in the reader's channel until the next input. This
    /// is the fix the recovered design calls for ("move the cockpit reads onto
    /// gpui's async executor"): a foreground task in `run_window` calls this on a
    /// short timer, so a connected node's receipts are drained — and the
    /// ReceiptInspector / live organ panels advance LIVE — with no user input. Each
    /// freshly-arrived receipt fires `cx.notify()` (inside `drain_live_stream`), so
    /// the next paint reflects it. Returns whether the pump should keep running (a
    /// stream is still connected). No-op (returns `false`) for the embedded-only image.
    pub fn pump_live(&mut self, cx: &mut Context<Self>) -> bool {
        if self.live_stream.is_none() {
            return false;
        }
        self.drain_live_stream(cx);
        true
    }
}
