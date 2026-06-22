//! [`ChatSource`] — the synchronous data seam the deos-chat UI renders against.
//!
//! The gpui UI never touches `matrix-sdk` or tokio directly. It pulls rooms,
//! timelines, and the local user id from a [`ChatSource`], and it sends messages
//! back through the same trait. Two implementors exist:
//!
//!   * [`crate::worker::MatrixHandle`] — the real client (login/sync/timeline over
//!     `matrix-rust-sdk`, on its own tokio runtime). The blocking facade already
//!     matches this shape exactly.
//!   * [`MockSource`] — a recorded/synthetic sync. With no live homeserver creds
//!     the UI is STILL real: a room list, a populated timeline, and a composer
//!     that appends locally. This is what makes the demo render offline.
//!
//! Keeping the UI behind this trait is the same discipline as the editor's `Fs`
//! seam in `deos-zed`: the view depends on a trait, and the backend (real vs
//! mock vs — later — a confined comms-PD) is one impl swap.

use std::sync::Mutex;

use crate::client::{RoomSummary, TimelineMessage};
use crate::Result;

/// The synchronous surface the chat UI renders against. Object-safe so the UI can
/// hold a `Box<dyn ChatSource>` and not care which backend it is.
pub trait ChatSource: Send + Sync + 'static {
    /// The logged-in user's full id (`@user:server`), if known. Used to align
    /// own-vs-other message bubbles and the composer's "sending as" line.
    fn whoami(&self) -> Option<String>;

    /// List joined rooms, sorted for display. May do network I/O (the real
    /// backend syncs); the UI calls this off the paint path (a spawned task).
    fn rooms(&self) -> Result<Vec<RoomSummary>>;

    /// Read a room's recent timeline (oldest-first), up to `limit` messages.
    fn timeline(&self, room_id: &str, limit: u16) -> Result<Vec<TimelineMessage>>;

    /// Send a plain-text message to a room. Returns the event id on success. The
    /// mock appends locally and echoes a synthetic id; the real backend POSTs and
    /// the next sync folds the echo in.
    fn send(&self, room_id: &str, body: &str) -> Result<String>;

    /// Pull one sync round-trip (real backend) or refresh the mock's clock. The
    /// UI calls this on a timer so new messages appear.
    fn sync(&self) -> Result<()> {
        Ok(())
    }

    /// A short human label for the backend (shown in the title bar). "matrix",
    /// "mock", "firmament-comms-pd", …
    fn backend_label(&self) -> &'static str;
}

// ---------------------------------------------------------------------------
// MatrixHandle is a real ChatSource (the live backend).
// ---------------------------------------------------------------------------

impl ChatSource for crate::worker::MatrixHandle {
    fn whoami(&self) -> Option<String> {
        // The handle does not cache the user id; the real comms-PD will thread it
        // through. For now the UI reads it from the session at login and passes
        // it in. Returning None here keeps the trait honest (no fabrication).
        None
    }

    fn rooms(&self) -> Result<Vec<RoomSummary>> {
        self.joined_rooms()
    }

    fn timeline(&self, room_id: &str, limit: u16) -> Result<Vec<TimelineMessage>> {
        self.recent_timeline(room_id.to_string(), limit)
    }

    fn send(&self, _room_id: &str, _body: &str) -> Result<String> {
        // Send is a worker request the protocol foundation does not yet expose
        // (the headless core proves login/sync/list/read). Wiring it is a single
        // WorkerRequest variant + a `Room::send` call; the UI is ready for it.
        Err(crate::Error::Other(
            "MatrixHandle::send not yet wired (add a WorkerRequest::SendMessage variant)".into(),
        ))
    }

    fn sync(&self) -> Result<()> {
        self.sync_once()
    }

    fn backend_label(&self) -> &'static str {
        "matrix"
    }
}

// ---------------------------------------------------------------------------
// MockSource — a recorded sync so the UI is real with no homeserver.
// ---------------------------------------------------------------------------

/// A synthetic chat backend: a fixed set of rooms with seeded timelines, plus a
/// working `send` that appends to the room's timeline in memory. This makes the
/// deos-chat UI fully exercisable offline — the room list, the timeline, and the
/// composer all do real work against in-memory state.
pub struct MockSource {
    me: String,
    rooms: Vec<RoomSummary>,
    /// Per-room timelines, parallel to `rooms` by index of the room_id.
    timelines: Mutex<Vec<(String, Vec<TimelineMessage>)>>,
    clock: Mutex<u64>,
}

impl MockSource {
    /// A deos-flavoured seeded world: a few rooms, a few voices, some chatter
    /// that hints at the membrane seam this client exists to carry.
    pub fn seeded() -> Self {
        use matrix_sdk::ruma::RoomId;
        let me = "@ember:deos.local".to_string();

        fn room(id: &str, name: &str, topic: &str, members: u64, encrypted: bool) -> RoomSummary {
            RoomSummary {
                room_id: RoomId::parse(id).expect("valid room id"),
                display_name: name.to_string(),
                topic: Some(topic.to_string()),
                is_encrypted: encrypted,
                is_space: false,
                is_direct: false,
                joined_members: members,
                unread_notifications: 0,
            }
        }

        let rooms = vec![
            room(
                "!deoslab:deos.local",
                "deos-lab",
                "the live image — drop membranes here",
                7,
                true,
            ),
            room(
                "!firmament:deos.local",
                "firmament",
                "one cap across distance",
                4,
                true,
            ),
            room(
                "!hpriori:deos.local",
                "houyhnhnm-priori",
                "branch-and-stitch & distributed time-travel",
                3,
                false,
            ),
            room(
                "!ember:deos.local",
                "ember (DM)",
                "direct",
                2,
                true,
            ),
        ];

        let mut clock = 1_718_000_000_000u64; // a fixed plausible ms epoch
        let mut step = || {
            clock += 47_000;
            clock
        };

        let msg = |sender: &str, body: &str, ts: u64| TimelineMessage {
            event_id: format!("$evt{ts}"),
            sender: sender.to_string(),
            body: body.to_string(),
            timestamp_ms: ts,
        };

        let timelines = vec![
            (
                rooms[0].room_id.to_string(),
                vec![
                    msg("@grok:deos.local", "the live image boots on seL4 again — BALANCE_SUM=0 holds", step()),
                    msg("@ember:deos.local", "drop a membrane of the cell graph you're looking at", step()),
                    msg("@grok:deos.local", "sending a frustum-culled fork now — cap-bounded to the cells in view", step()),
                    msg("@ember:deos.local", "rehydrated. driving a SetField turn on the fork. will stitch back.", step()),
                ],
            ),
            (
                rooms[1].room_id.to_string(),
                vec![
                    msg("@pug:deos.local", "n=1 collapse: local seL4-cap == distributed dregg-cap == window", step()),
                    msg("@ember:deos.local", "surface IS the membrane boundary then", step()),
                ],
            ),
            (
                rooms[2].room_id.to_string(),
                vec![
                    msg("@fare:deos.local", "a stitch is a pushout in the event-structure config lattice", step()),
                    msg("@ember:deos.local", "and linearity makes the inconsistent events lossy-dropped — exactly where Σδ=0 / nullifiers force it", step()),
                    msg("@fare:deos.local", "conflicts-as-objects. patch theory validates the merge.", step()),
                ],
            ),
            (
                rooms[3].room_id.to_string(),
                vec![msg("@ember:deos.local", "note to self: wire the SendMessage worker variant", step())],
            ),
        ];

        Self {
            me,
            rooms,
            timelines: Mutex::new(timelines),
            clock: Mutex::new(clock),
        }
    }
}

impl ChatSource for MockSource {
    fn whoami(&self) -> Option<String> {
        Some(self.me.clone())
    }

    fn rooms(&self) -> Result<Vec<RoomSummary>> {
        Ok(self.rooms.clone())
    }

    fn timeline(&self, room_id: &str, limit: u16) -> Result<Vec<TimelineMessage>> {
        let timelines = self.timelines.lock().unwrap();
        for (id, msgs) in timelines.iter() {
            if id == room_id {
                let n = msgs.len();
                let start = n.saturating_sub(limit as usize);
                return Ok(msgs[start..].to_vec());
            }
        }
        Ok(Vec::new())
    }

    fn send(&self, room_id: &str, body: &str) -> Result<String> {
        let ts = {
            let mut clock = self.clock.lock().unwrap();
            *clock += 1_000;
            *clock
        };
        let event_id = format!("$local{ts}");
        let mut timelines = self.timelines.lock().unwrap();
        for (id, msgs) in timelines.iter_mut() {
            if id == room_id {
                msgs.push(TimelineMessage {
                    event_id: event_id.clone(),
                    sender: self.me.clone(),
                    body: body.to_string(),
                    timestamp_ms: ts,
                });
                return Ok(event_id);
            }
        }
        Err(crate::Error::Other(format!("no such room: {room_id}")))
    }

    fn backend_label(&self) -> &'static str {
        "mock"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mock_lists_rooms_and_timelines() {
        let src = MockSource::seeded();
        let rooms = src.rooms().unwrap();
        assert!(rooms.len() >= 3, "expected several seeded rooms");
        let first = rooms[0].room_id.to_string();
        let tl = src.timeline(&first, 50).unwrap();
        assert!(!tl.is_empty(), "first room has a seeded timeline");
        // Oldest-first ordering.
        for w in tl.windows(2) {
            assert!(w[0].timestamp_ms <= w[1].timestamp_ms);
        }
    }

    #[test]
    fn mock_send_appends_and_echoes() {
        let src = MockSource::seeded();
        let rooms = src.rooms().unwrap();
        let room = rooms[0].room_id.to_string();
        let before = src.timeline(&room, 100).unwrap().len();
        let id = src.send(&room, "hello membrane").unwrap();
        assert!(id.starts_with("$local"));
        let after = src.timeline(&room, 100).unwrap();
        assert_eq!(after.len(), before + 1);
        assert_eq!(after.last().unwrap().body, "hello membrane");
        assert_eq!(after.last().unwrap().sender, src.whoami().unwrap());
    }
}
