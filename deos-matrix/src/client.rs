//! The async Matrix client core.
//!
//! Thin, deos-shaped wrapper over [`matrix_sdk::Client`]. Every method is
//! `async`; the synchronous-caller bridge lives in [`crate::worker`]. The SDK
//! handles the protocol (sync, room state, ruma events) and E2E encryption
//! (vodozemac, via the default `e2e-encryption` feature + the SQLite crypto
//! store). We add: a homeserver+store builder, password login with session
//! persistence, an encrypted `sync_once` + a continuous `sync`, a flat room
//! summary, and a recent-timeline read.

use std::path::Path;

use matrix_sdk::{
    authentication::matrix::MatrixSession,
    config::SyncSettings,
    ruma::{
        api::client::filter::RoomEventFilter,
        events::room::message::MessageType, events::AnySyncTimelineEvent, OwnedRoomId, UserId,
    },
    Client, RoomState,
};

use crate::{session::StoredSession, Error, Result};

/// A native deos Matrix client over `matrix-rust-sdk`.
pub struct MatrixClient {
    inner: Client,
}

/// A flat, UI-agnostic summary of a joined room.
#[derive(Debug, Clone)]
pub struct RoomSummary {
    pub room_id: OwnedRoomId,
    pub display_name: String,
    pub topic: Option<String>,
    pub is_encrypted: bool,
    pub is_space: bool,
    pub is_direct: bool,
    pub joined_members: u64,
    pub unread_notifications: u64,
}

/// A single rendered timeline message (text-only projection for the headless core).
#[derive(Debug, Clone)]
pub struct TimelineMessage {
    pub event_id: String,
    pub sender: String,
    pub body: String,
    /// Origin server timestamp, milliseconds since the Unix epoch.
    pub timestamp_ms: u64,
}

impl MatrixClient {
    /// Build a client for `homeserver_url`, backed by a SQLite store at
    /// `store_path` (state + E2E crypto). The store is opened with `passphrase`.
    pub async fn build(
        homeserver_url: &str,
        store_path: &Path,
        passphrase: &str,
    ) -> Result<Self> {
        let inner = Client::builder()
            .homeserver_url(homeserver_url)
            .sqlite_store(store_path, Some(passphrase))
            .build()
            .await?;
        Ok(Self { inner })
    }

    /// Log in with a username (localpart or full `@user:server`) and password,
    /// returning a [`StoredSession`] the caller should persist. The
    /// `initial_device_display_name` is what other devices see in this account's
    /// device list.
    pub async fn login_password(
        homeserver_url: &str,
        store_path: &Path,
        passphrase: &str,
        username: &str,
        password: &str,
        device_display_name: &str,
    ) -> Result<(Self, StoredSession)> {
        let me = Self::build(homeserver_url, store_path, passphrase).await?;

        me.inner
            .matrix_auth()
            .login_username(username, password)
            .initial_device_display_name(device_display_name)
            .send()
            .await?;

        let session = me
            .inner
            .matrix_auth()
            .session()
            .ok_or_else(|| Error::Other("login succeeded but no session present".into()))?;

        let stored = StoredSession {
            homeserver: homeserver_url.to_string(),
            session,
            store_path: store_path.to_path_buf(),
            store_passphrase: passphrase.to_string(),
        };
        Ok((me, stored))
    }

    /// Rebuild an authenticated client from a previously persisted session.
    pub async fn restore(stored: &StoredSession) -> Result<Self> {
        let me = Self::build(
            &stored.homeserver,
            &stored.store_path,
            &stored.store_passphrase,
        )
        .await?;
        me.inner
            .restore_session(stored.session.clone())
            .await?;
        Ok(me)
    }

    /// Run a single sync round-trip (state + encrypted events flow into the
    /// store). Cheap, deterministic — ideal for the headless CLI and tests.
    pub async fn sync_once(&self) -> Result<()> {
        self.inner.sync_once(SyncSettings::default()).await?;
        Ok(())
    }

    /// Run the continuous sync loop. Never returns except on error. This is what
    /// the long-lived comms-PD drives.
    pub async fn sync_forever(&self) -> Result<()> {
        self.inner.sync(SyncSettings::default()).await?;
        Ok(())
    }

    /// List joined rooms as flat [`RoomSummary`] values.
    pub async fn joined_rooms(&self) -> Result<Vec<RoomSummary>> {
        let mut out = Vec::new();
        for room in self.inner.joined_rooms() {
            // `display_name` resolves the room name, or computes one from members
            // (the Matrix heroes algorithm) for unnamed/DM rooms.
            let display_name = match room.display_name().await {
                Ok(name) => name.to_string(),
                Err(_) => room.room_id().to_string(),
            };
            out.push(RoomSummary {
                room_id: room.room_id().to_owned(),
                display_name,
                topic: room.topic(),
                is_encrypted: room.encryption_state().is_encrypted(),
                is_space: room.is_space(),
                is_direct: room.is_direct().await.unwrap_or(false),
                joined_members: room.joined_members_count(),
                unread_notifications: room.unread_notification_counts().notification_count,
            });
        }
        // Stable, human-friendly ordering by display name.
        out.sort_by(|a, b| a.display_name.to_lowercase().cmp(&b.display_name.to_lowercase()));
        Ok(out)
    }

    /// Read the most recent `limit` messages of a room (text projection).
    ///
    /// This uses the SDK's `messages` pagination (backward from the live edge).
    /// The richer [`matrix_sdk_ui::Timeline`] (edits/reactions/threads folded in)
    /// is the UI-phase upgrade; the headless core only needs the raw recent
    /// message bodies to prove the protocol path end to end.
    pub async fn recent_timeline(
        &self,
        room_id: &str,
        limit: u16,
    ) -> Result<Vec<TimelineMessage>> {
        let room_id = matrix_sdk::ruma::RoomId::parse(room_id)?;
        let room = self
            .inner
            .get_room(&room_id)
            .ok_or_else(|| Error::Other(format!("not a joined room: {room_id}")))?;
        if room.state() != RoomState::Joined {
            return Err(Error::Other(format!("room {room_id} is not joined")));
        }

        let mut options = matrix_sdk::room::MessagesOptions::backward();
        options.limit = matrix_sdk::ruma::UInt::from(limit);
        // Only fetch room message events; cuts down deserialization noise.
        let mut filter = RoomEventFilter::default();
        filter.types = Some(vec!["m.room.message".to_string()]);
        options.filter = filter;

        let response = room.messages(options).await?;

        let mut out = Vec::new();
        for ev in response.chunk {
            // `ev.raw()` is a serialized timeline event; the SDK has already
            // decrypted encrypted events into their cleartext form in the store.
            let Ok(any) = ev.raw().deserialize() else {
                continue;
            };
            if let AnySyncTimelineEvent::MessageLike(
                matrix_sdk::ruma::events::AnySyncMessageLikeEvent::RoomMessage(msg),
            ) = any
            {
                if let Some(original) = msg.as_original() {
                    let body = match &original.content.msgtype {
                        MessageType::Text(t) => t.body.clone(),
                        MessageType::Emote(t) => format!("* {}", t.body),
                        MessageType::Notice(t) => t.body.clone(),
                        MessageType::Image(i) => format!("[image] {}", i.body),
                        MessageType::File(f) => format!("[file] {}", f.body),
                        MessageType::Audio(a) => format!("[audio] {}", a.body),
                        MessageType::Video(v) => format!("[video] {}", v.body),
                        other => format!("[{}]", other.msgtype()),
                    };
                    out.push(TimelineMessage {
                        event_id: original.event_id.to_string(),
                        sender: original.sender.to_string(),
                        body,
                        timestamp_ms: u64::from(original.origin_server_ts.0),
                    });
                }
            }
        }
        // `messages(backward)` yields newest-first; present oldest-first.
        out.reverse();
        Ok(out)
    }

    /// The logged-in user's full id, if any.
    pub fn user_id(&self) -> Option<&UserId> {
        self.inner.user_id()
    }

    /// Borrow the underlying SDK client (for the worker bridge / UI layer).
    pub fn sdk(&self) -> &Client {
        &self.inner
    }

    /// The active SDK session, if logged in (for re-persisting after token refresh).
    pub fn session(&self) -> Option<MatrixSession> {
        self.inner.matrix_auth().session()
    }
}
