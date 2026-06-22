//! The sync→async bridge (the iamb `worker.rs` shape).
//!
//! `matrix-rust-sdk` is tokio-async; dregg's embedded executor is sync. The
//! confined comms-PD that hosts this client cannot block on a future directly —
//! it must hand work to a worker owning the tokio runtime and get a value back
//! over a channel. This module is the minimal, REAL version of that bridge:
//!
//! - [`MatrixWorker::spawn`] starts a multi-thread tokio runtime on its own OS
//!   thread, builds nothing yet, and listens for [`WorkerRequest`]s.
//! - [`MatrixHandle`] is the synchronous facade: each call sends a request plus a
//!   oneshot reply channel and blocks on the reply. This is exactly the
//!   request/response discipline iamb uses (`Requester` ⇄ `ClientWorker`), and the
//!   exact shape the dregg-side seam will cross.
//!
//! Scope note: the headless CLI talks to [`MatrixClient`] directly (it is already
//! an async `main`). This worker exists so the protocol foundation already
//! carries the sync-facing seam the comms-PD needs — it is wired and compiles,
//! and the UI/PD phase fills in the remaining request variants.

use std::path::PathBuf;
use std::thread::JoinHandle;

use tokio::sync::{mpsc, oneshot};

use crate::client::{MatrixClient, RoomSummary, TimelineMessage};
use crate::session::StoredSession;
use crate::Result;

/// Requests a synchronous caller can issue to the async worker.
pub enum WorkerRequest {
    /// Log in with a password; reply carries the persistable session.
    LoginPassword {
        homeserver: String,
        store_path: PathBuf,
        passphrase: String,
        username: String,
        password: String,
        device_display_name: String,
        reply: oneshot::Sender<Result<StoredSession>>,
    },
    /// Restore a persisted session.
    Restore {
        stored: StoredSession,
        reply: oneshot::Sender<Result<()>>,
    },
    /// One sync round-trip.
    SyncOnce {
        reply: oneshot::Sender<Result<()>>,
    },
    /// List joined rooms.
    JoinedRooms {
        reply: oneshot::Sender<Result<Vec<RoomSummary>>>,
    },
    /// Read a room's recent timeline.
    RecentTimeline {
        room_id: String,
        limit: u16,
        reply: oneshot::Sender<Result<Vec<TimelineMessage>>>,
    },
    /// Shut the worker down.
    Shutdown,
}

/// The async worker: owns the tokio runtime and the live [`MatrixClient`].
pub struct MatrixWorker;

impl MatrixWorker {
    /// Spawn the worker thread; returns a synchronous [`MatrixHandle`].
    pub fn spawn() -> std::io::Result<(MatrixHandle, JoinHandle<()>)> {
        let (tx, rx) = mpsc::unbounded_channel::<WorkerRequest>();
        let thread = std::thread::Builder::new()
            .name("deos-matrix-worker".into())
            .spawn(move || {
                let rt = tokio::runtime::Builder::new_multi_thread()
                    .enable_all()
                    .build()
                    .expect("build tokio runtime");
                rt.block_on(Self::run(rx));
            })?;
        Ok((MatrixHandle { tx }, thread))
    }

    async fn run(mut rx: mpsc::UnboundedReceiver<WorkerRequest>) {
        let mut client: Option<MatrixClient> = None;
        while let Some(req) = rx.recv().await {
            match req {
                WorkerRequest::LoginPassword {
                    homeserver,
                    store_path,
                    passphrase,
                    username,
                    password,
                    device_display_name,
                    reply,
                } => {
                    let result = MatrixClient::login_password(
                        &homeserver,
                        &store_path,
                        &passphrase,
                        &username,
                        &password,
                        &device_display_name,
                    )
                    .await;
                    let _ = reply.send(match result {
                        Ok((c, session)) => {
                            client = Some(c);
                            Ok(session)
                        }
                        Err(e) => Err(e),
                    });
                }
                WorkerRequest::Restore { stored, reply } => {
                    let _ = reply.send(match MatrixClient::restore(&stored).await {
                        Ok(c) => {
                            client = Some(c);
                            Ok(())
                        }
                        Err(e) => Err(e),
                    });
                }
                WorkerRequest::SyncOnce { reply } => {
                    let _ = reply.send(Self::with(&client, |c| c.sync_once()).await);
                }
                WorkerRequest::JoinedRooms { reply } => {
                    let _ = reply.send(Self::with(&client, |c| c.joined_rooms()).await);
                }
                WorkerRequest::RecentTimeline {
                    room_id,
                    limit,
                    reply,
                } => {
                    let _ = reply
                        .send(Self::with(&client, |c| c.recent_timeline(&room_id, limit)).await);
                }
                WorkerRequest::Shutdown => break,
            }
        }
    }

    async fn with<'a, T, F, Fut>(client: &'a Option<MatrixClient>, f: F) -> Result<T>
    where
        F: FnOnce(&'a MatrixClient) -> Fut,
        Fut: std::future::Future<Output = Result<T>>,
    {
        match client {
            Some(c) => f(c).await,
            None => Err(crate::Error::Other("not logged in".into())),
        }
    }
}

/// Synchronous facade over the worker. Cloneable; each call blocks on a oneshot.
#[derive(Clone)]
pub struct MatrixHandle {
    tx: mpsc::UnboundedSender<WorkerRequest>,
}

impl MatrixHandle {
    fn call<T>(&self, build: impl FnOnce(oneshot::Sender<Result<T>>) -> WorkerRequest) -> Result<T> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx
            .send(build(reply_tx))
            .map_err(|_| crate::Error::Other("matrix worker is gone".into()))?;
        reply_rx
            .blocking_recv()
            .map_err(|_| crate::Error::Other("matrix worker dropped the reply".into()))?
    }

    pub fn login_password(
        &self,
        homeserver: String,
        store_path: PathBuf,
        passphrase: String,
        username: String,
        password: String,
        device_display_name: String,
    ) -> Result<StoredSession> {
        self.call(|reply| WorkerRequest::LoginPassword {
            homeserver,
            store_path,
            passphrase,
            username,
            password,
            device_display_name,
            reply,
        })
    }

    pub fn restore(&self, stored: StoredSession) -> Result<()> {
        self.call(|reply| WorkerRequest::Restore { stored, reply })
    }

    pub fn sync_once(&self) -> Result<()> {
        self.call(|reply| WorkerRequest::SyncOnce { reply })
    }

    pub fn joined_rooms(&self) -> Result<Vec<RoomSummary>> {
        self.call(|reply| WorkerRequest::JoinedRooms { reply })
    }

    pub fn recent_timeline(&self, room_id: String, limit: u16) -> Result<Vec<TimelineMessage>> {
        self.call(|reply| WorkerRequest::RecentTimeline {
            room_id,
            limit,
            reply,
        })
    }

    /// Ask the worker to stop. The caller may then `join` the worker thread.
    pub fn shutdown(&self) {
        let _ = self.tx.send(WorkerRequest::Shutdown);
    }
}
