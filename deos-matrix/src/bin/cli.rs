//! `deos-matrix-cli` — the headless harness for the protocol foundation.
//!
//! No UI. Proves the matrix-rust-sdk path end to end so the foundation is
//! testable before gpui exists:
//!
//!   deos-matrix-cli login   --homeserver https://matrix.org --user @me:matrix.org
//!   deos-matrix-cli rooms
//!   deos-matrix-cli timeline --room '!abc:matrix.org' --limit 30
//!
//! The session (and the SQLite state + E2E crypto store) persist under the OS
//! data dir, so `rooms`/`timeline` restore without re-login.

use std::path::PathBuf;

use clap::{Parser, Subcommand};
use deos_matrix::{MatrixClient, StoredSession};

#[derive(Parser)]
#[command(
    name = "deos-matrix-cli",
    about = "Headless deos Matrix client core (matrix-rust-sdk foundation)."
)]
struct Cli {
    /// Override the data directory (session + sqlite store live here).
    #[arg(long, env = "DEOS_MATRIX_DATA")]
    data_dir: Option<PathBuf>,
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Log in with a password and persist the session.
    Login {
        #[arg(long)]
        homeserver: String,
        #[arg(long)]
        user: String,
        /// Password (omit to be prompted without echo).
        #[arg(long)]
        password: Option<String>,
        #[arg(long, default_value = "deos-matrix")]
        device_name: String,
    },
    /// Log in with a pre-issued access token (the SSO / admin-token path; no
    /// password held). Needs the user id + device id the token belongs to.
    LoginToken {
        #[arg(long)]
        homeserver: String,
        #[arg(long)]
        user: String,
        #[arg(long)]
        access_token: String,
        #[arg(long, default_value = "deos-matrix")]
        device_id: String,
    },
    /// Sync once and list joined rooms.
    Rooms,
    /// Sync once and print a room's recent timeline.
    Timeline {
        #[arg(long)]
        room: String,
        #[arg(long, default_value_t = 20)]
        limit: u16,
    },
    /// Send a plain-text message to a room (prints the event id).
    Send {
        #[arg(long)]
        room: String,
        #[arg(long)]
        body: String,
    },
    /// Send a membrane-bearing message to a room (a sample mock envelope rides
    /// under the `software.ember.deos.membrane` custom key). Proves the
    /// deos-pilling over a real homeserver.
    SendMembrane {
        #[arg(long)]
        room: String,
        /// Human fallback body (empty → the membrane's text_fallback is used).
        #[arg(long, default_value = "")]
        body: String,
    },
    /// Send a dregg semantic object (the generalized membrane) to a room. `kind`
    /// selects which sample object to mint and send.
    SendObject {
        #[arg(long)]
        room: String,
        /// Which object kind: cell | capability | transclusion | affordance |
        /// receipt | membrane.
        #[arg(long, default_value = "cell")]
        kind: String,
        #[arg(long, default_value = "")]
        body: String,
    },
    /// List joined spaces (the room hierarchy) and their child rooms.
    Spaces,
    /// Search the homeserver's public room directory.
    Directory {
        /// Optional search query (empty → popular rooms).
        #[arg(long)]
        query: Option<String>,
        #[arg(long, default_value_t = 20)]
        limit: u16,
    },
    /// Join a room by id or alias (`!abc:server` or `#room:server`).
    Join {
        #[arg(long)]
        room: String,
    },
    /// List pending room invites.
    Invites,
    /// Accept a pending room invite.
    AcceptInvite {
        #[arg(long)]
        room: String,
    },
    /// Show a room's power levels (basic room settings).
    Power {
        #[arg(long)]
        room: String,
    },
    /// Show this account's device id + key-backup status (E2E health for a heavy
    /// user: "do my keys survive a device loss?").
    Encryption,
    /// Show the logged-in user.
    Whoami,
}

fn data_dir(override_dir: Option<PathBuf>) -> PathBuf {
    override_dir.unwrap_or_else(|| {
        directories::ProjectDirs::from("software", "ember", "deos-matrix")
            .map(|d| d.data_dir().to_path_buf())
            .unwrap_or_else(|| PathBuf::from(".deos-matrix"))
    })
}

fn session_path(dir: &std::path::Path) -> PathBuf {
    dir.join("session.json")
}

fn store_path(dir: &std::path::Path) -> PathBuf {
    dir.join("store")
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "deos_matrix=info,warn".into()),
        )
        .init();

    let cli = Cli::parse();
    let dir = data_dir(cli.data_dir);
    std::fs::create_dir_all(&dir)?;
    let sess_path = session_path(&dir);

    match cli.cmd {
        Cmd::Login {
            homeserver,
            user,
            password,
            device_name,
        } => {
            let password = match password {
                Some(p) => p,
                None => rpassword::prompt_password(format!("password for {user}: "))?,
            };
            // Random store passphrase, persisted with the session.
            let passphrase = format!("{:016x}", rand_u64());
            let (_client, stored) = MatrixClient::login_password(
                &homeserver,
                &store_path(&dir),
                &passphrase,
                &user,
                &password,
                &device_name,
            )
            .await?;
            stored.save(&sess_path)?;
            println!("logged in as {}", stored.session.meta.user_id);
            println!("session saved to {}", sess_path.display());
        }
        Cmd::LoginToken {
            homeserver,
            user,
            access_token,
            device_id,
        } => {
            let passphrase = format!("{:016x}", rand_u64());
            let (_client, stored) = MatrixClient::login_access_token(
                &homeserver,
                &store_path(&dir),
                &passphrase,
                &user,
                &access_token,
                &device_id,
            )
            .await?;
            stored.save(&sess_path)?;
            println!("logged in as {} (token)", stored.session.meta.user_id);
            println!("session saved to {}", sess_path.display());
        }
        Cmd::Whoami => {
            let client = restore(&sess_path).await?;
            match client.user_id() {
                Some(uid) => println!("{uid}"),
                None => println!("(not logged in)"),
            }
        }
        Cmd::Send { room, body } => {
            let client = restore(&sess_path).await?;
            client.sync_once().await?;
            let event_id = client.send_text(&room, &body).await?;
            println!("sent to {room}: {event_id}");
        }
        Cmd::SendMembrane { room, body } => {
            let client = restore(&sess_path).await?;
            client.sync_once().await?;
            let env = deos_matrix::MockMembraneHost::sample_envelope();
            let event_id = client.send_membrane(&room, &body, &env).await?;
            println!("sent membrane to {room}: {event_id}");
            println!("  wire key: software.ember.deos.membrane");
            println!("  fallback: {}", env.text_fallback());
        }
        Cmd::SendObject { room, kind, body } => {
            let client = restore(&sess_path).await?;
            client.sync_once().await?;
            let object = sample_object(&kind)?;
            let event_id = client.send_object(&room, &body, &object).await?;
            println!("sent {} object to {room}: {event_id}", object.kind());
            println!("  wire key: {}", deos_matrix::DREGG_OBJECT_KEY);
            println!("  fallback: {}", object.text_fallback());
        }
        Cmd::Spaces => {
            let client = restore(&sess_path).await?;
            client.sync_once().await?;
            let spaces = client.spaces().await?;
            println!("{} joined space(s):", spaces.len());
            for s in spaces {
                println!("  {} ({}) · {} children", s.display_name, s.room_id, s.child_room_ids.len());
                for c in &s.child_room_ids {
                    println!("      ↳ {c}");
                }
            }
        }
        Cmd::Directory { query, limit } => {
            let client = restore(&sess_path).await?;
            let rooms = client.search_public_rooms(query.as_deref(), limit).await?;
            println!("{} public room(s):", rooms.len());
            for r in rooms {
                println!(
                    "  {:<40} {:>5} members  {}{}",
                    r.name.unwrap_or_else(|| r.room_id.clone()),
                    r.joined_members,
                    r.alias.map(|a| format!("{a} ")).unwrap_or_default(),
                    r.room_id
                );
            }
        }
        Cmd::Join { room } => {
            let client = restore(&sess_path).await?;
            client.sync_once().await?;
            let joined = client.join(&room).await?;
            println!("joined {joined}");
        }
        Cmd::Invites => {
            let client = restore(&sess_path).await?;
            client.sync_once().await?;
            let invites = client.invited_rooms().await?;
            println!("{} pending invite(s):", invites.len());
            for r in invites {
                println!("  {} ({}) · {} members", r.display_name, r.room_id, r.joined_members);
            }
        }
        Cmd::AcceptInvite { room } => {
            let client = restore(&sess_path).await?;
            client.sync_once().await?;
            let joined = client.accept_invite(&room).await?;
            println!("accepted invite, joined {joined}");
        }
        Cmd::Power { room } => {
            let client = restore(&sess_path).await?;
            client.sync_once().await?;
            let p = client.power_levels(&room).await?;
            println!("power levels for {room}:");
            println!("  your level:    {}", p.my_level);
            println!("  users_default: {}", p.users_default);
            println!("  invite:        {}", p.invite);
            println!("  kick:          {}", p.kick);
            println!("  ban:           {}", p.ban);
            println!("  redact:        {}", p.redact);
        }
        Cmd::Encryption => {
            let client = restore(&sess_path).await?;
            client.sync_once().await?;
            println!("device id:      {}", client.device_id().unwrap_or_else(|| "(none)".into()));
            println!("key backup:     {}", if client.backup_enabled().await { "enabled" } else { "DISABLED — run recovery setup" });
        }
        Cmd::Rooms => {
            let client = restore(&sess_path).await?;
            client.sync_once().await?;
            let rooms = client.joined_rooms().await?;
            println!("{} joined room(s):", rooms.len());
            for r in rooms {
                let flags = [
                    r.is_encrypted.then_some("E2E"),
                    r.is_space.then_some("space"),
                    r.is_direct.then_some("dm"),
                ]
                .into_iter()
                .flatten()
                .collect::<Vec<_>>()
                .join(",");
                println!(
                    "  {:<48} {:>4} members  {}{}",
                    r.display_name,
                    r.joined_members,
                    if flags.is_empty() { String::new() } else { format!("[{flags}] ") },
                    r.room_id
                );
            }
        }
        Cmd::Timeline { room, limit } => {
            let client = restore(&sess_path).await?;
            client.sync_once().await?;
            let msgs = client.recent_timeline(&room, limit).await?;
            println!("{} message(s) in {room}:", msgs.len());
            for m in msgs {
                println!("  [{}] {}: {}", m.timestamp_ms, m.sender, m.body);
                // If the message carried a deos membrane, the receive-side
                // extraction parsed it back into a typed envelope — surface it so
                // the deos-pilling is visible end to end (kind=Membrane).
                if let Some(env) = &m.membrane {
                    println!(
                        "      ↳ deos membrane [kind={:?}] · {} cells · sturdyref {} · rehydratable={}",
                        m.kind,
                        env.cut.cell_count,
                        env.sturdyref,
                        env.is_rehydratable(),
                    );
                }
            }
        }
    }
    Ok(())
}

async fn restore(sess_path: &std::path::Path) -> anyhow::Result<MatrixClient> {
    if !sess_path.exists() {
        anyhow::bail!("no session at {} — run `login` first", sess_path.display());
    }
    let stored = StoredSession::load(sess_path)?;
    Ok(MatrixClient::restore(&stored).await?)
}

/// Mint a sample [`DreggObject`] of the named kind — for the CLI's `send-object`
/// (so each kind's wire round-trip is exercisable against a real homeserver).
fn sample_object(kind: &str) -> anyhow::Result<deos_matrix::DreggObject> {
    use deos_matrix::{
        Affordance, CapabilityGrant, CellId, CellRef, DreggObject, MockMembraneHost,
        ReceiptObject, Transclusion,
    };
    let cell = CellId::derive("!deoslab:deos.local");
    Ok(match kind {
        "cell" => DreggObject::Cell(CellRef {
            cell_id: cell,
            label: "the deos-lab room cell".into(),
            cell_kind: Some("room".into()),
        }),
        "capability" => DreggObject::Capability(CapabilityGrant {
            sturdyref: "dregg://cap/post/deoslab".into(),
            label: "post to deos-lab".into(),
            lineage: vec![0xca, 0x9a, 0xb1, 0xe],
        }),
        "transclusion" => DreggObject::Transclusion(Transclusion {
            source_cell: cell,
            field: "members.count".into(),
            value: "7".into(),
            bound_root: [0xab; 32],
        }),
        "affordance" => DreggObject::Affordance(Affordance {
            target_cell: cell,
            action: "approve".into(),
            label: "Approve the merge".into(),
            required_cap: "dregg://cap/approve".into(),
        }),
        "receipt" => DreggObject::Receipt(ReceiptObject {
            cell_id: cell,
            turn_index: 7,
            post_root: [0xef; 32],
        }),
        "membrane" => DreggObject::Membrane(MockMembraneHost::sample_envelope()),
        other => anyhow::bail!(
            "unknown object kind {other:?} — use one of: cell capability transclusion affordance receipt membrane"
        ),
    })
}

/// Tiny non-crypto random for the store passphrase (the passphrase only protects
/// a local at-rest store; in the deos integration this is sealed to the identity
/// cell instead — see README §deos integration).
fn rand_u64() -> u64 {
    use std::hash::{BuildHasher, Hasher};
    std::collections::hash_map::RandomState::new()
        .build_hasher()
        .finish()
}
