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

/// Tiny non-crypto random for the store passphrase (the passphrase only protects
/// a local at-rest store; in the deos integration this is sealed to the identity
/// cell instead — see README §deos integration).
fn rand_u64() -> u64 {
    use std::hash::{BuildHasher, Hasher};
    std::collections::hash_map::RandomState::new()
        .build_hasher()
        .finish()
}
