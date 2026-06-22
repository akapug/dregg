//! Session persistence.
//!
//! A logged-in Matrix session is two things: the SDK's [`MatrixSession`] (user
//! id, device id, access/refresh tokens) and the homeserver URL it belongs to.
//! We persist both as JSON alongside the SQLite store directory so the CLI (and,
//! later, the confined comms-PD) can restore without re-entering a password.
//!
//! # deos note (roadmap)
//!
//! In the deos integration the access token + device keys are NOT a plaintext
//! JSON file: they are sealed to the user's deos identity cell, and the device
//! keys become caps (see `README.md` §deos integration). The plaintext form here
//! is the headless-foundation stand-in so the protocol layer is testable today.

use std::path::{Path, PathBuf};

use matrix_sdk::authentication::matrix::MatrixSession;
use serde::{Deserialize, Serialize};

use crate::Result;

/// Everything needed to rebuild an authenticated client without a password.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StoredSession {
    /// The homeserver this session authenticated against.
    pub homeserver: String,
    /// The SDK session (user id, device id, tokens).
    pub session: MatrixSession,
    /// Path to the SQLite store directory holding state + crypto (E2E) data.
    pub store_path: PathBuf,
    /// Passphrase the SQLite store was opened with (random per-session).
    pub store_passphrase: String,
}

impl StoredSession {
    /// Read a stored session from `path` (JSON).
    pub fn load(path: &Path) -> Result<Self> {
        let bytes = std::fs::read(path)?;
        Ok(serde_json::from_slice(&bytes)?)
    }

    /// Write this session to `path` (JSON), creating parent dirs as needed.
    pub fn save(&self, path: &Path) -> Result<()> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let bytes = serde_json::to_vec_pretty(self)?;
        std::fs::write(path, bytes)?;
        Ok(())
    }
}
