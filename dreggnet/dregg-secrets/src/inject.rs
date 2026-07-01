//! THE EXEC-SECRET-INJECTION SEAM — confined runtime delivery of secrets.
//!
//! A workload DECLARES the secrets it needs (a [`SecretRequest`]: which secret,
//! delivered as which env var or file path). At run time exec calls
//! [`inject_for_workload`], which resolves each binding through the cap-gated,
//! audited [`SecretStore::read`] and assembles the confined material into an
//! [`InjectedSecrets`]. exec then sets those env vars / writes those files INTO
//! THE SANDBOX — and nowhere else.
//!
//! This is the BYO-LLM-key confinement pattern (`exec::openai_compat::ProviderKey`)
//! generalized: the secret reaches ONLY where it must (the sandbox), never the
//! request body the agent sees, a tool-call, a receipt, the run report, the
//! operator view, or a log line. [`InjectedSecrets`]'s `Debug` is redacted (a
//! confinement tooth), and [`InjectedSecrets::redaction_set`] / [`scrub`] give a
//! caller the values to assert-absent / strip from any text it is about to emit.
//!
//! Fail-closed: if ANY declared secret is refused (cap, account, or absence),
//! the whole injection fails and NO secret is delivered — a workload never runs
//! with a partial, ambiguous secret environment.
//!
//! ## The live wire (exec side, not edited here — swarm-safe)
//! `exec::run_workload_with_input` resolves a workload's lease → an account
//! [`SecretStore`] + the lease's credential → calls [`inject_for_workload`] →
//! applies [`InjectedSecrets::env_vars`] / [`InjectedSecrets::files`] to the
//! sandbox spec. That edit lands in `exec` when this crate is adopted.

use std::collections::BTreeMap;

use zeroize::Zeroizing;

use crate::SecretError;
use crate::store::SecretStore;

/// How a resolved secret is delivered into the sandbox.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Delivery {
    /// Set environment variable `name` to the secret value.
    Env(String),
    /// Mount the secret value at file path `path` inside the sandbox.
    File(String),
}

/// One declared secret need: read secret `secret_name`, deliver it `as`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecretBinding {
    pub secret_name: String,
    pub deliver_as: Delivery,
}

impl SecretBinding {
    pub fn env(secret_name: impl Into<String>, var: impl Into<String>) -> SecretBinding {
        SecretBinding {
            secret_name: secret_name.into(),
            deliver_as: Delivery::Env(var.into()),
        }
    }
    pub fn file(secret_name: impl Into<String>, path: impl Into<String>) -> SecretBinding {
        SecretBinding {
            secret_name: secret_name.into(),
            deliver_as: Delivery::File(path.into()),
        }
    }
}

/// A workload's declared secret needs (cap-gated at resolution).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SecretRequest {
    pub bindings: Vec<SecretBinding>,
}

impl SecretRequest {
    pub fn new() -> SecretRequest {
        SecretRequest::default()
    }
    pub fn with(mut self, binding: SecretBinding) -> SecretRequest {
        self.bindings.push(binding);
        self
    }
    /// The secret names this request will read (for a pre-flight cap check).
    pub fn names(&self) -> Vec<&str> {
        self.bindings
            .iter()
            .map(|b| b.secret_name.as_str())
            .collect()
    }
}

/// The resolved, confined material handed to the sandbox. The values are
/// [`Zeroizing`] and the `Debug` is redacted — they must not be cloned into any
/// operator-visible surface.
#[derive(Default)]
pub struct InjectedSecrets {
    env: BTreeMap<String, Zeroizing<Vec<u8>>>,
    files: BTreeMap<String, Zeroizing<Vec<u8>>>,
}

impl InjectedSecrets {
    /// The env vars to set in the sandbox (name → value bytes).
    pub fn env_vars(&self) -> impl Iterator<Item = (&str, &[u8])> {
        self.env.iter().map(|(k, v)| (k.as_str(), &v[..]))
    }

    /// The files to mount in the sandbox (path → value bytes).
    pub fn files(&self) -> impl Iterator<Item = (&str, &[u8])> {
        self.files.iter().map(|(k, v)| (k.as_str(), &v[..]))
    }

    /// How many secrets were injected.
    pub fn len(&self) -> usize {
        self.env.len() + self.files.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The set of injected secret VALUES (as strings, lossy) — the redaction
    /// tooth. A caller about to emit a log line / receipt / report can assert
    /// none of these appear, or strip them with [`scrub`](Self::scrub).
    pub fn redaction_set(&self) -> Vec<String> {
        self.env
            .values()
            .chain(self.files.values())
            .map(|v| String::from_utf8_lossy(v).into_owned())
            .collect()
    }

    /// Replace every injected secret value occurring in `text` with `<redacted>`
    /// — the confinement helper for any surface that handles workload-adjacent
    /// text (so an accidental echo cannot leak a secret).
    pub fn scrub(&self, text: &str) -> String {
        let mut out = text.to_string();
        for v in self.redaction_set() {
            if !v.is_empty() {
                out = out.replace(&v, "<redacted>");
            }
        }
        out
    }
}

impl std::fmt::Debug for InjectedSecrets {
    /// REDACTED — values never print; only the shape (a confinement tooth).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InjectedSecrets")
            .field("env_vars", &self.env.keys().collect::<Vec<_>>())
            .field("files", &self.files.keys().collect::<Vec<_>>())
            .field("values", &"<redacted>")
            .finish()
    }
}

/// THE EXEC-SECRET-INJECTION SEAM. Resolve a workload's declared secrets,
/// cap-gated + audited, into confined sandbox material. Fail-closed: any refused
/// binding fails the whole injection (no partial secret environment).
///
/// `cred_enc` is the lease's credential (the workload's authority); `now` is the
/// verifier clock. Each binding is read through [`SecretStore::read`], so each
/// resolution is cap-checked and emits an audit receipt.
pub fn inject_for_workload(
    store: &SecretStore,
    cred_enc: &str,
    req: &SecretRequest,
    now: u64,
) -> Result<InjectedSecrets, SecretError> {
    let mut out = InjectedSecrets::default();
    for binding in &req.bindings {
        let value = store.read(cred_enc, &binding.secret_name, now)?;
        match &binding.deliver_as {
            Delivery::Env(var) => {
                out.env.insert(var.clone(), value);
            }
            Delivery::File(path) => {
                out.files.insert(path.clone(), value);
            }
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cap::mint_secret_caps;
    use crate::kms::KmsRoot;
    use dreggnet_webauth::cred::RootKey;

    fn store(root: &RootKey) -> SecretStore {
        SecretStore::new(
            "acct-A",
            root.public(),
            KmsRoot::operator_held([5u8; 32]),
            [6u8; 32],
        )
    }

    #[test]
    fn a_workload_with_the_cap_gets_its_secret_injected() {
        let root = RootKey::from_seed([40u8; 32]);
        let store = store(&root);
        store
            .put("my-app/DB_URL", b"postgres://secret", 100)
            .unwrap();
        store.put("my-app/TOKEN", b"tok-abc", 100).unwrap();

        let cred = mint_secret_caps(&root, ["my-app/DB_URL", "my-app/TOKEN"], None).encode();
        let req = SecretRequest::new()
            .with(SecretBinding::env("my-app/DB_URL", "DATABASE_URL"))
            .with(SecretBinding::file("my-app/TOKEN", "/run/secrets/token"));

        let injected = inject_for_workload(&store, &cred, &req, 200).unwrap();
        let env: BTreeMap<_, _> = injected.env_vars().map(|(k, v)| (k, v.to_vec())).collect();
        assert_eq!(
            env.get("DATABASE_URL").map(|v| &v[..]),
            Some(&b"postgres://secret"[..])
        );
        let files: BTreeMap<_, _> = injected.files().map(|(k, v)| (k, v.to_vec())).collect();
        assert_eq!(
            files.get("/run/secrets/token").map(|v| &v[..]),
            Some(&b"tok-abc"[..])
        );
    }

    #[test]
    fn a_workload_without_the_cap_is_refused_and_nothing_injected() {
        let root = RootKey::from_seed([41u8; 32]);
        let store = store(&root);
        store
            .put("my-app/DB_URL", b"postgres://secret", 100)
            .unwrap();

        // Cred grants only TOKEN, but the request also needs DB_URL → fail-closed.
        let cred = mint_secret_caps(&root, ["my-app/TOKEN"], None).encode();
        let req = SecretRequest::new().with(SecretBinding::env("my-app/DB_URL", "DATABASE_URL"));
        assert!(inject_for_workload(&store, &cred, &req, 200).is_err());
    }

    #[test]
    fn debug_and_scrub_never_leak_the_value() {
        let root = RootKey::from_seed([42u8; 32]);
        let store = store(&root);
        store.put("s/A", b"top-secret-xyz", 100).unwrap();
        let cred = mint_secret_caps(&root, ["s/A"], None).encode();
        let req = SecretRequest::new().with(SecretBinding::env("s/A", "VAL"));
        let injected = inject_for_workload(&store, &cred, &req, 200).unwrap();

        let dbg = format!("{injected:?}");
        assert!(
            !dbg.contains("top-secret-xyz"),
            "Debug leaked the value: {dbg}"
        );
        let scrubbed = injected.scrub("the value is top-secret-xyz here");
        assert!(!scrubbed.contains("top-secret-xyz"));
        assert!(scrubbed.contains("<redacted>"));
    }
}
