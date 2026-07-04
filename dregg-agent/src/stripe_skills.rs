//! `stripe_skills` — the **real Stripe Skills for Hermes**, wired as the agent's
//! self-provisioning + self-paying transport.
//!
//! The NVIDIA × Stripe × Nous hackathon headline is *"Stripe Skills for Hermes
//! let your agent buy what it needs, provision its own SaaS, and pay for the
//! services it uses."* Those Skills are not an LLM endpoint — they are **two
//! CLIs** the agent shells out to (per `docs/HACKATHON-STACK.md`):
//!
//! - **`official/payments/stripe-projects`** — the Stripe Projects CLI:
//!   `stripe projects add <provider>/<service>` provisions real SaaS (Neon /
//!   Twilio / Vercel) into the user's own provider accounts and syncs the
//!   credentials. The agent **provisions its own infrastructure**.
//! - **`official/payments/stripe-link-cli`** — `@stripe/link-cli`: pays a vendor
//!   via one-time virtual cards + Shared Payment Tokens (the HTTP-402 / per-call
//!   merchants). The agent **pays for the services it uses**.
//!
//! This module is the **transport** behind the two cap-gated, budget-metered,
//! receipted agent tools (`stripe_provision` / `stripe_pay`, registered on the
//! operator rail in [`crate::tools`]). It is deliberately split stub-vs-live:
//!
//! - **[`CliStripeSkills`]** (live) shells the real CLIs through an injected
//!   process runner, reads the key (`STRIPE_API_KEY` / `~/.stripekey`) **at
//!   runtime**, passes it to the child via the **environment** (never argv), and
//!   **redacts** it from every captured byte before it reaches a summary, a
//!   receipt, or a log (the BYO-key confinement pattern). Goes live the moment the
//!   CLIs + a test key are present.
//! - **[`RecordedStripeSkills`]** (stub) is a faithful recorded transport for the
//!   green tests + the offline demo: deterministic, clearly labelled *"(Stripe
//!   Skill live leg needs the CLI + a test key)"* — it never fakes a live success.
//!
//! [`detect`] picks the live transport when the CLIs + a key are present and the
//! recorded one otherwise, so the same build runs offline today and live the
//! moment the key + CLIs land.
//!
//! The **bounds live on the rail, not here**: the budget cell draws the spend
//! *before* the CLI runs (an over-ceiling pay is refused in-band — no money
//! moves), the cap bundle gates `provision:<provider>` / `pay:<vendor>` per
//! resource, and the outcome is sealed into an ed25519 receipt (a forged "I paid
//! $5 not $500" breaks the signature). This module only performs the (redacted)
//! call and reports the receipt-safe facts.

use std::process::Command;

use crate::receipt::BodyHasher;

/// What `stripe projects add <provider>/<service>` produced — the **receipt-safe**
/// facts only (the synced credential *names*, never their secret values).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvisionOutcome {
    /// The SaaS provider (e.g. `neon`, `twilio`, `vercel`).
    pub provider: String,
    /// The service within the provider (e.g. `postgres`, `sms`).
    pub service: String,
    /// The provisioned resource handle the CLI reported (or a deterministic
    /// stand-in in the recorded transport). Never a secret.
    pub resource_id: String,
    /// The credential *keys* that were synced to `.env` / the vault — the NAMES
    /// only (e.g. `DATABASE_URL`), so the receipt records *what* was provisioned
    /// without ever binding a secret value.
    pub synced_creds: Vec<String>,
    /// A human, **key-redacted** summary of the call.
    pub detail: String,
    /// `true` iff this came from the real CLI; `false` for the recorded transport.
    pub live: bool,
}

/// What the `link-cli` pay produced — the receipt-safe facts of a vendor payment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PayOutcome {
    /// The vendor / merchant paid.
    pub vendor: String,
    /// The amount moved, in USD-cents (the same amount the budget cell drew).
    pub amount_cents: i64,
    /// The Stripe payment handle the CLI reported (`lsrq_…` spend-request / `pi_…`
    /// PaymentIntent), or a deterministic stand-in in the recorded transport.
    pub payment_id: String,
    /// The payment method used (`virtual-card` for a checkout form, `spt` for an
    /// HTTP-402 Shared-Payment-Token merchant).
    pub method: String,
    /// A human, **key-redacted** summary of the call.
    pub detail: String,
    /// `true` iff this came from the real CLI; `false` for the recorded transport.
    pub live: bool,
}

/// The Stripe Skills transport seam: provision a SaaS, pay a vendor. The operator
/// tools call this behind the cap · budget · receipt rail; the impl is either the
/// live CLI transport or the recorded stub.
pub trait StripeSkills: Send + Sync {
    /// Provision `provider/service` (the Stripe Projects skill). `amount_cents` is
    /// the tier cost the rail already drew from the budget (recorded for the
    /// receipt; the CLI's own tier prompt is the live charge).
    fn provision(
        &self,
        provider: &str,
        service: &str,
        amount_cents: i64,
    ) -> Result<ProvisionOutcome, String>;

    /// Pay `vendor` `amount_cents` (the Stripe Link skill). The amount was already
    /// drawn from the budget cell (over-ceiling refused before this runs).
    fn pay(&self, vendor: &str, amount_cents: i64, memo: &str) -> Result<PayOutcome, String>;

    /// `"live"` (the real CLIs) or `"recorded"` (the stub transport).
    fn mode(&self) -> &'static str;
}

// ── the recorded (stub) transport ─────────────────────────────────────────────

/// The faithful **recorded** Stripe Skills transport: deterministic, offline, and
/// clearly labelled — it never fakes a live success. The green-test + offline-demo
/// default; [`detect`] swaps in [`CliStripeSkills`] the moment the CLIs + key land.
#[derive(Clone, Debug, Default)]
pub struct RecordedStripeSkills;

impl RecordedStripeSkills {
    /// A recorded transport.
    pub fn new() -> RecordedStripeSkills {
        RecordedStripeSkills
    }
}

/// The honest label every recorded outcome carries, so a reader is never misled
/// into thinking money/infra actually moved.
const RECORDED_NOTE: &str = "(Stripe Skill live leg needs the CLI + a test key)";

impl StripeSkills for RecordedStripeSkills {
    fn provision(
        &self,
        provider: &str,
        service: &str,
        amount_cents: i64,
    ) -> Result<ProvisionOutcome, String> {
        if provider.is_empty() || service.is_empty() {
            return Err("stripe_provision: need a `provider` and a `service`".into());
        }
        let resource_id = synthetic_id("rec-proj", &format!("{provider}/{service}"));
        let synced_creds = recorded_cred_keys(provider);
        Ok(ProvisionOutcome {
            provider: provider.to_string(),
            service: service.to_string(),
            resource_id: resource_id.clone(),
            synced_creds: synced_creds.clone(),
            detail: format!(
                "recorded: `stripe projects add {provider}/{service}` → {resource_id} \
                 (tier {amount_cents}c; synced {}) {RECORDED_NOTE}",
                synced_creds.join(", ")
            ),
            live: false,
        })
    }

    fn pay(&self, vendor: &str, amount_cents: i64, memo: &str) -> Result<PayOutcome, String> {
        if vendor.is_empty() {
            return Err("stripe_pay: need a `vendor`".into());
        }
        if amount_cents <= 0 {
            return Err("stripe_pay: amount_cents must be > 0".into());
        }
        let payment_id = synthetic_id("rec-lsrq", &format!("{vendor}:{amount_cents}:{memo}"));
        Ok(PayOutcome {
            vendor: vendor.to_string(),
            amount_cents,
            payment_id: payment_id.clone(),
            method: "virtual-card".to_string(),
            detail: format!(
                "recorded: `link-cli` pay {amount_cents}c to {vendor} → {payment_id} \
                 {RECORDED_NOTE}"
            ),
            live: false,
        })
    }

    fn mode(&self) -> &'static str {
        "recorded"
    }
}

// ── the live CLI transport ─────────────────────────────────────────────────────

/// A child-process invocation the live transport runs: the program, its args, and
/// the env pairs (the key rides here, **never** in `args`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CliInvocation {
    /// The program to run (`stripe`, `npx`, `link-cli`).
    pub program: String,
    /// Its arguments (no secrets).
    pub args: Vec<String>,
    /// Environment pairs for the child (e.g. `STRIPE_API_KEY=<key>`).
    pub env: Vec<(String, String)>,
}

/// What a CLI invocation returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CliOutput {
    /// The process exit code.
    pub exit: i32,
    /// Captured standard output.
    pub stdout: String,
    /// Captured standard error.
    pub stderr: String,
}

/// A **CLI runner**: spawn `inv` and report its [`CliOutput`] (or an `Err` on a
/// spawn failure). The bin injects a `std::process::Command` runner; tests inject
/// a deterministic stand-in (so the live path's build, parsing, and redaction are
/// proven without the real CLIs installed).
pub type CliRunner = Box<dyn Fn(&CliInvocation) -> Result<CliOutput, String> + Send + Sync>;

/// The **live** Stripe Skills transport: shells the real `stripe projects` /
/// `link-cli` CLIs through an injected [`CliRunner`], with the BYO key read at
/// runtime, passed via the child environment, and redacted from every captured
/// byte before it reaches a summary / receipt / log.
pub struct CliStripeSkills {
    key: String,
    /// `npx` prefix for the link CLI when it is not on PATH as `link-cli`
    /// (`@stripe/link-cli`). Empty → call `link-cli` directly.
    use_npx: bool,
    runner: CliRunner,
}

impl CliStripeSkills {
    /// A live transport authenticating with `key`, running CLIs through `runner`.
    /// `use_npx` calls the link CLI as `npx @stripe/link-cli` (vs a global
    /// `link-cli`). The bin passes the real process runner; tests pass a stand-in.
    pub fn new(key: impl Into<String>, use_npx: bool, runner: CliRunner) -> CliStripeSkills {
        CliStripeSkills {
            key: key.into(),
            use_npx,
            runner,
        }
    }

    /// A live transport over the real OS process runner ([`real_cli_runner`]).
    pub fn with_real_runner(key: impl Into<String>, use_npx: bool) -> CliStripeSkills {
        CliStripeSkills::new(key, use_npx, Box::new(real_cli_runner))
    }

    /// Redact the key from a captured string (defense in depth — the key rides in
    /// the env, but a CLI could still echo it).
    fn redact(&self, s: &str) -> String {
        redact_secret(s, &self.key)
    }

    /// The link-CLI invocation prefix (`link-cli …` or `npx @stripe/link-cli …`).
    fn link_cli(&self, mut tail: Vec<String>) -> CliInvocation {
        let (program, mut args) = if self.use_npx {
            ("npx".to_string(), vec!["@stripe/link-cli".to_string()])
        } else {
            ("link-cli".to_string(), Vec::new())
        };
        args.append(&mut tail);
        CliInvocation {
            program,
            args,
            env: vec![("STRIPE_API_KEY".to_string(), self.key.clone())],
        }
    }
}

impl StripeSkills for CliStripeSkills {
    fn provision(
        &self,
        provider: &str,
        service: &str,
        amount_cents: i64,
    ) -> Result<ProvisionOutcome, String> {
        if provider.is_empty() || service.is_empty() {
            return Err("stripe_provision: need a `provider` and a `service`".into());
        }
        // `stripe projects add <provider>/<service>` — the Stripe Projects skill.
        let inv = CliInvocation {
            program: "stripe".to_string(),
            args: vec![
                "projects".to_string(),
                "add".to_string(),
                format!("{provider}/{service}"),
            ],
            env: vec![("STRIPE_API_KEY".to_string(), self.key.clone())],
        };
        let out = (self.runner)(&inv)?;
        let stdout = self.redact(&out.stdout);
        let stderr = self.redact(&out.stderr);
        if out.exit != 0 {
            return Err(format!(
                "stripe projects add {provider}/{service} failed [exit {}]: {}",
                out.exit,
                first_line(&stderr).unwrap_or_else(|| first_line(&stdout).unwrap_or_default())
            ));
        }
        let resource_id = scan_id(&stdout, &["proj_", "prj_", "project_"])
            .unwrap_or_else(|| synthetic_id("live-proj", &format!("{provider}/{service}")));
        let synced_creds = scan_cred_keys(&stdout);
        Ok(ProvisionOutcome {
            provider: provider.to_string(),
            service: service.to_string(),
            resource_id,
            synced_creds,
            detail: format!(
                "live: stripe projects add {provider}/{service} (tier {amount_cents}c) — {}",
                first_line(&stdout).unwrap_or_else(|| "ok".to_string())
            ),
            live: true,
        })
    }

    fn pay(&self, vendor: &str, amount_cents: i64, memo: &str) -> Result<PayOutcome, String> {
        if vendor.is_empty() {
            return Err("stripe_pay: need a `vendor`".into());
        }
        if amount_cents <= 0 {
            return Err("stripe_pay: amount_cents must be > 0".into());
        }
        // `link-cli spend-request create --amount <cents> --merchant <vendor>` —
        // the Stripe Link skill. (Flag names per the live skill docs; the budget /
        // cap / receipt teeth do not depend on the exact flag spelling.)
        let inv = self.link_cli(vec![
            "spend-request".to_string(),
            "create".to_string(),
            "--amount".to_string(),
            amount_cents.to_string(),
            "--merchant".to_string(),
            vendor.to_string(),
            "--memo".to_string(),
            memo.to_string(),
        ]);
        let out = (self.runner)(&inv)?;
        let stdout = self.redact(&out.stdout);
        let stderr = self.redact(&out.stderr);
        if out.exit != 0 {
            return Err(format!(
                "link-cli pay {amount_cents}c to {vendor} failed [exit {}]: {}",
                out.exit,
                first_line(&stderr).unwrap_or_else(|| first_line(&stdout).unwrap_or_default())
            ));
        }
        let payment_id = scan_id(&stdout, &["lsrq_", "pi_", "pm_"])
            .unwrap_or_else(|| synthetic_id("live-lsrq", &format!("{vendor}:{amount_cents}")));
        Ok(PayOutcome {
            vendor: vendor.to_string(),
            amount_cents,
            payment_id,
            method: "spt".to_string(),
            detail: format!(
                "live: link-cli pay {amount_cents}c to {vendor} — {}",
                first_line(&stdout).unwrap_or_else(|| "ok".to_string())
            ),
            live: true,
        })
    }

    fn mode(&self) -> &'static str {
        "live"
    }
}

// ── detection + the real OS runner ────────────────────────────────────────────

/// Pick the transport: the **live** [`CliStripeSkills`] when a key is present AND
/// the `stripe` CLI is on PATH (the link CLI is reachable via `npx` as a
/// fallback); the **recorded** stub otherwise. Reads `STRIPE_API_KEY` then
/// `~/.stripekey`. The returned transport is ready to wire onto the operator
/// toolkit with [`crate::tools::OperatorTools::with_stripe_skills`].
pub fn detect() -> Box<dyn StripeSkills> {
    match resolve_key() {
        Some(key) if cli_on_path("stripe") => {
            // The link CLI: prefer a global `link-cli`, else go through `npx`.
            let use_npx = !cli_on_path("link-cli");
            Box::new(CliStripeSkills::with_real_runner(key, use_npx))
        }
        _ => Box::new(RecordedStripeSkills::new()),
    }
}

/// A one-line label for the chosen transport (for the demo banner): whether the
/// live leg is armed, and what unlocks it if not.
pub fn status_line() -> String {
    let key = resolve_key().is_some();
    let stripe = cli_on_path("stripe");
    match (key, stripe) {
        (true, true) => {
            "LIVE — `stripe` CLI + key present (real test-mode provision + pay)".to_string()
        }
        (true, false) => "RECORDED — key present but `stripe` CLI not on PATH \
             (install stripe-cli + the projects plugin for the live leg)"
            .to_string(),
        (false, _) => "RECORDED — set ~/.stripekey or STRIPE_API_KEY + install the Stripe \
             CLIs for the live leg"
            .to_string(),
    }
}

/// Resolve the Stripe key: `STRIPE_API_KEY` env, then `~/.stripekey`. Trimmed,
/// non-empty, or `None`.
pub fn resolve_key() -> Option<String> {
    if let Ok(k) = std::env::var("STRIPE_API_KEY") {
        let k = k.trim().to_string();
        if !k.is_empty() {
            return Some(k);
        }
    }
    let home = std::env::var_os("HOME")?;
    let path = std::path::Path::new(&home).join(".stripekey");
    let raw = std::fs::read_to_string(path).ok()?;
    let k = raw.trim().to_string();
    if k.is_empty() { None } else { Some(k) }
}

/// `true` iff `prog` resolves on PATH (a `command -v` style probe).
fn cli_on_path(prog: &str) -> bool {
    Command::new(prog)
        .arg("--version")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// The real OS process runner: spawn the invocation, set its env, capture
/// stdout/stderr/exit. The bin wires this into [`CliStripeSkills`].
pub fn real_cli_runner(inv: &CliInvocation) -> Result<CliOutput, String> {
    let mut cmd = Command::new(&inv.program);
    cmd.args(&inv.args)
        .stdin(std::process::Stdio::null())
        .env_clear_keep_path();
    for (k, v) in &inv.env {
        cmd.env(k, v);
    }
    let out = cmd
        .output()
        .map_err(|e| format!("spawn {}: {e}", inv.program))?;
    Ok(CliOutput {
        exit: out.status.code().unwrap_or(-1),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    })
}

/// `std::process::Command` helper: keep only `PATH`/`HOME` from the ambient env
/// (so the child gets the explicit Stripe env we set, plus enough to find the
/// CLI), then layer the invocation's own pairs on top.
trait CommandEnvExt {
    fn env_clear_keep_path(&mut self) -> &mut Self;
}
impl CommandEnvExt for Command {
    fn env_clear_keep_path(&mut self) -> &mut Self {
        let path = std::env::var_os("PATH");
        let home = std::env::var_os("HOME");
        self.env_clear();
        if let Some(p) = path {
            self.env("PATH", p);
        }
        if let Some(h) = home {
            self.env("HOME", h);
        }
        self
    }
}

// ── helpers (redaction, parsing, synthetic ids) ───────────────────────────────

/// Replace every occurrence of `secret` in `s` with `«redacted»` (no-op for an
/// empty secret). The BYO-key confinement: the key never survives into a summary,
/// a receipt, or a log even if a CLI echoes it.
pub fn redact_secret(s: &str, secret: &str) -> String {
    if secret.is_empty() {
        return s.to_string();
    }
    s.replace(secret, "«redacted»")
}

/// The first non-empty line of `s`, trimmed (for a compact summary).
fn first_line(s: &str) -> Option<String> {
    s.lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .map(String::from)
}

/// Scan whitespace/punctuation tokens for the first one starting with a known
/// id prefix (`lsrq_`, `pi_`, `proj_`, …).
fn scan_id(s: &str, prefixes: &[&str]) -> Option<String> {
    s.split(|c: char| c.is_whitespace() || matches!(c, '"' | '\'' | ',' | ':' | '=' | '(' | ')'))
        .find(|tok| {
            prefixes
                .iter()
                .any(|p| tok.starts_with(p) && tok.len() > p.len())
        })
        .map(|tok| tok.to_string())
}

/// Scan output for credential KEY names that were synced (UPPER_SNAKE tokens that
/// look like env keys, e.g. `DATABASE_URL`). Names only — never values.
fn scan_cred_keys(s: &str) -> Vec<String> {
    let mut keys: Vec<String> = s
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter(|t| looks_like_env_key(t))
        .map(|t| t.to_string())
        .collect();
    keys.sort();
    keys.dedup();
    keys.truncate(8);
    keys
}

/// `true` iff `t` looks like an UPPER_SNAKE env-key name (≥ 4 chars, has an `_`,
/// all uppercase/digits/underscore, starts with a letter).
fn looks_like_env_key(t: &str) -> bool {
    t.len() >= 4
        && t.contains('_')
        && t.starts_with(|c: char| c.is_ascii_uppercase())
        && t.chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
}

/// The credential key names the recorded transport reports for a known provider
/// (representative of what the real `stripe projects add` syncs).
fn recorded_cred_keys(provider: &str) -> Vec<String> {
    match provider {
        "neon" => vec!["DATABASE_URL".to_string()],
        "twilio" => vec![
            "TWILIO_ACCOUNT_SID".to_string(),
            "TWILIO_AUTH_TOKEN".to_string(),
        ],
        "vercel" => vec!["VERCEL_TOKEN".to_string()],
        _ => vec![format!("{}_API_KEY", provider.to_ascii_uppercase())],
    }
}

/// A deterministic, secret-free synthetic id (`<tag>_<12 hex>`) for the recorded
/// transport / a live fallback when the CLI emitted no parseable id.
fn synthetic_id(tag: &str, seed: &str) -> String {
    let mut h = BodyHasher::new(b"dregg-agent-stripe-skill-id-v1");
    h.field(tag.as_bytes()).field(seed.as_bytes());
    let digest = h.finalize();
    let hex: String = digest.iter().take(6).map(|b| format!("{b:02x}")).collect();
    format!("{tag}_{hex}")
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── the recorded transport is deterministic + honestly labelled ───────────
    #[test]
    fn recorded_provision_and_pay_are_deterministic_and_labelled() {
        let s = RecordedStripeSkills::new();
        let p1 = s.provision("neon", "postgres", 1900).unwrap();
        let p2 = s.provision("neon", "postgres", 1900).unwrap();
        assert_eq!(p1, p2, "recorded provision is deterministic");
        assert!(!p1.live, "recorded is never labelled live");
        assert!(
            p1.detail.contains(RECORDED_NOTE),
            "honest label: {}",
            p1.detail
        );
        assert!(
            p1.synced_creds.contains(&"DATABASE_URL".to_string()),
            "neon syncs DATABASE_URL: {:?}",
            p1.synced_creds
        );

        let pay = s.pay("openai", 500, "inference").unwrap();
        assert_eq!(pay.amount_cents, 500);
        assert!(!pay.live);
        assert!(pay.payment_id.starts_with("rec-lsrq_"));
        assert!(pay.detail.contains(RECORDED_NOTE));
        assert_eq!(s.mode(), "recorded");
    }

    #[test]
    fn recorded_rejects_empty_args() {
        let s = RecordedStripeSkills::new();
        assert!(s.provision("", "x", 1).is_err());
        assert!(s.pay("", 1, "").is_err());
        assert!(s.pay("v", 0, "").is_err(), "non-positive amount refused");
    }

    /// A fake CLI runner returning canned `stripe projects add` / `link-cli`
    /// output — the live path's build, parsing, and REDACTION proven without the
    /// real CLIs. The canned output deliberately ECHOES the key so the redaction
    /// tooth is observable.
    fn fake_runner(key: &'static str) -> CliRunner {
        Box::new(move |inv: &CliInvocation| {
            // The key must ride in the env, NEVER in the args.
            assert!(
                !inv.args.iter().any(|a| a.contains(key)),
                "the key must never appear in argv: {:?}",
                inv.args
            );
            assert!(
                inv.env
                    .iter()
                    .any(|(k, v)| k == "STRIPE_API_KEY" && v == key),
                "the key must ride in STRIPE_API_KEY env"
            );
            let stdout = if inv.program == "stripe" {
                // Echo the key in the output to prove redaction scrubs it.
                format!(
                    "Provisioning… created proj_abc123 using key {key}\n\
                     Synced DATABASE_URL to .env\n"
                )
            } else {
                format!("Spend request created: lsrq_xyz789 (auth via {key})\n")
            };
            Ok(CliOutput {
                exit: 0,
                stdout,
                stderr: String::new(),
            })
        })
    }

    // ── the live transport shells the CLIs, parses ids, REDACTS the key ───────
    #[test]
    fn live_provision_parses_id_and_redacts_the_key() {
        let key = "sk_test_LIVE_SECRET_DO_NOT_LEAK";
        let s = CliStripeSkills::new(key, false, fake_runner(key));
        let out = s.provision("neon", "postgres", 1900).unwrap();
        assert!(out.live, "labelled live");
        assert_eq!(out.resource_id, "proj_abc123", "parsed the project id");
        assert!(
            out.synced_creds.contains(&"DATABASE_URL".to_string()),
            "scanned the synced cred KEY name: {:?}",
            out.synced_creds
        );
        // THE CONFINEMENT TOOTH: the key never survives into the detail.
        assert!(
            !out.detail.contains(key),
            "the key must be redacted from the summary: {}",
            out.detail
        );
        assert_eq!(s.mode(), "live");
    }

    #[test]
    fn live_pay_parses_id_and_redacts_the_key() {
        let key = "sk_test_LIVE_SECRET_DO_NOT_LEAK";
        let s = CliStripeSkills::new(key, true, fake_runner(key)); // use_npx
        let out = s.pay("openai", 500, "inference").unwrap();
        assert!(out.live);
        assert_eq!(out.payment_id, "lsrq_xyz789", "parsed the spend-request id");
        assert_eq!(out.amount_cents, 500);
        assert!(!out.detail.contains(key), "key redacted: {}", out.detail);
    }

    // ── a CLI failure (non-zero exit) is a real error, key-redacted ───────────
    #[test]
    fn live_cli_failure_is_an_error_with_the_key_redacted() {
        let key = "sk_test_BOOM";
        let runner: CliRunner = Box::new(move |_inv| {
            Ok(CliOutput {
                exit: 1,
                stdout: String::new(),
                stderr: format!("auth failed for key {key}\n"),
            })
        });
        let s = CliStripeSkills::new(key, false, runner);
        let err = s
            .pay("openai", 500, "x")
            .expect_err("a non-zero exit is an error");
        assert!(err.contains("failed"), "{err}");
        assert!(
            !err.contains(key),
            "the key must be redacted from errors: {err}"
        );
    }

    #[test]
    fn redact_scrubs_every_occurrence() {
        let s = "key=abc123 again abc123 end";
        assert_eq!(
            redact_secret(s, "abc123"),
            "key=«redacted» again «redacted» end"
        );
        assert_eq!(redact_secret(s, ""), s, "empty secret is a no-op");
    }

    #[test]
    fn scan_id_finds_known_prefixes_only() {
        assert_eq!(
            scan_id("made lsrq_777 ok", &["lsrq_"]),
            Some("lsrq_777".to_string())
        );
        assert_eq!(scan_id("nothing here", &["lsrq_"]), None);
        // A bare prefix with no suffix is not an id.
        assert_eq!(scan_id("lsrq_ alone", &["lsrq_"]), None);
    }
}
