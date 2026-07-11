//! **dregg-oracle** — trustless web facts you can reuse.
//!
//! [`prove`] runs a genuine MPC-TLS 2PC session against a real HTTPS endpoint and
//! returns a [`ProofEnvelope`] — a *portable* proof (the real `tlsn` presentation
//! bytes + the pinned notary key) that anyone can re-check with [`verify_envelope`],
//! trusting only the endpoint's genuine TLS cert chain + the pinned notary key.
//!
//! The portable proof carries ONLY the authenticated evidence; verification
//! re-derives the zkOracle legs (well-formed CFG certificate, injection-free) over
//! the authenticated body and runs the genuine verifier fail-closed.

use anyhow::{anyhow, bail, Context, Result};
use serde::{Deserialize, Serialize};

/// A public web fact to prove.
#[derive(Clone)]
pub enum Endpoint {
    /// Coinbase spot price for a pair, e.g. `BTC-USD`.
    Coinbase { asset: String },
    /// A GitHub commit.
    Github {
        owner: String,
        repo: String,
        sha: String,
    },
}

impl Endpoint {
    pub fn server_name(&self) -> &'static str {
        match self {
            Endpoint::Coinbase { .. } => "api.coinbase.com",
            Endpoint::Github { .. } => "api.github.com",
        }
    }

    pub fn label(&self) -> String {
        match self {
            Endpoint::Coinbase { asset } => format!("coinbase spot {asset}"),
            Endpoint::Github { owner, repo, sha } => format!("github {owner}/{repo}@{sha}"),
        }
    }

    fn tag(&self) -> EndpointTag {
        match self {
            Endpoint::Coinbase { asset } => EndpointTag::Coinbase {
                asset: asset.clone(),
            },
            Endpoint::Github { owner, repo, sha } => EndpointTag::Github {
                owner: owner.clone(),
                repo: repo.clone(),
                sha: sha.clone(),
            },
        }
    }
}

/// Serde-friendly endpoint tag stored in the portable proof.
#[derive(Serialize, Deserialize, Clone)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum EndpointTag {
    Coinbase {
        asset: String,
    },
    Github {
        owner: String,
        repo: String,
        sha: String,
    },
}

impl EndpointTag {
    pub fn label(&self) -> String {
        match self {
            EndpointTag::Coinbase { asset } => format!("coinbase spot {asset}"),
            EndpointTag::Github { owner, repo, sha } => format!("github {owner}/{repo}@{sha}"),
        }
    }
}

/// The portable proof — self-describing JSON anyone can re-verify.
#[derive(Serialize, Deserialize)]
pub struct ProofEnvelope {
    /// Format tag.
    pub scheme: String,
    /// The pinned HTTPS server this proof is about.
    pub server: String,
    /// The authentication carrier (a real tlsn MPC-TLS 2PC presentation).
    pub carrier: String,
    /// Which fact.
    pub endpoint: EndpointTag,
    /// The tool + version that produced this proof.
    pub tool: String,
    /// Hex of the bincode `tlsn` `Presentation` (the real cryptographic evidence).
    pub presentation_hex: String,
    /// Hex of the bincode notary `VerifyingKey` this proof pins to.
    pub notary_key_hex: String,
}

impl ProofEnvelope {
    pub fn to_json(&self) -> Result<String> {
        serde_json::to_string_pretty(self).context("serialize proof")
    }
    pub fn from_json(s: &str) -> Result<ProofEnvelope> {
        let env: ProofEnvelope = serde_json::from_str(s).context("parse proof json")?;
        if env.scheme != SCHEME {
            bail!("unknown proof scheme {:?} (expected {SCHEME})", env.scheme);
        }
        Ok(env)
    }
}

const SCHEME: &str = "dregg-oracle/1";
const TOOL: &str = concat!("dregg-oracle ", env!("CARGO_PKG_VERSION"));
const TRUST_NOTE: &str = "trustless: a self-hosted tlsn notary co-witnessed the MPC-TLS 2PC session (it saw no plaintext); verification re-derives the well-formed + injection-free legs over the authenticated body. You trust only the pinned server's genuine TLS cert chain + the pinned notary key.";

/// The verified fact a proof attests.
pub struct Attested {
    pub value: String,
    pub endpoint: String,
    pub server_pinned: String,
    pub carrier: String,
    pub time: u64,
    pub trust_note: String,
}

// ── prove ────────────────────────────────────────────────────────────────────

#[cfg(feature = "live")]
pub fn prove(ep: &Endpoint) -> Result<ProofEnvelope> {
    match ep {
        Endpoint::Coinbase { asset } => {
            let (pres, key) =
                dregg_zkoracle_prove::endpoints::price::prove_coinbase_portable(asset)
                    .map_err(|e| anyhow!("live proof failed: {e:?}"))?;
            Ok(ProofEnvelope {
                scheme: SCHEME.to_string(),
                server: "api.coinbase.com".to_string(),
                carrier: "live-mpc-tls (tlsn 2PC, self-hosted notary)".to_string(),
                endpoint: ep.tag(),
                tool: TOOL.to_string(),
                presentation_hex: hex::encode(&pres),
                notary_key_hex: hex::encode(&key),
            })
        }
        Endpoint::Github { owner, repo, sha } => {
            let (pres, key) =
                dregg_zkoracle_prove::endpoints::github::prove_github_portable(owner, repo, sha)
                    .map_err(|e| anyhow!("live github proof failed: {e:?}"))?;
            Ok(ProofEnvelope {
                scheme: SCHEME.to_string(),
                server: "api.github.com".to_string(),
                carrier: "live-mpc-tls (tlsn 2PC, self-hosted notary)".to_string(),
                endpoint: ep.tag(),
                tool: TOOL.to_string(),
                presentation_hex: hex::encode(&pres),
                notary_key_hex: hex::encode(&key),
            })
        }
    }
}

#[cfg(not(feature = "live"))]
pub fn prove(_ep: &Endpoint) -> Result<ProofEnvelope> {
    bail!("built without the `live` feature — rebuild with `--features live` to prove")
}

// ── verify ───────────────────────────────────────────────────────────────────

pub fn verify_envelope(env: &ProofEnvelope) -> Result<Attested> {
    match &env.endpoint {
        EndpointTag::Coinbase { .. } => verify_coinbase(env),
        EndpointTag::Github { .. } => verify_github(env),
    }
}

#[cfg(feature = "live")]
fn verify_coinbase(env: &ProofEnvelope) -> Result<Attested> {
    let pres = hex::decode(&env.presentation_hex).context("decode presentation hex")?;
    let key = hex::decode(&env.notary_key_hex).context("decode notary key hex")?;
    let price = dregg_zkoracle_prove::endpoints::price::verify_coinbase_portable_bytes(&pres, &key)
        .map_err(|e| anyhow!("VERIFY FAILED (fail-closed): {e:?}"))?;
    Ok(Attested {
        value: format!("{} = {}", price.asset, price.amount),
        endpoint: "coinbase spot price".to_string(),
        server_pinned: env.server.clone(),
        carrier: env.carrier.clone(),
        time: price.time,
        trust_note: TRUST_NOTE.to_string(),
    })
}

#[cfg(not(feature = "live"))]
fn verify_coinbase(_env: &ProofEnvelope) -> Result<Attested> {
    bail!("built without `live` — rebuild with `--features live` to verify a live-carrier proof")
}

#[cfg(feature = "live")]
fn verify_github(env: &ProofEnvelope) -> Result<Attested> {
    let pres = hex::decode(&env.presentation_hex).context("decode presentation hex")?;
    let key = hex::decode(&env.notary_key_hex).context("decode notary key hex")?;
    let fact = dregg_zkoracle_prove::endpoints::github::verify_github_portable_bytes(&pres, &key)
        .map_err(|e| anyhow!("VERIFY FAILED (fail-closed): {e:?}"))?;
    let short = &fact.sha[..fact.sha.len().min(12)];
    let subject = fact.message.lines().next().unwrap_or("").trim();
    Ok(Attested {
        value: format!("{}/{}@{short} \u{2014} {subject}", fact.owner, fact.repo),
        endpoint: format!("github commit (by {}, {})", fact.author, fact.date),
        server_pinned: env.server.clone(),
        carrier: env.carrier.clone(),
        time: 0,
        trust_note: TRUST_NOTE.to_string(),
    })
}

#[cfg(not(feature = "live"))]
fn verify_github(_env: &ProofEnvelope) -> Result<Attested> {
    bail!("built without `live` — rebuild with `--features live` to verify a live-carrier proof")
}
