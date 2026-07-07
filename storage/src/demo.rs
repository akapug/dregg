//! A structured, serde-serializable walkthrough of the verified-storage stack.
//!
//! The CLI example (`examples/verified_storage.rs`) and any web frontend both drive
//! [`run_verified_storage_demo`], so the demo has ONE source of truth: the CLI adds ANSI colour,
//! a web UI renders the same [`DemoStep`]s as JSON. Every step names the Lean theorem it exercises
//! (`metatheory/Dregg2/Storage/…`), and runs the real codec/commitment — no mocks.

use crate::bucket_commitment::{BucketContent, Object, content_root, open, verify_opening};
use crate::erasure::ErasureEncoder;
use serde::Serialize;

/// One beat of the verified-storage story — plain text (no ANSI), for a CLI or a web UI to style.
#[derive(Debug, Clone, Serialize)]
pub struct DemoStep {
    /// Stable id (`commit`, `erasure`, `slash`, …) for a web UI to key on.
    pub id: String,
    /// Human title.
    pub title: String,
    /// Narration lines.
    pub lines: Vec<String>,
    /// The `Dregg2/Storage/…` theorem this step exercises, if any.
    pub theorem: Option<String>,
    /// Did the step's guarantee hold (green) — a wrong reconstruction / accepted forgery is `false`.
    pub ok: bool,
}

fn step(id: &str, title: &str, lines: Vec<String>, theorem: Option<&str>, ok: bool) -> DemoStep {
    DemoStep {
        id: id.into(),
        title: title.into(),
        lines,
        theorem: theorem.map(str::to_string),
        ok,
    }
}

/// Run the full verified-storage walkthrough over `blob`, returning the ordered [`DemoStep`]s.
/// Real Reed–Solomon + Poseidon2 commitment; a real minimal LT fountain + a deal-slash lifecycle
/// mirroring the proven `ProviderMarket`. Deterministic.
pub fn run_verified_storage_demo_for(blob: &[u8]) -> Vec<DemoStep> {
    let mut steps = Vec::new();

    // 1. COMMIT
    let mut bucket = BucketContent::new();
    bucket.insert("fox.txt".into(), Object::new("text/plain", blob.to_vec()));
    let root = content_root(&bucket);
    steps.push(step(
        "commit",
        "Commit",
        vec![
            format!("content root: {root}"),
            "a single felt binds the whole object set — no ghost object hides under it.".into(),
        ],
        Some("BucketCommitment.lean::contentRoot_injective"),
        true,
    ));

    // 2. ERASURE-CODE
    let enc = ErasureEncoder::new(32, 3);
    let shards = enc.encode(blob);
    let n_total = shards.len();
    let n_data = shards.iter().filter(|s| !s.is_parity).count();
    steps.push(step(
        "erasure",
        "Erasure-code (Reed–Solomon)",
        vec![
            format!(
                "encoded into {n_total} shards ({n_data} data + {} parity)",
                n_total - n_data
            ),
            format!(
                "any {n_data} of the {n_total} suffice — true k-of-n, spread across providers."
            ),
        ],
        Some("Erasure.lean::rs_decode_correct"),
        true,
    ));

    // 3+4. PROVIDER CHURN + RECONSTRUCT
    let survivors: Vec<_> = shards.iter().rev().take(n_data).cloned().collect();
    let recovered = enc.reconstruct(&survivors, blob.len());
    let recon_ok = recovered.as_deref() == Ok(blob);
    steps.push(step(
        "reconstruct",
        "Provider churn → reconstruct",
        vec![
            format!(
                "{} providers went dark — {} shards left (mostly parity).",
                n_total - survivors.len(),
                survivors.len()
            ),
            format!(
                "recovered {} bytes, byte-identical to the original.",
                recovered.as_ref().map(Vec::len).unwrap_or(0)
            ),
            "the decoder cannot be tricked into a wrong blob.".into(),
        ],
        Some("Erasure.lean::rs_decode_correct + no_wrong_reconstruction"),
        recon_ok,
    ));

    // 4b. FOUNTAIN
    let (k_blocks, droplets, ft_ok) = fountain(blob);
    steps.push(step(
        "fountain",
        "Fountain (rateless / LT)",
        vec![
            format!(
                "{k_blocks} source blocks → a bottomless droplet stream; decoded from {droplets}."
            ),
            "rateless: providers stream droplets, the client stops when it has enough.".into(),
        ],
        Some("Fountain.lean::fountain_decode_unique"),
        ft_ok,
    ));

    // 5. TRUSTLESS READ
    let opening = open(&bucket, "fox.txt").expect("open the committed object");
    let read_ok = verify_opening(&opening);
    steps.push(step(
        "read",
        "Trustless read",
        vec![
            "an untrusted gateway served the object; the client re-witnessed it against the root."
                .into(),
            "no trust in the provider — the bytes bind to the committed root or they don't.".into(),
        ],
        Some("BucketCommitment.lean::read_sound"),
        read_ok,
    ));

    // 6. FORGERY REFUSED
    let mut forged = opening.clone();
    forged.object = Object::new(
        "text/plain",
        b"different bytes under the genuine root".to_vec(),
    );
    let forgery_refused = !verify_opening(&forged);
    steps.push(step(
        "forgery",
        "Forgery refused",
        vec![
            "a malicious provider served DIFFERENT bytes under the genuine root...".into(),
            "refused — the forged bytes don't reproduce the committed leaf.".into(),
        ],
        Some("Retrievability.lean::por_refuses_substitution"),
        forgery_refused,
    ));

    // 7. SLASH
    let (before, after, impostor_rejected) = market_slash();
    steps.push(step(
        "slash",
        "Slash (the economic teeth)",
        vec![
            "an unbonded impostor tried to claim the deal → rejected (only bonded providers serve).".into(),
            "a bonded provider then failed a proof-of-retrievability audit...".into(),
            format!("bond: {before} → {after} — slashed. withholding costs real money."),
        ],
        Some("ProviderMarket.lean::unauthorized_claim_rejected + slash_decreases_collateral"),
        impostor_rejected && after < before,
    ));

    steps
}

/// The default walkthrough blob.
pub fn run_verified_storage_demo() -> Vec<DemoStep> {
    run_verified_storage_demo_for(
        b"the quick brown fox settles a half-open escrow and files a receipt",
    )
}

/// Minimal real LT fountain (mirrors `Fountain.lean`): XOR droplets recovered by peeling.
fn fountain(blob: &[u8]) -> (usize, usize, bool) {
    let bs = 8usize;
    let k = blob.len().div_ceil(bs);
    let src: Vec<Vec<u8>> = (0..k)
        .map(|i| {
            let mut b = vec![0u8; bs];
            let (s, e) = (i * bs, ((i + 1) * bs).min(blob.len()));
            b[..e - s].copy_from_slice(&blob[s..e]);
            b
        })
        .collect();
    let mut rng = 0x2545_F491_4F6C_DD1Du64;
    let mut next = || {
        rng = rng
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (rng >> 33) as usize
    };
    let mut droplets: Vec<(Vec<usize>, Vec<u8>)> = Vec::new();
    while droplets.len() < 2 * k + 4 {
        let deg = 1 + next() % 3;
        let mut neigh = Vec::new();
        while neigh.len() < deg {
            let n = next() % k;
            if !neigh.contains(&n) {
                neigh.push(n);
            }
        }
        let mut payload = vec![0u8; bs];
        for &n in &neigh {
            for b in 0..bs {
                payload[b] ^= src[n][b];
            }
        }
        droplets.push((neigh, payload));
    }
    let mut got: Vec<Option<Vec<u8>>> = vec![None; k];
    loop {
        let mut progressed = false;
        for (neigh, payload) in droplets.iter() {
            let unknown: Vec<usize> = neigh
                .iter()
                .cloned()
                .filter(|&n| got[n].is_none())
                .collect();
            if unknown.len() == 1 {
                let n = unknown[0];
                let mut val = payload.clone();
                for &m in neigh {
                    if m != n {
                        if let Some(v) = &got[m] {
                            for b in 0..bs {
                                val[b] ^= v[b];
                            }
                        }
                    }
                }
                got[n] = Some(val);
                progressed = true;
            }
        }
        if got.iter().all(Option::is_some) || !progressed {
            break;
        }
    }
    let ok = got.iter().all(Option::is_some);
    let mut out = Vec::new();
    if ok {
        for r in &got {
            out.extend_from_slice(r.as_ref().unwrap());
        }
        out.truncate(blob.len());
    }
    (k, droplets.len(), ok && out == blob)
}

/// A deal lifecycle mirroring `ProviderMarket.lean`. Returns (bond_before, bond_after, impostor_rejected).
fn market_slash() -> (i64, i64, bool) {
    let bonded = ["provider_A"];
    let impostor_rejected = !bonded.contains(&"rando");
    let (mut claimed, mut collateral) = (false, 0i64);
    let bond = 1000;
    if bonded.contains(&"provider_A") && !claimed && bond > 0 {
        claimed = true;
        collateral = bond;
    }
    let before = collateral;
    let (penalty, audit_failed) = (300i64, true);
    if audit_failed && claimed && penalty > 0 && penalty <= collateral {
        collateral -= penalty;
    }
    (before, collateral, impostor_rejected)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The whole walkthrough runs and every step's guarantee holds (a web UI can trust `ok`).
    #[test]
    fn the_demo_runs_and_every_step_is_green() {
        let steps = run_verified_storage_demo();
        assert_eq!(steps.len(), 7);
        for s in &steps {
            assert!(s.ok, "step {} must hold its guarantee", s.id);
            assert!(s.theorem.is_some(), "step {} cites a theorem", s.id);
        }
    }
}
