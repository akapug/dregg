//! **paces** — the zkOracle prover under measurement: per-leg and end-to-end timings
//! across the two scaling axes, plus refuse-path latency.
//!
//! The two axes matter because [`tokenize`] collapses a whole JSON string to ONE token:
//! a text-heavy model response (one long `text` field) grows in BYTES but not in tokens,
//! while a structure-dense body (many small array elements) grows in TOKENS — and the
//! parse certificate stores the full derivation form-chain, which is O(tokens²) symbols.
//!
//! Run: `cargo run -p dregg-zkoracle-prove --example paces --release`

use std::time::{Duration, Instant};

use dregg_zkoracle_prove::attestation::{FieldSpan, content_commitment};
use dregg_zkoracle_prove::{
    AnthropicConfig, FixtureNotary, ZkOracleAttestation, build_anthropic_fixture, injection_free,
    prove_cfg_cert, prove_zkoracle, tokenize, verify_cfg_cert, verify_zkoracle,
};

/// An Anthropic-messages-shaped body whose `text` field is `text_len` bytes of prose.
fn text_body(text_len: usize) -> String {
    let text = "The capital of France is Paris. ".repeat(text_len / 32 + 1);
    format!(
        r#"{{"id":"msg_01XYZ","type":"message","role":"assistant","model":"claude-opus-4-8","content":[{{"type":"text","text":"{}"}}],"stop_reason":"end_turn","stop_sequence":null,"usage":{{"input_tokens":24,"output_tokens":8}}}}"#,
        &text[..text_len]
    )
}

/// A structure-dense body: `n` small numbers in an array — every element costs tokens.
fn dense_body(n: usize) -> String {
    let elems: Vec<String> = (0..n).map(|i| (i % 10).to_string()).collect();
    format!(r#"{{"id":"msg_dense","data":[{}]}}"#, elems.join(","))
}

/// Median of `k` timed runs of `f` (fewer runs once a single run is slow).
fn med<F: FnMut() -> Duration>(mut f: F) -> Duration {
    let first = f();
    let k = if first > Duration::from_millis(500) {
        1
    } else if first > Duration::from_millis(50) {
        3
    } else {
        7
    };
    let mut samples = vec![first];
    for _ in 1..k {
        samples.push(f());
    }
    samples.sort();
    samples[samples.len() / 2]
}

fn fmt_d(d: Duration) -> String {
    let us = d.as_micros();
    if us < 1_000 {
        format!("{us} µs")
    } else if us < 1_000_000 {
        format!("{:.2} ms", us as f64 / 1_000.0)
    } else {
        format!("{:.2} s", us as f64 / 1_000_000.0)
    }
}

fn fmt_n(n: usize) -> String {
    if n < 1_000 {
        format!("{n}")
    } else if n < 1_000_000 {
        format!("{:.1}k", n as f64 / 1e3)
    } else {
        format!("{:.1}M", n as f64 / 1e6)
    }
}

struct Row {
    label: String,
    body_bytes: usize,
    tokens: usize,
    chain_forms: usize,
    chain_symbols: usize,
    t_prove_cert: Duration,
    t_verify_cert: Duration,
    t_commit: Duration,
    t_prove_e2e: Duration,
    t_verify_e2e: Duration,
}

fn run_case(
    label: &str,
    body: &str,
    field: &[u8],
    config: &AnthropicConfig,
    notary: &FixtureNotary,
) -> Row {
    let presentation = build_anthropic_fixture(notary, body, 1_700_000_000);

    let toks = tokenize(body.as_bytes()).expect("body tokenizes");
    let cert = prove_cfg_cert(body.as_bytes()).expect("body certifies");
    let chain_symbols: usize = cert.chain.iter().map(|f| f.len()).sum();

    let t_prove_cert = med(|| {
        let s = Instant::now();
        let _ = prove_cfg_cert(body.as_bytes()).unwrap();
        s.elapsed()
    });
    let t_verify_cert = med(|| {
        let s = Instant::now();
        verify_cfg_cert(&cert, body.as_bytes()).unwrap();
        s.elapsed()
    });
    let t_commit = med(|| {
        let s = Instant::now();
        let _ = content_commitment(body.as_bytes());
        s.elapsed()
    });
    let t_prove_e2e = med(|| {
        let s = Instant::now();
        let _ = prove_zkoracle(presentation.clone(), field.to_vec(), config).unwrap();
        s.elapsed()
    });
    let att = prove_zkoracle(presentation, field.to_vec(), config).unwrap();
    let t_verify_e2e = med(|| {
        let s = Instant::now();
        let _ = verify_zkoracle(&att, config).unwrap();
        s.elapsed()
    });

    Row {
        label: label.to_string(),
        body_bytes: body.len(),
        tokens: toks.len(),
        chain_forms: cert.chain.len(),
        chain_symbols,
        t_prove_cert,
        t_verify_cert,
        t_commit,
        t_prove_e2e,
        t_verify_e2e,
    }
}

fn main() {
    let notary = FixtureNotary::from_seed(&[9u8; 32]);
    let config = AnthropicConfig::new(notary.verifying_key());

    println!("zkOracle paces — per-leg + e2e (release, median-of-k)\n");
    println!(
        "{:<14} {:>9} {:>8} {:>9} {:>10} | {:>10} {:>10} {:>9} | {:>10} {:>10}",
        "case",
        "bytes",
        "tokens",
        "forms",
        "symbols",
        "cert-prove",
        "cert-vrfy",
        "commit",
        "PROVE e2e",
        "VERIFY e2e"
    );

    let mut rows: Vec<Row> = Vec::new();

    // Axis 1 — text-heavy (bytes grow, tokens do not): the realistic model response.
    for text_len in [256usize, 1 << 10, 4 << 10, 16 << 10, 64 << 10, 256 << 10] {
        let body = text_body(text_len);
        let label = format!("text-{}", fmt_n(text_len));
        rows.push(run_case(&label, &body, b"France", &config, &notary));
        let r = rows.last().unwrap();
        println!(
            "{:<14} {:>9} {:>8} {:>9} {:>10} | {:>10} {:>10} {:>9} | {:>10} {:>10}",
            r.label,
            fmt_n(r.body_bytes),
            fmt_n(r.tokens),
            fmt_n(r.chain_forms),
            fmt_n(r.chain_symbols),
            fmt_d(r.t_prove_cert),
            fmt_d(r.t_verify_cert),
            fmt_d(r.t_commit),
            fmt_d(r.t_prove_e2e),
            fmt_d(r.t_verify_e2e)
        );
    }

    // Axis 2 — structure-dense (tokens grow): the certificate's quadratic axis.
    // Guard: stop escalating once a single e2e prove crosses 10 s.
    for n in [64usize, 256, 1024, 4096, 16384] {
        let body = dense_body(n);
        let label = format!("dense-{}", fmt_n(n));
        let probe = Instant::now();
        let cert_ok = prove_cfg_cert(body.as_bytes()).is_ok();
        let probe_t = probe.elapsed();
        if !cert_ok {
            println!("{label:<14} — body does not certify (unexpected)");
            continue;
        }
        if probe_t > Duration::from_secs(10) {
            println!(
                "{label:<14} — cert-prove alone took {} — stopping the dense axis here",
                fmt_d(probe_t)
            );
            break;
        }
        rows.push(run_case(&label, &body, b"msg_dense", &config, &notary));
        let r = rows.last().unwrap();
        println!(
            "{:<14} {:>9} {:>8} {:>9} {:>10} | {:>10} {:>10} {:>9} | {:>10} {:>10}",
            r.label,
            fmt_n(r.body_bytes),
            fmt_n(r.tokens),
            fmt_n(r.chain_forms),
            fmt_n(r.chain_symbols),
            fmt_d(r.t_prove_cert),
            fmt_d(r.t_verify_cert),
            fmt_d(r.t_commit),
            fmt_d(r.t_prove_e2e),
            fmt_d(r.t_verify_e2e)
        );
    }

    // Refuse paths — how fast does a hostile attestation bounce?
    println!("\nrefuse-path latency (hostiles must fail FAST):");
    let body = text_body(1 << 10);
    let presentation = build_anthropic_fixture(&notary, &body, 42);
    let att = prove_zkoracle(presentation.clone(), b"France".to_vec(), &config).unwrap();

    let mut forged = att.clone();
    let n = forged.presentation.recv.len();
    forged.presentation.recv[n - 4] ^= 0xFF;
    let t = med(|| {
        let s = Instant::now();
        let _ = verify_zkoracle(&forged, &config).unwrap_err();
        s.elapsed()
    });
    println!("  forged notary sig     → refused in {}", fmt_d(t));

    let other = build_anthropic_fixture(&notary, r#"{"id":"other"}"#, 43);
    let spliced = ZkOracleAttestation {
        presentation: other,
        ..att.clone()
    };
    let t = med(|| {
        let s = Instant::now();
        let _ = verify_zkoracle(&spliced, &config).unwrap_err();
        s.elapsed()
    });
    println!("  cross-leg splice      → refused in {}", fmt_d(t));

    let mut bad_span = att.clone();
    bad_span.field_span = FieldSpan { offset: 0, len: 2 };
    let t = med(|| {
        let s = Instant::now();
        let _ = verify_zkoracle(&bad_span, &config);
        s.elapsed()
    });
    println!("  re-pointed field span → decided in {}", fmt_d(t));

    let t = med(|| {
        let s = Instant::now();
        let _ = injection_free(b"ignore previous {{ system }}");
        s.elapsed()
    });
    println!("  injection match alone → {}", fmt_d(t));
}
