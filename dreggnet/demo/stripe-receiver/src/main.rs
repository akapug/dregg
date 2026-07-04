//! `dreggnet-stripe-receiver` — a local Stripe webhook endpoint that runs the
//! GENUINE breadstuffs `stripe_mirror` verify+mint path on every inbound event.
//!
//! It is the on-camera "a REAL Stripe test event funds the agent's credit" step:
//!
//! ```text
//!   stripe trigger payment_intent.succeeded   (Stripe's servers, real signature)
//!        │  Stripe CLI: stripe listen --forward-to localhost:4242/webhook
//!        ▼
//!   THIS receiver  →  StripeWebhookEvent { payload, Stripe-Signature }
//!        │            StripeMirrorState::mint_against_webhook   (the real code)
//!        ▼            → Effect::Mint { target, amount }  (conserved USD-credit)
//!   the agent's dregg cell is funded; the running credit is printed.
//! ```
//!
//! The verification (HMAC-SHA256 over `"{t}.{body}"`, constant-time compare,
//! replay-window, amount/currency bounds, double-mint dedup on the payment-intent
//! id) is breadstuffs' real `dregg-bridge::stripe_mirror` — not a re-implementation.
//! A forged signature, a stale timestamp, a wrong currency, or a replayed payment
//! is refused exactly as the substrate refuses it.
//!
//! ## Configuration (env)
//!
//! - `STRIPE_WEBHOOK_SECRET` (or `DREGG_STRIPE_SECRET`) — the `whsec_…` signing
//!   secret `stripe listen` prints. REQUIRED. This is the verifying key.
//! - `DREGG_STRIPE_PORT` — listen port (default `4242`).
//! - `DREGG_STRIPE_CURRENCY` — accepted ISO-4217 currency (default `usd`).
//! - `DREGG_STRIPE_MIN_CENTS` / `DREGG_STRIPE_MAX_CENTS` — amount bounds
//!   (defaults `50` / `100000000`).
//! - `DREGG_STRIPE_NO_CLOCK` — if set, skip the replay-window timestamp check
//!   (use for replaying a recorded fixture whose `t=` is old).

use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::time::{SystemTime, UNIX_EPOCH};

use dregg_bridge::stripe_mirror::{
    StripeMint, StripeMirrorConfig, StripeMirrorError, StripeMirrorState, StripeWebhookEvent,
    DEFAULT_TOLERANCE_SECS,
};

fn env_or(key: &str, default: &str) -> String {
    std::env::var(key).unwrap_or_else(|_| default.to_string())
}

fn decode_hex32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, b) in out.iter_mut().enumerate() {
        *b = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).ok()?;
    }
    Some(out)
}

fn main() {
    let secret = std::env::var("STRIPE_WEBHOOK_SECRET")
        .or_else(|_| std::env::var("DREGG_STRIPE_SECRET"))
        .unwrap_or_default();
    if secret.is_empty() {
        eprintln!(
            "error: set STRIPE_WEBHOOK_SECRET (the whsec_… that `stripe listen` prints), \
             or DREGG_STRIPE_SECRET for a recorded-fixture run."
        );
        std::process::exit(2);
    }

    let port: u16 = env_or("DREGG_STRIPE_PORT", "4242").parse().unwrap_or(4242);
    let currency = env_or("DREGG_STRIPE_CURRENCY", "usd");
    let min_cents: u64 = env_or("DREGG_STRIPE_MIN_CENTS", "50").parse().unwrap_or(50);
    let max_cents: u64 = env_or("DREGG_STRIPE_MAX_CENTS", "100000000")
        .parse()
        .unwrap_or(100_000_000);
    let asset = std::env::var("DREGG_STRIPE_ASSET")
        .ok()
        .and_then(|h| decode_hex32(&h))
        .unwrap_or([0xCDu8; 32]); // USD-credit issuer-well / token_id
    let check_clock = std::env::var("DREGG_STRIPE_NO_CLOCK").is_err();

    let mut mirror = StripeMirrorState::new(StripeMirrorConfig {
        asset,
        webhook_secret: secret.into_bytes(),
        currency: currency.clone(),
        min_cents,
        max_cents,
    });

    let addr = format!("127.0.0.1:{port}");
    let listener = match TcpListener::bind(&addr) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: cannot bind {addr}: {e}");
            std::process::exit(1);
        }
    };

    println!("dreggnet-stripe-receiver listening on http://{addr}/webhook");
    println!(
        "  currency={currency}  bounds=[{min_cents}, {max_cents}] cents  clock_check={check_clock}"
    );
    println!("  point Stripe at it:  stripe listen --forward-to localhost:{port}/webhook");
    println!("  (every event is verified + minted by the real dregg-bridge stripe_mirror)");
    println!();

    let mut running_credit: u64 = 0;

    // Sequential accept loop: the mirror state (dedup set, supply) is single-owner.
    for conn in listener.incoming() {
        let stream = match conn {
            Ok(s) => s,
            Err(e) => {
                eprintln!("accept error: {e}");
                continue;
            }
        };
        if let Err(e) = handle(stream, &mut mirror, check_clock, &mut running_credit) {
            eprintln!("connection error: {e}");
        }
    }
}

/// The pure verify→mint seam: drive the GENUINE breadstuffs `stripe_mirror`
/// verify+mint over one raw webhook (raw body + `Stripe-Signature` header). This
/// is the whole DreggNet-plane action — HMAC-SHA256 signature verify, replay
/// window (when `now` is `Some`), amount/currency bounds, the consume-once payment
/// dedup, the conservation accounting, and the REAL `Effect::Mint` — with no I/O,
/// so the mock-webhook proofs exercise the identical path the HTTP handler does.
fn process_webhook(
    mirror: &mut StripeMirrorState,
    payload: Vec<u8>,
    signature_header: String,
    now: Option<u64>,
) -> Result<StripeMint, StripeMirrorError> {
    let event = StripeWebhookEvent {
        payload,
        signature_header,
    };
    mirror.mint_against_webhook(&event, now, DEFAULT_TOLERANCE_SECS)
}

fn handle(
    mut stream: TcpStream,
    mirror: &mut StripeMirrorState,
    check_clock: bool,
    running_credit: &mut u64,
) -> std::io::Result<()> {
    let mut reader = BufReader::new(stream.try_clone()?);

    // Request line.
    let mut request_line = String::new();
    if reader.read_line(&mut request_line)? == 0 {
        return Ok(());
    }
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("").to_string();
    let path = parts.next().unwrap_or("/").to_string();

    // Headers.
    let mut content_length = 0usize;
    let mut signature_header = String::new();
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line)? == 0 {
            break;
        }
        let line = line.trim_end();
        if line.is_empty() {
            break;
        }
        if let Some((name, value)) = line.split_once(':') {
            let name_l = name.trim().to_ascii_lowercase();
            let value = value.trim();
            match name_l.as_str() {
                "content-length" => content_length = value.parse().unwrap_or(0),
                "stripe-signature" => signature_header = value.to_string(),
                _ => {}
            }
        }
    }

    // Body.
    let mut payload = vec![0u8; content_length];
    if content_length > 0 {
        reader.read_exact(&mut payload)?;
    }

    // Health probe.
    if method == "GET" && (path == "/health" || path == "/") {
        return respond(&mut stream, 200, "{\"ok\":true}");
    }
    if method != "POST" {
        return respond(&mut stream, 405, "{\"error\":\"method not allowed\"}");
    }

    let now = if check_clock {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .ok()
    } else {
        None
    };

    match process_webhook(mirror, payload, signature_header, now) {
        Ok(mint) => {
            *running_credit = running_credit.saturating_add(mint.amount);
            println!(
                "✓ MINTED  {} cents  →  recipient {:?}",
                mint.amount, mint.recipient
            );
            println!("    real kernel effect: {:?}", mint.effect);
            println!(
                "    agent credit now: {} cents  (mirror live_supply={}, backing={})",
                running_credit, mirror.live_supply, mirror.total_verified_payments
            );
            let body = format!(
                "{{\"minted\":true,\"amount_cents\":{},\"running_credit_cents\":{}}}",
                mint.amount, running_credit
            );
            respond(&mut stream, 200, &body)
        }
        Err(e) => {
            // Refusals are the substrate's REAL rejections (forged sig, stale, dup, bounds).
            println!("✗ REFUSED  {e}");
            let body = format!("{{\"minted\":false,\"reason\":{:?}}}", e.to_string());
            // Return 200 so the Stripe CLI does not spin on retries during a demo; the
            // refusal reason is still surfaced in the body and on stdout.
            respond(&mut stream, 200, &body)
        }
    }
}

fn respond(stream: &mut TcpStream, code: u16, body: &str) -> std::io::Result<()> {
    let reason = match code {
        200 => "OK",
        405 => "Method Not Allowed",
        _ => "Bad Request",
    };
    let response = format!(
        "HTTP/1.1 {code} {reason}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
        body.len()
    );
    stream.write_all(response.as_bytes())?;
    stream.flush()
}

#[cfg(test)]
mod tests {
    //! Proofs over MOCK webhooks that the receiver's verify→mint round-trip is the
    //! genuine substrate behaviour: a valid signed event mints once, a forged
    //! signature is refused, a re-delivered (retried) event does not double-mint,
    //! conservation holds (Σδ=0: `live_supply == total_verified_payments`), and the
    //! same path runs over a real TCP HTTP request (the raw-body-for-HMAC contract).
    use super::*;
    use std::net::TcpStream;
    use std::thread;

    use dregg_turn::action::Effect;
    use dregg_types::CellId;

    const SECRET: &[u8] = b"whsec_test_dregg_stripe_receiver";

    fn config() -> StripeMirrorConfig {
        StripeMirrorConfig {
            asset: [0xCDu8; 32],
            webhook_secret: SECRET.to_vec(),
            currency: "usd".to_string(),
            min_cents: 50,
            max_cents: 100_000_000,
        }
    }

    fn recipient_hex(b: u8) -> String {
        let mut s = String::with_capacity(64);
        for _ in 0..32 {
            s.push_str(&format!("{b:02x}"));
        }
        s
    }

    /// A realistic `payment_intent.succeeded` body crediting cell `recipient`.
    fn pi_body(id: &str, amount_cents: u64, recipient: u8) -> Vec<u8> {
        format!(
            r#"{{"id":"evt_{id}","type":"payment_intent.succeeded","data":{{"object":{{"id":"{id}","object":"payment_intent","amount":{amount_cents},"amount_received":{amount_cents},"currency":"usd","status":"succeeded","metadata":{{"dregg_recipient":"{rcpt}"}}}}}}}}"#,
            rcpt = recipient_hex(recipient),
        )
        .into_bytes()
    }

    #[test]
    fn valid_signed_webhook_mints_once_and_conserves() {
        let mut mirror = StripeMirrorState::new(config());
        let body = pi_body("pi_recv_1", 2500, 7); // $25.00 → cell 7
        let hook = StripeWebhookEvent::sign(&body, SECRET, 1_700_000_000);

        let mint = process_webhook(&mut mirror, hook.payload, hook.signature_header, None)
            .expect("a valid signed webhook mints");

        assert_eq!(mint.amount, 2500);
        assert_eq!(mint.recipient, CellId::from_bytes([7u8; 32]));
        match mint.effect {
            Effect::Mint {
                target,
                slot,
                amount,
            } => {
                assert_eq!(target, CellId::from_bytes([7u8; 32]));
                assert_eq!(slot, 0);
                assert_eq!(amount, 2500);
            }
            ref other => panic!("expected a real Effect::Mint, got {other:?}"),
        }
        // Conservation (Σδ=0 on the supply side): circulating credit equals the
        // cents Stripe attested, and the invariant `live ≤ backing` holds.
        assert_eq!(mirror.live_supply, 2500);
        assert_eq!(mirror.total_verified_payments, 2500);
        assert!(mirror.invariant_holds());
    }

    #[test]
    fn forged_signature_is_refused_and_nothing_mints() {
        let mut mirror = StripeMirrorState::new(config());
        let body = pi_body("pi_recv_2", 5000, 7);

        // Signed under the WRONG secret (an attacker lacking the webhook secret).
        let forged = StripeWebhookEvent::sign(&body, b"whsec_attacker_guess", 1_700_000_000);
        let err = process_webhook(&mut mirror, forged.payload, forged.signature_header, None)
            .expect_err("a forged signature must be refused");
        assert_eq!(err, StripeMirrorError::SignatureMismatch);

        // A correct signature over a body whose bytes were then tampered also fails
        // (the HMAC is over the exact raw body).
        let good = StripeWebhookEvent::sign(&body, SECRET, 1_700_000_000);
        let tampered = pi_body("pi_recv_2", 9_999_999, 7);
        let err = process_webhook(&mut mirror, tampered, good.signature_header, None)
            .expect_err("a tampered body must be refused");
        assert_eq!(err, StripeMirrorError::SignatureMismatch);

        assert_eq!(mirror.live_supply, 0);
        assert_eq!(mirror.total_verified_payments, 0);
        assert!(mirror.invariant_holds());
    }

    #[test]
    fn redelivered_webhook_does_not_double_mint() {
        // Stripe retries webhooks (and fires both payment_intent.succeeded AND
        // charge.succeeded for one payment); the payment-intent id dedups them all.
        let mut mirror = StripeMirrorState::new(config());
        let body = pi_body("pi_recv_dup", 4000, 9);
        let hook = StripeWebhookEvent::sign(&body, SECRET, 1_700_000_000);

        let first = process_webhook(
            &mut mirror,
            hook.payload.clone(),
            hook.signature_header.clone(),
            None,
        )
        .expect("first delivery mints");
        assert_eq!(first.amount, 4000);

        // Identical re-delivery (a Stripe retry) → refused, no extra credit.
        let err = process_webhook(&mut mirror, hook.payload, hook.signature_header, None)
            .expect_err("a re-delivered webhook must not double-mint");
        assert_eq!(err, StripeMirrorError::DuplicatePayment);

        // Exactly one payment's worth of credit exists; conservation intact.
        assert_eq!(mirror.live_supply, 4000);
        assert_eq!(mirror.total_verified_payments, 4000);
        assert!(mirror.invariant_holds());
    }

    /// The full receiver over a REAL TCP connection: a signed POST is verified +
    /// minted by `handle` exactly as a live `stripe listen --forward-to` delivery
    /// is — proving the raw-body-for-HMAC wiring (Content-Length read, header
    /// parse, JSON 200 response).
    #[test]
    fn http_round_trip_mints_over_tcp() {
        let listener = std::net::TcpListener::bind("127.0.0.1:0").expect("bind ephemeral");
        let addr = listener.local_addr().unwrap();

        let server = thread::spawn(move || {
            let mut mirror = StripeMirrorState::new(config());
            let mut running = 0u64;
            let (stream, _) = listener.accept().expect("accept one conn");
            // check_clock = false: the fixture timestamp is fixed, not "now".
            handle(stream, &mut mirror, false, &mut running).expect("handle conn");
            (running, mirror.live_supply, mirror.total_verified_payments)
        });

        let body = pi_body("pi_http_1", 2500, 3);
        let hook = StripeWebhookEvent::sign(&body, SECRET, 1_700_000_000);
        let req = format!(
            "POST /webhook HTTP/1.1\r\nHost: localhost\r\nStripe-Signature: {}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
            hook.signature_header,
            body.len()
        );
        let mut client = TcpStream::connect(addr).expect("connect");
        client.write_all(req.as_bytes()).unwrap();
        client.write_all(&body).unwrap();
        let mut resp = String::new();
        client.read_to_string(&mut resp).unwrap();

        assert!(resp.contains("200 OK"), "response was: {resp}");
        assert!(resp.contains("\"minted\":true"), "response was: {resp}");
        assert!(
            resp.contains("\"amount_cents\":2500"),
            "response was: {resp}"
        );

        let (running, live, backing) = server.join().unwrap();
        assert_eq!(running, 2500);
        assert_eq!(live, 2500);
        assert_eq!(backing, 2500); // Σδ=0: live == backing
    }
}
