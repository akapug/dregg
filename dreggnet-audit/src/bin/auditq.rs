//! `auditq` — query/correlate/stats/replay over the dreggnet-audit JSONL store.
//!
//! The store is the canonical append-only directory of `audit-YYYY-MM-DD.jsonl`
//! files every frontend writes (`docs/BOT-AUDIT-LOGGING-DESIGN.md` §5/§7). This
//! tool reads it back through the crate's own torn-tail-tolerant reader and
//! answers the two questions the receipt chain cannot: *what did people try*
//! (including everything that did NOT land) and *which human act produced this
//! receipt* (the `turn_hash` join).
//!
//! Zero deps beyond the crate's own (`serde_json`); arg parsing is hand-rolled.
//! Reads only — this tool never writes the store.

use dreggnet_audit::{AuditEvent, AuditOutcome, civil_from_days, days_from_civil, read_events_dir};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::ExitCode;

const USAGE: &str = "\
auditq — query/replay the dreggnet bot audit store (append-only JSONL envelope)

USAGE:
  auditq <COMMAND> [--dir <DIR>] [OPTIONS]

  <DIR> is the audit directory (files audit-YYYY-MM-DD.jsonl). Defaults to
  $DREGG_AUDIT_DIR when --dir is not given.

COMMANDS:
  query        Filter + print events.
  correlate <ID>
               The full ordered interaction chain for <ID>, which may be a
               correlation_id, a session_id, or a 64-hex turn_hash (the
               receipt→envelope join). Landed events print their receipt join.
  stats        Counts by decision / outcome / offering / surface / platform.
  replay       Emit the ordered input sequence (a replay script) for one
               --session or --correlation. See the honesty note it prints:
               this EMITS the script; it does not re-drive a live host.

FILTER OPTIONS (query, stats; replay takes --session/--correlation/--until-corr):
  --actor <ID>         Matches actor.platform_id OR actor.dregg_identity.
  --platform <P>       discord | telegram | web | tg-miniapp
  --surface <S>        command | component | modal | callback | web_app_data |
                       http | init_data | message | chain_command | resume
  --offering <KEY>     e.g. dungeon, market
  --decision <KIND>    routed | refused | gated | error
  --reason <SUBSTR>    Substring match on decision.reason.
  --outcome <KIND>     landed | refused | verified | none | error
  --session <SID>      Exact session_id.
  --correlation <CID>  Exact correlation_id.
  --turn-hash <HEX>    Exact Landed turn_hash.
  --since <T>          Unix millis, or YYYY-MM-DD (from UTC midnight).
  --until <T>          Unix millis, or YYYY-MM-DD (through end of that UTC day).
  --limit <N>          Print at most the LAST N matches.
  --json               Machine output: one JSON event per line (passthrough).

EXAMPLES:
  auditq query --actor 123456789 --since 2026-07-16
  auditq query --decision refused --reason not_offered --offering market
  auditq query --outcome error --json
  auditq correlate 019f4a…                      # one interaction
  auditq correlate dungeon-web                  # a whole session, in order
  auditq correlate <64-hex turn_hash>           # receipt → the human act
  auditq stats --platform web
  auditq replay --session dungeon-web --json > replay-script.jsonl
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("auditq: {e}");
            ExitCode::FAILURE
        }
    }
}

fn run(args: &[String]) -> Result<(), String> {
    let Some(cmd) = args.first() else {
        eprint!("{USAGE}");
        return Err("missing command".into());
    };
    match cmd.as_str() {
        "query" => cmd_query(&args[1..]),
        "correlate" => cmd_correlate(&args[1..]),
        "stats" => cmd_stats(&args[1..]),
        "replay" => cmd_replay(&args[1..]),
        "--help" | "-h" | "help" => {
            print!("{USAGE}");
            Ok(())
        }
        other => {
            eprint!("{USAGE}");
            Err(format!("unknown command {other:?}"))
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Options / filters
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Default)]
struct Opts {
    dir: Option<PathBuf>,
    actor: Option<String>,
    platform: Option<String>,
    surface: Option<String>,
    offering: Option<String>,
    decision: Option<String>,
    reason: Option<String>,
    outcome: Option<String>,
    session: Option<String>,
    correlation: Option<String>,
    turn_hash: Option<String>,
    since_ms: Option<u64>,
    until_ms: Option<u64>,
    limit: Option<usize>,
    json: bool,
    /// replay only: stop one event AFTER this correlation_id is emitted.
    until_corr: Option<String>,
    /// positional args (correlate's <ID>).
    positional: Vec<String>,
}

fn parse_opts(args: &[String]) -> Result<Opts, String> {
    let mut o = Opts::default();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let mut val = |name: &str| -> Result<String, String> {
            it.next()
                .cloned()
                .ok_or_else(|| format!("{name} needs a value"))
        };
        match a.as_str() {
            "--dir" => o.dir = Some(PathBuf::from(val("--dir")?)),
            "--actor" => o.actor = Some(val("--actor")?),
            "--platform" => o.platform = Some(val("--platform")?),
            "--surface" => o.surface = Some(val("--surface")?),
            "--offering" => o.offering = Some(val("--offering")?),
            "--decision" => o.decision = Some(val("--decision")?),
            "--reason" => o.reason = Some(val("--reason")?),
            "--outcome" => o.outcome = Some(val("--outcome")?),
            "--session" => o.session = Some(val("--session")?),
            "--correlation" => o.correlation = Some(val("--correlation")?),
            "--turn-hash" => o.turn_hash = Some(val("--turn-hash")?),
            "--since" => o.since_ms = Some(parse_time(&val("--since")?, false)?),
            "--until" => o.until_ms = Some(parse_time(&val("--until")?, true)?),
            "--limit" => {
                o.limit = Some(
                    val("--limit")?
                        .parse()
                        .map_err(|_| "--limit needs an integer".to_string())?,
                )
            }
            "--until-corr" => o.until_corr = Some(val("--until-corr")?),
            "--json" => o.json = true,
            "--help" | "-h" => {
                print!("{USAGE}");
                std::process::exit(0);
            }
            p if !p.starts_with("--") => o.positional.push(p.to_string()),
            other => return Err(format!("unknown option {other:?}")),
        }
    }
    Ok(o)
}

/// `1784380826967` (unix millis) or `2026-07-18` (UTC). For an end-of-range
/// date, the whole day is included (`end_of_day`).
fn parse_time(s: &str, end_of_day: bool) -> Result<u64, String> {
    if s.chars().all(|c| c.is_ascii_digit()) && !s.is_empty() {
        return s.parse().map_err(|_| format!("bad time {s:?}"));
    }
    let b = s.as_bytes();
    let ok = b.len() == 10 && b[4] == b'-' && b[7] == b'-';
    let parsed = ok
        .then(|| {
            let y: i64 = s[0..4].parse().ok()?;
            let m: u32 = s[5..7].parse().ok()?;
            let d: u32 = s[8..10].parse().ok()?;
            if !(1..=12).contains(&m) || !(1..=31).contains(&d) {
                return None;
            }
            let day = days_from_civil(y, m, d) + i64::from(end_of_day);
            u64::try_from(day).ok()?.checked_mul(86_400_000)
        })
        .flatten();
    parsed
        .map(|ms| if end_of_day { ms.saturating_sub(1) } else { ms })
        .ok_or_else(|| format!("bad time {s:?} (want unix millis or YYYY-MM-DD)"))
}

fn matches(ev: &AuditEvent, o: &Opts) -> bool {
    if let Some(a) = &o.actor {
        let hit = ev.actor.platform_id == *a || ev.actor.dregg_identity.as_deref() == Some(a);
        if !hit {
            return false;
        }
    }
    if let Some(p) = &o.platform
        && ev.platform != *p
    {
        return false;
    }
    if let Some(s) = &o.surface
        && surface_str(ev) != *s
    {
        return false;
    }
    if let Some(k) = &o.offering
        && ev.offering.as_deref() != Some(k)
    {
        return false;
    }
    if let Some(d) = &o.decision
        && ev.decision.kind != *d
    {
        return false;
    }
    if let Some(r) = &o.reason
        && !ev.decision.reason.contains(r.as_str())
    {
        return false;
    }
    if let Some(k) = &o.outcome
        && outcome_kind(&ev.outcome) != *k
    {
        return false;
    }
    if let Some(s) = &o.session
        && ev.session_id.as_deref() != Some(s)
    {
        return false;
    }
    if let Some(c) = &o.correlation
        && ev.correlation_id != *c
    {
        return false;
    }
    if let Some(h) = &o.turn_hash {
        let hit = matches!(&ev.outcome, AuditOutcome::Landed { turn_hash, .. } if turn_hash == h);
        if !hit {
            return false;
        }
    }
    if let Some(since) = o.since_ms
        && ev.ts_ms < since
    {
        return false;
    }
    if let Some(until) = o.until_ms
        && ev.ts_ms > until
    {
        return false;
    }
    true
}

// ─────────────────────────────────────────────────────────────────────────────
// Store loading + rendering helpers
// ─────────────────────────────────────────────────────────────────────────────

fn load(o: &Opts) -> Result<Vec<AuditEvent>, String> {
    let dir = o
        .dir
        .clone()
        .or_else(|| std::env::var("DREGG_AUDIT_DIR").ok().map(PathBuf::from))
        .ok_or("no audit dir: pass --dir or set DREGG_AUDIT_DIR")?;
    let (mut events, skipped) =
        read_events_dir(&dir).map_err(|e| format!("cannot read {}: {e}", dir.display()))?;
    if skipped > 0 {
        eprintln!("auditq: note: skipped {skipped} non-event line(s) (audit_meta / torn tails)");
    }
    // Files arrive in date order; make the interleaving exact.
    events.sort_by_key(|e| e.ts_ms);
    Ok(events)
}

/// The serialized (snake_case) surface word — the same string the JSONL holds.
fn surface_str(ev: &AuditEvent) -> String {
    serde_json::to_value(ev.surface)
        .ok()
        .and_then(|v| v.as_str().map(str::to_string))
        .unwrap_or_default()
}

fn outcome_kind(o: &AuditOutcome) -> &'static str {
    match o {
        AuditOutcome::Landed { .. } => "landed",
        AuditOutcome::Refused { .. } => "refused",
        AuditOutcome::Verified { .. } => "verified",
        AuditOutcome::None => "none",
        AuditOutcome::Error { .. } => "error",
    }
}

fn fmt_ts(ms: u64) -> String {
    let days = (ms / 86_400_000) as i64;
    let (y, mo, d) = civil_from_days(days);
    let rem = ms % 86_400_000;
    let (h, mi, s, milli) = (
        rem / 3_600_000,
        (rem / 60_000) % 60,
        (rem / 1000) % 60,
        rem % 1000,
    );
    format!("{y:04}-{mo:02}-{d:02}T{h:02}:{mi:02}:{s:02}.{milli:03}Z")
}

fn fmt_outcome(o: &AuditOutcome) -> String {
    match o {
        AuditOutcome::Landed { turn_hash, ended } => {
            format!("landed turn={turn_hash} ended={ended}")
        }
        AuditOutcome::Refused { why } => format!("refused({why})"),
        AuditOutcome::Verified { verified, turns } => {
            format!("verified={verified} turns={turns}")
        }
        AuditOutcome::None => "none".into(),
        AuditOutcome::Error { what } => format!("error({what})"),
    }
}

fn fmt_event(ev: &AuditEvent) -> String {
    let decision = if ev.decision.reason.is_empty() {
        ev.decision.kind.clone()
    } else {
        format!("{}({})", ev.decision.kind, ev.decision.reason)
    };
    let ident = ev
        .actor
        .dregg_identity
        .as_deref()
        .map(|i| format!(" id={}", ellipt(i)))
        .unwrap_or_default();
    let sess = ev
        .session_id
        .as_deref()
        .map(|s| format!(" sess={s}"))
        .unwrap_or_default();
    let off = ev
        .offering
        .as_deref()
        .map(|o| format!(" off={o}"))
        .unwrap_or_default();
    format!(
        "{} {}/{} {}[{}]{} {:?} {} -> {}{}{} corr={}",
        fmt_ts(ev.ts_ms),
        ev.platform,
        surface_str(ev),
        ev.actor.platform_id,
        ev.actor.grade,
        ident,
        ev.input.kind,
        decision,
        fmt_outcome(&ev.outcome),
        off,
        sess,
        ev.correlation_id,
    )
}

fn ellipt(s: &str) -> String {
    if s.len() > 16 {
        format!("{}…", &s[..12])
    } else {
        s.to_string()
    }
}

fn print_events(events: &[AuditEvent], json: bool) {
    for ev in events {
        if json {
            if let Ok(line) = serde_json::to_string(ev) {
                println!("{line}");
            }
        } else {
            println!("{}", fmt_event(ev));
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// query
// ─────────────────────────────────────────────────────────────────────────────

fn cmd_query(args: &[String]) -> Result<(), String> {
    let o = parse_opts(args)?;
    let events = load(&o)?;
    let mut hits: Vec<&AuditEvent> = events.iter().filter(|e| matches(e, &o)).collect();
    let total = hits.len();
    if let Some(n) = o.limit
        && hits.len() > n
    {
        hits.drain(..hits.len() - n);
    }
    let owned: Vec<AuditEvent> = hits.into_iter().cloned().collect();
    print_events(&owned, o.json);
    if !o.json {
        eprintln!(
            "auditq: {total} match(es) of {} event(s){}",
            events.len(),
            o.limit
                .filter(|n| total > *n)
                .map(|n| format!(" (showing last {n})"))
                .unwrap_or_default()
        );
    }
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────
// correlate
// ─────────────────────────────────────────────────────────────────────────────

fn cmd_correlate(args: &[String]) -> Result<(), String> {
    let o = parse_opts(args)?;
    let id = o
        .positional
        .first()
        .ok_or("correlate needs an id: a correlation_id, session_id, or 64-hex turn_hash")?
        .clone();
    let events = load(&o)?;

    // Classify by what actually matches the store, most-specific first.
    let by_corr: Vec<&AuditEvent> = events.iter().filter(|e| e.correlation_id == id).collect();
    let by_sess: Vec<&AuditEvent> = events
        .iter()
        .filter(|e| e.session_id.as_deref() == Some(id.as_str()))
        .collect();
    let by_hash: Vec<&AuditEvent> = events
        .iter()
        .filter(
            |e| matches!(&e.outcome, AuditOutcome::Landed { turn_hash, .. } if *turn_hash == id),
        )
        .collect();

    let (label, chain) = if !by_corr.is_empty() {
        ("correlation_id", by_corr)
    } else if !by_sess.is_empty() {
        ("session_id", by_sess)
    } else if !by_hash.is_empty() {
        ("turn_hash (receipt → envelope)", by_hash)
    } else {
        return Err(format!(
            "no event matches {id:?} as correlation_id, session_id, or landed turn_hash"
        ));
    };

    if o.json {
        let owned: Vec<AuditEvent> = chain.into_iter().cloned().collect();
        print_events(&owned, true);
        return Ok(());
    }

    println!(
        "chain for {label} = {id} ({} event(s), ordered):",
        chain.len()
    );
    for ev in &chain {
        println!("  {}", fmt_event(ev));
        if let AuditOutcome::Landed { turn_hash, ended } = &ev.outcome {
            let off = ev.offering.as_deref().unwrap_or("<offering?>");
            let sid = ev.session_id.as_deref().unwrap_or("<session?>");
            println!(
                "    receipt join: turn_hash={turn_hash} (ended={ended}) — chained on \
                 session {sid}'s receipt log; re-verify via the offering verifier \
                 (GET /offerings/{off}/session/{sid}/verify | /verify | verifychain:), \
                 move-log <session-dir>/{off}/{sid}.log"
            );
        }
    }
    let landed = chain
        .iter()
        .filter(|e| matches!(e.outcome, AuditOutcome::Landed { .. }))
        .count();
    println!(
        "summary: {} routed / {} refused / {} gated / {} error; {landed} landed (on-chain), \
         {} never reached the receipt chain",
        chain.iter().filter(|e| e.decision.kind == "routed").count(),
        chain
            .iter()
            .filter(|e| e.decision.kind == "refused")
            .count(),
        chain.iter().filter(|e| e.decision.kind == "gated").count(),
        chain.iter().filter(|e| e.decision.kind == "error").count(),
        chain.len() - landed,
    );
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────
// stats
// ─────────────────────────────────────────────────────────────────────────────

fn cmd_stats(args: &[String]) -> Result<(), String> {
    let o = parse_opts(args)?;
    let events = load(&o)?;
    let hits: Vec<&AuditEvent> = events.iter().filter(|e| matches(e, &o)).collect();

    let mut decision: BTreeMap<String, u64> = BTreeMap::new();
    let mut reasons: BTreeMap<String, u64> = BTreeMap::new();
    let mut outcome: BTreeMap<String, u64> = BTreeMap::new();
    let mut offering: BTreeMap<String, u64> = BTreeMap::new();
    let mut surface: BTreeMap<String, u64> = BTreeMap::new();
    let mut platform: BTreeMap<String, u64> = BTreeMap::new();
    for ev in &hits {
        *decision.entry(ev.decision.kind.clone()).or_default() += 1;
        if !ev.decision.reason.is_empty() {
            *reasons
                .entry(format!("{}:{}", ev.decision.kind, ev.decision.reason))
                .or_default() += 1;
        }
        *outcome.entry(outcome_kind(&ev.outcome).into()).or_default() += 1;
        *offering
            .entry(ev.offering.clone().unwrap_or_else(|| "(none)".into()))
            .or_default() += 1;
        *surface.entry(surface_str(ev)).or_default() += 1;
        *platform.entry(ev.platform.clone()).or_default() += 1;
    }

    if o.json {
        let out = serde_json::json!({
            "events": hits.len(),
            "span_ms": hits.first().map(|e| e.ts_ms).zip(hits.last().map(|e| e.ts_ms)),
            "decision": decision, "decision_reasons": reasons, "outcome": outcome,
            "offering": offering, "surface": surface, "platform": platform,
        });
        println!("{out}");
        return Ok(());
    }

    println!("{} event(s)", hits.len());
    if let (Some(a), Some(b)) = (hits.first(), hits.last()) {
        println!("span: {} .. {}", fmt_ts(a.ts_ms), fmt_ts(b.ts_ms));
    }
    for (name, map) in [
        ("decision", &decision),
        ("decision reasons (non-routed)", &reasons),
        ("outcome", &outcome),
        ("offering", &offering),
        ("surface", &surface),
        ("platform", &platform),
    ] {
        println!("by {name}:");
        let mut rows: Vec<(&String, &u64)> = map.iter().collect();
        rows.sort_by(|a, b| b.1.cmp(a.1).then_with(|| a.0.cmp(b.0)));
        for (k, v) in rows {
            println!("  {v:>7}  {k}");
        }
    }
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────
// replay — EMITS the script; does not re-drive (that needs a live host)
// ─────────────────────────────────────────────────────────────────────────────

const REPLAY_NOTE: &str = "\
NOTE — what this is, honestly: this script is the ORDERED INPUT SEQUENCE plus
the decisions/outcomes observed AT RECORD TIME. Re-driving it needs, beyond
this file:
  1. a live host with the same offering build registered
     (dreggnet_catalog::full_catalog_host) — behavior differences vs record
     time are code changes, which is exactly what a replay diff surfaces;
  2. a fresh session seeded from the SAME session_id (sessions are
     deterministically seeded from the session id);
  3. credentials the audit log deliberately omits: the bot master secret for
     custodial-grade actors, the user's own Ed25519 key for signed acts — the
     log carries only PUBLIC identities, so signed/custodial turns must be
     re-signed by whoever holds those keys;
  4. gate context that is environment, not input (initData HMAC secret, live
     signature counters) — 'gated' expectations compare, they don't reproduce.
Under those, every formerly-landed step must land with the SAME turn_hash
(divergence = nondeterminism or a code change) and every refusal must refuse
with the same reason.";

fn cmd_replay(args: &[String]) -> Result<(), String> {
    let o = parse_opts(args)?;
    if o.session.is_none() && o.correlation.is_none() {
        return Err("replay needs --session <sid> or --correlation <cid>".into());
    }
    let events = load(&o)?;
    let mut steps: Vec<&AuditEvent> = events.iter().filter(|e| matches(e, &o)).collect();
    if let Some(stop) = &o.until_corr {
        if let Some(pos) = steps.iter().position(|e| e.correlation_id == *stop) {
            steps.truncate(pos + 1);
        } else {
            return Err(format!("--until-corr {stop:?} not in the selected chain"));
        }
    }
    if steps.is_empty() {
        return Err("no events match the requested session/correlation".into());
    }

    let scope = o
        .session
        .as_deref()
        .map(|s| format!("session {s}"))
        .or_else(|| o.correlation.as_deref().map(|c| format!("correlation {c}")))
        .unwrap_or_default();

    if o.json {
        // stdout: pure JSONL script (header line + one step per line).
        // stderr: the honesty note.
        eprintln!("{REPLAY_NOTE}");
        let header = serde_json::json!({
            "replay_script": 1,
            "scope": scope,
            "steps": steps.len(),
            "requires": [
                "live host: dreggnet_catalog::full_catalog_host with the offering registered",
                "fresh session deterministically seeded from the same session_id",
                "re-signing keys for custodial/signed actors (NOT in the audit log)",
                "gate environment (initData secret, counters) for gated steps",
            ],
        });
        println!("{header}");
        for (i, ev) in steps.iter().enumerate() {
            let line = serde_json::json!({
                "seq": i + 1,
                "ts_ms": ev.ts_ms,
                "correlation_id": ev.correlation_id,
                "platform": ev.platform,
                "surface": surface_str(ev),
                "actor": ev.actor,
                "input": ev.input,
                "offering": ev.offering,
                "session_id": ev.session_id,
                "expect": { "decision": ev.decision, "outcome": ev.outcome },
            });
            println!("{line}");
        }
        return Ok(());
    }

    println!(
        "replay script for {scope} — {} step(s), in recorded order",
        steps.len()
    );
    println!("{REPLAY_NOTE}");
    println!();
    for (i, ev) in steps.iter().enumerate() {
        let detail = serde_json::to_string(&ev.input.detail).unwrap_or_else(|_| "null".into());
        println!(
            "step {:>3}  {}  {}[{}] on {}/{}",
            i + 1,
            fmt_ts(ev.ts_ms),
            ev.actor.platform_id,
            ev.actor.grade,
            ev.platform,
            surface_str(ev),
        );
        println!("      input:  {} {}", ev.input.kind, detail);
        let decision = if ev.decision.reason.is_empty() {
            ev.decision.kind.clone()
        } else {
            format!("{}({})", ev.decision.kind, ev.decision.reason)
        };
        println!(
            "      expect: decision={decision} outcome={}",
            fmt_outcome(&ev.outcome)
        );
    }
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────
// Unit tests (pure helpers; end-to-end CLI tests live in tests/auditq_cli.rs)
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn time_parsing_millis_and_dates() {
        assert_eq!(
            parse_time("1784380826967", false).unwrap(),
            1_784_380_826_967
        );
        // 2026-07-18 UTC midnight.
        let start = parse_time("2026-07-18", false).unwrap();
        let end = parse_time("2026-07-18", true).unwrap();
        assert_eq!(end - start, 86_400_000 - 1, "until spans the whole day");
        assert_eq!(start % 86_400_000, 0);
        // The real record's ts falls inside its own day.
        assert!(start <= 1_784_380_826_967 && 1_784_380_826_967 <= end);
        assert!(parse_time("2026-7-18", false).is_err());
        assert!(parse_time("yesterday", false).is_err());
    }

    #[test]
    fn ts_formatting_round_trips_the_fixture() {
        assert_eq!(fmt_ts(0), "1970-01-01T00:00:00.000Z");
        // The real hbox record's timestamp: 1784380826967 % 86400000 =
        // 48026967 ms into 2026-07-18 UTC = 13:20:26.967.
        assert_eq!(fmt_ts(1_784_380_826_967), "2026-07-18T13:20:26.967Z");
    }

    #[test]
    fn opts_reject_dangling_values_and_unknown_flags() {
        assert!(parse_opts(&["--actor".to_string()]).is_err());
        assert!(parse_opts(&["--frobnicate".to_string(), "x".to_string()]).is_err());
        let o = parse_opts(&[
            "--actor".into(),
            "42".into(),
            "--json".into(),
            "some-id".into(),
        ])
        .unwrap();
        assert_eq!(o.actor.as_deref(), Some("42"));
        assert!(o.json);
        assert_eq!(o.positional, vec!["some-id".to_string()]);
    }
}
