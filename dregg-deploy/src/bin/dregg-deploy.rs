//! `dregg-deploy` — the DreggDL CLI.
//!
//! ```text
//!   dregg-deploy check <file.dregg.toml>     parse → lower → static assurance verdict
//!   dregg-deploy check --ring <file>         also run the ring-balance check
//!   dregg-deploy check --json <file>         emit the assurance as JSON
//!   dregg-deploy lower <file.dregg.toml>     emit the lowered CallForest as JSON
//!                                            (feed it to `dregg-uverify`)
//!   dregg-deploy fmt   <file.dregg.toml>     round-trip: parse and re-serialize canonical TOML
//! ```
//!
//! `check` exits 0 on a passing assurance, 1 on findings, 2 on input/parse
//! error — so it composes into CI / pre-submit hooks.

use std::process::ExitCode;

use dregg_deploy::{check, parse_toml, serialize_toml, Lowered};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cmd = args.first().map(String::as_str);

    match cmd {
        Some("check") => run_check(&args[1..]),
        Some("lower") => run_lower(&args[1..]),
        Some("fmt") => run_fmt(&args[1..]),
        Some("-h") | Some("--help") | None => {
            print_help();
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("unknown subcommand `{other}`\n");
            print_help();
            ExitCode::from(2)
        }
    }
}

fn print_help() {
    eprintln!(
        "dregg-deploy — DreggDL, a checkable deployment spec (CapDL for dregg)\n\n\
         USAGE:\n  \
           dregg-deploy check [--ring] [--json] <file.dregg.toml>\n      \
               parse → lower → run the static assurance over the whole authority layout\n  \
           dregg-deploy lower <file.dregg.toml>\n      \
               emit the lowered dregg_turn::CallForest as JSON (pipe to dregg-uverify)\n  \
           dregg-deploy fmt   <file.dregg.toml>\n      \
               round-trip: parse and re-emit canonical TOML\n\n\
         EXIT (check): 0 = Pass, 1 = findings, 2 = input/parse error."
    );
}

fn read_file(args: &[String]) -> Result<String, ExitCode> {
    let file = args.iter().find(|a| !a.starts_with("--"));
    match file {
        Some(path) => std::fs::read_to_string(path).map_err(|e| {
            eprintln!("error reading `{path}`: {e}");
            ExitCode::from(2)
        }),
        None => {
            eprintln!("error: expected a <file.dregg.toml> argument");
            Err(ExitCode::from(2))
        }
    }
}

fn run_check(args: &[String]) -> ExitCode {
    let as_ring = args.iter().any(|a| a == "--ring");
    let as_json = args.iter().any(|a| a == "--json");
    let text = match read_file(args) {
        Ok(t) => t,
        Err(c) => return c,
    };
    let verdict = match check(&text, as_ring) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };

    if as_json {
        // Emit the underlying assurance object (the Verdict types are
        // serde-serializable in dregg-userspace-verify).
        match serde_json::to_string_pretty(&verdict.assurance) {
            Ok(j) => println!("{j}"),
            Err(e) => {
                eprintln!("error serializing verdict: {e}");
                return ExitCode::from(2);
            }
        }
    } else {
        print_human(&verdict);
    }

    if verdict.pass() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}

fn print_human(v: &dregg_deploy::DeployVerdict) {
    println!("dregg-deploy: resolved deployment");
    println!("  federation turns (effect-groups): {}", v.turn_count);
    if !v.factories.is_empty() {
        println!("  factories:");
        for (name, vk) in &v.factories {
            println!("    {name:<16} factory_vk b3:{}…", &vk[..16]);
        }
    }
    if !v.cells.is_empty() {
        println!("  cells:");
        for (name, id) in &v.cells {
            println!("    {name:<16} cell      {}…", &id[..16]);
        }
    }
    println!();

    let a = &v.assurance;
    let line = |name: &str, vd: &dregg_userspace_verify::Verdict| {
        if vd.is_pass() {
            println!("  [PASS] {name}");
        } else {
            println!("  [FAIL] {name}");
            for f in vd.findings() {
                println!("         @ {}  —  {}", f.locus, f.message);
            }
        }
    };
    println!("static assurance over the declared authority layout:");
    line("B  conservation      (funding transfers net to zero)", &a.conservation);
    line("A  no-amplification  (grant edges are attenuations)  ", &a.no_amplification);
    line("   well-formedness   (structural shape)              ", &a.wellformed);
    line("   ring balance                                      ", &a.ring_balance);
    println!();
    if v.pass() {
        println!(
            "VERDICT: PASS (static). The whole declared cap layout conserves and \
             does not amplify. NOTE: a Pass is necessary, not sufficient — the \
             executor still checks holding, balances, credentials, freshness, and \
             the state commitment at submit time."
        );
    } else {
        println!(
            "VERDICT: FAIL — fix the findings above; this deployment would be \
             rejected by the executor (you'd pay gas to be rejected)."
        );
    }
}

fn run_lower(args: &[String]) -> ExitCode {
    let text = match read_file(args) {
        Ok(t) => t,
        Err(c) => return c,
    };
    let dep = match parse_toml(&text) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };
    let lowered = match Lowered::from_deployment(&dep) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };
    match serde_json::to_string_pretty(&lowered.forest) {
        Ok(j) => {
            println!("{j}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("error serializing forest: {e}");
            ExitCode::from(2)
        }
    }
}

fn run_fmt(args: &[String]) -> ExitCode {
    let text = match read_file(args) {
        Ok(t) => t,
        Err(c) => return c,
    };
    let dep = match parse_toml(&text) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };
    match serialize_toml(&dep) {
        Ok(t) => {
            print!("{t}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("error serializing: {e}");
            ExitCode::from(2)
        }
    }
}
