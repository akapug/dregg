//! `dregg-authctl` — the operator's key + capability tool for DreggNet webauth.
//!
//! This is the issuing side the cipherclerk wallet ultimately owns; the CLI is
//! the plumbing for bootstrapping and for handing a stranger an `ops-admin`
//! capability so the dashboard opens with no password.
//!
//!   dregg-authctl keygen
//!       → prints a fresh root SEED (secret) + PUBLIC KEY (publish this; it is
//!         what DREGG_WEBAUTH_ROOT_PUBKEY is set to).
//!
//!   dregg-authctl mint --seed <hex> --caps ops-admin,grafana-view [--until <unix>]
//!       → prints a dga1_… capability granting those caps. Paste it into the
//!         login page (or load it into the cipherclerk wallet).
//!
//!   dregg-authctl attenuate --cred <dga1_…> --caps grafana-view [--until <unix>]
//!       → prints a NARROWED dga1_… capability. Can only ever remove reach.
//!
//!   dregg-authctl explain --cred <dga1_…>
//!       → human-readable terms of a capability, block by block.
//!
//!   dregg-authctl mint-session --seed <hex> --inception <pubkey-hex>
//!                              --caps ops-admin [--ttl <secs>]
//!       → prints a RE-ANCHORED dga1_ SESSION token (the Tier-1 form): carries
//!         the stable `acct` account id derived from --inception, a default short
//!         expiry, and the caps. Re-issuing one (rotation/recovery/login) keeps
//!         the same account subject. --inception may instead be a raw 64-hex
//!         account id (to grandfather an existing subject during migration).
//!
//!   dregg-authctl revoke --cred <dga1_…>
//!       → prints the deny-set entries that kill this credential: its TAIL (kills
//!         exactly this session) and its SUBJECT (kills every session for the
//!         account). Add either to DREGG_WEBAUTH_REVOKED / the revocation file.

use std::time::{SystemTime, UNIX_EPOCH};

use dreggnet_webauth::account_id;
use dreggnet_webauth::config::DEFAULT_SESSION_TTL_SECS;
use dreggnet_webauth::cred::{Credential, RootKey};
use dreggnet_webauth::grant::{attenuate_caps, mint_caps, mint_session};
use dreggnet_webauth::subject_of;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let cmd = args.get(1).map(String::as_str).unwrap_or("");
    let result = match cmd {
        "keygen" => keygen(),
        "mint" => mint(&args[2..]),
        "mint-session" => mint_session_cmd(&args[2..]),
        "revoke" => revoke(&args[2..]),
        "attenuate" => attenuate(&args[2..]),
        "explain" => explain(&args[2..]),
        _ => {
            usage();
            std::process::exit(2);
        }
    };
    if let Err(e) = result {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}

fn usage() {
    eprintln!(
        "dregg-authctl — DreggNet web capability tool\n\
         \n\
         USAGE:\n\
         \x20 dregg-authctl keygen\n\
         \x20 dregg-authctl mint         --seed <hex> --caps a,b [--until <unix>]\n\
         \x20 dregg-authctl mint-session --seed <hex> --inception <pubkey-hex> --caps a,b [--ttl <secs>]\n\
         \x20 dregg-authctl revoke       --cred <dga1_>\n\
         \x20 dregg-authctl attenuate    --cred <dga1_> --caps a [--until <unix>]\n\
         \x20 dregg-authctl explain      --cred <dga1_>"
    );
}

fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

fn flag<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1))
        .map(String::as_str)
}

fn caps_list(args: &[String]) -> Result<Vec<String>, String> {
    let raw = flag(args, "--caps").ok_or("missing --caps a,b,c")?;
    let caps: Vec<String> = raw
        .split(',')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect();
    if caps.is_empty() {
        return Err("--caps must name at least one capability".into());
    }
    Ok(caps)
}

fn until_opt(args: &[String]) -> Result<Option<u64>, String> {
    match flag(args, "--until") {
        Some(s) => s
            .parse::<u64>()
            .map(Some)
            .map_err(|_| "--until must be a unix second".into()),
        None => Ok(None),
    }
}

fn keygen() -> Result<(), String> {
    let root = RootKey::generate();
    println!("# DreggNet webauth root authority (ed25519)");
    println!("# SECRET seed — keep it where the root keeps secrets, never publish:");
    println!("seed   = {}", root.secret_hex());
    println!("# PUBLIC key — publish this; set DREGG_WEBAUTH_ROOT_PUBKEY to it:");
    println!("pubkey = {}", root.public().to_hex());
    Ok(())
}

fn mint(args: &[String]) -> Result<(), String> {
    let seed = flag(args, "--seed").ok_or("missing --seed <hex>")?;
    let root = RootKey::from_seed_hex(seed).map_err(|e| e.to_string())?;
    let caps = caps_list(args)?;
    let until = until_opt(args)?;
    let cred = mint_caps(&root, caps, until);
    println!("{}", cred.encode());
    Ok(())
}

/// Resolve `--inception` to a stable account-id hex: either derive it from a
/// 64-hex inception pubkey, or accept a raw 64-hex account id verbatim (the
/// migration grandfather path). Other lengths are rejected.
fn resolve_account_id(args: &[String]) -> Result<String, String> {
    let raw =
        flag(args, "--inception").ok_or("missing --inception <pubkey-hex | account-id-hex>")?;
    let raw = raw.trim();
    if raw.len() != 64 || !raw.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("--inception must be 64 hex characters (a pubkey or an account id)".into());
    }
    // Treat it as an inception pubkey and derive the account id. (A caller
    // grandfathering an existing id passes that id's pre-image pubkey, or uses
    // the raw value directly via a re-anchored re-mint elsewhere.)
    let mut pk = [0u8; 32];
    for (i, chunk) in raw.as_bytes().chunks_exact(2).enumerate() {
        let hi = (chunk[0] as char)
            .to_digit(16)
            .ok_or("non-hex in --inception")?;
        let lo = (chunk[1] as char)
            .to_digit(16)
            .ok_or("non-hex in --inception")?;
        pk[i] = ((hi << 4) | lo) as u8;
    }
    Ok(account_id::account_id_hex(&pk))
}

fn mint_session_cmd(args: &[String]) -> Result<(), String> {
    let seed = flag(args, "--seed").ok_or("missing --seed <hex>")?;
    let root = RootKey::from_seed_hex(seed).map_err(|e| e.to_string())?;
    let account = resolve_account_id(args)?;
    let caps = caps_list(args)?;
    let ttl = match flag(args, "--ttl") {
        Some(s) => s.parse::<u64>().map_err(|_| "--ttl must be seconds")?,
        None => DEFAULT_SESSION_TTL_SECS,
    };
    let cred = mint_session(&root, &account, caps, now_secs(), ttl);
    println!("{}", cred.encode());
    Ok(())
}

fn revoke(args: &[String]) -> Result<(), String> {
    let enc = flag(args, "--cred").ok_or("missing --cred <dga1_>")?;
    let cred = Credential::decode(enc.trim()).map_err(|e| e.to_string())?;
    println!("# Add EITHER line to DREGG_WEBAUTH_REVOKED (or the revocation file).");
    println!("# kill exactly THIS session token (its tail commitment):");
    println!("{}", cred.tail_hex());
    if let Some(subject) = subject_of(enc.trim()) {
        println!("# kill EVERY session for this account (its subject):");
        println!("{subject}");
    }
    Ok(())
}

fn attenuate(args: &[String]) -> Result<(), String> {
    let enc = flag(args, "--cred").ok_or("missing --cred <dga1_>")?;
    let cred = Credential::decode(enc.trim()).map_err(|e| e.to_string())?;
    let caps = caps_list(args)?;
    let until = until_opt(args)?;
    let narrowed = attenuate_caps(cred, caps, until);
    println!("{}", narrowed.encode());
    Ok(())
}

fn explain(args: &[String]) -> Result<(), String> {
    let enc = flag(args, "--cred").ok_or("missing --cred <dga1_>")?;
    let cred = Credential::decode(enc.trim()).map_err(|e| e.to_string())?;
    println!("{}", cred.explain());
    Ok(())
}
