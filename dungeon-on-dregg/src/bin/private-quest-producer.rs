//! Offline client for the hosted private semantic quest.
//!
//! It owns the hidden graph, match, rule choice, and blindings only for the
//! lifetime of this process, then writes the two canonical opaque receipts a
//! player can submit through the web proof controls or the Telegram/Discord
//! operation route. No witness or hidden graph is serialized.

use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};

use dungeon_on_dregg::private_quest::{
    PrivateQuestMove, PrivateQuestRaid, encode_private_quest_receipt,
};

fn usage(program: &str) -> String {
    format!(
        "usage: {program} <babybear-session-id> <new-output-directory>\n\
         produces step-0.fhquest and step-1.fhquest; existing files are never overwritten"
    )
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("refusing to create {}: {error}", path.display()))?;
    file.write_all(bytes)
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("cannot durably write {}: {error}", path.display()))
}

fn run() -> Result<(PathBuf, PathBuf), String> {
    const BABYBEAR_P: u32 = 2_013_265_921;
    let mut args = std::env::args();
    let program = args
        .next()
        .unwrap_or_else(|| "dungeon-private-quest-producer".to_string());
    let session = args
        .next()
        .ok_or_else(|| usage(&program))?
        .parse::<u32>()
        .map_err(|_| "session id must be a canonical u32".to_string())?;
    if session >= BABYBEAR_P {
        return Err(format!(
            "session id {session} is outside the BabyBear field (must be < {})",
            BABYBEAR_P
        ));
    }
    let output = PathBuf::from(args.next().ok_or_else(|| usage(&program))?);
    if args.next().is_some() {
        return Err(usage(&program));
    }
    fs::create_dir_all(&output)
        .map_err(|error| format!("cannot create {}: {error}", output.display()))?;

    let mut producer = PrivateQuestRaid::new(session).map_err(|error| error.to_string())?;
    let first = producer
        .advance(producer.command(PrivateQuestMove::ScoutVeiledRoute))
        .map_err(|error| error.to_string())?;
    let second = producer
        .advance(producer.command(PrivateQuestMove::BreakWardenSeal))
        .map_err(|error| error.to_string())?;
    let first = encode_private_quest_receipt(&first).map_err(|error| error.to_string())?;
    let second = encode_private_quest_receipt(&second).map_err(|error| error.to_string())?;

    let first_path = output.join("step-0.fhquest");
    let second_path = output.join("step-1.fhquest");
    write_new(&first_path, &first)?;
    if let Err(error) = write_new(&second_path, &second) {
        // The first receipt is independently valid and intentionally retained;
        // report the partial output rather than destructively deleting it.
        return Err(format!(
            "{error}; {} was already written and remains usable",
            first_path.display()
        ));
    }
    Ok((first_path, second_path))
}

fn main() {
    match run() {
        Ok((first, second)) => {
            println!("wrote {}", first.display());
            println!("wrote {}", second.display());
            println!(
                "upload in order as application/vnd.dregg.private-quest-reduction.v1+postcard"
            );
        }
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(2);
        }
    }
}
