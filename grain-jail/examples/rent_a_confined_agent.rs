//! `rent_a_confined_agent` — a runnable demo of the confined-body grain.
//!
//! Rent a grain, drive it with a body that speaks only the confined-body line
//! protocol, and watch every action get cap-gated, metered, minted as a
//! committed kernel turn, and verified (R2) by the renter.
//!
//! ```text
//! cargo run -p grain-jail --example rent_a_confined_agent
//! cargo run -p grain-jail --example rent_a_confined_agent --features real-jail
//! ```
//!
//! Without a feature the body runs in-process. With `--features real-jail` the
//! SAME body runs in a firmament OS-jail (macOS Seatbelt / Linux seccomp+
//! Landlock) — file/net/exec denied — and the drive is byte-for-byte the same,
//! because the jail is just a swap of the channel's backing transport.

use agent_platform::AgentPlatform;
use dregg_agent::agent::AgentBrain;
use dregg_types::CellId;
use grain_jail::ConfinedBrain;
use grain_jail::protocol::{BodyMsg, DoneNote, Proposal};
use hosted_lease::LeaseTerms;

fn cid(n: u8) -> CellId {
    CellId::from_bytes([n; 32])
}

/// The body's proposed work: write two of the grain's own cells, then finish.
fn body_script() -> Vec<BodyMsg> {
    vec![
        BodyMsg::Propose(Proposal {
            tool: "cell-write".into(),
            amount_cents: None,
            path: Some("notes/1".into()),
            value: Some("hello from a confined agent".into()),
        }),
        BodyMsg::Propose(Proposal {
            tool: "cell-write".into(),
            amount_cents: None,
            path: Some("notes/2".into()),
            value: Some("every turn is auditable".into()),
        }),
        BodyMsg::Done(DoneNote::default()),
    ]
}

/// Drive the grain with `brain`, then print what the renter can verify.
fn drive_and_report(platform: &AgentPlatform, host: &str, brain: &mut dyn AgentBrain) {
    let report = platform
        .drive_serving(host, "write my notes", brain)
        .expect("the confined body drives the grain");
    println!(
        "  the grain admitted {} action(s) — each cap-gated, metered, and minted \
         as a committed kernel turn",
        report.admitted
    );
    if report.cap_refused > 0 {
        println!(
            "  {} proposal(s) were cap-refused (the body cannot exceed its caps)",
            report.cap_refused
        );
    }
    println!(
        "  the lease meter drew down {} budget unit(s)",
        platform.consumed(host).unwrap()
    );

    let r2 = platform.verify_r2(host).expect("R2 verify");
    println!(
        "  R2: the renter verified {}/{} turns are views over committed kernel turns",
        r2.linked, report.admitted
    );
    let att = platform.attest(host).expect("attest");
    let forged_ok = att.verify_r2(&[[0u8; 32]]).is_ok();
    println!(
        "  anti-forgery: a manifest naming turns never committed is {}",
        if forged_ok {
            "ACCEPTED (BUG!)"
        } else {
            "refused"
        }
    );
}

fn main() {
    let platform = AgentPlatform::new();
    let wd = std::env::temp_dir().join(format!("confined-agent-demo-{}", std::process::id()));
    std::fs::create_dir_all(&wd).unwrap();

    // provider=2, lease cell=7, asset=9; rent 100 every 50 blocks from 1000.
    let terms = LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0);
    let host = platform
        .rent(
            "demo.agents.dregg",
            "dga1_demo",
            "cell:notes/1,cell:notes/2",
            10_000,
            wd.to_str().unwrap(),
            terms,
            None,
        )
        .expect("provision the confined grain");

    println!("rented a confined grain at `{host}`");
    println!(
        "  caps: cell:notes/1, cell:notes/2  (a raw `shell` would be refused — hosted session)"
    );

    #[cfg(not(feature = "real-jail"))]
    {
        use grain_jail::LineChannel;
        use std::io::Cursor;
        let mut buf = String::new();
        for m in body_script() {
            buf.push_str(&serde_json::to_string(&m).unwrap());
            buf.push('\n');
        }
        let channel = LineChannel::new(Cursor::new(buf.into_bytes()), Vec::new());
        let mut brain = ConfinedBrain::new(channel);
        println!("driving with an IN-PROCESS body over the line protocol...");
        drive_and_report(&platform, &host, &mut brain);
        println!("(rebuild with `--features real-jail` to run the SAME body OS-jailed)");
    }

    #[cfg(feature = "real-jail")]
    {
        use grain_jail::jail::spawn_confined_body;
        use std::io::{BufRead, BufReader, Write};

        let lines: Vec<Vec<u8>> = body_script()
            .iter()
            .map(|m| {
                let mut s = serde_json::to_string(m).unwrap();
                s.push('\n');
                s.into_bytes()
            })
            .collect();
        let n_proposals = lines.len() - 1;

        let kernel = dregg_firmament::process_kernel::ProcessKernel::new();
        let (handle, channel) = spawn_confined_body(&kernel, move |surf| {
            // Prove the ambient jail: a host-file read must be denied.
            if std::fs::File::open("/etc/passwd").is_ok() {
                return 77;
            }
            let mut w = match surf.try_clone() {
                Ok(w) => w,
                Err(_) => return 66,
            };
            let mut r = BufReader::new(surf);
            for (i, line) in lines.iter().enumerate() {
                if w.write_all(line).and_then(|_| w.flush()).is_err() {
                    return 66;
                }
                if i < n_proposals {
                    let mut discard = String::new();
                    if r.read_line(&mut discard).map(|n| n == 0).unwrap_or(true) {
                        return 66;
                    }
                }
            }
            0
        })
        .expect("spawn the OS-jailed body");

        let mut brain = ConfinedBrain::new(channel);
        println!("driving with an OS-JAILED body (firmament process-PD: file/net/exec denied)...");
        drive_and_report(&platform, &host, &mut brain);
        let code = handle.join().expect("join the jailed body");
        println!(
            "  the body ran OS-jailed and was DENIED /etc/passwd; exit {code} \
             (77 would be a confinement leak)"
        );
    }

    println!(
        "\nA renter rented a confined agent, watched it work, and verified every action \
              against the chain — without trusting the host."
    );
}
