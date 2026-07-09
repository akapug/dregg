//! THE WELD — Hermes runs as a grain-jail CONFINED BODY, not just tool-call-gated.
//!
//! The confined Hermes body (a brain-driven `HermesAgentPeer` over the on-box
//! `LocalBrain`) rides a `grain_jail::BodyChannel` ([`AcpBodyChannel`]): each ACP
//! `session/request_permission` it raises is a `grain_jail::Proposal`; each host
//! `grain_jail::Verdict` is fed back as the ACP permission outcome. The host gates
//! every proposal through the PROVEN [`HermesGateway`] / `ToolGateway` — so the
//! interception STAYS under confinement.
//!
//! Three poles, each biting:
//!   (i)   GATED-UNDER-CONFINEMENT — a tool-call the confined body emits over the
//!         `BodyChannel` STILL becomes a cap-gated, RECEIPTED dregg turn.
//!   (ii)  ONE-EGRESS-DOOR / OUT-OF-DOOR-DENIED — the body's confinement grants
//!         EXACTLY the model endpoint and denies every sibling/host/path. Portable:
//!         the door WIRING. macOS: a REAL firmament PD proves the jail EPERMs an
//!         out-of-door connect while the one granted door is reachable, its ACP
//!         stream riding the grain-jail channel.
//!   (iii) IN-BAND-REFUSAL-SEEN — a denied proposal's refusal rides back over the
//!         channel; the confined body SEES it and continues (it does not escape).
//!
//! Run: `cd deos-hermes && cargo test --test confined_body_weld`

use std::sync::{Arc, RwLock};

use deos_hermes::{
    GrantRegistry, HermesGateway, LocalBrain, confined_hermes_channel, drive_confined_hermes,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// A session gateway with the standard per-tool floors (everything the on-box
/// brain reaches for is granted).
fn open_gateway(rt: &AgentRuntime, root: HeldToken) -> HermesGateway<'_> {
    let registry =
        GrantRegistry::default_for_session(1_000_000).with_standard_tool_grants(1_000_000);
    HermesGateway::new(rt, root, registry)
}

/// (i) GATED-UNDER-CONFINEMENT — the confined Hermes body proposes tool-calls over
/// the grain-jail `BodyChannel`; each is STILL a cap-gated, RECEIPTED dregg turn
/// through the proven gateway. The interception is preserved under confinement.
#[test]
fn confined_body_tool_call_is_still_a_receipted_gated_turn() {
    let (rt, root) = grantor();
    let mut gateway = open_gateway(&rt, root);

    // The confined body reaches the host ONLY through the channel — no ambient I/O.
    let mut channel = confined_hermes_channel(
        "sess-weld",
        LocalBrain::new(),
        "/deos/confined",
        "search the docs then read the source",
    );
    let report =
        drive_confined_hermes(&mut channel, &mut gateway, 100).expect("drive the confined body");

    // The body proposed at least one tool-call, and every admitted proposal left a
    // real 64-hex dregg receipt (a committed metered turn on the verified executor).
    assert!(
        report.proposals >= 1,
        "the confined body proposed tool-calls over the BodyChannel, got {}",
        report.proposals
    );
    assert!(
        report.admitted >= 1,
        "a proposal the confined body emitted became a receipted turn, got {} admits",
        report.admitted
    );
    assert_eq!(
        report.receipts.len(),
        report.admitted,
        "every admitted proposal carries a receipt"
    );
    for r in &report.receipts {
        assert_eq!(r.len(), 64, "a real hex 32-byte turn hash: {r}");
        assert!(r.chars().all(|c| c.is_ascii_hexdigit()), "hex receipt: {r}");
    }
    // The gateway metered the confined body's admitted turns (the interception ran).
    assert!(
        gateway.calls_made(deos_hermes::ToolKind::Fetch)
            + gateway.calls_made(deos_hermes::ToolKind::Read)
            >= 1,
        "the confined body's proposals metered on the gateway"
    );
    // The body finished its turn cleanly (it did not wedge or escape).
    assert!(
        !channel.agent_text().is_empty(),
        "the confined body streamed its own account of the turn"
    );
}

/// (iii) IN-BAND-REFUSAL-SEEN — a denied proposal's refusal rides back over the
/// channel; the confined body SEES it and continues (adapts, does not escape). The
/// same grain-jail `Verdict` → ACP outcome path the gateway drives.
#[test]
fn in_band_refusal_is_surfaced_to_the_confined_body_which_continues() {
    let (rt, root) = grantor();
    // Deny `write_file` outright (rate 0); everything else within the floors.
    let registry = GrantRegistry::default_for_session(1_000_000)
        .with_standard_tool_grants(1_000_000)
        .with_grant_for_tool_deny("write_file");
    let mut gateway = HermesGateway::new(&rt, root, registry);

    // A prompt that makes the on-box brain reach for a search AND a write; the write
    // is refused in-band, and the brain must adapt (drop the denied tool, fall back).
    let mut channel = confined_hermes_channel(
        "sess-weld-refuse",
        LocalBrain::new(),
        "/deos/confined",
        "search for dregg then write a notes file",
    );
    let report = drive_confined_hermes(&mut channel, &mut gateway, 200)
        .expect("drive the confined body through a partially-denying gateway");

    // THE GATE REFUSED the over-cap tool in-band, naming the leg that bit…
    assert!(
        report.refused >= 1,
        "the denied write_file was refused in-band, got {} refusals",
        report.refused
    );
    let bit = report
        .refusals
        .iter()
        .any(|r| r.contains("rate") || r.contains("scope"));
    assert!(
        bit,
        "the refusal names the leg that bit: {:?}",
        report.refusals
    );

    // …the confined body SAW the refusal and CONTINUED: it reached the denied tool
    // (write_file), and STILL landed at least one receipted turn (the search / the
    // read-only fallback the brain injected after the refusal).
    let reached_write = channel
        .tool_calls_seen()
        .iter()
        .any(|c| c.name == "write_file");
    assert!(
        reached_write,
        "the confined body reached for the denied write_file"
    );
    assert!(
        report.admitted >= 1,
        "the body adapted and still committed a receipted turn under confinement"
    );
    // The brain's own summary shows it worked WITHIN the caps (it did not escape).
    assert!(
        channel.agent_text().contains("refused by confinement")
            || channel.agent_text().contains("within the caps"),
        "the confined body's account acknowledges the confinement: {:?}",
        channel.agent_text()
    );

    // The denied tool never committed a turn (fail-closed).
    assert_eq!(
        gateway.calls_made(deos_hermes::ToolKind::Edit),
        0,
        "the denied write_file never advanced a counter"
    );
}

/// (ii, portable) ONE-EGRESS-DOOR WIRING — the confined body's egress policy grants
/// EXACTLY the model endpoint and denies every other host, port, and path. This is
/// the door the jailed body's ONLY outbound reach rides; everything else is sealed.
#[cfg(unix)]
#[test]
fn the_one_egress_door_admits_only_the_model_endpoint() {
    use deos_hermes::model_egress_policy;

    let policy = model_egress_policy("http://127.0.0.1:8899/v1");
    // Exactly the model endpoint is a door…
    assert!(
        policy.admits_connect("127.0.0.1", 8899),
        "the granted model endpoint is the one door"
    );
    // …and NOTHING else: not another port, not another host, not a file path.
    assert!(
        !policy.admits_connect("127.0.0.1", 9999),
        "other port denied"
    );
    assert!(!policy.admits_connect("1.1.1.1", 8899), "other host denied");
    assert!(
        !policy.admits_connect("api.anthropic.com", 443),
        "other provider denied"
    );
    assert!(!policy.admits_read("/etc/passwd"), "host file reads denied");
    assert!(!policy.admits_read("/deos/confined"), "cwd read denied");
    assert!(!policy.is_sealed(), "the model door is an egress grant");

    // A base URL with no host grants NO door (sealed) — fail-closed.
    assert!(
        model_egress_policy("").is_sealed(),
        "a hostless base URL opens no door"
    );
}

/// (ii, macOS) OUT-OF-DOOR-DENIED, FOR REAL — the confined Hermes body runs INSIDE
/// an OS-sandboxed firmament PD with exactly one granted egress door (a mock model
/// endpoint). Its ACP tool-call stream rides the grain-jail `BodyChannel`; the
/// gateway receipts each proposal; and the jail EPERMs an out-of-door connect while
/// the one granted door is reachable — the body is genuinely OS-confined.
#[cfg(target_os = "macos")]
#[test]
fn a_real_jailed_hermes_body_drives_over_the_channel_with_one_egress_door() {
    use deos_hermes::{drive_confined_hermes_in_jail, model_egress_policy};
    use dregg_firmament::process_kernel::ProcessKernel;
    use std::net::TcpListener;

    // The MOCK MODEL door: a listener the jailed body may connect to (the one
    // granted endpoint). A live model replaces this — the named seam.
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind mock model door");
    let model_addr = listener.local_addr().unwrap();
    let granted = ("127.0.0.1", model_addr.port());
    // An out-of-door endpoint the jail must EPERM (a sibling of the granted door).
    let ungranted = ("127.0.0.1", model_addr.port().wrapping_add(1).max(2));

    // The one egress door: exactly the mock model endpoint, everything else sealed.
    let egress = model_egress_policy(&format!("http://127.0.0.1:{}", model_addr.port()));

    let (rt, root) = grantor();
    let mut gateway = open_gateway(&rt, root);

    let kernel = ProcessKernel::new();
    let (report, jail_verdict) = drive_confined_hermes_in_jail(
        &kernel,
        &egress,
        &mut gateway,
        "sess-weld-jail",
        "search the docs then read the source",
        LocalBrain::new(),
        Some(granted),
        Some(ungranted),
    )
    .expect("drive the real firmament-jailed Hermes body over the grain-jail channel");

    use deos_hermes::confined::probe;

    // The four base jail teeth held — the body is OS-confined (file/net/exec/extra-fd
    // denied bar the Endpoint).
    assert_eq!(
        jail_verdict & probe::ALL,
        probe::ALL,
        "the confined body is genuinely OS-jailed; verdict=0x{jail_verdict:x}"
    );
    // The ONE granted door was reachable, and the out-of-door endpoint was DENIED —
    // the door is to a SPECIFIC endpoint, not "the network".
    assert!(
        jail_verdict & probe::EGRESS_NET_GRANTED_OPEN != 0,
        "the granted model door was reachable; verdict=0x{jail_verdict:x}"
    );
    assert!(
        jail_verdict & probe::EGRESS_NET_SIBLING_DENIED != 0,
        "an out-of-door connect stayed EPERM'd; verdict=0x{jail_verdict:x}"
    );

    // GATED-UNDER-REAL-CONFINEMENT — the jailed body's proposals rode the grain-jail
    // channel and each admitted one is a real receipted turn.
    assert!(
        report.admitted >= 1,
        "the real jailed body's tool-calls were gated + receipted over the channel"
    );
    for r in &report.receipts {
        assert_eq!(r.len(), 64, "a real hex receipt from the jailed run: {r}");
    }
}
