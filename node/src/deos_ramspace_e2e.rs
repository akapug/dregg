//! DEOS-RAMSPACE: two signed agents coordinate through a hosted deos private server
//! whose node data directory is backed by /dev/shm.
//!
//! This is the owner-priority substrate probe: no cockpit, no new client surface. The
//! existing deos-host publishes a private-server affordance surface, and two independent
//! AgentCipherclerks fire signed turns over the node's `/turns/submit` HTTP ingress.
#![cfg(all(test, feature = "deos-host"))]

use std::io::Write;
use std::net::SocketAddr;
use std::path::Path;
use std::process::Command;
use std::time::{Duration, Instant};

use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::action::Effect;
use zeroize::Zeroizing;

use crate::state::NodeState;

const RAMSPACE_CHILD_ENV: &str = "DREGG_DEOS_RAMSPACE_CHILD";
const RAMSPACE_TEST_NAME: &str =
    "deos_ramspace_e2e::ramspace_deos_private_server_coordinates_two_agents_over_http";

#[cfg(target_os = "linux")]
unsafe extern "C" {
    #[link_name = "_exit"]
    fn exit_without_atexit(status: std::os::raw::c_int) -> !;
}

struct ProbeAgent {
    name: &'static str,
    clerk: AgentCipherclerk,
    cell: CellId,
    pubkey: [u8; 32],
}

#[derive(Debug)]
struct StepReport {
    actor: &'static str,
    method: &'static str,
    receipt_hash: String,
    previous_receipt_hash: Option<String>,
    latency: Duration,
}

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn default_token_id() -> [u8; 32] {
    *blake3::hash(b"default").as_bytes()
}

fn hex_of(id: &CellId) -> String {
    dregg_types::hex_encode(id.as_bytes())
}

fn hex32(bytes: &[u8; 32]) -> String {
    dregg_types::hex_encode(bytes)
}

fn agent_cell_for(pubkey: &[u8; 32]) -> CellId {
    CellId(dregg_cell::CellId::derive_raw(pubkey, &default_token_id()).0)
}

fn forked_cell_for(seed: &str) -> CellId {
    let public_key = *blake3::hash(seed.as_bytes()).as_bytes();
    CellId(dregg_cell::CellId::derive_raw(&public_key, &default_token_id()).0)
}

fn pack_u64(v: u64) -> dregg_cell::state::FieldElement {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

fn unpack_u64(fe: &dregg_cell::state::FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

fn seeded_agent(name: &'static str, seed: &'static [u8]) -> ProbeAgent {
    let clerk = AgentCipherclerk::from_key_bytes(Zeroizing::new(*blake3::hash(seed).as_bytes()));
    let pubkey = clerk.public_key().0;
    let cell = agent_cell_for(&pubkey);
    ProbeAgent {
        name,
        clerk,
        cell,
        pubkey,
    }
}

async fn mint_agent_cell(state: &NodeState, agent: &ProbeAgent) {
    let mut s = state.write().await;
    let mut cell = Cell::with_balance(agent.pubkey, default_token_id(), 1_000_000);
    cell.permissions = open_permissions();
    assert_eq!(cell.id(), agent.cell, "{} cell id derivation", agent.name);
    s.ledger
        .insert_cell(cell)
        .unwrap_or_else(|e| panic!("insert {} agent cell: {e}", agent.name));
}

async fn board_field(state: &NodeState, board: &CellId, index: usize) -> u64 {
    let s = state.read().await;
    s.ledger
        .get(board)
        .expect("board cell present")
        .state
        .get_field(index)
        .map(unpack_u64)
        .unwrap_or(0)
}

async fn fire_step(
    state: &NodeState,
    node_url: &str,
    agent: &ProbeAgent,
    method: &'static str,
    effects: Vec<Effect>,
    federation_id: &str,
) -> StepReport {
    let (before_len, expected_prev) = {
        let s = state.read().await;
        let chain = s.cclerk.receipt_chain();
        (chain.len(), chain.last().map(|r| r.receipt_hash()))
    };

    let started = Instant::now();
    let outcome = dregg_sdk_net::fire_affordance(
        node_url,
        &agent.clerk,
        agent.cell,
        method,
        effects,
        federation_id,
    )
    .await
    .unwrap_or_else(|e| panic!("{} fires {method}: {e}", agent.name));
    let latency = started.elapsed();

    assert!(
        outcome.accepted,
        "{} {method} accepted; error={:?}",
        agent.name, outcome.error
    );

    let (after_len, receipt) = {
        let s = state.read().await;
        let chain = s.cclerk.receipt_chain();
        (
            chain.len(),
            chain.last().expect("fire appends receipt").clone(),
        )
    };
    assert_eq!(
        after_len,
        before_len + 1,
        "{method} appended exactly one receipt"
    );
    assert_eq!(
        receipt.previous_receipt_hash, expected_prev,
        "{method} threads the prior chain head"
    );
    assert_eq!(
        receipt.agent, agent.cell,
        "{method} receipt agent is the firing agent"
    );
    if let Some(turn_hash) = outcome.turn_hash.as_deref() {
        assert_eq!(
            turn_hash,
            hex32(&receipt.turn_hash),
            "{method} response names the committed turn"
        );
    }

    StepReport {
        actor: agent.name,
        method,
        receipt_hash: hex32(&receipt.receipt_hash()),
        previous_receipt_hash: receipt.previous_receipt_hash.map(|h| hex32(&h)),
        latency,
    }
}

fn assert_receipt_segment_links(
    chain: &[dregg_turn::TurnReceipt],
    base_len: usize,
    expected_new: usize,
) {
    assert_eq!(
        chain.len(),
        base_len + expected_new,
        "every coordination act produced one receipt"
    );
    for idx in base_len..chain.len() {
        assert_eq!(
            chain[idx].previous_receipt_hash,
            idx.checked_sub(1).map(|prev| chain[prev].receipt_hash()),
            "receipt {idx} links to the immediately prior receipt"
        );
    }
}

fn assert_ram_backed_data_dir(data_dir: &Path) {
    let shm = Path::new("/dev/shm");
    assert!(shm.is_dir(), "/dev/shm is required for DEOS-RAMSPACE");
    let canonical_data = data_dir
        .canonicalize()
        .expect("canonical ramspace data dir");
    let canonical_shm = shm.canonicalize().expect("canonical /dev/shm");
    assert!(
        canonical_data.starts_with(&canonical_shm),
        "data dir {} is not under /dev/shm",
        canonical_data.display()
    );
    assert!(
        data_dir.join("dregg.redb").exists(),
        "NodeState store lives under the RAM-backed data dir"
    );
    assert!(
        data_dir.join("node.key").exists(),
        "NodeState key file lives under the RAM-backed data dir"
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn ramspace_deos_private_server_coordinates_two_agents_over_http() {
    #[cfg(not(target_os = "linux"))]
    {
        eprintln!("DEOS-RAMSPACE skipped: /dev/shm ramspace probe is Linux-specific");
        return;
    }

    #[cfg(target_os = "linux")]
    {
        if std::env::var_os(RAMSPACE_CHILD_ENV).is_none() {
            run_ramspace_probe_child_process();
            return;
        }

        run_ramspace_probe_body().await;
        let _ = std::io::stdout().flush();
        let _ = std::io::stderr().flush();
        // The deos host owns a process-global SpiderMonkey runtime on a long-lived
        // thread. The probe has already asserted success; avoid C++ teardown races.
        unsafe { exit_without_atexit(0) }
    }
}

#[cfg(target_os = "linux")]
fn run_ramspace_probe_child_process() {
    let output = Command::new(std::env::current_exe().expect("current test binary"))
        .arg("--exact")
        .arg(RAMSPACE_TEST_NAME)
        .arg("--nocapture")
        .env(RAMSPACE_CHILD_ENV, "1")
        .output()
        .expect("spawn isolated DEOS-RAMSPACE child test");

    std::io::stdout()
        .write_all(&output.stdout)
        .expect("relay child stdout");
    std::io::stderr()
        .write_all(&output.stderr)
        .expect("relay child stderr");

    assert!(
        output.status.success(),
        "isolated DEOS-RAMSPACE child failed with status {}",
        output.status
    );
}

#[cfg(target_os = "linux")]
async fn run_ramspace_probe_body() {
    let _ = rustls::crypto::ring::default_provider().install_default();

    let tmp = tempfile::Builder::new()
        .prefix("dregg-deos-ramspace-")
        .tempdir_in("/dev/shm")
        .expect("create /dev/shm-backed data dir");
    let state = NodeState::new(tmp.path(), vec![]).expect("build NodeState on /dev/shm");
    assert_ram_backed_data_dir(tmp.path());
    {
        let mut s = state.write().await;
        s.unlocked = true;
    }

    let claude = seeded_agent("claude", b"deos-ramspace-claude");
    let codex = seeded_agent("codex", b"deos-ramspace-codex");
    mint_agent_cell(&state, &claude).await;
    mint_agent_cell(&state, &codex).await;

    let program = r#"
            var board = deos.server.fork("ramspace-board");
            deos.server.grant("__CLAUDE__", board, "none");
            deos.server.grant("__CODEX__", board, "none");
            ["claim_slot", "release_slot", "post_note", "read_board"].forEach(function(name) {
                deos.server.defineAffordance({
                    name: name,
                    required: "signature",
                    instance: board
                });
            });
            (board && board.length === 64) ? 1 : 0;
        "#
    .replace("__CLAUDE__", &hex_of(&claude.cell))
    .replace("__CODEX__", &hex_of(&codex.cell));

    let _server_cell = crate::deos_host::host_server_program(
        &state,
        "ramspace-coordination-server",
        AuthRequired::None,
        program,
    )
    .await
    .expect("host ramspace coordination server");

    let board = forked_cell_for("ramspace-board");
    let board_hex = hex_of(&board);
    {
        let s = state.read().await;
        assert!(s.ledger.get(&board).is_some(), "board cell lives on ledger");
        let specs = s
            .deos_server_surfaces
            .get(&board)
            .expect("board surface is published");
        for name in ["claim_slot", "release_slot", "post_note", "read_board"] {
            assert!(
                specs.iter().any(|(n, _)| n == name),
                "board surface exposes {name}"
            );
        }
    }

    let metrics_handle = crate::metrics::install_recorder();
    let router = crate::api::router_with_cors(
        state.clone(),
        false,
        metrics_handle,
        std::collections::HashSet::new(),
    );
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0")
        .await
        .expect("bind ephemeral port");
    let addr = listener.local_addr().expect("local addr");
    let server = tokio::spawn(async move {
        axum::serve(
            listener,
            router.into_make_service_with_connect_info::<SocketAddr>(),
        )
        .await
        .expect("serve");
    });
    let node_url = format!("http://{addr}");

    let discovery = dregg_sdk_net::discover_server_affordances(&node_url, &board_hex, "signature")
        .await
        .expect("discover board surface");
    for name in ["claim_slot", "release_slot", "post_note", "read_board"] {
        assert!(discovery.has(name), "signature viewer discovers {name}");
    }

    let base_len = {
        let s = state.read().await;
        s.cclerk.receipt_chain_length()
    };

    let mut reports = Vec::new();
    let mut observed_claim_slots = std::collections::BTreeSet::new();
    reports.push(
        fire_step(
            &state,
            &node_url,
            &claude,
            "claim_slot",
            vec![Effect::SetField {
                cell: board,
                index: 0,
                value: pack_u64(1),
            }],
            &discovery.executor_federation_id,
        )
        .await,
    );
    assert!(
        observed_claim_slots.insert(0),
        "claim_slot transcript does not double-claim slot 0"
    );
    assert_eq!(
        board_field(&state, &board, 0).await,
        1,
        "claude owns slot 0"
    );

    reports.push(
        fire_step(
            &state,
            &node_url,
            &codex,
            "claim_slot",
            vec![Effect::SetField {
                cell: board,
                index: 1,
                value: pack_u64(1),
            }],
            &discovery.executor_federation_id,
        )
        .await,
    );
    assert!(
        observed_claim_slots.insert(1),
        "claim_slot transcript does not double-claim slot 1"
    );
    assert_eq!(board_field(&state, &board, 1).await, 1, "codex owns slot 1");

    reports.push(
        fire_step(
            &state,
            &node_url,
            &claude,
            "post_note",
            vec![Effect::SetField {
                cell: board,
                index: 2,
                value: pack_u64(101),
            }],
            &discovery.executor_federation_id,
        )
        .await,
    );
    reports.push(
        fire_step(
            &state,
            &node_url,
            &codex,
            "post_note",
            vec![Effect::SetField {
                cell: board,
                index: 3,
                value: pack_u64(202),
            }],
            &discovery.executor_federation_id,
        )
        .await,
    );

    reports.push(
        fire_step(
            &state,
            &node_url,
            &claude,
            "read_board",
            vec![Effect::SetField {
                cell: board,
                index: 4,
                value: pack_u64(1),
            }],
            &discovery.executor_federation_id,
        )
        .await,
    );
    reports.push(
        fire_step(
            &state,
            &node_url,
            &codex,
            "read_board",
            vec![Effect::SetField {
                cell: board,
                index: 5,
                value: pack_u64(1),
            }],
            &discovery.executor_federation_id,
        )
        .await,
    );

    reports.push(
        fire_step(
            &state,
            &node_url,
            &codex,
            "release_slot",
            vec![Effect::SetField {
                cell: board,
                index: 1,
                value: pack_u64(0),
            }],
            &discovery.executor_federation_id,
        )
        .await,
    );

    assert_eq!(
        board_field(&state, &board, 0).await,
        1,
        "slot 0 remains held"
    );
    assert_eq!(board_field(&state, &board, 1).await, 0, "slot 1 released");
    assert_eq!(
        board_field(&state, &board, 2).await,
        101,
        "claude note posted"
    );
    assert_eq!(
        board_field(&state, &board, 3).await,
        202,
        "codex note posted"
    );
    assert_eq!(
        board_field(&state, &board, 4).await,
        1,
        "claude read marker"
    );
    assert_eq!(board_field(&state, &board, 5).await, 1, "codex read marker");

    let chain = {
        let s = state.read().await;
        s.cclerk.receipt_chain().to_vec()
    };
    assert_receipt_segment_links(&chain, base_len, reports.len());
    assert!(
        chain[base_len..].iter().any(|r| r.agent == claude.cell),
        "claude receipts present"
    );
    assert!(
        chain[base_len..].iter().any(|r| r.agent == codex.cell),
        "codex receipts present"
    );

    let latency_ms: Vec<String> = reports
        .iter()
        .map(|r| format!("{}:{}={}ms", r.actor, r.method, r.latency.as_millis()))
        .collect();
    let receipt_span: Vec<String> = reports
        .iter()
        .map(|r| {
            format!(
                "{}:{} receipt={} prev={}",
                r.actor,
                r.method,
                r.receipt_hash,
                r.previous_receipt_hash.as_deref().unwrap_or("none")
            )
        })
        .collect();
    eprintln!(
        "DEOS-RAMSPACE transcript: claude claim_slot(0) -> codex claim_slot(1) -> notes(101,202) -> both read_board -> codex release_slot(1)"
    );
    eprintln!("DEOS-RAMSPACE latencies: {}", latency_ms.join(", "));
    eprintln!("DEOS-RAMSPACE receipts: {}", receipt_span.join(" | "));
    eprintln!(
        "DEOS-RAMSPACE panel: coordinating in the ledger is OS-like at the binding layer; AX-native surface and conflict-prevention CAS remain follow-up work."
    );

    server.abort();
}
