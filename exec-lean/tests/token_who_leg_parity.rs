//! The TOKEN WHO leg, decided by both executors on the covered path.
//!
//! An SDK `SubAgent` presents `Authorization::Token { key_ref: BiscuitIssuer, encoded }` on every
//! worker turn: a biscuit granting `service(hex(cell), hex(method))`, issued by the key the worker
//! cell names as its verification key. The Rust executor admits it through
//! `TurnExecutor::verify_token_credential`; the verified kernel's WHO leg is
//! `portalVerify (.token key sig)`, and the producer marshaller folds the executor's verdict into
//! that pair (`lean_shadow::token_echo_wire`).
//!
//! Until that fold, the wire carried the 256-bit issuer key against a 64-bit credential hash, which
//! can never be equal, so Lean refused every token turn Rust committed: `LeanShadowVeto` on every
//! SDK worker turn once those turns carried a `valid_until` (issue #46). These tests drive a turn of
//! exactly that shape through `produce_via_lean` and assert that the turn is COVERED and that the two
//! executors AGREE, on the admit pole and on the refusal poles.
//!
//! Run (needs the Lean archive):
//!   DREGG_TEST_REQUIRE_LEAN=1 cargo nextest run -p dregg-exec-lean --test token_who_leg_parity

use dregg_cell::{Cell, CellId, Ledger, VerificationKey};
use dregg_token::AuthToken;
use dregg_token::biscuit_auth::KeyPair;
use dregg_turn::action::TokenKeyRef;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

const HEIGHT: u64 = 1000;
const METHOD: [u8; 32] = [0x11; 32];
const OTHER_METHOD: [u8; 32] = [0x22; 32];

fn executor() -> TurnExecutor {
    let mut executor = TurnExecutor::new(ComputronCosts::zero())
        .with_shadow_observer(dregg_exec_lean::LeanShadowObserver::arc());
    executor.set_block_height(HEIGHT);
    executor
}

fn issuer_bytes(kp: &KeyPair) -> [u8; 32] {
    kp.public()
        .to_bytes()
        .try_into()
        .expect("ed25519 pk is 32 bytes")
}

/// The worker cell as `AgentRuntime::spawn_sub_agent_scoped_with` creates it: a funded cell whose
/// verification key is the biscuit issuer.
fn worker_ledger(issuer: [u8; 32]) -> (Ledger, CellId) {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    pk[31] = 9;
    let mut cell = Cell::with_balance(pk, [0u8; 32], 100_000);
    cell.verification_key = Some(VerificationKey {
        hash: *blake3::hash(&issuer).as_bytes(),
        data: issuer.to_vec(),
    });
    let id = cell.id();
    let mut l = Ledger::new();
    l.insert_cell(cell).unwrap();
    (l, id)
}

/// A credential of the shape `sdk::runtime::mint_subagent_cap_token` mints.
fn credential(kp: &KeyPair, cell: CellId, method: [u8; 32]) -> Vec<u8> {
    let services = vec![(hex::encode(cell.as_bytes()), hex::encode(method))];
    dregg_token::BiscuitToken::mint_dregg(kp, &[], &services, &[], &[], &[], None)
        .expect("mint")
        .to_encoded()
        .expect("encode")
        .into_bytes()
}

/// The SDK worker's turn fee (`SubAgent::execute_method`).
const WORKER_FEE: u64 = 5_000;

/// The worker turn as `SubAgent::execute_method` builds it: one `IncrementNonce` under the token
/// and a height deadline, with the given fee.
fn worker_turn(
    agent: CellId,
    method: [u8; 32],
    encoded: Vec<u8>,
    issuer: [u8; 32],
    fee: u64,
) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method,
        args: vec![],
        authorization: Authorization::Token {
            encoded,
            key_ref: TokenKeyRef::BiscuitIssuer {
                issuer_pubkey: issuer,
            },
        },
        preconditions: Default::default(),
        effects: vec![Effect::IncrementNonce { cell: agent }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce: 0,
        call_forest: forest,
        fee,
        memo: None,
        valid_until: Some(dregg_turn::valid_until_at(
            HEIGHT,
            dregg_turn::DEFAULT_TURN_VALIDITY_HORIZON_BLOCKS,
        )),
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn require_lean() -> bool {
    dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "verified Turn executor archive (lean_available)",
    )
}

/// Drive one worker turn through the authoritative producer; assert it was COVERED and that Lean
/// and Rust agreed.
fn decide(ledger: &mut Ledger, turn: &Turn, case: &str) -> dregg_turn::TurnResult {
    let (result, outcome) = dregg_exec_lean::produce_via_lean(&executor(), turn, ledger);
    assert!(
        matches!(
            outcome,
            dregg_exec_lean::ProducerOutcome::LeanAuthoritative { .. }
        ),
        "{case}: the token turn must be covered (Lean decides it), got {outcome:?}"
    );
    assert!(
        !outcome.rust_bug_surfaced(),
        "{case}: Lean and Rust must agree on the token WHO leg, got {outcome:?}"
    );
    result
}

/// A refusal pole: the turn is refused by BOTH executors and nothing is installed.
///
/// At fee 0 the two executors agree EXACTLY (`!rust_bug_surfaced`): commit bit, anchor and every
/// cell. At the worker's real fee they agree on the commit bit (that is the WHO-leg verdict this
/// file is about) but the differential reports an `Anchor` divergence between the two NON-installed
/// rejected ledgers: the Rust reference leaves its phase-one fee debit in place on a rejection ("the
/// host owns candidate rollback, including phase-one fee/nonce", `TurnExecutor::execute_candidate`)
/// while `execute_via_lean` replays the fee move only on commit. It is not a token matter and it
/// does not reach the ledger (a verified rejection installs the pre-state), so it is pinned here as
/// the measured shape rather than hidden by testing only at fee 0.
/// The agent cell's (balance, nonce): what a refused worker turn must leave untouched.
fn agent_scalars(ledger: &Ledger, agent: &CellId) -> Option<(i64, u64)> {
    ledger
        .get(agent)
        .map(|c| (c.state.balance() as i64, c.state.nonce() as u64))
}

fn refused_by_both(make: impl Fn(u64) -> (Ledger, Turn), case: &str) {
    // Exact agreement at fee 0.
    let (mut ledger, turn) = make(0);
    let pre = agent_scalars(&ledger, &turn.agent);
    let result = decide(&mut ledger, &turn, case);
    assert!(
        !result.is_committed(),
        "{case} (fee 0): must be refused, got {result:?}"
    );
    assert_eq!(
        agent_scalars(&ledger, &turn.agent),
        pre,
        "{case} (fee 0): a refusal installs nothing"
    );

    // The worker's fee: the commit bits agree, nothing is installed.
    let (mut ledger, turn) = make(WORKER_FEE);
    let pre = agent_scalars(&ledger, &turn.agent);
    let (result, outcome) = dregg_exec_lean::produce_via_lean(&executor(), &turn, &mut ledger);
    match &outcome {
        dregg_exec_lean::ProducerOutcome::LeanAuthoritative {
            committed: false,
            rust_committed: false,
            divergence,
            ..
        } => assert!(
            matches!(
                divergence,
                None | Some(dregg_exec_lean::ProducerDivergence::Anchor { .. })
            ),
            "{case} (fee {WORKER_FEE}): the only permitted residue is the rejected-ledger fee \
             anchor, got {outcome:?}"
        ),
        other => panic!(
            "{case} (fee {WORKER_FEE}): both executors must refuse on the covered path, got {other:?}"
        ),
    }
    assert!(!result.is_committed());
    assert_eq!(
        agent_scalars(&ledger, &turn.agent),
        pre,
        "{case} (fee {WORKER_FEE}): a refusal installs nothing"
    );
}

#[test]
fn genuine_worker_token_commits_on_both_executors() {
    if !require_lean() {
        return;
    }
    let kp = KeyPair::new();
    let issuer = issuer_bytes(&kp);
    let (mut ledger, agent) = worker_ledger(issuer);
    let turn = worker_turn(
        agent,
        METHOD,
        credential(&kp, agent, METHOD),
        issuer,
        WORKER_FEE,
    );
    let result = decide(&mut ledger, &turn, "genuine in-scope credential");
    assert!(
        result.is_committed(),
        "a genuine in-scope worker credential must commit, got {result:?}"
    );
}

#[test]
fn out_of_scope_method_is_refused_by_both_executors() {
    if !require_lean() {
        return;
    }
    let kp = KeyPair::new();
    let issuer = issuer_bytes(&kp);
    // The credential grants METHOD; the turn invokes OTHER_METHOD.
    refused_by_both(
        |fee| {
            let (ledger, agent) = worker_ledger(issuer);
            let turn = worker_turn(
                agent,
                OTHER_METHOD,
                credential(&kp, agent, METHOD),
                issuer,
                fee,
            );
            (ledger, turn)
        },
        "method outside the grant",
    );
}

#[test]
fn untrusted_issuer_is_refused_by_both_executors() {
    if !require_lean() {
        return;
    }
    let trusted = KeyPair::new();
    let rogue = KeyPair::new();
    // A well-formed in-scope credential, issued and presented under a key the cell does not trust.
    refused_by_both(
        |fee| {
            let (ledger, agent) = worker_ledger(issuer_bytes(&trusted));
            let turn = worker_turn(
                agent,
                METHOD,
                credential(&rogue, agent, METHOD),
                issuer_bytes(&rogue),
                fee,
            );
            (ledger, turn)
        },
        "untrusted issuer",
    );
}

#[test]
fn forged_credential_under_the_trusted_key_is_refused_by_both_executors() {
    if !require_lean() {
        return;
    }
    let trusted = KeyPair::new();
    let rogue = KeyPair::new();
    let issuer = issuer_bytes(&trusted);
    // Minted by the rogue key, presented as if the trusted issuer signed it.
    refused_by_both(
        |fee| {
            let (ledger, agent) = worker_ledger(issuer);
            let turn = worker_turn(
                agent,
                METHOD,
                credential(&rogue, agent, METHOD),
                issuer,
                fee,
            );
            (ledger, turn)
        },
        "forged credential under the trusted key",
    );
}
