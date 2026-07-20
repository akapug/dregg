//! Active private box projection for fhIR.
//!
//! The affine convex engine deliberately accepts only a statically certified
//! identity prox.  This module is the first executable fhIR product in which a
//! box clamp may actually bind.  It operates on n-of-n mod-`t` additive shares
//! and uses the strict party-MPC comparison circuit three times:
//!
//! * `input_bound < x` is a fail-closed range gate;
//! * `x < lower` selects the lower face;
//! * `upper < x` selects the upper face.
//!
//! No operand, difference, residue, or output value reaches the coordinator.
//! Each comparison retains only Beaver-masked gate openings plus one bit.  The
//! resulting output remains additively shared and can be checked against a
//! public differential oracle using [`PrivateBoxRun::verify_public_output`],
//! which itself releases only an equality bit.
//!
//! ## Deliberate privacy/security boundary
//!
//! This first product reveals which public box face was selected (lower,
//! interior, or upper).  It therefore closes active projection *execution* and
//! operand/output-value hiding, not branch-oblivious prox.  The online protocol
//! is semi-honest, n-of-n and in-memory, with the existing trusted Beaver-triple
//! preprocessing helper.  There are no MPC MACs, malicious input-validity
//! proofs, authenticated transport, or crash recovery.  Exact canonical range
//! checking is obtained by requiring `t = 2^value_bits`; every reconstructed
//! residue then has a unique comparison representation before the explicit
//! `input_bound` gate.

use std::collections::BTreeSet;
use std::thread;
use std::time::Duration;

use rand::rngs::StdRng;
use rand::SeedableRng;
use sha2::{Digest, Sha256};

use crate::mpc_party::{
    local_channels, run_party_comparison, run_party_equality, trusted_dealer_triples,
    ComparisonTranscript, DistributedComparisonRun, DistributedDecisionRun, PartyComparisonInput,
    PartyEqualityInput, PartyMpcError, PartyMpcSession,
};

const SESSION_DOMAIN: &[u8] = b"fhegg/fhir/private-box/session/v1";
const LEG_DOMAIN: &[u8] = b"fhegg/fhir/private-box/leg/v1";
const OUTPUT_DOMAIN: &[u8] = b"fhegg/fhir/private-box/output-binding/v1";

pub type Result<T> = std::result::Result<T, PrivateBoxError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateBoxError {
    InvalidPartyCount,
    InvalidValueBits,
    PlaintextModulusMustEqualCanonicalDomain {
        expected: u64,
        actual: u64,
    },
    InvalidBounds,
    ZeroTimeout,
    InvalidParty {
        party: usize,
        n_parties: usize,
    },
    DuplicateParty {
        party: usize,
    },
    MissingParties {
        have: usize,
        need: usize,
    },
    SessionMismatch,
    NonCanonicalShare {
        party: usize,
        share: u64,
        modulus: u64,
    },
    InputOutOfRange,
    InconsistentBranch,
    InvalidExpectedOutput,
    CandidateChainMismatch,
    Mpc(PartyMpcError),
    PartyPanicked,
}

impl From<PartyMpcError> for PrivateBoxError {
    fn from(value: PartyMpcError) -> Self {
        Self::Mpc(value)
    }
}

impl std::fmt::Display for PrivateBoxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private fhIR box projection error: {self:?}")
    }
}

impl std::error::Error for PrivateBoxError {}

/// Public, candidate-bound description of one active fhIR box projection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBoxSession {
    program_digest: [u8; 32],
    candidate_digest: [u8; 32],
    n_parties: usize,
    value_bits: usize,
    plaintext_modulus: u64,
    input_bound: u64,
    lower: u64,
    upper: u64,
    timeout: Duration,
    session_id: [u8; 32],
}

impl PrivateBoxSession {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        program_digest: [u8; 32],
        candidate_digest: [u8; 32],
        n_parties: usize,
        value_bits: usize,
        plaintext_modulus: u64,
        input_bound: u64,
        lower: u64,
        upper: u64,
        timeout: Duration,
    ) -> Result<Self> {
        if n_parties < 2 {
            return Err(PrivateBoxError::InvalidPartyCount);
        }
        if !(1..=63).contains(&value_bits) {
            return Err(PrivateBoxError::InvalidValueBits);
        }
        let canonical_domain = 1u64 << value_bits;
        if plaintext_modulus != canonical_domain {
            return Err(PrivateBoxError::PlaintextModulusMustEqualCanonicalDomain {
                expected: canonical_domain,
                actual: plaintext_modulus,
            });
        }
        if lower > upper || upper > input_bound || input_bound >= plaintext_modulus {
            return Err(PrivateBoxError::InvalidBounds);
        }
        if timeout.is_zero() {
            return Err(PrivateBoxError::ZeroTimeout);
        }
        let mut hash = Sha256::new();
        hash.update(SESSION_DOMAIN);
        hash.update(program_digest);
        hash.update(candidate_digest);
        hash.update((n_parties as u64).to_le_bytes());
        hash.update((value_bits as u64).to_le_bytes());
        hash.update(plaintext_modulus.to_le_bytes());
        hash.update(input_bound.to_le_bytes());
        hash.update(lower.to_le_bytes());
        hash.update(upper.to_le_bytes());
        hash.update(timeout.as_nanos().to_le_bytes());
        let session_id = hash.finalize().into();
        Ok(Self {
            program_digest,
            candidate_digest,
            n_parties,
            value_bits,
            plaintext_modulus,
            input_bound,
            lower,
            upper,
            timeout,
            session_id,
        })
    }

    pub fn program_digest(&self) -> [u8; 32] {
        self.program_digest
    }

    pub fn candidate_digest(&self) -> [u8; 32] {
        self.candidate_digest
    }

    pub fn session_id(&self) -> [u8; 32] {
        self.session_id
    }

    pub fn n_parties(&self) -> usize {
        self.n_parties
    }

    pub fn value_bits(&self) -> usize {
        self.value_bits
    }

    pub fn plaintext_modulus(&self) -> u64 {
        self.plaintext_modulus
    }

    pub fn input_bound(&self) -> u64 {
        self.input_bound
    }

    pub fn lower(&self) -> u64 {
        self.lower
    }

    pub fn upper(&self) -> u64 {
        self.upper
    }

    fn leg_nonce(&self, leg: &[u8], extra: u64) -> [u8; 32] {
        let mut hash = Sha256::new();
        hash.update(LEG_DOMAIN);
        hash.update(self.session_id);
        hash.update((leg.len() as u64).to_le_bytes());
        hash.update(leg);
        hash.update(extra.to_le_bytes());
        hash.finalize().into()
    }

    fn comparison_session(&self, leg: &[u8]) -> Result<PartyMpcSession> {
        Ok(PartyMpcSession::less_than(
            self.leg_nonce(leg, 0),
            self.n_parties,
            self.value_bits,
            self.plaintext_modulus,
            self.timeout,
        )?)
    }
}

/// One party's opaque input share. It has no `Clone`, `Debug`, or share getter.
pub struct PartyBoxInput {
    session_id: [u8; 32],
    party: usize,
    share: u64,
}

impl PartyBoxInput {
    pub fn new(session: &PrivateBoxSession, party: usize, share: u64) -> Result<Self> {
        if party >= session.n_parties {
            return Err(PrivateBoxError::InvalidParty {
                party,
                n_parties: session.n_parties,
            });
        }
        if share >= session.plaintext_modulus {
            return Err(PrivateBoxError::NonCanonicalShare {
                party,
                share,
                modulus: session.plaintext_modulus,
            });
        }
        Ok(Self {
            session_id: session.session_id,
            party,
            share,
        })
    }

    pub fn party(&self) -> usize {
        self.party
    }
}

/// Public branch disclosure of this first active-prox product.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BoxBranch {
    Lower,
    Interior,
    Upper,
}

/// Party-local output state. The projected value remains additively shared.
/// No raw-share accessor is exposed outside this module.
pub struct PartyBoxOutput {
    session_id: [u8; 32],
    party: usize,
    share: u64,
}

/// Coordinator-visible result. Public transcripts expose only the constant
/// range-valid bit and the two branch bits; output shares remain opaque.
pub struct PrivateBoxRun {
    session: PrivateBoxSession,
    branch: BoxBranch,
    range_transcript: ComparisonTranscript,
    lower_transcript: ComparisonTranscript,
    upper_transcript: ComparisonTranscript,
    outputs: Vec<PartyBoxOutput>,
}

impl PrivateBoxRun {
    pub fn session(&self) -> &PrivateBoxSession {
        &self.session
    }

    pub fn branch(&self) -> BoxBranch {
        self.branch
    }

    pub fn range_transcript(&self) -> &ComparisonTranscript {
        &self.range_transcript
    }

    pub fn lower_transcript(&self) -> &ComparisonTranscript {
        &self.lower_transcript
    }

    pub fn upper_transcript(&self) -> &ComparisonTranscript {
        &self.upper_transcript
    }

    /// Digest-only handle for chaining the still-private projected shares into
    /// another fhIR box step. It binds the exact source session, disclosed
    /// branch, and all three reveal-only comparison transcripts.
    pub fn output_binding_digest(&self) -> [u8; 32] {
        let mut hash = Sha256::new();
        hash.update(OUTPUT_DOMAIN);
        hash.update(self.session.session_id);
        hash.update([match self.branch {
            BoxBranch::Lower => 0,
            BoxBranch::Interior => 1,
            BoxBranch::Upper => 2,
        }]);
        bind_comparison_transcript(&mut hash, &self.range_transcript);
        bind_comparison_transcript(&mut hash, &self.lower_transcript);
        bind_comparison_transcript(&mut hash, &self.upper_transcript);
        hash.finalize().into()
    }

    /// Consume this result into a subsequent active box step without exposing
    /// any output share. The next session must name this exact output binding
    /// as its candidate and retain the same program/domain/roster.
    pub fn project_again(self, next: &PrivateBoxSession) -> Result<PrivateBoxRun> {
        if next.candidate_digest != self.output_binding_digest()
            || next.program_digest != self.session.program_digest
            || next.n_parties != self.session.n_parties
            || next.value_bits != self.session.value_bits
            || next.plaintext_modulus != self.session.plaintext_modulus
        {
            return Err(PrivateBoxError::CandidateChainMismatch);
        }
        let inputs = self
            .outputs
            .into_iter()
            .map(|output| PartyBoxInput {
                session_id: next.session_id,
                party: output.party,
                share: output.share,
            })
            .collect();
        project_private_box(next, inputs)
    }

    /// Differential/public-settlement tooth: compare the still-shared output
    /// to a public expected value and reveal only the equality bit.
    pub fn verify_public_output(&self, expected: u64) -> Result<DistributedDecisionRun> {
        if expected >= self.session.plaintext_modulus {
            return Err(PrivateBoxError::InvalidExpectedOutput);
        }
        if self.outputs.iter().enumerate().any(|(party, output)| {
            output.session_id != self.session.session_id || output.party != party
        }) {
            return Err(PrivateBoxError::SessionMismatch);
        }
        let session = PartyMpcSession::equality(
            self.session.leg_nonce(b"output-equality", expected),
            self.session.n_parties,
            self.session.value_bits,
            self.session.plaintext_modulus,
            self.session.timeout,
        )?;
        let left = self.outputs.iter().map(|output| output.share).collect();
        let right = public_shares(self.session.n_parties, expected);
        run_equality(&session, left, right, seed_from_nonce(session.nonce()))
    }
}

fn bind_comparison_transcript(hash: &mut Sha256, transcript: &ComparisonTranscript) {
    hash.update((transcript.masked.len() as u64).to_le_bytes());
    for opening in &transcript.masked {
        hash.update((opening.gate as u64).to_le_bytes());
        hash.update([opening.d, opening.e]);
    }
    hash.update([transcript.revealed_less_than]);
    for value in [
        transcript.and_gates,
        transcript.scalar_opening_rounds,
        transcript.modeled_batched_rounds,
        transcript.gate_share_messages,
        transcript.output_share_messages,
    ] {
        hash.update((value as u64).to_le_bytes());
    }
}

fn public_shares(n_parties: usize, value: u64) -> Vec<u64> {
    let mut shares = vec![0; n_parties];
    shares[0] = value;
    shares
}

fn seed_from_nonce(nonce: [u8; 32]) -> u64 {
    u64::from_le_bytes(nonce[..8].try_into().expect("eight-byte prefix"))
}

fn run_comparison(
    session: &PartyMpcSession,
    left: Vec<u64>,
    right: Vec<u64>,
    seed: u64,
) -> Result<DistributedComparisonRun> {
    if left.len() != session.n_parties() || right.len() != session.n_parties() {
        return Err(PrivateBoxError::MissingParties {
            have: left.len().min(right.len()),
            need: session.n_parties(),
        });
    }
    let inputs = left
        .into_iter()
        .zip(right)
        .enumerate()
        .map(|(party, (left, right))| {
            let mut rng = StdRng::seed_from_u64(seed ^ 0x636f_6d70 ^ party as u64);
            PartyComparisonInput::new(session, party, left, right, &mut rng)
        })
        .collect::<std::result::Result<Vec<_>, _>>()?;
    let mut triple_rng = StdRng::seed_from_u64(seed ^ 0x7472_6970_6c65);
    let triples = trusted_dealer_triples(session, &mut triple_rng)?;
    let (coordinator, endpoints) = local_channels(session);
    let workers = inputs
        .into_iter()
        .zip(triples)
        .zip(endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_party_comparison(input, triples, endpoint))
        })
        .collect::<Vec<_>>();
    let run = coordinator.coordinate_comparison(session);
    let mut party_error = None;
    for worker in workers {
        match worker.join() {
            Err(_) if party_error.is_none() => party_error = Some(PrivateBoxError::PartyPanicked),
            Ok(Err(error)) if party_error.is_none() => {
                party_error = Some(PrivateBoxError::Mpc(error))
            }
            _ => {}
        }
    }
    if let Some(error) = party_error {
        return Err(error);
    }
    let run = run?;
    if run.session_nonce() != session.nonce() || !run.transcript.is_reveal_only(session) {
        return Err(PrivateBoxError::SessionMismatch);
    }
    Ok(run)
}

fn run_equality(
    session: &PartyMpcSession,
    left: Vec<u64>,
    right: Vec<u64>,
    seed: u64,
) -> Result<DistributedDecisionRun> {
    if left.len() != session.n_parties() || right.len() != session.n_parties() {
        return Err(PrivateBoxError::MissingParties {
            have: left.len().min(right.len()),
            need: session.n_parties(),
        });
    }
    let inputs = left
        .into_iter()
        .zip(right)
        .enumerate()
        .map(|(party, (left, right))| {
            let mut rng = StdRng::seed_from_u64(seed ^ 0x6571_7561_6c ^ party as u64);
            PartyEqualityInput::new(session, party, left, right, &mut rng)
        })
        .collect::<std::result::Result<Vec<_>, _>>()?;
    let mut triple_rng = StdRng::seed_from_u64(seed ^ 0x7472_6970_6c65);
    let triples = trusted_dealer_triples(session, &mut triple_rng)?;
    let (coordinator, endpoints) = local_channels(session);
    let workers = inputs
        .into_iter()
        .zip(triples)
        .zip(endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_party_equality(input, triples, endpoint))
        })
        .collect::<Vec<_>>();
    let run = coordinator.coordinate_equality(session);
    let mut party_error = None;
    for worker in workers {
        match worker.join() {
            Err(_) if party_error.is_none() => party_error = Some(PrivateBoxError::PartyPanicked),
            Ok(Err(error)) if party_error.is_none() => {
                party_error = Some(PrivateBoxError::Mpc(error))
            }
            _ => {}
        }
    }
    if let Some(error) = party_error {
        return Err(error);
    }
    let run = run?;
    if run.session_nonce() != session.nonce() || !run.transcript.is_reveal_only(session) {
        return Err(PrivateBoxError::SessionMismatch);
    }
    Ok(run)
}

/// Execute one active two-sided projection.  Inputs are consumed so the same
/// session share cannot accidentally be reused as two roster members.
pub fn project_private_box(
    session: &PrivateBoxSession,
    inputs: Vec<PartyBoxInput>,
) -> Result<PrivateBoxRun> {
    if inputs.len() < session.n_parties {
        return Err(PrivateBoxError::MissingParties {
            have: inputs.len(),
            need: session.n_parties,
        });
    }
    let mut seen = BTreeSet::new();
    let mut ordered = inputs;
    ordered.sort_by_key(PartyBoxInput::party);
    for input in &ordered {
        if input.party >= session.n_parties {
            return Err(PrivateBoxError::InvalidParty {
                party: input.party,
                n_parties: session.n_parties,
            });
        }
        if input.session_id != session.session_id {
            return Err(PrivateBoxError::SessionMismatch);
        }
        if !seen.insert(input.party) {
            return Err(PrivateBoxError::DuplicateParty { party: input.party });
        }
    }
    if seen != (0..session.n_parties).collect() {
        return Err(PrivateBoxError::MissingParties {
            have: seen.len(),
            need: session.n_parties,
        });
    }
    let shares = ordered.iter().map(|input| input.share).collect::<Vec<_>>();

    // First prove the actual reconstructed canonical residue is within the
    // public fhIR input bound. Because t=2^bits, no truncation alias exists.
    let range_session = session.comparison_session(b"range")?;
    let range = run_comparison(
        &range_session,
        public_shares(session.n_parties, session.input_bound),
        shares.clone(),
        seed_from_nonce(range_session.nonce()),
    )?;
    if range.is_less_than() {
        return Err(PrivateBoxError::InputOutOfRange);
    }

    let lower_session = session.comparison_session(b"lower")?;
    let lower = run_comparison(
        &lower_session,
        shares.clone(),
        public_shares(session.n_parties, session.lower),
        seed_from_nonce(lower_session.nonce()),
    )?;
    let upper_session = session.comparison_session(b"upper")?;
    let upper = run_comparison(
        &upper_session,
        public_shares(session.n_parties, session.upper),
        shares.clone(),
        seed_from_nonce(upper_session.nonce()),
    )?;
    if lower.is_less_than() && upper.is_less_than() {
        return Err(PrivateBoxError::InconsistentBranch);
    }

    let (branch, projected) = if lower.is_less_than() {
        (
            BoxBranch::Lower,
            public_shares(session.n_parties, session.lower),
        )
    } else if upper.is_less_than() {
        (
            BoxBranch::Upper,
            public_shares(session.n_parties, session.upper),
        )
    } else {
        (BoxBranch::Interior, shares)
    };
    let outputs = projected
        .into_iter()
        .enumerate()
        .map(|(party, share)| PartyBoxOutput {
            session_id: session.session_id,
            party,
            share,
        })
        .collect();
    Ok(PrivateBoxRun {
        session: session.clone(),
        branch,
        range_transcript: range.transcript,
        lower_transcript: lower.transcript,
        upper_transcript: upper.transcript,
        outputs,
    })
}
