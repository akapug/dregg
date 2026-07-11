//! # coauthor_api — COLLECTIVE CO-AUTHORING: a crowd quorum-votes structured edits to ONE shared
//! dungeon draft that grows over time and stays playable.
//!
//! The "collectivity" heart. Additive to the `/game` + `/party` lanes: a THIRD lane over a
//! server-held [`shared_draft::Draft`] that the crowd co-authors by quorum-certified vote. The
//! crowd PROPOSES bounded, typed edits; the quorum CERTIFIES which edit wins; and the VALIDATOR
//! DISPOSES — a voted-for edit that would break the world is refused and rolled back EVEN THOUGH it
//! was voted for, mirroring "the AI proposes, the world resolves".
//!
//! ## The three movements
//!
//! * **The crowd proposes** — [`handle_propose`] adds a bounded, typed [`shared_draft::Edit`]
//!   (`AddRoom | AddExit | PlaceItem | SetObjective`) to the open proposal pool. An edit is a typed
//!   proposal, NOT prose; the ids are sanitized on the way in.
//! * **The quorum certifies** — [`handle_open`] opens a real
//!   [`collective_choice::CollectiveChoice`] poll over the pending proposals (the SAME engine the
//!   `/party` lane votes on: `WriteOnce` ballots + `Monotonic` tally + the polis `AffineLe` quorum
//!   gate, M of N). [`handle_vote`] casts one cap-bounded ballot per seat; [`handle_close`] resolves
//!   only at quorum, emitting a verifiable QUORUM CERTIFICATE for the winning edit.
//! * **The validator disposes** — the certified edit is passed to [`shared_draft::Draft::dispose`],
//!   which applies it to a fresh draft, renders `.dungeon` source, and RE-VALIDATES via
//!   `attested_dm::parse_dungeon`. A well-formed edit is APPLIED (the draft grows); a breaking edit
//!   (a dangling exit, an unreachable objective, an unplaced win item) is REFUSED and rolled back —
//!   reported honestly — despite the passing vote. Every disposition is appended to an append-only,
//!   quorum-certified edit HISTORY: the provenance of the co-authored dungeon.
//!
//! ## What is REAL vs the labeled gap (honest, same as `/party`)
//!
//! The quorum mechanism, the `WriteOnce` ballots, the `Monotonic` tally, the light-client
//! recomputation, and the fail-closed validator (`parse_dungeon`) are all REAL. The identities are
//! DEMO keys (each seat's electorate key is `blake3(name)`); a production deployment binds each
//! seat to a real custody key + a signed ballot, and persists the draft (here it is server memory).
//! The draft is server-held process state; a fuller version persists + binds custody keys.

use std::collections::BTreeMap;
use std::sync::Mutex;

use collective_choice::{
    CollectiveChoice, Decision, PollId, PollSpec, Tally, VoteEngine, VoteError, MAX_OPTIONS,
};
use http_serve::WebResponse;
use serde_json::{json, Value};
use shared_draft::{Disposition, Draft, Edit, EditGate};

// ─────────────────────────────────────────────────────────────────────────────
// The seated co-authors — the fixed electorate, mirroring the /party roster shape (demo keys).
// ─────────────────────────────────────────────────────────────────────────────

/// The federation the backing collective-choice engine commits its ballot/tally turns under
/// (distinct from the `/party` federation so the two lanes' engines never collide).
const COAUTHOR_FEDERATION: [u8; 32] = [0xC1; 32];

/// The seated co-authors — the fixed electorate that holds edit ballots. A voter outside this
/// roster holds no ballot cap and is refused as ineligible (a real eligibility tooth).
const COAUTHOR_ROSTER: &[&str] = &["Ansel", "Briar", "Cyra", "Doon", "Elowen"];

/// The quorum threshold `M`: an edit certifies (and reaches the validator) only once at least this
/// many ballots are cast — the polis `AffineLe` gate. A majority of the five-seat roster.
const COAUTHOR_QUORUM: u64 = 3;

/// The one-line honest description of the collective-choice model, surfaced everywhere the lane
/// speaks. Quorum-certified over demo identities; the labeled gaps are custody keys + persistence.
const VOTE_MODEL: &str = "quorum-certified collective co-authoring on the real collective-choice \
    engine (WriteOnce ballots + Monotonic tally + the polis AffineLe quorum gate, M=3 of a 5-seat \
    roster) over demo identities \u{2014} an edit certifies only once the quorum gate admits it, \
    then the validator (parse_dungeon) disposes; a production deployment adds real custody keys per \
    seat and persists the draft";

/// A voter's deterministic electorate public key (a stable demo identity per seat name).
fn voter_pk(voter: &str) -> [u8; 32] {
    *blake3::hash(voter.as_bytes()).as_bytes()
}

/// A commitment over the electorate — `blake3` of the sorted seat keys, surfaced raw in the cert so
/// a reader can recompute it from the public roster.
fn electorate_commitment_hex() -> String {
    let mut keys: Vec<[u8; 32]> = COAUTHOR_ROSTER.iter().map(|n| voter_pk(n)).collect();
    keys.sort();
    let mut h = blake3::Hasher::new();
    for k in &keys {
        h.update(k);
    }
    hex(h.finalize().as_bytes())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// A stable content hash over the current draft source — the provenance fingerprint the history
/// carries so a reader can see the draft change (or NOT change, on a refusal) at a glance.
fn source_hash_hex(source: &str) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"shared-draft-source-v1");
    h.update(source.as_bytes());
    hex(h.finalize().as_bytes())
}

// ─────────────────────────────────────────────────────────────────────────────
// The lane state — ONE shared draft, an open proposal pool, an open vote round, an append-only
// certified history.
// ─────────────────────────────────────────────────────────────────────────────

/// One proposed edit sitting in the open pool, awaiting a vote.
#[derive(Clone)]
struct PendingEdit {
    id: u64,
    edit: Edit,
    proposer: String,
}

/// An open vote round over a FROZEN slate of pending edits, backed by a live
/// [`CollectiveChoice`] engine (one embedded executor hosting this round's poll + ballots + tally).
struct EditRound {
    id: u64,
    question: String,
    /// The frozen ballot slate — the proposals under vote, index-aligned with the poll's options.
    options: Vec<PendingEdit>,
    engine: CollectiveChoice,
    poll: PollId,
    /// voter name → option index cast (a mirror of the engine's per-voter ballot).
    votes: BTreeMap<String, usize>,
}

impl EditRound {
    /// The authoritative per-option tally, read from the engine's monotone poll-cell slots.
    fn tally(&self) -> Tally {
        self.engine.tally(self.poll).unwrap_or_else(|_| {
            let mut per_option = vec![0u64; self.options.len()];
            for &oid in self.votes.values() {
                if let Some(c) = per_option.get_mut(oid) {
                    *c += 1;
                }
            }
            let total = per_option.iter().sum();
            Tally { per_option, total }
        })
    }

    fn counts(&self) -> Vec<u64> {
        let mut c = self.tally().per_option;
        c.resize(self.options.len(), 0);
        c
    }
}

/// One append-only entry in the quorum-certified edit history — the provenance of the co-authored
/// dungeon. Records EVERY disposed round (applied AND validator-refused), each carrying its cert.
struct HistoryEntry {
    seq: u64,
    round_id: u64,
    summary: String,
    kind: &'static str,
    /// `"applied"` or `"refused"`.
    disposition: &'static str,
    /// For a refusal, the stage (`"apply"` / `"validate"`) + the legible reason; else empty.
    refuse_stage: &'static str,
    reason: String,
    /// The draft source hash AFTER the disposition (unchanged from the prior entry on a refusal —
    /// the visible proof of rollback).
    source_hash: String,
    /// The verifiable quorum certificate for the edit (the same cert the close returns).
    cert: Value,
}

/// The `/coauthor` lane state.
pub struct CoAuthorState {
    draft: Draft,
    proposals: Vec<PendingEdit>,
    round: Option<EditRound>,
    history: Vec<HistoryEntry>,
    next_proposal_id: u64,
    next_round_id: u64,
    next_seq: u64,
}

/// Build the lane state around a fresh seed draft (a start room + an obtainable objective).
pub fn build_coauthor_state() -> CoAuthorState {
    CoAuthorState {
        draft: Draft::seed(),
        proposals: Vec::new(),
        round: None,
        history: Vec::new(),
        next_proposal_id: 1,
        next_round_id: 1,
        next_seq: 1,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// JSON views.
// ─────────────────────────────────────────────────────────────────────────────

/// The draft rendered as a room graph in the SAME shape `/game/map` returns, so the co-author page
/// can echo `roommap.ts`: `[{id, name, exits:[{name, to, toName, locked, gateReason}]}]`. In the
/// authoring view a gated exit reads `locked` (its gate reason on hover) and all rooms are known.
fn map_json(draft: &Draft) -> Vec<Value> {
    draft
        .rooms
        .iter()
        .map(|r| {
            let exits: Vec<Value> = r
                .exits
                .iter()
                .map(|e| {
                    let to_name = draft
                        .room(&e.to)
                        .map(|rr| rr.name.clone())
                        .unwrap_or_else(|| e.to.clone());
                    let (locked, reason) = match &e.gate {
                        None => (false, Value::Null),
                        Some(EditGate::Item(i)) => (true, json!(format!("requires the {i}"))),
                        Some(EditGate::Flag(f, v)) => {
                            (true, json!(format!("requires flag {f} \u{2265} {v}")))
                        }
                    };
                    json!({
                        "name": e.dir,
                        "to": e.to,
                        "toName": to_name,
                        "locked": locked,
                        "gateReason": reason,
                    })
                })
                .collect();
            json!({ "id": r.id, "name": r.name, "exits": exits })
        })
        .collect()
}

/// The full draft view — the source, the room map, the objective, whether it currently plays, and
/// the append-only certified edit history.
fn draft_json(st: &CoAuthorState) -> Value {
    let source = st.draft.render();
    json!({
        "name": st.draft.name,
        "source": source,
        "sourceHash": source_hash_hex(&source),
        "start": st.draft.start,
        "objective": {
            "room": st.draft.objective_room,
            "holding": st.draft.objective_holding,
            "text": format!("Carry the {} to {}.", titleize(&st.draft.objective_holding), room_name(&st.draft, &st.draft.objective_room)),
        },
        "roomCount": st.draft.rooms.len(),
        "map": map_json(&st.draft),
        "plays": st.draft.plays(),
        "history": history_json(st),
        "appliedCount": st.history.iter().filter(|h| h.disposition == "applied").count(),
        "voteModel": VOTE_MODEL,
    })
}

fn room_name(draft: &Draft, id: &str) -> String {
    draft
        .room(id)
        .map(|r| r.name.clone())
        .unwrap_or_else(|| id.to_string())
}

fn titleize(id: &str) -> String {
    id.replace('_', " ")
}

/// The append-only certified history as JSON (oldest first) — each applied AND refused edit with
/// its cert + the source hash after (unchanged on a refusal = the visible rollback proof).
fn history_json(st: &CoAuthorState) -> Vec<Value> {
    st.history
        .iter()
        .map(|h| {
            json!({
                "seq": h.seq,
                "roundId": h.round_id,
                "summary": h.summary,
                "kind": h.kind,
                "disposition": h.disposition,
                "refuseStage": if h.refuse_stage.is_empty() { Value::Null } else { json!(h.refuse_stage) },
                "reason": if h.reason.is_empty() { Value::Null } else { json!(h.reason) },
                "sourceHash": h.source_hash,
                "cert": h.cert,
            })
        })
        .collect()
}

/// A pending proposal as JSON (the ballot option, before/at a round).
fn proposal_json(p: &PendingEdit, option_id: Option<usize>) -> Value {
    json!({
        "proposalId": p.id,
        "optionId": option_id,
        "kind": p.edit.kind(),
        "summary": p.edit.summary(),
        "proposer": p.proposer,
        "edit": edit_json(&p.edit),
    })
}

/// A structured edit as JSON (the typed proposal, echoed back so the page can render it).
fn edit_json(e: &Edit) -> Value {
    match e {
        Edit::AddRoom {
            id,
            name,
            description,
        } => json!({ "type": "AddRoom", "id": id, "name": name, "description": description }),
        Edit::AddExit {
            from,
            dir,
            to,
            gate,
        } => {
            json!({ "type": "AddExit", "from": from, "dir": dir, "to": to, "gate": gate_json(gate) })
        }
        Edit::PlaceItem { room, item } => {
            json!({ "type": "PlaceItem", "room": room, "item": item })
        }
        Edit::SetObjective { room, holding } => {
            json!({ "type": "SetObjective", "room": room, "holding": holding })
        }
    }
}

fn gate_json(g: &Option<EditGate>) -> Value {
    match g {
        None => Value::Null,
        Some(EditGate::Item(i)) => json!({ "item": i }),
        Some(EditGate::Flag(f, v)) => json!({ "flag": [f, v] }),
    }
}

/// The live quorum state over an open round.
fn quorum_json(round: &EditRound) -> Value {
    let total = round.tally().total;
    json!({
        "threshold": COAUTHOR_QUORUM,
        "ballotsCast": total,
        "met": total >= COAUTHOR_QUORUM,
        "electorateSize": COAUTHOR_ROSTER.len(),
        "gate": "polis AffineLe M\u{00b7}RESOLVED \u{2212} \u{03a3} TALLY \u{2264} 0 \u{2014} the decision-turn commits only at \u{03a3} ballots \u{2265} M",
    })
}

/// The per-option tally over an open round + quorum state.
fn tally_json(round: &EditRound) -> Value {
    let counts = round.counts();
    let rows: Vec<Value> = round
        .options
        .iter()
        .enumerate()
        .map(|(i, p)| {
            json!({
                "optionId": i,
                "proposalId": p.id,
                "kind": p.edit.kind(),
                "summary": p.edit.summary(),
                "count": counts.get(i).copied().unwrap_or(0),
            })
        })
        .collect();
    json!({
        "roundId": round.id,
        "open": true,
        "question": round.question,
        "totalVotes": round.votes.len(),
        "tally": rows,
        "quorum": quorum_json(round),
    })
}

/// The verifiable QUORUM CERTIFICATE for a certified edit — reads the engine's monotone tally + an
/// independent light-client replay, labels exactly what is real vs the production gap. `decision`
/// is the engine's certified [`Decision`] (argmax; lowest-index tie-break), produced only because
/// the quorum gate admitted the RESOLVED turn.
fn cert_json(round: &EditRound, decision: &Decision) -> Value {
    let t = round.tally();
    let light_agrees = round
        .engine
        .light_client_tally(round.poll)
        .map(|l| l.per_option == t.per_option && l.total == t.total)
        .unwrap_or(false);
    let per_option: Vec<Value> = round
        .options
        .iter()
        .enumerate()
        .map(|(i, p)| {
            json!({
                "optionId": i,
                "proposalId": p.id,
                "summary": p.edit.summary(),
                "count": t.per_option.get(i).copied().unwrap_or(0),
            })
        })
        .collect();
    let winner = round.options.get(decision.winner).map(|w| {
        json!({
            "optionId": decision.winner,
            "proposalId": w.id,
            "kind": w.edit.kind(),
            "summary": w.edit.summary(),
            "edit": edit_json(&w.edit),
        })
    });
    json!({
        "kind": "quorum-certificate",
        "question": round.question,
        "quorumThreshold": COAUTHOR_QUORUM,
        "ballotsCast": t.total,
        "quorumMet": t.total >= COAUTHOR_QUORUM,
        "resolved": true,
        "winner": winner.unwrap_or(Value::Null),
        "winnerTally": decision.winner_tally,
        "perOption": per_option,
        "electorate": {
            "size": COAUTHOR_ROSTER.len(),
            "seats": COAUTHOR_ROSTER,
            "commitmentHex": electorate_commitment_hex(),
        },
        "lightClientAgrees": light_agrees,
        "mechanism": "each ballot is a WriteOnce cap-bounded turn on a factory-born ballot cell; the tally is Monotonic; the decision-turn (RESOLVED:=1) is admitted only by the polis AffineLe quorum gate M\u{00b7}RESOLVED \u{2212} \u{03a3} TALLY \u{2264} 0; a double vote is refused by the ballot nullifier.",
        "proves": "the winning EDIT was chosen by a quorum-certified monotone tally of one-vote-per-seat ballots, and an independent light-client replay of the cast log recomputes the same board.",
        "real": "quorum-certified tally over DEMO identities \u{2014} each seat's electorate key is blake3(name); the quorum gate, the WriteOnce ballots, the Monotonic tally, and the light-client recomputation are all REAL verified turns.",
        "productionGap": "a production deployment binds each seat to a real CUSTODY KEY and a signed ballot, and persists the draft; here the identities are deterministic demo keys and the draft is server memory.",
        "disposedBy": "the certificate governs WHICH edit won; the VALIDATOR (parse_dungeon) then disposes \u{2014} a certified edit that would break the world is refused + rolled back despite this cert.",
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Field sanitizers — a proposal's ids are single sanitized words (bounded, not free-form DSL).
// ─────────────────────────────────────────────────────────────────────────────

/// Sanitize an id/word field to `[a-z0-9_]`, lowercased. Empty ⇒ `None` (a 400).
fn sanitize_id(raw: &str) -> Option<String> {
    let s: String = raw
        .trim()
        .to_lowercase()
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else if c.is_whitespace() || c == '-' {
                '_'
            } else {
                '\0'
            }
        })
        .filter(|c| *c != '\0')
        .collect();
    let s = s.trim_matches('_').to_string();
    if s.is_empty() {
        None
    } else {
        Some(s.chars().take(48).collect())
    }
}

/// Sanitize a free-text field (a name / description) — trim + cap length. The renderer strips
/// comment starters + quotes, so this only bounds length + trims.
fn sanitize_text(raw: &str, cap: usize) -> String {
    raw.trim().chars().take(cap).collect()
}

/// Parse a `/coauthor/propose` body into a typed [`Edit`], or an error message (a 400).
fn parse_edit(v: &Value) -> Result<Edit, String> {
    let ty = v
        .get("editType")
        .and_then(Value::as_str)
        .ok_or("missing string field `editType`")?;
    let id_field = |k: &str| -> Result<String, String> {
        let raw = v
            .get(k)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("missing string field `{k}`"))?;
        sanitize_id(raw).ok_or_else(|| format!("`{k}` has no usable id characters (a-z, 0-9, _)"))
    };
    match ty {
        "AddRoom" => Ok(Edit::AddRoom {
            id: id_field("id")?,
            name: sanitize_text(v.get("name").and_then(Value::as_str).unwrap_or(""), 60),
            description: sanitize_text(
                v.get("description").and_then(Value::as_str).unwrap_or(""),
                240,
            ),
        }),
        "AddExit" => {
            let gate = match v.get("gate") {
                None | Some(Value::Null) => None,
                Some(g) => {
                    if let Some(item) = g.get("item").and_then(Value::as_str) {
                        Some(EditGate::Item(
                            sanitize_id(item).ok_or("gate `item` has no usable id")?,
                        ))
                    } else if let Some(arr) = g.get("flag").and_then(Value::as_array) {
                        let name = arr
                            .first()
                            .and_then(Value::as_str)
                            .and_then(sanitize_id)
                            .ok_or("gate `flag` needs [name, value]")?;
                        let val = arr.get(1).and_then(Value::as_i64).unwrap_or(1);
                        Some(EditGate::Flag(name, val))
                    } else {
                        return Err("gate must be {item:\"x\"} or {flag:[\"f\",1]}".into());
                    }
                }
            };
            Ok(Edit::AddExit {
                from: id_field("from")?,
                dir: id_field("dir")?,
                to: id_field("to")?,
                gate,
            })
        }
        "PlaceItem" => Ok(Edit::PlaceItem {
            room: id_field("room")?,
            item: id_field("item")?,
        }),
        "SetObjective" => Ok(Edit::SetObjective {
            room: id_field("room")?,
            holding: id_field("holding")?,
        }),
        other => Err(format!(
            "unknown editType `{other}` \u{2014} one of AddRoom, AddExit, PlaceItem, SetObjective"
        )),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Handlers.
// ─────────────────────────────────────────────────────────────────────────────

/// `GET /coauthor/draft` — the current shared draft (source + room map + objective + plays) and the
/// append-only certified edit history.
pub fn handle_draft(cs: &Mutex<CoAuthorState>) -> WebResponse {
    let st = cs.lock().unwrap();
    WebResponse::json(draft_json(&st).to_string().into_bytes())
}

/// `GET /coauthor/proposals` — the open proposal pool, any open round, the quorum + roster.
pub fn handle_proposals(cs: &Mutex<CoAuthorState>) -> WebResponse {
    let st = cs.lock().unwrap();
    // If a round is open, tag each pool proposal with its option index in the frozen slate.
    let opt_of = |pid: u64| -> Option<usize> {
        st.round
            .as_ref()
            .and_then(|r| r.options.iter().position(|o| o.id == pid))
    };
    let pool: Vec<Value> = st
        .proposals
        .iter()
        .map(|p| proposal_json(p, opt_of(p.id)))
        .collect();
    let round = st.round.as_ref().map(tally_json).unwrap_or(Value::Null);
    let resp = json!({
        "proposals": pool,
        "round": round,
        "voteModel": VOTE_MODEL,
        "quorum": { "threshold": COAUTHOR_QUORUM, "electorateSize": COAUTHOR_ROSTER.len(), "seats": COAUTHOR_ROSTER },
        "editTypes": ["AddRoom", "AddExit", "PlaceItem", "SetObjective"],
    });
    WebResponse::json(resp.to_string().into_bytes())
}

/// `POST /coauthor/propose {editType, ...}` — add one bounded typed edit to the proposal pool.
pub fn handle_propose(cs: &Mutex<CoAuthorState>, body: &[u8]) -> WebResponse {
    let parsed: Value = match serde_json::from_slice(body) {
        Ok(v) => v,
        Err(e) => return WebResponse::error(400, format!("bad JSON: {e}")),
    };
    let edit = match parse_edit(&parsed) {
        Ok(e) => e,
        Err(m) => return WebResponse::error(400, m),
    };
    let proposer = parsed
        .get("proposer")
        .and_then(Value::as_str)
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .unwrap_or("someone")
        .to_string();

    let mut st = cs.lock().unwrap();
    let id = st.next_proposal_id;
    st.next_proposal_id += 1;
    let pending = PendingEdit {
        id,
        edit: edit.clone(),
        proposer,
    };
    st.proposals.push(pending.clone());
    let resp = json!({
        "ok": true,
        "proposalId": id,
        "proposal": proposal_json(&pending, None),
        "poolSize": st.proposals.len(),
    });
    WebResponse::json(resp.to_string().into_bytes())
}

/// `POST /coauthor/open` — open a fresh quorum round over the pending proposals (options = the
/// pool). Opening while a round is open REPLACES it. Requires at least one pending proposal.
pub fn handle_open(cs: &Mutex<CoAuthorState>) -> WebResponse {
    let mut st = cs.lock().unwrap();
    if st.proposals.is_empty() {
        return WebResponse::json(
            json!({
                "ok": false,
                "reason": "no pending proposals \u{2014} POST /coauthor/propose an edit first",
            })
            .to_string()
            .into_bytes(),
        );
    }
    // The backing poll cell tallies at most MAX_OPTIONS; freeze the first MAX_OPTIONS proposals.
    let options: Vec<PendingEdit> = st.proposals.iter().take(MAX_OPTIONS).cloned().collect();
    let id = st.next_round_id;
    let question = format!("Which edit does the crowd apply to the draft? (round {id})");

    let mut engine = CollectiveChoice::new(COAUTHOR_FEDERATION);
    let electorate: Vec<[u8; 32]> = COAUTHOR_ROSTER.iter().map(|n| voter_pk(n)).collect();
    let spec = PollSpec {
        question: question.clone(),
        options: options.iter().map(|o| o.edit.summary()).collect(),
        electorate,
        quorum_m: COAUTHOR_QUORUM,
    };
    let poll = match engine.open_poll(spec) {
        Ok(p) => p,
        Err(e) => {
            return WebResponse::json(
                json!({ "ok": false, "reason": format!("could not open a quorum poll: {e}") })
                    .to_string()
                    .into_bytes(),
            )
        }
    };

    st.next_round_id += 1;
    let options_json: Vec<Value> = options
        .iter()
        .enumerate()
        .map(|(i, p)| proposal_json(p, Some(i)))
        .collect();
    let round = EditRound {
        id,
        question,
        options,
        engine,
        poll,
        votes: BTreeMap::new(),
    };
    let quorum = quorum_json(&round);
    st.round = Some(round);
    let resp = json!({
        "ok": true,
        "roundId": id,
        "options": options_json,
        "voteModel": VOTE_MODEL,
        "quorum": quorum,
    });
    WebResponse::json(resp.to_string().into_bytes())
}

/// `POST /coauthor/vote {"voter":"<name>","optionId":<n>}` — cast one seat's ballot as a REAL turn
/// on the round's engine. Not-seated / already-voted / unknown-option / no-round are all refused
/// honestly (mirroring `/party/vote`).
pub fn handle_vote(cs: &Mutex<CoAuthorState>, body: &[u8]) -> WebResponse {
    let parsed: Value = match serde_json::from_slice(body) {
        Ok(v) => v,
        Err(e) => return WebResponse::error(400, format!("bad JSON: {e}")),
    };
    let voter = match parsed.get("voter").and_then(Value::as_str) {
        Some(s) if !s.trim().is_empty() => s.trim().to_string(),
        _ => return WebResponse::error(400, "missing non-empty string field `voter`"),
    };
    let option_id = match parsed.get("optionId").and_then(Value::as_u64) {
        Some(n) => n as usize,
        None => return WebResponse::error(400, "missing integer field `optionId`"),
    };

    let mut st = cs.lock().unwrap();
    let round = match st.round.as_mut() {
        Some(r) => r,
        None => {
            return WebResponse::json(
                json!({ "ok": false, "refused": "no-round", "reason": "no vote round is open \u{2014} POST /coauthor/open first" })
                    .to_string()
                    .into_bytes(),
            )
        }
    };
    if option_id >= round.options.len() {
        return WebResponse::error(
            400,
            format!(
                "unknown optionId {option_id} \u{2014} this round has {} options (0..{})",
                round.options.len(),
                round.options.len().saturating_sub(1)
            ),
        );
    }
    if !COAUTHOR_ROSTER.iter().any(|s| *s == voter) {
        return WebResponse::json(
            json!({
                "ok": false,
                "refused": "not-seated",
                "reason": format!("{voter} is not a seated co-author \u{2014} only the roster [{}] holds ballots", COAUTHOR_ROSTER.join(", ")),
                "voter": voter,
                "tally": tally_json(round),
            })
            .to_string()
            .into_bytes(),
        );
    }
    if let Some(prev) = round.votes.get(&voter).copied() {
        return WebResponse::json(
            json!({
                "ok": false,
                "refused": "already-voted",
                "reason": format!("{voter} has already cast a ballot this round (for option {prev}) \u{2014} one ballot per co-author"),
                "voter": voter,
                "previousOptionId": prev,
                "tally": tally_json(round),
            })
            .to_string()
            .into_bytes(),
        );
    }

    // THE REAL CAST — mint (idempotently) this seat's single-use ballot cap and exercise it.
    let pk = voter_pk(&voter);
    let cap = match round.engine.issue_ballot(round.poll, pk) {
        Ok(c) => c,
        Err(e) => {
            let refused = match e {
                VoteError::Ineligible => "not-seated",
                _ => "engine-refused",
            };
            return WebResponse::json(
                json!({ "ok": false, "refused": refused, "reason": format!("the ballot could not be issued: {e}"), "voter": voter, "tally": tally_json(round) })
                    .to_string()
                    .into_bytes(),
            );
        }
    };
    if let Err(e) = round.engine.cast(round.poll, &cap, option_id) {
        let refused = match e {
            VoteError::DoubleVote => "already-voted",
            VoteError::BadOption => "bad-option",
            _ => "engine-refused",
        };
        return WebResponse::json(
            json!({ "ok": false, "refused": refused, "reason": format!("the executor refused the ballot turn: {e}"), "voter": voter, "tally": tally_json(round) })
                .to_string()
                .into_bytes(),
        );
    }

    round.votes.insert(voter.clone(), option_id);
    let resp =
        json!({ "ok": true, "voter": voter, "optionId": option_id, "tally": tally_json(round) });
    WebResponse::json(resp.to_string().into_bytes())
}

/// `GET /coauthor/tally` — the engine's monotone per-option tally + quorum for the open round.
pub fn handle_tally(cs: &Mutex<CoAuthorState>) -> WebResponse {
    let st = cs.lock().unwrap();
    let resp = match st.round.as_ref() {
        Some(r) => tally_json(r),
        None => json!({ "open": false, "totalVotes": 0, "tally": [] }),
    };
    WebResponse::json(resp.to_string().into_bytes())
}

/// `POST /coauthor/close` — close the open round through the REAL quorum gate, then LET THE
/// VALIDATOR DISPOSE. `engine.resolve` admits the decision-turn only at `Σ ballots ≥ M`, so a
/// sub-quorum round does NOT resolve (`refused:"below-quorum"`, kept open). Once quorum is met, the
/// certified winning EDIT is passed to [`Draft::dispose`]: a sound edit is APPLIED (the draft
/// grows), a breaking edit is REFUSED + rolled back despite the passing vote. Either disposition is
/// appended to the append-only certified history and returned with the quorum CERTIFICATE.
pub fn handle_close(cs: &Mutex<CoAuthorState>) -> WebResponse {
    let mut st = cs.lock().unwrap();
    let mut round = match st.round.take() {
        Some(r) => r,
        None => {
            return WebResponse::json(
                json!({ "ok": false, "refused": "no-round", "reason": "no vote round is open \u{2014} POST /coauthor/open first" })
                    .to_string()
                    .into_bytes(),
            )
        }
    };
    if round.votes.is_empty() {
        st.round = Some(round);
        return WebResponse::error(
            400,
            "cannot close a round with no ballots \u{2014} cast at least one vote first",
        );
    }

    // THE QUORUM GATE DECIDES.
    let decision = match round.engine.resolve(round.poll) {
        Ok(Some(d)) => d,
        Ok(None) => {
            // BELOW QUORUM: keep the round open so the crowd can gather more ballots.
            let quorum = quorum_json(&round);
            let tally = tally_json(&round);
            let id = round.id;
            st.round = Some(round);
            return WebResponse::json(
                json!({
                    "ok": false,
                    "refused": "below-quorum",
                    "roundId": id,
                    "reason": format!(
                        "the quorum gate refused the decision-turn \u{2014} {} of {} ballots cast, {} needed. Gather more votes.",
                        quorum["ballotsCast"], COAUTHOR_ROSTER.len(), COAUTHOR_QUORUM
                    ),
                    "quorum": quorum,
                    "tally": tally,
                })
                .to_string()
                .into_bytes(),
            );
        }
        Err(e) => {
            let id = round.id;
            st.round = Some(round);
            return WebResponse::error(
                500,
                format!("round #{id}: the engine errored on resolve: {e}"),
            );
        }
    };

    let winner = match round.options.get(decision.winner).cloned() {
        Some(w) => w,
        None => {
            return WebResponse::error(
                500,
                format!(
                    "the certified winner index {} is out of range",
                    decision.winner
                ),
            )
        }
    };
    let cert = cert_json(&round, &decision);
    let tally = tally_json(&round);
    let round_id = round.id;
    let winner_summary = winner.edit.summary();
    let winner_kind = winner.edit.kind();

    // THE VALIDATOR DISPOSES — pass the certified edit to the fail-closed validator.
    let disposition = st.draft.dispose(&winner.edit);
    let (applied, disp_tag, stage, reason, source_after) = match disposition {
        Disposition::Applied { draft, source } => {
            st.draft = draft;
            (true, "applied", "", String::new(), source)
        }
        Disposition::Refused { stage, reason } => {
            // ROLLBACK: the draft is left exactly as it was (dispose took &self). Report honestly.
            (false, "refused", stage.tag(), reason, st.draft.render())
        }
    };
    let source_hash = source_hash_hex(&source_after);

    // The certified winner is decided — remove it from the pool whether applied or refused (a
    // refused breaking edit can never apply; a losing proposal stays pending for the next round).
    st.proposals.retain(|p| p.id != winner.id);

    // Append to the append-only certified history (the provenance of the co-authored dungeon).
    let seq = st.next_seq;
    st.next_seq += 1;
    st.history.push(HistoryEntry {
        seq,
        round_id,
        summary: winner_summary.clone(),
        kind: winner_kind,
        disposition: disp_tag,
        refuse_stage: stage,
        reason: reason.clone(),
        source_hash: source_hash.clone(),
        cert: cert.clone(),
    });

    let resp = json!({
        "ok": true,
        "roundId": round_id,
        "quorumCertified": true,
        "cert": cert,
        "tally": tally,
        "winner": { "kind": winner_kind, "summary": winner_summary, "edit": edit_json(&winner.edit) },
        // THE DISPOSITION — what the VALIDATOR did with the certified edit.
        "disposition": {
            "applied": applied,
            "outcome": disp_tag,
            "stage": if stage.is_empty() { Value::Null } else { json!(stage) },
            "reason": if reason.is_empty() { Value::Null } else { json!(reason) },
            "note": if applied {
                "the certified edit was SOUND \u{2014} applied to the draft (it parses + validates + plays)"
            } else {
                "the certified edit would BREAK the world \u{2014} REFUSED by the validator and rolled back despite the passing vote (the crowd proposes, the validator disposes)"
            },
        },
        "historySeq": seq,
        "draft": draft_json(&st),
    });
    WebResponse::json(resp.to_string().into_bytes())
}

/// `POST /coauthor/reset` — reset the shared draft to the minimal seed and clear the pool / round /
/// history (a clean slate for a fresh co-authoring session or the driver).
pub fn handle_reset(cs: &Mutex<CoAuthorState>) -> WebResponse {
    let mut st = cs.lock().unwrap();
    *st = build_coauthor_state();
    let resp = json!({ "ok": true, "draft": draft_json(&st) });
    WebResponse::json(resp.to_string().into_bytes())
}
