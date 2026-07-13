//! # `dreggnet-doc` — the COLLABORATIVE DOCUMENT offering.
//!
//! The dungeon is offering #0 (a confined narrative world). This is the
//! **productivity/collaboration** one, and it is the same five-part shape:
//!
//! 1. **A per-session confined thing** — one live shared document (a real
//!    `dregg_cell::Cell`, committed over its `fields_root`).
//! 2. **Real verifiable turns** — an EDIT is one real
//!    [`dregg_turn::TurnExecutor::execute`] turn through the document substrate's
//!    sole executor entry ([`dregg_doc::ExecutorDrivenDoc::edit`]), landing a
//!    genuine finalized [`TurnReceipt`].
//! 3. **The referee is the executor + the document soundness core, never prose** —
//!    an *unauthorized* edit (an actor without the region's edit cap) is refused
//!    **in-band by the executor** (`TurnError::CapabilityNotHeld`); a *conflicting*
//!    edit (one that would leave the document carrying an unresolved antichain or
//!    field clash) is refused by `dregg-doc`'s own conflict semantics. Nothing
//!    commits on a refusal (the anti-ghost tooth).
//! 4. **Payment-gated** — [`Offering::price`] names a per-edit [`RunCost`]
//!    (free tier by default; a resolution is always free).
//! 5. **Verifiable end to end** — [`Offering::verify`] re-drives the WHOLE edit
//!    chain from genesis through the real executor and checks that the document
//!    reproduces, byte for byte, at every step. A forged edit fails.
//!
//! ## What is consumed, and what is NOT re-implemented
//!
//! Every document semantic comes from [`dregg_doc`] — the Pijul-shaped patch
//! theory (`DocGraph` / `Patch` / `Op` / `History`), the categorical merge
//! (`merge` = the pushout as a total graph union), the conflict model
//! (`content`'s first-class antichain / field-clash [`ConflictRegion`]s + the
//! two-regime [`Regime`] classifier), provenance/blame, and the executor-drive
//! seam ([`ExecutorDrivenDoc`], where a per-region edit cap is a c-list capability
//! the executor's `check_cross_cell_permission` gate enforces). This crate adds
//! **no CRDT, no merge rule, no conflict rule** of its own: it is the *session +
//! affordance + verification* layer that presents the substrate as an
//! [`Offering`].
//!
//! ## The session model (and the honest gaps)
//!
//! A [`DocSession`] holds the document's [`History`] (the patch chain — the
//! document IS its history), the current fold, an ordered roster of collaborators
//! (each with a [`Role`], which decides whether their editor cell holds the
//! region's edit capability), and the [`CommittedEdit`] log — one entry per landed
//! turn, binding the turn's deterministic core (`turn_hash` / `effects_hash` /
//! pre- and post-state roots) and the document's commitment after it.
//!
//! - **One editor cell per document instance.** [`ExecutorDrivenDoc`] binds a
//!   SINGLE editor cell at construction, so a session cannot hold one long-lived
//!   ledger with N editor cells. Each edit therefore **re-bases** a per-actor
//!   executor-driven document at the session's current fold
//!   ([`ExecutorDrivenDoc::new_at`]) and drives that actor's turn on it. Each edit
//!   is still a genuine cap-gated, journaled, `Finality::Final` executor turn; what
//!   is lost is the executor's own cross-edit per-agent nonce / receipt chain (each
//!   turn starts at nonce 0 with no `previous_receipt_hash`, and the region cell's
//!   nonce reads 1 at every committed edit rather than counting up across the
//!   session). The session's chain is instead the **document-commitment chain**
//!   every turn's pre/post state roots bind, which [`Offering::verify`] re-derives
//!   edit by edit. Closing this properly is a multi-editor constructor in
//!   `dregg-doc` (a NAMED gap — this crate does not modify the substrate).
//! - **The conflict gate is the fold, not `PullRequest::merge`.** A live session is
//!   the *fast-forward* case (the new history is the old history plus one patch).
//!   `PullRequest`'s pushout is `merge(base_fold, head_fold)`, and the field union
//!   re-introduces a base assignment a *superseding* `SetField` just collapsed — so
//!   a resolution can never land through the PR path on a fast-forward (dregg-doc's
//!   own `DriveDivergedFromPushout` flags exactly this order-sensitivity). The
//!   session therefore gates on the fold of the new history with dregg-doc's own
//!   detector ([`content`] + [`Regime`]) — the same detector `PullRequest::conflicts`
//!   reads — and applies the forge's rule (refuse to land an edit that leaves an
//!   unresolved conflict). The `PullRequest` path stays the right thing for a
//!   genuine *fork* (a review branch); `tests/driven.rs` pins the fast-forward
//!   limitation as a live falsifier.
//! - **The affordance wire carries no free text.** A deos affordance is
//!   `{turn, arg: i64}`. A document edit needs a *string* payload, so an edit's text
//!   rides the [`Action::label`] (which round-trips through a [`Frontend`]'s
//!   present/collect exactly as the button text does). A string-carrying affordance
//!   arg is the NAMED gap for a real editor surface.
//!
//! ## What a fuller collaborative document adds
//!
//! Rich inline marks (bold/comment ranges — `dregg_doc::marks` exists and merges
//! independently of the text; unwired here), review threads (`dregg_doc::review` —
//! comments + approvals as receipted atoms, which need a `PullRequest`), presence /
//! cursors (ephemeral, uncommitted, no substrate analogue yet), and character-level
//! granularity via `Doc::edit`'s token LCS (this offering's edits are span-level
//! `Add`/`Delete`, which is the substrate's own atom granularity).

use std::collections::BTreeMap;

use deos_view::{MenuItem, ViewNode};
use dregg_doc::{
    AtomId, Author, ConflictRegion, DocGraph, ExecutorDrivenDoc, History, Op, Patch, Regime,
    Rendered, content, walk_atoms,
};
use dregg_turn::{TurnError, TurnReceipt};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RecordVerify, RunCost, SessionConfig,
    Surface, VerifyReport,
};

/// Insert a text span into the document, ordered after the anchor named by
/// [`Action::arg`] (see [`DocSession::anchors`]). The span's TEXT is the action's
/// [`Action::label`] (the affordance wire carries no string payload — see the crate
/// docs). Desugars to `dregg_doc::Op::Add`.
pub const TURN_INSERT: &str = "insert";
/// Tombstone the live cell named by [`Action::arg`] (1-based over
/// [`DocSession::cells`]). Desugars to `dregg_doc::Op::Delete` — a monotone
/// tombstone, never a physical removal (the atom survives for provenance).
pub const TURN_DELETE: &str = "delete";
/// Assign the document's single-valued `title` field (the non-monotone fragment).
/// The VALUE is the action's [`Action::label`]. Desugars to a **non-superseding**
/// `dregg_doc::Op::SetField` — a second, differing assignment is a real
/// [`Regime::Field`] clash, and is refused.
pub const TURN_SET_TITLE: &str = "set_title";
/// **Resolve** a `title` clash by settling it: a **superseding**
/// `dregg_doc::Op::SetField` that collapses the whole assignment set to the chosen
/// value ([`Action::label`]). This is the "a conflict is a first-class state a
/// later patch resolves" face — and it is always [`RunCost::free`].
pub const TURN_RESOLVE_TITLE: &str = "resolve_title";
/// **Resolve** a prose antichain by ORDERING it: `Connect(a, b)` — "a comes before
/// b" — collapsing the antichain into a chain. [`Action::arg`] is the index of the
/// conflict region (0-based over [`DocSession::conflicts`]); the alternatives are
/// ordered in the region's canonical order. Desugars to `dregg_doc::Op::Connect`.
pub const TURN_ORDER_CONFLICT: &str = "order_conflict";

/// The document's single-valued title field (the non-monotone/authority fragment
/// the [`Regime::Field`] classifier guards).
pub const FIELD_TITLE: &str = "title";

/// A collaborator's role — and therefore whether their editor cell holds the
/// document region's **edit capability**.
///
/// This is not a decoration: [`Role::Editor`] grants a real c-list capability to
/// the region cell, and [`Role::Commenter`] does not — so a commenter's edit turn
/// is refused **by the executor** (`check_cross_cell_permission` →
/// `TurnError::CapabilityNotHeld`), in-band, with nothing committed. An actor who
/// is not on the roster at all is treated as an outsider: same gate, same refusal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    /// Holds the region's edit cap — their edits commit.
    Editor,
    /// Does NOT hold the region's edit cap — the executor refuses their edits.
    /// (Read/comment affordances are the fuller-collaboration seam; see the crate
    /// docs.)
    Commenter,
}

impl Role {
    /// Whether this role's editor cell is granted the region's edit capability.
    pub fn holds_edit_cap(self) -> bool {
        matches!(self, Role::Editor)
    }

    /// A short label for the surface.
    pub fn label(self) -> &'static str {
        match self {
            Role::Editor => "editor",
            Role::Commenter => "commenter (no edit cap)",
        }
    }
}

/// A roster entry: who, their [`Role`], and the deterministic **editor-cell seed**
/// their turns are signed from. The seed is the roster index + 1, so it is stable
/// under replay (the verifier re-derives the same editor cell — hence the same
/// agent, the same ledger roots, the same `turn_hash`).
#[derive(Debug, Clone)]
pub struct Collaborator {
    /// The frontend-agnostic identity.
    pub who: DreggIdentity,
    /// Editor (holds the region edit cap) or commenter (does not).
    pub role: Role,
    /// The deterministic editor-cell seed (roster index + 1).
    pub seed: u8,
}

/// The seed an actor who is NOT on the roster gets: a real editor cell, with **no**
/// region capability — so an outsider's edit reaches the executor and is refused
/// there (not pre-filtered by us).
const OUTSIDER_SEED: u8 = 200;

/// **One landed edit** — the record of a real committed turn.
///
/// It binds the *deterministic core* of the executor's receipt: the `turn_hash`
/// (the turn the executor admitted), the `effects_hash` (the `SetField` writes it
/// applied), and the pre/post ledger state roots. It deliberately does NOT bind
/// `TurnReceipt::receipt_hash()`, which absorbs the receipt's wall-clock
/// `timestamp` and so is not replay-reproducible — an honest boundary, not a
/// weaker one: the turn, its effects, and the state it moved are all pinned.
#[derive(Debug, Clone)]
pub struct CommittedEdit {
    /// Who made the edit.
    pub actor: DreggIdentity,
    /// The document patch it committed (the real `dregg_doc::Patch`).
    pub patch: Patch,
    /// The genuine turn hash the executor admitted.
    pub turn_hash: [u8; 32],
    /// The genuine effects hash (the kernel writes).
    pub effects_hash: [u8; 32],
    /// The ledger state root before the turn.
    pub pre_state_hash: [u8; 32],
    /// The ledger state root after the turn.
    pub post_state_hash: [u8; 32],
    /// The DOCUMENT's commitment after this edit — the region cell's canonical
    /// state commitment (which absorbs `fields_root`, the digest of the document
    /// projection the executor wrote). This is the chain a light client follows.
    pub doc_commitment: [u8; 32],
}

/// The **public, transmissible record** of a document session — what a frontend
/// serializes, transmits, persists, and might receive back FORGED. The
/// [`RecordVerify`] seam re-checks it against the session's authentic identity
/// (the private region seed + the roster, which never leave the offering).
#[derive(Debug, Clone)]
pub struct DocRecord {
    /// Every landed edit, in order.
    pub edits: Vec<CommittedEdit>,
    /// The document's commitment at the end of the chain.
    pub commitment: [u8; 32],
}

/// **A live collaborative document session** over the real `dregg-doc` substrate.
///
/// The document IS its patch history ([`History`]); the current content is the fold
/// ([`History::replay`]). Every landed edit is one real executor turn; the
/// [`CommittedEdit`] log is the chain [`Offering::verify`] re-drives.
pub struct DocSession {
    /// The document (region) cell's deterministic seed — the session's private
    /// world identity. A verifier re-derives the SAME region cell from it, so a
    /// forged record cannot re-target another document.
    region_seed: u8,
    /// The collaborators, in invitation order (the index fixes each one's editor
    /// cell seed, so replay reproduces the same agents).
    roster: Vec<Collaborator>,
    /// The document's patch history — the document, as its edits.
    history: History,
    /// The fold of `history` (kept in lockstep; every landed edit advances both).
    graph: DocGraph,
    /// One entry per landed turn.
    edits: Vec<CommittedEdit>,
}

impl DocSession {
    /// Invite `who` with `role` — assigning them a deterministic editor cell.
    /// A [`Role::Editor`] is granted the document region's edit capability (their
    /// turns commit); a [`Role::Commenter`] is not (the executor refuses their
    /// edits). Re-inviting an existing collaborator UPDATES their role and keeps
    /// their cell.
    pub fn invite(&mut self, who: DreggIdentity, role: Role) {
        if let Some(existing) = self.roster.iter_mut().find(|c| c.who == who) {
            existing.role = role;
            return;
        }
        let seed = (self.roster.len() as u8).saturating_add(1);
        self.roster.push(Collaborator { who, role, seed });
    }

    /// The roster, in invitation order.
    pub fn roster(&self) -> &[Collaborator] {
        &self.roster
    }

    /// `who`'s role, or `None` if they are not on the roster (an outsider).
    pub fn role_of(&self, who: &DreggIdentity) -> Option<Role> {
        self.roster.iter().find(|c| c.who == *who).map(|c| c.role)
    }

    /// The (editor-cell seed, holds-the-region-edit-cap) pair the executor drives
    /// `who`'s turn with. An outsider gets a real cell with NO cap — their edit
    /// still reaches the executor, and is refused there.
    fn actor_cell(&self, who: &DreggIdentity) -> (u8, bool) {
        match self.roster.iter().find(|c| c.who == *who) {
            Some(c) => (c.seed, c.role.holds_edit_cap()),
            None => (OUTSIDER_SEED, false),
        }
    }

    /// The document's patch history (the document, as its edits).
    pub fn history(&self) -> &History {
        &self.history
    }

    /// The current fold — the live document graph.
    pub fn graph(&self) -> &DocGraph {
        &self.graph
    }

    /// The landed-edit log (one entry per committed turn).
    pub fn edits(&self) -> &[CommittedEdit] {
        &self.edits
    }

    /// The document's rendered content — clean runs plus any first-class conflict
    /// regions (dregg-doc's own fold).
    pub fn rendered(&self) -> Rendered {
        content(&self.graph)
    }

    /// The document's text (conflicts rendered legibly between markers).
    pub fn text(&self) -> String {
        self.rendered().to_marked_string()
    }

    /// The document's live conflict regions (empty in a healthy session — the
    /// landing gate refuses an edit that would introduce one; a conflict can still
    /// be *carried* if one is ever admitted, which is why the surface renders them).
    pub fn conflicts(&self) -> Vec<ConflictRegion> {
        self.rendered().conflicts().cloned().collect()
    }

    /// The document's live cells (atoms) in document order — the editable units.
    pub fn cells(&self) -> Vec<(AtomId, String)> {
        walk_atoms(&self.graph)
    }

    /// The single-valued `title` field's live assignments. Two-or-more is a real
    /// [`Regime::Field`] clash.
    pub fn title(&self) -> Vec<String> {
        self.graph
            .field(FIELD_TITLE)
            .iter()
            .map(|a| a.value.clone())
            .collect()
    }

    /// The anchor positions an insert can name: `arg = 0` is the start of the
    /// document (`AtomId::ROOT`); `arg = i` (1-based) is "after the i-th live cell".
    /// Inserting at a NON-tip anchor that another actor has already extended is
    /// exactly the concurrent-edit case that produces an antichain — the landing
    /// gate refuses it.
    pub fn anchors(&self) -> Vec<(i64, String)> {
        let mut out = vec![(0i64, "the start of the document".to_string())];
        for (i, (_, text)) in self.cells().iter().enumerate() {
            out.push(((i + 1) as i64, format!("after \"{text}\"")));
        }
        out
    }

    /// The atom an insert's `arg` anchors after (`0` → `AtomId::ROOT`).
    fn anchor_at(&self, arg: i64) -> Option<AtomId> {
        if arg == 0 {
            return Some(AtomId::ROOT);
        }
        let idx = usize::try_from(arg.checked_sub(1)?).ok()?;
        self.cells().get(idx).map(|(id, _)| *id)
    }

    /// The live atom a delete's `arg` names (1-based over [`DocSession::cells`]).
    fn cell_at(&self, arg: i64) -> Option<AtomId> {
        let idx = usize::try_from(arg.checked_sub(1)?).ok()?;
        self.cells().get(idx).map(|(id, _)| *id)
    }

    /// The number of real verified turns so far (one per landed edit).
    pub fn turns(&self) -> usize {
        self.edits.len()
    }

    /// The document's CURRENT commitment — the region cell's real canonical state
    /// commitment, **as the executor wrote it** on the last committed edit (the
    /// value a light client trusts). An untouched document's commitment is its
    /// genesis cell's.
    ///
    /// It is deliberately NOT recomputed by re-seeding a cell at the current fold:
    /// the canonical state commitment absorbs the region cell's `nonce` as well as
    /// its `fields_root`, and the executor ADVANCES that nonce on the turn it
    /// commits. (Measured: a written cell and a re-seeded cell at the same fold have
    /// byte-identical `fields_map` — the document projection — and differ only in the
    /// nonce.) So the commitment binds "the document, as edited", not merely the
    /// fold; taking it from the committed chain keeps it the executor's value rather
    /// than a reconstruction of it.
    pub fn commitment(&self) -> [u8; 32] {
        match self.edits.last() {
            Some(last) => last.doc_commitment,
            None => genesis_commitment(self.region_seed),
        }
    }

    /// The public, transmissible session record (the [`RecordVerify`] input).
    pub fn record(&self) -> DocRecord {
        DocRecord {
            edits: self.edits.clone(),
            commitment: self.commitment(),
        }
    }

    /// Per-author contribution counts (dregg-doc's `blame_summary` over the live
    /// fold — attribution that does NOT move when the surrounding text does,
    /// because atom ids are content-addressed).
    pub fn contributions(&self) -> BTreeMap<u64, usize> {
        dregg_doc::blame_summary(&self.graph)
            .into_iter()
            .map(|(a, n)| (a.0, n))
            .collect()
    }

    /// Which collaborator an [`Author`] label belongs to (the author id IS the
    /// editor-cell seed).
    pub fn author_name(&self, author: Author) -> String {
        self.roster
            .iter()
            .find(|c| c.seed as u64 == author.0)
            .map(|c| c.who.as_str().to_string())
            .unwrap_or_else(|| format!("author {}", author.0))
    }
}

/// The commitment of an UNEDITED document: the genesis region cell at the session's
/// private seed (an empty fold, nonce 0), read through the real
/// `compute_canonical_state_commitment`. Nothing is driven, so no cap is needed.
fn genesis_commitment(region_seed: u8) -> [u8; 32] {
    ExecutorDrivenDoc::new_at(&DocGraph::new(), OUTSIDER_SEED, region_seed, false)
        .state_commitment()
}

/// **What the session does with an edit that would leave a conflict standing** —
/// and the reason the [`Regime`] classifier is load-bearing here rather than
/// decorative.
///
/// dregg-doc's two-regime split says a conflict is not one thing: a **prose
/// antichain** (two concurrent inserts at one position) is *illusory* — benign,
/// legible, unilaterally resolvable, never blocking the rest of the document —
/// while a **single-valued field clash** is a *real* conservation/authority clash
/// that [`Regime::needs_consensus`] says must be settled. A collaborative document
/// offering can take either stance, and it should say which:
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConflictPolicy {
    /// **The forge's landing rule** (the default): a shared document stays clean —
    /// an edit that would leave ANY unresolved conflict standing is refused, and
    /// nothing commits. This is `PullRequest::merge`'s
    /// `UnresolvedConflict` discipline restated for a live linear session: the
    /// concurrent author re-anchors at the tip (or opens a branch).
    RefuseUnresolved,
    /// **Conflicts as first-class objects** (dregg-doc's own doctrine): a benign
    /// [`Regime::Prose`] antichain is ADMITTED — it commits as real state, the
    /// surface renders both alternatives with who wrote which, and a later patch
    /// ([`TURN_ORDER_CONFLICT`]) resolves it. A [`Regime::Field`] clash
    /// ([`Regime::needs_consensus`]) is still refused — it is the conservation
    /// boundary. The document never *fails to merge*; it carries the state.
    CarryProseConflicts,
}

/// **The collaborative-document offering.** A stateless factory: each
/// [`open`](Offering::open) is a fresh empty document under a deterministic region
/// identity. `edit_credits` prices a per-edit run-credit (the free tier by default);
/// [`ConflictPolicy`] decides what happens to a conflicting edit.
pub struct DocOffering {
    /// Run-credits a landed edit costs (`0` → free tier). A resolution is always
    /// free — settling a conflict is never taxed.
    edit_credits: u64,
    /// What a conflicting edit does (see [`ConflictPolicy`]).
    policy: ConflictPolicy,
}

impl DocOffering {
    /// The free-tier document (no credit debited per edit), keeping the shared
    /// document clean ([`ConflictPolicy::RefuseUnresolved`]).
    pub fn new() -> Self {
        DocOffering {
            edit_credits: 0,
            policy: ConflictPolicy::RefuseUnresolved,
        }
    }

    /// A paid-tier document: each landed edit costs `credits` run-credits (the
    /// frontend debits them; the core only names the cost). The substrate turn
    /// itself is always free and verifiable.
    pub fn paid(credits: u64) -> Self {
        DocOffering {
            edit_credits: credits,
            policy: ConflictPolicy::RefuseUnresolved,
        }
    }

    /// The document that carries a benign prose antichain as first-class state
    /// (and still refuses a field/authority clash) —
    /// [`ConflictPolicy::CarryProseConflicts`].
    pub fn carrying_prose_conflicts(mut self) -> Self {
        self.policy = ConflictPolicy::CarryProseConflicts;
        self
    }

    /// This offering's conflict policy.
    pub fn policy(&self) -> ConflictPolicy {
        self.policy
    }

    /// The affordances on the document's surface, **cap-gated for `actor`** when one
    /// is given: an actor without the region's edit cap sees every edit affordance
    /// **dimmed** (`enabled: false`) — the cap tooth SHOWN, not hidden. It is only a
    /// decoration: firing a dimmed affordance still lands a real executor
    /// [`Outcome::Refused`] (the executor is the sole referee). With `actor = None`
    /// the affordances are the session's own (enabled where the position is legal).
    pub fn actions_for(&self, session: &DocSession, actor: Option<&DreggIdentity>) -> Vec<Action> {
        let may_edit = match actor {
            Some(a) => session
                .role_of(a)
                .map(Role::holds_edit_cap)
                .unwrap_or(false),
            None => true,
        };

        let mut out = Vec::new();
        let cells = session.cells();

        // Append at the tip — the always-clean insert position.
        out.push(Action::new(
            "…continue the document".to_string(),
            TURN_INSERT,
            cells.len() as i64,
            may_edit,
        ));
        // Insert at the start.
        out.push(Action::new(
            "…open the document".to_string(),
            TURN_INSERT,
            0,
            may_edit,
        ));
        // Delete each live cell.
        for (i, (_, text)) in cells.iter().enumerate() {
            out.push(Action::new(
                format!("delete \"{text}\""),
                TURN_DELETE,
                (i + 1) as i64,
                may_edit,
            ));
        }
        // The single-valued title (the non-monotone fragment).
        out.push(Action::new(
            "set the title".to_string(),
            TURN_SET_TITLE,
            0,
            may_edit,
        ));
        // Resolution affordances — offered only where a conflict actually stands
        // (nothing is fabricated).
        for (i, region) in session.conflicts().iter().enumerate() {
            match region.regime {
                Regime::Field => out.push(Action::new(
                    "settle the title clash".to_string(),
                    TURN_RESOLVE_TITLE,
                    0,
                    may_edit,
                )),
                Regime::Prose => out.push(Action::new(
                    "order the concurrent alternatives".to_string(),
                    TURN_ORDER_CONFLICT,
                    i as i64,
                    may_edit,
                )),
            }
        }
        out
    }

    /// The document's surface, **rendered for `actor`** (their cap-gated
    /// affordances). [`Offering::render`] is this with `actor = None`.
    pub fn render_for(&self, session: &DocSession, actor: Option<&DreggIdentity>) -> Surface {
        let rendered = session.rendered();
        let title = match session.title().as_slice() {
            [] => "untitled".to_string(),
            [one] => one.clone(),
            many => format!("CLASH: {}", many.join(" | ")),
        };

        let cells: Vec<ViewNode> = session
            .cells()
            .iter()
            .enumerate()
            .map(|(i, (id, text))| {
                let who = session
                    .graph
                    .atom(*id)
                    .map(|a| session.author_name(a.provenance.author))
                    .unwrap_or_else(|| "?".to_string());
                ViewNode::Text(format!("[{}] {text}  — {who}", i + 1))
            })
            .collect();

        let roster: Vec<ViewNode> = session
            .roster()
            .iter()
            .map(|c| ViewNode::Text(format!("{} — {}", c.who.as_str(), c.role.label())))
            .collect();

        let mut children = vec![
            ViewNode::Section {
                title: "Text".to_string(),
                tag: "accent".to_string(),
                children: vec![ViewNode::Text(rendered.to_marked_string())],
            },
            ViewNode::Section {
                title: "Cells".to_string(),
                tag: "muted".to_string(),
                children: if cells.is_empty() {
                    vec![ViewNode::Text("(empty document)".to_string())]
                } else {
                    cells
                },
            },
            ViewNode::Section {
                title: "Collaborators".to_string(),
                tag: "muted".to_string(),
                children: if roster.is_empty() {
                    vec![ViewNode::Text("(nobody invited yet)".to_string())]
                } else {
                    roster
                },
            },
            ViewNode::Section {
                title: "Verified edits".to_string(),
                tag: "genuine".to_string(),
                children: vec![ViewNode::Text(format!(
                    "{} real committed turns · commitment {}",
                    session.turns(),
                    hex8(&session.commitment())
                ))],
            },
        ];

        // A conflict is a FIRST-CLASS STATE, so the surface shows it (with who wrote
        // which alternative — provenance is a fact, not a guess).
        let conflicts = session.conflicts();
        if !conflicts.is_empty() {
            let mut kids = Vec::new();
            for region in &conflicts {
                let alts: Vec<String> = region
                    .alternatives
                    .iter()
                    .map(|a| {
                        format!(
                            "\"{}\" ({})",
                            a.text,
                            session.author_name(a.provenance.author)
                        )
                    })
                    .collect();
                kids.push(ViewNode::Text(format!(
                    "[{}] {}",
                    region.regime.label(),
                    alts.join("  vs  ")
                )));
            }
            children.push(ViewNode::Section {
                title: "Unresolved".to_string(),
                tag: "warn".to_string(),
                children: kids,
            });
        }

        let items = self
            .actions_for(session, actor)
            .iter()
            .map(|a| MenuItem {
                label: a.label.clone(),
                turn: a.turn.clone(),
                arg: a.arg,
                enabled: a.enabled,
            })
            .collect();
        children.push(ViewNode::Section {
            title: "Edit".to_string(),
            tag: "accent".to_string(),
            children: vec![ViewNode::Menu { items }],
        });

        Surface(ViewNode::Section {
            title: format!("{title} — a shared document"),
            tag: "accent".to_string(),
            children,
        })
    }
}

impl Default for DocOffering {
    fn default() -> Self {
        DocOffering::new()
    }
}

/// Build the real `dregg_doc::Patch` an [`Action`] denotes, at the session's current
/// fold, authored by the actor's editor cell. `None` for an ill-formed affordance
/// (an unknown verb, an out-of-range anchor, an empty span) — which is refused
/// without ever reaching the executor (no turn, nothing committed).
///
/// The atom seed is derived from the edit's INDEX in the chain plus the author's
/// cell seed, so it is deterministic under replay (the verifier re-derives the same
/// atom ids — hence the same patch, the same effects, the same `turn_hash`) while
/// still keeping two actors' identical text distinct.
fn build_patch(session: &DocSession, input: &Action, seed: u8) -> Option<Patch> {
    let author = Author(seed as u64);
    let atom_seed = (session.edits.len() as u64)
        .wrapping_mul(257)
        .wrapping_add(seed as u64)
        .wrapping_add(1);

    match input.turn.as_str() {
        TURN_INSERT => {
            if input.label.trim().is_empty() {
                return None;
            }
            let anchor = session.anchor_at(input.arg)?;
            Some(Patch::by(
                author,
                [Patch::add(atom_seed, &input.label, anchor).1],
            ))
        }
        TURN_DELETE => {
            let id = session.cell_at(input.arg)?;
            Some(Patch::by(author, [Op::Delete { id }]))
        }
        TURN_SET_TITLE => {
            if input.label.trim().is_empty() {
                return None;
            }
            Some(Patch::by(
                author,
                [Op::SetField {
                    name: FIELD_TITLE.to_string(),
                    value: input.label.clone(),
                    superseding: false,
                }],
            ))
        }
        TURN_RESOLVE_TITLE => {
            if input.label.trim().is_empty() {
                return None;
            }
            Some(Patch::by(
                author,
                [Op::SetField {
                    name: FIELD_TITLE.to_string(),
                    value: input.label.clone(),
                    // SUPERSEDING: collapses the whole clashing assignment set to
                    // this value (dregg-doc's `supersede_field`) — the resolution.
                    superseding: true,
                }],
            ))
        }
        TURN_ORDER_CONFLICT => {
            let idx = usize::try_from(input.arg).ok()?;
            let region = session.conflicts().into_iter().nth(idx)?;
            if region.regime != Regime::Prose {
                return None;
            }
            let heads = region.heads();
            // Order the antichain into a chain: h0 -> h1 -> … (dregg-doc's
            // `Op::Connect` — the prose-conflict resolution primitive).
            let ops: Vec<Op> = heads
                .windows(2)
                .map(|w| Op::Connect {
                    from: w[0],
                    to: w[1],
                })
                .collect();
            if ops.is_empty() {
                return None;
            }
            Some(Patch::by(author, ops))
        }
        _ => None,
    }
}

/// Why an edit was refused, as a human line for the surface.
#[derive(Debug, Clone)]
struct Refusal(String);

/// The landing result of one driven edit.
struct Landed {
    receipt: TurnReceipt,
    graph: DocGraph,
    doc_commitment: [u8; 32],
}

/// **Drive ONE edit** at `base_graph`, as `seed`'s editor cell, on the region cell
/// `region_seed`. Two gates, in dregg-doc's own order (`PullRequest::land_checked`
/// gates conflicts → … → the executor's cap, in-band, per driven turn):
///
/// 1. **Document soundness** — the fold of the new history must not leave an
///    unresolved conflict standing, as `policy` reads it. The DETECTION is entirely
///    dregg-doc's ([`content`]'s first-class antichain / field-clash regions + the
///    two-regime [`Regime`] classifier); the POLICY is the forge's landing rule.
///    A refused edit is refused BEFORE any turn is built: the executor never sees
///    an unsound document.
/// 2. **Authority** — the edit is driven through
///    [`ExecutorDrivenDoc::edit`], the substrate's SOLE `TurnExecutor::execute`
///    entry. An editor cell without the region's c-list capability is refused
///    IN-BAND by `check_cross_cell_permission` (`TurnError::CapabilityNotHeld`);
///    the executor rolls the ledger back and nothing commits.
///
/// A refusal is total: the caller's session is never touched (this function works
/// on clones and returns before any session mutation).
fn drive_edit(
    base_graph: &DocGraph,
    patch: &Patch,
    seed: u8,
    holds_cap: bool,
    region_seed: u8,
    policy: ConflictPolicy,
) -> Result<Landed, Refusal> {
    // GATE 1 — DOCUMENT SOUNDNESS (dregg-doc's own conflict semantics).
    let next = patch.apply_to(base_graph);
    let before = content(base_graph);
    let after = content(&next);
    // The conflict region this edit would INTRODUCE (one that does not already
    // stand). A resolution introduces none — it removes one.
    let introduced = after
        .conflicts()
        .find(|c| !before.conflicts().any(|b| b == *c))
        .cloned();
    if let Some(region) = introduced {
        let refuse = match policy {
            ConflictPolicy::RefuseUnresolved => true,
            // The two-regime classifier decides: a benign prose antichain is
            // carried as first-class state; a conservation/authority clash is not.
            ConflictPolicy::CarryProseConflicts => region.regime.needs_consensus(),
        };
        if refuse {
            return Err(Refusal(conflict_reason(Some(&region))));
        }
    }

    // GATE 2 — AUTHORITY: the REAL executor (the cap gate lives inside).
    let mut doc = ExecutorDrivenDoc::new_at(base_graph, seed, region_seed, holds_cap);
    match doc.edit(patch.clone()) {
        Ok(receipt) => {
            if !doc.commitment_matches_projection() {
                return Err(Refusal(
                    "refused: the committed cell and the document fold diverged".to_string(),
                ));
            }
            Ok(Landed {
                receipt,
                graph: doc.graph().clone(),
                doc_commitment: doc.state_commitment(),
            })
        }
        Err(TurnError::CapabilityNotHeld { .. }) => Err(Refusal(
            "refused by the executor: this actor does not hold the document region's edit \
             capability (TurnError::CapabilityNotHeld) — nothing committed"
                .to_string(),
        )),
        Err(TurnError::EmptyForest) => Err(Refusal(
            "refused: this edit is a no-op at the committed document (nothing to commit)"
                .to_string(),
        )),
        Err(e) => Err(Refusal(format!("refused by the executor: {e:?}"))),
    }
}

/// The refusal line for an edit that would leave the document carrying an
/// unresolved conflict — naming the REGIME (dregg-doc's two-regime classifier:
/// a prose antichain vs a single-valued field/authority clash).
fn conflict_reason(region: Option<&ConflictRegion>) -> String {
    match region {
        Some(c) if c.regime == Regime::Field => format!(
            "refused: this edit leaves an unresolved FIELD conflict on \"{}\" ({} clashing values) \
             — a conservation/authority clash the two-regime classifier says needs consensus; \
             settle it with a superseding resolution",
            c.field.as_deref().unwrap_or(FIELD_TITLE),
            c.alternatives.len()
        ),
        Some(c) => format!(
            "refused: this edit leaves an unresolved PROSE conflict — {} live, mutually-unordered \
             alternatives at one position (a concurrent edit at a stale anchor); re-anchor at the \
             tip, or order the antichain",
            c.alternatives.len()
        ),
        None => "refused: this edit leaves an unresolved conflict".to_string(),
    }
}

impl Offering for DocOffering {
    type Session = DocSession;

    /// Open a fresh shared document: an empty patch history under a deterministic
    /// region identity (the config seed pins the region cell, so a verifier
    /// re-derives the same document cell and a forged record cannot re-target
    /// another one). Collaborators are invited with [`DocSession::invite`].
    fn open(&self, cfg: SessionConfig) -> Result<DocSession, OfferingError> {
        let region_seed = ((cfg.seed.unwrap_or(1) % 251) + 1) as u8;
        Ok(DocSession {
            region_seed,
            roster: Vec::new(),
            history: History::new(),
            graph: DocGraph::new(),
            edits: Vec::new(),
        })
    }

    /// The document's edit affordances (session-level; [`DocOffering::actions_for`]
    /// is the per-actor cap-gated view).
    fn actions(&self, session: &DocSession) -> Vec<Action> {
        self.actions_for(session, None)
    }

    /// **An EDIT is ONE real turn.** The typed [`Action`] is desugared into a real
    /// `dregg_doc::Patch` and driven through the substrate's sole executor entry:
    ///
    /// - a legal, authorized edit lands a genuine finalized [`TurnReceipt`]
    ///   ([`Outcome::Landed`]) and advances the document's history + fold;
    /// - an edit by an actor without the region's edit cap is a real **executor**
    ///   refusal ([`TurnError::CapabilityNotHeld`]) — [`Outcome::Refused`], nothing
    ///   committed;
    /// - an edit that would leave the document carrying an unresolved conflict (a
    ///   concurrent insert at a stale anchor → an antichain; a second differing
    ///   `title` assignment → a field clash) is refused by dregg-doc's own conflict
    ///   semantics — [`Outcome::Refused`], nothing committed.
    ///
    /// The anti-ghost tooth: on ANY refusal the session is byte-untouched (no
    /// patch, no receipt, no commitment move).
    fn advance(&self, session: &mut DocSession, input: Action, actor: DreggIdentity) -> Outcome {
        let (seed, holds_cap) = session.actor_cell(&actor);

        let Some(patch) = build_patch(session, &input, seed) else {
            return Outcome::Refused(format!(
                "refused: \"{}\" (arg {}) is not a well-formed edit on this document",
                input.turn, input.arg
            ));
        };

        match drive_edit(
            &session.graph,
            &patch,
            seed,
            holds_cap,
            session.region_seed,
            self.policy,
        ) {
            Ok(landed) => {
                let edit = CommittedEdit {
                    actor,
                    patch: patch.clone(),
                    turn_hash: landed.receipt.turn_hash,
                    effects_hash: landed.receipt.effects_hash,
                    pre_state_hash: landed.receipt.pre_state_hash,
                    post_state_hash: landed.receipt.post_state_hash,
                    doc_commitment: landed.doc_commitment,
                };
                session.history.commit(patch);
                session.graph = landed.graph;
                session.edits.push(edit);
                Outcome::Landed {
                    receipt: landed.receipt,
                    // A document is never "ended" — it is a living object.
                    ended: false,
                }
            }
            Err(Refusal(why)) => Outcome::Refused(why),
        }
    }

    /// **Re-verify the document's whole edit chain by RE-DRIVING it.** See
    /// [`RecordVerify::verify_record`] — [`Offering::verify`] is that, over the
    /// session's own authentic record.
    fn verify(&self, session: &DocSession) -> VerifyReport {
        self.verify_record(session, &session.record())
    }

    /// The document's surface: title, text (conflicts legible), the live cells with
    /// their authors, the roster, the verified-turn count + the real commitment, and
    /// the edit affordances as a cap-gated [`ViewNode::Menu`].
    fn render(&self, session: &DocSession) -> Surface {
        self.render_for(session, None)
    }

    /// A landed edit costs `edit_credits` run-credits; a **resolution is free**
    /// (settling a conflict is never taxed). The substrate turn itself is always
    /// free and verifiable — the credit prices the hosted document service.
    fn price(&self, input: &Action) -> RunCost {
        match input.turn.as_str() {
            TURN_RESOLVE_TITLE | TURN_ORDER_CONFLICT => RunCost::free(),
            _ => RunCost::credits(self.edit_credits),
        }
    }
}

/// **The frontend-facing tamper-verify seam.** A frontend holds a [`DocRecord`]
/// (the edit chain) which it may serialize, transmit, and receive back FORGED. It
/// cannot reach the session's authentic identity — the private region seed and the
/// roster (who actually holds the edit cap) — so it cannot re-check the record
/// itself. This seam does: the record supplies only the EDITS; the authentic
/// identity comes from the `session`.
impl RecordVerify for DocOffering {
    type Session = DocSession;
    type Record = DocRecord;

    /// Export the session's authentic record — the edit chain + the final
    /// commitment. No private world identity leaves the offering.
    fn export_record(&self, session: &DocSession) -> DocRecord {
        session.record()
    }

    /// **Re-drive the recorded chain from genesis through the REAL executor.**
    ///
    /// Starting from an empty document under the session's authentic region seed,
    /// each recorded edit is re-driven as its recorded actor (the roster — NOT the
    /// record — decides whether that actor's cell holds the edit cap, so a forger
    /// cannot promote themselves), through the SAME two gates a live edit passes.
    /// The re-drive must reproduce, at every step:
    ///
    /// - that the edit still LANDS (a recorded edit that no longer lands — an
    ///   unauthorized actor, a conflicting patch, a spliced/reordered edit — breaks);
    /// - the turn's deterministic core: `turn_hash`, `effects_hash`, and the pre/post
    ///   ledger state roots (a forged patch changes the atom ids → the effects → the
    ///   turn);
    /// - the DOCUMENT's commitment after the edit (the real region-cell state
    ///   commitment);
    ///
    /// and finally the whole document must reproduce (the fold of the re-driven
    /// history equals the record's final commitment). The document reproduces from
    /// its edits, or the report is broken.
    fn verify_record(&self, session: &DocSession, record: &DocRecord) -> VerifyReport {
        let n = record.edits.len();
        let mut graph = DocGraph::new();
        // The commitment the chain stands at: genesis, then each edit's own
        // executor-WRITTEN commitment as it is re-driven.
        let mut commitment = genesis_commitment(session.region_seed);

        for (i, edit) in record.edits.iter().enumerate() {
            // The AUTHENTIC identity: the session's roster decides the cell + cap.
            let (seed, holds_cap) = session.actor_cell(&edit.actor);
            // The patch's author must be the actor's own editor cell — a patch
            // attributed to someone else's cell is a forged provenance.
            if edit.patch.author != Author(seed as u64) {
                return VerifyReport::broken(
                    i,
                    format!(
                        "edit #{i}: the recorded patch is authored by cell {} but the actor's cell \
                         is {seed} — forged provenance",
                        edit.patch.author.0
                    ),
                );
            }
            match drive_edit(
                &graph,
                &edit.patch,
                seed,
                holds_cap,
                session.region_seed,
                self.policy,
            ) {
                Ok(landed) => {
                    if landed.receipt.turn_hash != edit.turn_hash {
                        return VerifyReport::broken(
                            i,
                            format!("edit #{i}: the re-driven turn hash does not match the record"),
                        );
                    }
                    if landed.receipt.effects_hash != edit.effects_hash {
                        return VerifyReport::broken(
                            i,
                            format!("edit #{i}: the re-driven effects hash does not match"),
                        );
                    }
                    if landed.receipt.pre_state_hash != edit.pre_state_hash
                        || landed.receipt.post_state_hash != edit.post_state_hash
                    {
                        return VerifyReport::broken(
                            i,
                            format!("edit #{i}: the re-driven state roots do not match"),
                        );
                    }
                    if landed.doc_commitment != edit.doc_commitment {
                        return VerifyReport::broken(
                            i,
                            format!(
                                "edit #{i}: the re-driven document commitment does not match the \
                                 record"
                            ),
                        );
                    }
                    graph = landed.graph;
                    commitment = landed.doc_commitment;
                }
                Err(Refusal(why)) => {
                    return VerifyReport::broken(i, format!("edit #{i} does not re-drive: {why}"));
                }
            }
        }

        if commitment != record.commitment {
            let text: String = content(&graph)
                .to_marked_string()
                .chars()
                .take(60)
                .collect();
            return VerifyReport::broken(
                n,
                format!(
                    "the document the recorded edits re-drive (\"{text}\") does not reproduce the \
                     recorded commitment"
                ),
            );
        }
        VerifyReport::ok(n)
    }
}

/// A short hex handle for a 32-byte root (the surface's commitment line).
fn hex8(h: &[u8; 32]) -> String {
    h.iter().take(4).map(|b| format!("{b:02x}")).collect()
}
