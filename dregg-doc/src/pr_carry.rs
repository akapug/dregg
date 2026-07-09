//! **The federated forge-grain: a pull request carried ACROSS the membrane.**
//!
//! [`crate::pull_request`] builds a [`PullRequest`] that opens, reviews, and lands
//! IN ONE PROCESS. This module makes a PR **portable**, so a PR cut on one instance
//! can be reviewed + landed on ANOTHER — the forge's named next slice (the
//! "federated forge-grain" seam in the `pull_request` module docs).
//!
//! It MIRRORS the proven card-fork carry (`starbridge-v2::card_carry_bridge` +
//! `starbridge-v2::distributed_card`): a PR is a *fork* (a `head` offered against a
//! `base` that share a merge base then diverge), exactly like a co-driven card is a
//! fork of a shared card. So it crosses the same way a card-fork does — sealed to a
//! canonical-byte payload with a domain-separated **anti-substitution root** tooth,
//! carried over a wire, re-opened fail-closed on the far side, and re-targeted onto
//! the receiver's own base.
//!
//! ## What crosses (and what does not)
//!
//! A PR's `base` is the *target branch* — the receiver already has it (or re-targets
//! onto their own). So the carry does NOT ship the base. What crosses is the **diff +
//! the review**:
//!
//! - **the head-suffix** — the head's patches past the merge base ([`PullRequest::divergence`]'s
//!   second half): the exact patch set the PR proposes to land, each keeping its own
//!   author/identity (no squash). This is the twin of the card carry's
//!   `driven_view_source`.
//! - **the review set** — the resolution patches accumulated on the PR
//!   ([`PullRequest::resolutions`]): review-as-stitcher, carried so the far side sees
//!   the same settled conflicts.
//! - **the merge-base anchor** — the *patch-id chain* of the shared ancestor the
//!   head-suffix was cut from. This is an IDENTITY, not the base content (no ops, no
//!   text) — the twin of the card carry's seed identity. It lets [`open_pull_request`]
//!   verify the receiver's local base is a **compatible** re-target target and refuse
//!   a skewed one ([`CarryError::BaseSkew`]) rather than silently graft the diff onto
//!   an unrelated history.
//!
//! ## The anti-substitution root (mirrors `fork_root`)
//!
//! [`PrEnvelope::pr_root`] is a domain-separated blake3 over EXACTLY the carried
//! payload (the anchor ids + the head-suffix bytes + the review bytes), the same
//! shape as [`distributed_card::CardForkEnvelope::fork_root`]. [`open_pull_request`]
//! re-derives it from the decoded payload and REFUSES a mismatch
//! ([`CarryError::RootMismatch`]) before a byte is trusted: a carry whose patches were
//! tampered while the root was left stale, or whose head-suffix was swapped, cannot
//! pass — exactly the anti-substitution tooth `open_envelope` fires.
//!
//! ## Honest scope: integrity here, sender-auth is the transport's
//!
//! As the card-carry review found, this tooth is **integrity, not authenticity**. It
//! binds the carried bytes to the carried root — it does NOT prove WHO put the PR on
//! the wire (a consistent forge that recomputes a matching root is admitted by the
//! tooth and caught by transport auth). Authenticity is delegated to the Matrix
//! TRANSPORT (matrix-sdk device/room keys authenticate the sender), exactly as in the
//! card carry. This module carries that honest scope forward unchanged.
//!
//! ## The wire seam (named, not built here)
//!
//! `dregg-doc` is a standalone workspace with no `deos-matrix` dependency, so it
//! cannot import [`deos_matrix::MembraneEnvelope`]. The faithful carry envelope is
//! defined HERE ([`PrEnvelope`] with [`PrEnvelope::to_wire_bytes`] /
//! [`PrEnvelope::from_wire_bytes`]), and the wire seam is: wrap
//! `(to_wire_bytes(), pr_root)` into a `deos_matrix::MembraneEnvelope` under a
//! `dregg://pull-request/` sturdyref (a `pr_carry_membrane` / `as_pr_carry` pair in
//! `deos-matrix`, the exact twin of `card_fork_membrane` / `as_card_fork_carry`), and
//! ride it over a Matrix room via `MatrixClient::send_membrane`. Only that room
//! transport is out-of-crate; the carried payload + the tooth are REAL and re-fire
//! here.

use crate::atom::PatchId;
use crate::doc_heap::{patches_from_bytes, patches_to_bytes};
use crate::history::History;
use crate::patch::Patch;
use crate::pull_request::PullRequest;

/// Domain/version tag heading the anti-substitution root preimage (the tooth's
/// domain separation, mirroring the card carry's
/// `b"deos-distributed-card-fork-root-v1"`).
const PR_ROOT_DOMAIN: &[u8] = b"dregg-doc-pull-request-carry-root-v1";

/// Domain/version tag heading the serialized wire payload.
const PR_WIRE_DOMAIN: &[u8] = b"dregg-doc/pull-request-carry/v1";

/// **A pull request made portable — the PR crossing an instance boundary.**
///
/// The twin of [`distributed_card::CardForkEnvelope`]. It carries the diff + the
/// review + the merge-base anchor (see the module docs), plus the anti-substitution
/// [`PrEnvelope::pr_root`] over exactly those fields.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrEnvelope {
    /// The merge-base anchor: the patch-id chain of the shared ancestor the
    /// head-suffix was cut from. NOT the base content — just its identity, so the
    /// receiver can verify their local base is a compatible re-target (no silent
    /// skew). The twin of the card carry's carried seed identity.
    merge_base_ids: Vec<u128>,
    /// The carried DIFF: the head's patches past the merge base — the set the PR
    /// proposes to land, each keeping its own author. The twin of the card carry's
    /// `driven_view_source`.
    head_suffix: Vec<Patch>,
    /// The carried REVIEW: the resolution patches accumulated on the PR
    /// (review-as-stitcher), so the far side sees the same settled conflicts.
    resolutions: Vec<Patch>,
    /// The anti-substitution root — a domain-separated blake3 over the carried
    /// payload (anchor ids + head-suffix + review). Mirrors `fork_root`: a
    /// tampered/substituted carry that leaves this stale is refused at
    /// [`open_pull_request`] ([`CarryError::RootMismatch`]).
    pr_root: [u8; 32],
}

impl PrEnvelope {
    /// Build a portable envelope from a live [`PullRequest`] (its head-suffix, its
    /// review set, and the merge-base anchor) — the originator's send half, via
    /// [`seal_pull_request`].
    pub fn of(pr: &PullRequest) -> Self {
        let merge_base_ids: Vec<u128> =
            pr.merge_base().patches().iter().map(|p| p.id().0).collect();
        let (_, head_suffix) = pr.divergence();
        let head_suffix = head_suffix.to_vec();
        let resolutions = pr.resolutions().to_vec();
        let pr_root = Self::compute_root(&merge_base_ids, &head_suffix, &resolutions);
        PrEnvelope {
            merge_base_ids,
            head_suffix,
            resolutions,
            pr_root,
        }
    }

    /// **The PR carry root — the anti-substitution tooth.** A domain-separated
    /// blake3 over EXACTLY the carried fields (the anchor ids, the head-suffix's
    /// canonical bytes, and the review's canonical bytes), mirroring
    /// [`distributed_card::CardForkEnvelope::fork_root`]. Every variable-length run
    /// is length-prefixed (no concat ambiguity), so a substituted or tampered carry
    /// is refused before a single byte is trusted.
    fn compute_root(
        merge_base_ids: &[u128],
        head_suffix: &[Patch],
        resolutions: &[Patch],
    ) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(PR_ROOT_DOMAIN);
        h.update(&(merge_base_ids.len() as u64).to_le_bytes());
        for id in merge_base_ids {
            h.update(&id.to_le_bytes());
        }
        let head_bytes = patches_to_bytes(head_suffix);
        h.update(&(head_bytes.len() as u64).to_le_bytes());
        h.update(&head_bytes);
        let review_bytes = patches_to_bytes(resolutions);
        h.update(&(review_bytes.len() as u64).to_le_bytes());
        h.update(&review_bytes);
        *h.finalize().as_bytes()
    }

    /// The claimed anti-substitution root (the tooth input the receiver re-checks).
    pub fn pr_root(&self) -> [u8; 32] {
        self.pr_root
    }

    /// The carried head-suffix (the proposed landing diff).
    pub fn head_suffix(&self) -> &[Patch] {
        &self.head_suffix
    }

    /// The carried review set (the resolution patches).
    pub fn resolutions(&self) -> &[Patch] {
        &self.resolutions
    }

    /// Serialize the envelope for the wire — a canonical, length-prefixed,
    /// domain-tagged byte payload (the twin of
    /// [`distributed_card::CardForkEnvelope::to_snapshot_bytes`]). These are the
    /// bytes that ride a `deos_matrix::MembraneEnvelope`'s snapshot field over the
    /// homeserver wire (the named seam).
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        enc_run(&mut out, PR_WIRE_DOMAIN);
        out.extend_from_slice(&(self.merge_base_ids.len() as u64).to_le_bytes());
        for id in &self.merge_base_ids {
            out.extend_from_slice(&id.to_le_bytes());
        }
        enc_run(&mut out, &patches_to_bytes(&self.head_suffix));
        enc_run(&mut out, &patches_to_bytes(&self.resolutions));
        out.extend_from_slice(&self.pr_root);
        out
    }

    /// Deserialize an envelope from wire bytes, fail-closed. `None` on a wrong
    /// domain tag, truncation, a malformed patch list, or trailing garbage — an
    /// untrusted carry byte is refused, never coerced (the twin of
    /// [`distributed_card::CardForkEnvelope::from_snapshot_bytes`]).
    ///
    /// This decode does NOT verify the tooth — it only recovers the two tooth
    /// inputs. [`open_pull_request`] re-derives the root and refuses a mismatch.
    pub fn from_wire_bytes(bytes: &[u8]) -> Option<PrEnvelope> {
        let mut d = Cursor { bytes, at: 0 };
        if d.run()? != PR_WIRE_DOMAIN {
            return None;
        }
        let n_ids = d.u64()? as usize;
        let mut merge_base_ids = Vec::with_capacity(n_ids);
        for _ in 0..n_ids {
            merge_base_ids.push(d.u128()?);
        }
        let head_suffix = patches_from_bytes(d.run()?)?;
        let resolutions = patches_from_bytes(d.run()?)?;
        let mut pr_root = [0u8; 32];
        pr_root.copy_from_slice(d.take(32)?);
        if d.at != bytes.len() {
            return None; // trailing garbage
        }
        Some(PrEnvelope {
            merge_base_ids,
            head_suffix,
            resolutions,
            pr_root,
        })
    }
}

/// **A principal seals its pull request for carry across the boundary.** Returns
/// the portable [`PrEnvelope`] (its bytes ride the wire, its [`PrEnvelope::pr_root`]
/// is the anti-substitution tooth the receiver re-checks). The twin of
/// [`distributed_card::seal_fork`].
pub fn seal_pull_request(pr: &PullRequest) -> PrEnvelope {
    PrEnvelope::of(pr)
}

/// **A receiver opens a carried pull request, fail-closed, and re-targets it onto
/// its OWN local base.** The twin of
/// [`distributed_card::open_envelope`] + `rehydrate_fork`.
///
/// The three fail-closed / re-target steps:
///
/// 1. **The tooth fires.** Re-derive [`PrEnvelope::pr_root`] from the decoded
///    payload; a mismatch is [`CarryError::RootMismatch`] (a tampered/substituted
///    carry is refused before it is trusted).
/// 2. **Anti-skew.** The receiver's `local_base` MUST contain the carried
///    merge-base anchor as a prefix (its first patches' ids equal the carried
///    chain). If it does not, the head-suffix was cut from an ancestor `local_base`
///    does not share — grafting it would silently skew, so it is refused
///    ([`CarryError::BaseSkew`]). A base that EXTENDS the anchor (the original base,
///    or a moved-but-compatible one) passes: the PR re-targets onto it.
/// 3. **Re-target + reconstruct.** The head-suffix is replayed onto `local_base`
///    (the new head = `local_base` then the carried patches), the PR is
///    [`PullRequest::open`]ed against `local_base`, and the carried review set is
///    reconstructed via [`PullRequest::resolve_with`]. The PR is now open against
///    THEIR base — the receiver reviews + `land`s it locally through their OWN
///    executor (cap-gated: a receiver without the base region's edit cap is refused
///    in-band with `CapabilityNotHeld`, exactly as an in-process land).
pub fn open_pull_request(env: &PrEnvelope, local_base: History) -> Result<PullRequest, CarryError> {
    // (1) THE TOOTH: the decoded payload MUST reproduce the claimed root.
    let derived = PrEnvelope::compute_root(&env.merge_base_ids, &env.head_suffix, &env.resolutions);
    if derived != env.pr_root {
        return Err(CarryError::RootMismatch);
    }
    // (2) ANTI-SKEW: local_base must extend the carried merge-base anchor.
    let base_patches = local_base.patches();
    if base_patches.len() < env.merge_base_ids.len() {
        return Err(CarryError::BaseSkew);
    }
    for (i, id) in env.merge_base_ids.iter().enumerate() {
        if base_patches[i].id() != PatchId(*id) {
            return Err(CarryError::BaseSkew);
        }
    }
    // (3) RE-TARGET: replay the head-suffix onto local_base, reconstruct the review.
    let mut head = local_base.branch();
    for p in &env.head_suffix {
        head.commit(p.clone());
    }
    let mut pr = PullRequest::open(local_base, head);
    for p in &env.resolutions {
        pr.resolve_with(p.clone());
    }
    Ok(pr)
}

/// **Open a carried PR straight off the wire, fail-closed** — the receiver's
/// primary entry (the twin of `open_card_fork_from_membrane`). Decodes the wire
/// bytes ([`PrEnvelope::from_wire_bytes`], refusing malformed bytes with
/// [`CarryError::MalformedCarry`]) and hands the decoded envelope to
/// [`open_pull_request`], where the tooth + anti-skew gates fire. In the deployed
/// forge these bytes arrive off a `deos_matrix::MembraneEnvelope`'s snapshot field
/// (the named wire seam).
pub fn open_pull_request_wire(wire: &[u8], local_base: History) -> Result<PullRequest, CarryError> {
    let env = PrEnvelope::from_wire_bytes(wire).ok_or(CarryError::MalformedCarry)?;
    open_pull_request(&env, local_base)
}

/// Errors the PR carry raises (the fail-closed paths — mirroring
/// [`distributed_card::DistributedCardError`]). `Display`/`Error` are hand-written
/// (no macro dep), matching the crate's carry discipline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CarryError {
    /// The wire bytes did not deserialize into an envelope (corrupt/truncated
    /// payload, unknown op tag, or trailing garbage) — fail-closed.
    MalformedCarry,
    /// The decoded envelope did not reproduce the claimed root — the
    /// anti-substitution tooth fired (refuse before trusting one byte).
    RootMismatch,
    /// The receiver's local base does not contain the carried merge-base anchor as
    /// a prefix: the head-suffix was cut from an ancestor this base does not share,
    /// so grafting it would silently skew. Re-target onto a compatible base (one
    /// that extends the anchor) instead.
    BaseSkew,
}

impl std::fmt::Display for CarryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CarryError::MalformedCarry => {
                write!(f, "pull-request carry is malformed (not a valid envelope)")
            }
            CarryError::RootMismatch => write!(
                f,
                "pull-request carry root mismatch — refusing to open a substituted PR envelope"
            ),
            CarryError::BaseSkew => write!(
                f,
                "the receiver's base does not extend the carried merge-base anchor (re-target skew refused)"
            ),
        }
    }
}

impl std::error::Error for CarryError {}

/// Append a length-prefixed byte run (the same framing the history codec uses).
fn enc_run(out: &mut Vec<u8>, b: &[u8]) {
    out.extend_from_slice(&(b.len() as u64).to_le_bytes());
    out.extend_from_slice(b);
}

/// A strict little-endian cursor over untrusted wire bytes: every read is
/// bounds-checked and any shortfall is `None`.
struct Cursor<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Cursor<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.at.checked_add(n)?;
        if end > self.bytes.len() {
            return None;
        }
        let s = &self.bytes[self.at..end];
        self.at = end;
        Some(s)
    }
    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().ok()?))
    }
    fn u128(&mut self) -> Option<u128> {
        Some(u128::from_le_bytes(self.take(16)?.try_into().ok()?))
    }
    fn run(&mut self) -> Option<&'a [u8]> {
        let n = self.u64()? as usize;
        self.take(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::{AtomId, Author};
    use crate::content::content;
    use crate::patch::Op;

    /// The same shared two-atom history the in-process PR tests use ("one\n" then
    /// "two\n"), returning it plus the two atom ids.
    fn shared_history() -> (History, AtomId, AtomId) {
        let mut h = History::new();
        let (s1, op1) = Patch::add(1, "one\n", AtomId::ROOT);
        let (s2, op2) = Patch::add(2, "two\n", s1);
        h.commit(Patch::by(Author(0), [op1]));
        h.commit(Patch::by(Author(0), [op2]));
        (h, s1, s2)
    }

    /// A clean PR: base tombstones "one\n", head appends "three\n" (the twin of the
    /// in-process `clean_pr`).
    fn clean_pr() -> PullRequest {
        let (shared, s1, s2) = shared_history();
        let mut base = shared.branch();
        base.commit(Patch::by(Author(1), [Op::Delete { id: s1 }]));
        let mut head = shared.branch();
        head.commit(Patch::by(Author(2), [Patch::add(3, "three\n", s2).1]));
        PullRequest::open(base, head)
    }

    /// A SECOND, distinct clean PR (head appends "four\n") — a different head-suffix.
    fn other_clean_pr() -> PullRequest {
        let (shared, s1, s2) = shared_history();
        let mut base = shared.branch();
        base.commit(Patch::by(Author(1), [Op::Delete { id: s1 }]));
        let mut head = shared.branch();
        head.commit(Patch::by(Author(2), [Patch::add(4, "four\n", s2).1]));
        PullRequest::open(base, head)
    }

    /// A conflicting PR: base and head each insert a different line after the same
    /// anchor — a genuine antichain (the twin of the in-process `conflicting_pr`).
    fn conflicting_pr() -> PullRequest {
        let (shared, _s1, s2) = shared_history();
        let mut base = shared.branch();
        base.commit(Patch::by(Author(1), [Patch::add(10, "alpha\n", s2).1]));
        let mut head = shared.branch();
        head.commit(Patch::by(Author(2), [Patch::add(11, "beta\n", s2).1]));
        PullRequest::open(base, head)
    }

    // ── POLE (i): ROUND-TRIP — seal, open against a matching base, same PR ────────

    #[test]
    fn round_trip_seal_open_reproduces_the_pr() {
        let pr = clean_pr();
        let env = seal_pull_request(&pr);

        // The carry survives the wire byte-intact (serialize → deserialize identity).
        let wire = env.to_wire_bytes();
        let back = PrEnvelope::from_wire_bytes(&wire).expect("the carry decodes off the wire");
        assert_eq!(env, back, "the PR carry survives the wire byte-intact");

        // Open against a MATCHING base (the same base the PR was cut against): the
        // tooth admits it and the head-suffix re-targets.
        let opened = open_pull_request(&env, pr.base().clone())
            .expect("the tooth admits the genuine carry + re-targets");

        // Same head-suffix crosses identically.
        let (_, orig_suffix) = pr.divergence();
        let (_, new_suffix) = opened.divergence();
        assert_eq!(
            orig_suffix, new_suffix,
            "the carried head-suffix crosses identically"
        );

        // Merges to the SAME graph, with the SAME landing set.
        let orig = pr.merge().expect("in-process PR merges");
        let carried = opened.merge().expect("carried PR merges");
        assert_eq!(
            carried.graph, orig.graph,
            "the rehydrated PR merges to the same graph"
        );
        assert_eq!(carried.patches, orig.patches, "the same landing set");
        assert_eq!(
            content(&carried.graph).to_marked_string(),
            "two\nthree\n",
            "both sides' edits in the merge"
        );
    }

    #[test]
    fn the_review_set_crosses_and_settles_on_the_far_side() {
        // Carry a REVIEWED PR: resolve the conflict with a keep-both order, then seal.
        let mut pr = conflicting_pr();
        let menu = pr.resolution_choices(Author(3));
        let order = menu[0]
            .choices
            .iter()
            .find(|c| c.keeps_all())
            .expect("an order (keep both) choice")
            .clone();
        pr.resolve(&order);
        assert!(pr.is_clean(), "the resolution settled it in-process");

        let env = seal_pull_request(&pr);
        assert_eq!(env.resolutions().len(), 1, "the review set is carried");

        let opened = open_pull_request(&env, pr.base().clone()).expect("the reviewed carry opens");
        assert_eq!(
            opened.resolutions().len(),
            1,
            "the review set crossed the membrane"
        );
        assert_eq!(
            opened.resolutions()[0].author,
            Author(3),
            "the resolver's authorship survives the carry"
        );
        assert!(
            opened.is_clean(),
            "the carried resolution settles the same conflict on the far side"
        );
        assert_eq!(
            opened.merge().unwrap().graph,
            pr.merge().unwrap().graph,
            "same reviewed pushout across the membrane"
        );
    }

    // ── POLE (ii): ANTI-SUBSTITUTION — a tampered carry is REFUSED ────────────────

    #[test]
    fn a_tampered_carry_is_refused_by_the_root_tooth() {
        let pr = clean_pr();
        let env = seal_pull_request(&pr);
        let base = pr.base().clone();

        // (a) FLIP the head-suffix payload while leaving the claimed root STALE — the
        //     classic forgery. The tooth sees payload↔root disagree and REFUSES.
        let mut altered = env.head_suffix().to_vec();
        altered[0].ops.push(Op::Delete { id: AtomId(0xDEAD) });
        let tampered = PrEnvelope {
            merge_base_ids: env.merge_base_ids.clone(),
            head_suffix: altered,
            resolutions: env.resolutions.clone(),
            pr_root: env.pr_root, // NOT recomputed — stale
        };
        assert!(
            matches!(
                open_pull_request(&tampered, base.clone()),
                Err(CarryError::RootMismatch)
            ),
            "a tampered head-suffix under a stale root is refused"
        );
        // …and identically when it rides the wire (from_wire_bytes recovers the two
        // tooth inputs; open re-decides acceptance).
        assert!(matches!(
            open_pull_request_wire(&tampered.to_wire_bytes(), base.clone()),
            Err(CarryError::RootMismatch)
        ));

        // (b) SWAP the head-suffix for a DIFFERENT PR's diff under the stale root.
        let other_env = seal_pull_request(&other_clean_pr());
        let swapped = PrEnvelope {
            merge_base_ids: env.merge_base_ids.clone(),
            head_suffix: other_env.head_suffix().to_vec(),
            resolutions: env.resolutions.clone(),
            pr_root: env.pr_root, // still clean_pr's root — stale for the swapped diff
        };
        assert!(matches!(
            open_pull_request(&swapped, base.clone()),
            Err(CarryError::RootMismatch)
        ));

        // (c) Malformed wire bytes are refused fail-closed (never half-trusted).
        assert!(matches!(
            open_pull_request_wire(b"\xff\x00 not a pr carry", base.clone()),
            Err(CarryError::MalformedCarry)
        ));

        // (d) The tooth is a BINDING check, not a blanket reject: the tampered payload
        //     opens against ITS OWN recomputed root (only substitution-under-stale-root
        //     fails). Proves the poles are about the binding, not a stuck-closed gate.
        let honest_root = PrEnvelope::compute_root(
            &tampered.merge_base_ids,
            &tampered.head_suffix,
            &tampered.resolutions,
        );
        let rebound = PrEnvelope {
            pr_root: honest_root,
            ..tampered.clone()
        };
        assert!(
            open_pull_request(&rebound, base).is_ok(),
            "the tooth binds payload↔root, it is not a blanket reject"
        );
    }

    // ── POLE (iv): RE-TARGET — a moved base re-targets; an alien base is refused ──

    #[test]
    fn re_target_handles_a_moved_base_and_refuses_an_alien_one() {
        let pr = clean_pr();
        let env = seal_pull_request(&pr);

        // (a) A COMPATIBLE moved base (the original base + an extra appended patch —
        //     still extends the merge-base anchor): re-targets successfully, the PR is
        //     now open against the moved base and the carried diff rides on top.
        let mut moved = pr.base().clone();
        moved.commit(Patch::by(
            Author(5),
            [Patch::add(99, "extra\n", AtomId::ROOT).1],
        ));
        let opened =
            open_pull_request(&env, moved.clone()).expect("a compatible moved base re-targets");
        assert_eq!(
            opened.base(),
            &moved,
            "the PR is re-targeted onto the receiver's own (moved) base"
        );
        assert_eq!(
            opened.divergence().1,
            env.head_suffix(),
            "the carried diff rides the moved base unchanged"
        );

        // (b) An ALIEN base (a different genesis — does NOT contain the anchor):
        //     REFUSED BaseSkew. No silent skew (the diff is never grafted onto an
        //     unrelated history).
        let mut alien = History::new();
        alien.commit(Patch::by(
            Author(6),
            [Patch::add(7, "alien\n", AtomId::ROOT).1],
        ));
        assert!(
            matches!(open_pull_request(&env, alien), Err(CarryError::BaseSkew)),
            "an incompatible base is refused, not silently skewed"
        );
    }

    // ── POLE (iii): CAP-GATED LANDING through the receiver's OWN executor ─────────

    #[cfg(feature = "substrate")]
    #[test]
    fn a_carried_pr_lands_cap_gated_with_the_same_outcome() {
        use crate::executor_drive::ExecutorDrivenDoc;
        use crate::pull_request::PullRequestError;
        use dregg_turn::{Finality, TurnError};

        let pr = clean_pr();
        let env = seal_pull_request(&pr);

        // (cap HELD) the receiver rehydrates + lands as finalized cap-gated turns,
        // reproducing the in-process MergeOutcome exactly.
        let opened = open_pull_request(&env, pr.base().clone()).expect("opens");
        let mut doc = ExecutorDrivenDoc::new_at(&opened.base().replay(), 1, 2, true);
        let receipts = opened.land(&mut doc).expect("a cap-holding receiver lands");
        assert!(!receipts.is_empty());
        for r in &receipts {
            assert_eq!(
                r.finality,
                Finality::Final,
                "each landing turn is finalized"
            );
        }
        assert_eq!(
            *doc.graph(),
            pr.merge().unwrap().graph,
            "the carried land reproduces the in-process merge"
        );
        assert_eq!(content(doc.graph()).to_marked_string(), "two\nthree\n");
        assert!(doc.commitment_matches_projection());

        // (cap NOT held) the receiver's executor refuses the first landing turn
        // in-band — the federated PR still respects the receiver's caps, nothing lands.
        let opened2 = open_pull_request(&env, pr.base().clone()).expect("opens");
        let mut capless = ExecutorDrivenDoc::new_at(&opened2.base().replay(), 1, 2, false);
        let pre = capless.state_commitment();
        match opened2.land(&mut capless) {
            Err(PullRequestError::Refused(TurnError::CapabilityNotHeld { actor, target })) => {
                assert_eq!(
                    actor,
                    capless.editor_id(),
                    "the receiver is the refused actor"
                );
                assert_eq!(
                    target,
                    capless.region_id(),
                    "the base region is the gated target"
                );
            }
            other => panic!("expected an in-band CapabilityNotHeld refusal, got {other:?}"),
        }
        assert_eq!(
            capless.state_commitment(),
            pre,
            "the federated PR respects the receiver's caps — nothing landed"
        );
    }
}
