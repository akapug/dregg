//! Adversarial tests against distributed GC (Lean `CapTPGC` / B4): the
//! Byzantine-resistance claim is "a DropRef from the wrong session cannot
//! decrement another holder's refcount" (no premature reclaim). We attack it.
//!
//! Adversary model: a "Byzantine peer / capability holder" who tries to force a
//! premature revoke of someone else's still-held capability (a confused-deputy
//! revocation / denial of capability).

use dregg_captp::gc::{DropResult, ExportGcManager};
use dregg_cell::CellId;
use dregg_types::FederationId;

fn cell() -> CellId {
    CellId([1; 32])
}
fn fed_a() -> FederationId {
    FederationId([0xa; 32])
}
fn fed_b() -> FederationId {
    FederationId([0xb; 32])
}

// ===========================================================================
// ATTACK 1 — Byzantine B drops A's ref on B's own session (B4 core).
// Lean claims: rejected; A's count unchanged.
// ===========================================================================

#[test]
fn attack_byzantine_wrong_session_drop_is_noop() {
    let mut mgr = ExportGcManager::new();
    mgr.record_export_with_session(cell(), fed_a(), 100, 10); // A on session 10
    mgr.record_export_with_session(cell(), fed_b(), 100, 20); // B on session 20
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 2);

    // Byzantine: claim to be A but present B's session id.
    let r = mgr.process_drop_with_session(cell(), fed_a(), 20);
    assert_eq!(r, DropResult::Invalid);
    // EVIDENCE: A's ref survived; no premature reclaim.
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 2);
    eprintln!("[GC ATTACK 1] wrong-session drop: DEFENDED");
}

// ===========================================================================
// ATTACK 2 — FINDING: the LEGACY unauthenticated `process_drop` path bypasses
// the session check entirely. Any caller who knows (cell_id, victim_federation)
// can decrement the victim's ref and, at count 0, force CanRevoke — a premature
// reclaim of a still-wanted capability. The session-Byzantine theorem only
// holds for callers that go through `process_drop_with_session`; the legacy
// entry point is an open door.
// ===========================================================================

#[test]
fn finding_legacy_process_drop_bypasses_session_byzantine_defense() {
    let mut mgr = ExportGcManager::new();
    // Honest A holds ONE ref under session 10. A still wants it.
    mgr.record_export_with_session(cell(), fed_a(), 100, 10);
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 1);

    // Attacker who never held the ref calls the SESSION-FREE drop with A's id.
    // No session is presented, so the Byzantine check cannot fire.
    let r = mgr.process_drop(cell(), fed_a());

    // FINDING: the drop is accepted and the export is reclaimed out from under A.
    assert_eq!(
        r,
        DropResult::CanRevoke,
        "if this is now Invalid, the legacy bypass was closed"
    );
    assert!(
        mgr.get(&cell()).is_none() || mgr.get(&cell()).unwrap().total_refs == 0,
        "victim's capability was prematurely reclaimed"
    );
    eprintln!("[GC ATTACK 2 / FINDING] legacy process_drop bypasses session defense: BROKEN");
}

// ===========================================================================
// ATTACK 3 — FINDING (subtle): session id is per-(cell, federation), NOT
// per-ref. A re-export to the same federation on a NEW session SUPERSEDES the
// session id of ALL that federation's existing refs (gc.rs:139). So if an
// adversary can induce a re-export under a session id they know (or if a holder
// reconnects), a subsequent wrong-original-session protection is lost: the
// "old session can no longer drop" while "new session can drop everything,
// including refs minted under the old session." We demonstrate the supersede.
// ===========================================================================

#[test]
fn finding_reexport_supersedes_session_for_all_existing_refs() {
    let mut mgr = ExportGcManager::new();
    // A acquires 2 refs under the original session 10.
    mgr.record_export_with_session(cell(), fed_a(), 100, 10);
    mgr.record_export_with_session(cell(), fed_a(), 100, 10);
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 2);

    // A re-exports / reconnects under a DIFFERENT session 99. This bumps count
    // to 3 AND rewrites session_id := 99 for the whole holder entry.
    mgr.record_export_with_session(cell(), fed_a(), 101, 99);
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 3);

    // The ORIGINAL session (10) can now no longer drop ANY of A's refs — even
    // the two that were minted under session 10. Their session was overwritten.
    let r_old = mgr.process_drop_with_session(cell(), fed_a(), 10);
    assert_eq!(
        r_old,
        DropResult::Invalid,
        "session 10 drop rejected because re-export rewrote the holder session to 99"
    );

    // Conversely, the NEW session can drop refs it never legitimately minted
    // (the two pre-existing ones), because session is holder-scoped not ref-scoped.
    let r_new = mgr.process_drop_with_session(cell(), fed_a(), 99);
    assert_eq!(r_new, DropResult::StillHeld);
    eprintln!(
        "[GC ATTACK 3 / FINDING] session is holder-scoped, not ref-scoped; re-export rewrites it: BROKEN-ish"
    );
}

// ===========================================================================
// ATTACK 4 — over-drop / underflow probe: drop more times than held.
// Lean claims counts never go negative (u64 saturating semantics matter).
// ===========================================================================

#[test]
fn attack_overdrop_does_not_underflow_or_overrevoke() {
    let mut mgr = ExportGcManager::new();
    mgr.record_export_with_session(cell(), fed_a(), 100, 10);
    // First drop is legitimate -> CanRevoke (count hits 0, holder removed).
    assert_eq!(mgr.process_drop_with_session(cell(), fed_a(), 10), DropResult::CanRevoke);
    // Second drop: holder gone -> Invalid (NOT an underflow panic, NOT a re-revoke).
    let r = mgr.process_drop_with_session(cell(), fed_a(), 10);
    assert_eq!(r, DropResult::Invalid);
    eprintln!("[GC ATTACK 4] over-drop: DEFENDED (no underflow)");
}
