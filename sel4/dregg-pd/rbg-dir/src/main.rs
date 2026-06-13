//! M2 — the Robigalia-personality heart, booting on seL4.
//!
//! This protection domain brings a real slice of `rbg/`'s userspace primitives
//! up as an seL4 component: a `DirectoryCell` (a versioned capability-list with
//! CAS `swap`, a membership ACL, and provenance) and the
//! `DirectoryFactory → seL4_Untyped_Retype` slot-caveat check mapped in
//! `../../RBG-TO-SEL4.md`.
//!
//! `rbg/src/{directory,factory}.rs` is the design heritage; it is `std`-bound
//! (`std::collections`, `dregg-cell`). This PD ports those *ideas* faithfully
//! onto `no_std` + `alloc` so they actually boot — the c-list, the versioned
//! CAS, the membership-bounded discovery, the factory slot-caveat. It is the
//! first rung where an rbg *idea* runs as a real seL4 *userspace component*.

#![no_std]
#![no_main]

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use sel4_microkit::{debug_println, protection_domain, Handler, Infallible};

// ── rbg DirectoryCell, no_std port (rbg/src/directory.rs) ───────────────────

/// A member of a directory's ACL — identified by a public-key hash, exactly as
/// `rbg::directory::MemberId`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct MemberId([u8; 32]);

/// A `dregg://` sturdy reference — the directory-entry payload pointing at a
/// capability (federation + cell + swiss number), as `rbg::directory::SturdyRef`.
#[derive(Clone)]
struct SturdyRef {
    cell: [u8; 32],
    swiss: [u8; 32],
}

/// What a directory entry represents (`rbg::directory::EntryKind`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum EntryKind {
    Service,
    SubDirectory,
    Factory,
    Capability,
}

/// A versioned directory entry (`rbg::directory::DirectoryEntry`). Every
/// mutation increments `version` — the CAS / cell-nonce discipline.
#[derive(Clone)]
struct DirectoryEntry {
    sturdy_ref: SturdyRef,
    version: u64,
    kind: EntryKind,
    /// Provenance: which member registered/last-updated this entry.
    registered_by: MemberId,
}

#[derive(Debug, PartialEq, Eq)]
enum DirectoryError {
    /// Caller is not in the directory's membership ACL.
    NotAMember,
    /// CAS failed: the expected version did not match the live version.
    VersionMismatch,
    NotFound,
}

/// The c-list itself: a name→entry map with a membership ACL and a monotonic
/// directory version. This is the seL4-userspace embodiment of an rbg
/// `DirectoryCell`; in the full port the name→slot index sits in userspace and
/// the entries are caps in a real seL4 CNode (`../../RBG-TO-SEL4.md`).
struct DirectoryCell {
    entries: BTreeMap<String, DirectoryEntry>,
    members: Vec<MemberId>,
    /// Monotonic version bumped on every successful mutation (the cell nonce).
    version: u64,
}

impl DirectoryCell {
    fn new(owner: MemberId) -> Self {
        let mut members = Vec::new();
        members.push(owner);
        DirectoryCell { entries: BTreeMap::new(), members, version: 0 }
    }

    fn is_member(&self, m: &MemberId) -> bool {
        self.members.iter().any(|x| x == m)
    }

    fn add_member(&mut self, m: MemberId) {
        if !self.is_member(&m) {
            self.members.push(m);
        }
    }

    /// Resolve a name to its entry — membership-gated discovery (the
    /// ScopedIntentPool property: you can only see inside a directory you
    /// belong to).
    fn get(&self, caller: MemberId, name: &str) -> Result<&DirectoryEntry, DirectoryError> {
        if !self.is_member(&caller) {
            return Err(DirectoryError::NotAMember);
        }
        self.entries.get(name).ok_or(DirectoryError::NotFound)
    }

    /// Atomic compare-and-swap register/update (`rbg::DirectoryCell::swap`).
    /// `expected_version` must match the live entry (or be 0 for a fresh name);
    /// on success the entry and directory versions both advance.
    fn swap(
        &mut self,
        caller: MemberId,
        name: &str,
        expected_version: u64,
        sturdy_ref: SturdyRef,
        kind: EntryKind,
    ) -> Result<u64, DirectoryError> {
        if !self.is_member(&caller) {
            return Err(DirectoryError::NotAMember);
        }
        let live = self.entries.get(name).map(|e| e.version).unwrap_or(0);
        if live != expected_version {
            return Err(DirectoryError::VersionMismatch);
        }
        let new_version = live + 1;
        self.entries.insert(
            name.to_string(),
            DirectoryEntry { sturdy_ref, version: new_version, kind, registered_by: caller },
        );
        self.version += 1;
        Ok(new_version)
    }

    fn len(&self) -> usize {
        self.entries.len()
    }
}

// ── rbg DirectoryFactory slot-caveat (rbg/src/factory.rs) ───────────────────
//
// The factory may ONLY mint objects of its declared shape. On seL4 this becomes
// `seL4_Untyped_Retype(untyped, declared_type, ...)`: the factory PD holds one
// Untyped cap + a retype template, and physically cannot mint anything but the
// declared type. Here we model the slot-caveat CHECK that the retype must pass
// (the kernel invocation itself is the next port; this is the userspace half of
// the caveat — the same predicate the factory descriptor carries on-ledger).

/// The shape a `DirectoryFactory` is permitted to mint — the
/// `FactoryDescriptor` slot-caveat (`rbg::factory::directory_factory_descriptor`).
struct RetypeTemplate {
    /// Only this object type may be retyped (maps to seL4's object type id).
    declared_object_type: u32,
    /// The factory's verification key, binding minted children to this factory.
    factory_vk: [u8; 32],
}

/// The seL4-object-type id a directory c-list maps to (a CNode — the kernel
/// capability table that backs the directory's c-list, `../../RBG-TO-SEL4.md`).
const SEL4_OBJECT_TYPE_CNODE: u32 = 10;

impl RetypeTemplate {
    /// The slot-caveat: a retype request is admissible iff it asks for exactly
    /// the declared type. This is the predicate that, on the kernel side,
    /// `seL4_Untyped_Retype` enforces by construction — the factory cannot mint
    /// a frame, an endpoint, or anything but the one declared shape.
    fn admits(&self, requested_object_type: u32) -> bool {
        requested_object_type == self.declared_object_type
    }
}

// ── The PD entry: exercise the primitives, print the verdicts ───────────────

#[protection_domain(heap_size = 0x10000)]
fn init() -> HandlerImpl {
    debug_println!("[m2] rbg DirectoryCell PD booted — the Robigalia heart");

    let owner = MemberId([0x01; 32]);
    let alice = MemberId([0x0a; 32]);
    let mallory = MemberId([0xff; 32]);

    let mut dir = DirectoryCell::new(owner);
    dir.add_member(alice);

    // 1. Owner registers a service entry (CAS from version 0).
    let svc = SturdyRef { cell: [0x11; 32], swiss: [0x22; 32] };
    match dir.swap(owner, "billing-service", 0, svc.clone(), EntryKind::Service) {
        Ok(v) => debug_println!("[m2] register 'billing-service' -> entry version {}", v),
        Err(_) => debug_println!("[m2] FAIL: register rejected"),
    }

    // 2. Alice (a member) resolves it — membership-gated discovery succeeds.
    match dir.get(alice, "billing-service") {
        Ok(e) => debug_println!(
            "[m2] member alice resolves 'billing-service' (kind=service, v={})",
            e.version
        ),
        Err(_) => debug_println!("[m2] FAIL: member resolve rejected"),
    }

    // 3. Mallory (NOT a member) is refused — the scope bound holds.
    match dir.get(mallory, "billing-service") {
        Err(DirectoryError::NotAMember) => {
            debug_println!("[m2] non-member mallory REFUSED (scope bound enforced) ✓")
        }
        _ => debug_println!("[m2] FAIL: non-member was not refused!"),
    }

    // 4. A stale CAS (wrong expected version) is rejected — no lost updates.
    match dir.swap(owner, "billing-service", 0, svc, EntryKind::Service) {
        Err(DirectoryError::VersionMismatch) => {
            debug_println!("[m2] stale CAS (expected v0, live v1) REJECTED ✓")
        }
        _ => debug_println!("[m2] FAIL: stale CAS was not rejected!"),
    }

    // 5. The DirectoryFactory slot-caveat: a retype to the declared CNode type
    //    is admitted; a retype to any other type is refused.
    let template =
        RetypeTemplate { declared_object_type: SEL4_OBJECT_TYPE_CNODE, factory_vk: [0x77; 32] };
    let _ = template.factory_vk; // bound into minted children in the full port
    if template.admits(SEL4_OBJECT_TYPE_CNODE) && !template.admits(/* Frame */ 1) {
        debug_println!("[m2] factory slot-caveat: mints CNode (c-list) ONLY ✓");
        debug_println!("[m2]   → maps to seL4_Untyped_Retype(untyped, CNode, ..)");
    } else {
        debug_println!("[m2] FAIL: factory slot-caveat not enforced");
    }

    debug_println!("[m2] directory holds {} entry(s); rbg heritage is alive on seL4", dir.len());
    HandlerImpl
}

struct HandlerImpl;

impl Handler for HandlerImpl {
    type Error = Infallible;
}
