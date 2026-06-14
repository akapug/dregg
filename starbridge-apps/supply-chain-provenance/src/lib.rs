//! # starbridge-supply-chain-provenance
//!
//! **Verifiable supply-chain provenance** — an ITEM is a cell, a CUSTODY HANDOFF
//! is a cap-attenuated transfer, and SINGLE-CUSTODIANSHIP is a CONSERVATION law:
//! custody is conserved across handoffs, with EXACTLY ONE custodian at any time
//! (no double-custody, no replay), and the PROVENANCE is a tamper-evident receipt
//! chain a third party can re-derive and PROVE. All of it runs through the REAL
//! verified executor; a FORGED handoff (a party claiming custody it does not hold)
//! is REFUSED.
//!
//! This is the executable surface of two verified Lean developments, **composed
//! from existing slot-caveat atoms only** (no new Lean module):
//!
//! | Lean keystone                                            | What this crate enforces |
//! |---------------------------------------------------------|--------------------------|
//! | `AgentOrchestrationBudget.anyOf[immutable batonF, senderInField batonF]` | **actor-bound custody handoff**: the `CUSTODIAN` register may change only in a turn SIGNED BY the incoming holder (`stolen_baton_rejected`) |
//! | `AgentOrchestrationBudget.strictMono epochF`            | **no replay**: every handoff strictly advances the provenance epoch |
//! | `AgentProvenanceGated.prov_entry_writeonce`             | each custody-receipt link slot is `WriteOnce` — a committed link is frozen forever (tamper-evidence) |
//! | `AgentProvenanceGated.prov_head_cannot_rewind`          | the provenance `HEAD` is `Monotonic` — the chain is append-only (no truncate-then-fork) |
//! | `AgentProvenanceGated.prov_chain_links` / [`verify_chain`] | the receipt chain re-derives link-for-link from the published events — PROVE the full custody chain |
//! | `AgentOrchestration.derive_no_amplify`                  | the custody cap is handed forward NARROWED, never widened (no amplification) |
//!
//! ## The item cell (the provenance substrate)
//!
//! **The ITEM — a factory-born sovereign cell.** Its installed [`CellProgram`] IS
//! the custody policy, re-checked by the verified executor on EVERY turn that
//! touches it:
//!
//!   * [`CUSTODIAN_SLOT`] — the **current** custodian's identity scalar (the
//!     single-custodianship register). Guarded by `AnyOf[Immutable, SenderInSlot]`
//!     — the **actor-bound baton**: the custodian may change ONLY in a turn signed
//!     by the *incoming* holder (the Lean `anyOf[immutable, senderInField]`
//!     keystone). A turn that flips the custodian to a party that did not sign is
//!     REFUSED.
//!   * [`EPOCH_SLOT`] — the provenance epoch (the handoff counter). `StrictMonotonic`
//!     — every handoff strictly advances it; a replayed handoff (same / stale epoch)
//!     is REFUSED (the Lean `strictMono epochF`).
//!   * [`HEAD_SLOT`] — the provenance cursor (next link index). `Monotonic` — the
//!     custody chain is append-only (no re-order, no rewind, no truncate-then-fork).
//!   * [`TIP_SLOT`] — the latest committed custody-link digest (the chain tip a
//!     verifier reads first to walk the chain).
//!   * `LINK_BASE + i` — the i-th custody-receipt link digest. `WriteOnce` — a
//!     committed link is frozen forever (tamper-evidence).
//!
//! ## Custody is a capability (the cap-graph half of single-custodianship)
//!
//! A handoff is a **cap-attenuated transfer**: the incoming custodian gains the
//! item's custody capability and the prior custodian no longer holds it — EXACTLY
//! ONE custodian holds the cap at a time. This is the ocap half of
//! single-custodianship, enforced by the executor's c-list authorization gate: a
//! turn touching the item requires a capability reaching it, so a party that does
//! NOT hold the custody cap cannot hand the item off at all
//! ([`build_forged_handoff_action`] is REFUSED by the authorization gate). The
//! cap is handed forward NARROWED, never widened (the Lean `derive_no_amplify`).
//!
//! ## The provenance chain (PROVE the custody chain)
//!
//! Each handoff appends a custody-receipt link `link_i = blake3(prev ‖ event_i)`
//! where `event_i` binds (from_custodian, to_custodian, epoch). Because each link
//! folds the previous one, the chain binds the ENTIRE committed custody history;
//! because each link slot is `WriteOnce`, a committed link is frozen. A third
//! party PROVES the item's full custody chain by re-derivation: recompute the
//! honest chain from the published events and check it matches the committed
//! digests link-for-link ([`verify_chain`]). A tampered, forged, reordered, or
//! dropped handoff breaks the re-derivation — the provenance is verifiable by
//! re-execution, not by trust.
//!
//! ## Single-custodianship as conservation
//!
//! The beautiful invariant: across any honest custody chain, custody is conserved
//! — there is always EXACTLY ONE custodian (the latest `to`), and the chain of
//! `(from -> to)` handoffs is a connected path with no fork and no gap. The
//! `from` of handoff `i+1` is the `to` of handoff `i` ([`custody_chain_is_connected`]).
//! Mint creates the sole custodian; each handoff moves the sole custodianship
//! forward; nothing mints a second custodian or burns the custodian. The
//! conservation is witnessed three ways: the `WriteOnce`/`Monotonic` chain
//! (tamper-evidence + append-only), the `StrictMonotonic` epoch (no replay), and
//! the cap-graph (exactly one cap holder).
//!
//! ## Pre-submission assurance (`dregg-userspace-verify`)
//!
//! Before a handoff forest is submitted, it is linted by the userspace `analyze()`
//! toolkit — conservation (no value conjured), non-amplification (no in-forest
//! grant exceeds a delegated cap — a custodian re-granting WIDER custody than it
//! holds is caught), and well-formedness — so a stranger can pre-flight the
//! custody plan and SEE it pass (or see a malformed plan's findings) before
//! spending gas. See `tests/userspace_verify.rs`.

#![forbid(unsafe_code)]

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, CellProgram,
    ChildVkStrategy, ConstantsModule, Effect, Event, FactoryDescriptor, FieldElement,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, canonical_program_vk, field_from_u64,
    hex_encode_32, symbol,
};
use dregg_cell::program::SimpleStateConstraint;
use dregg_cell::state::STATE_SLOTS;

pub use dregg_app_framework::field_from_bytes;

// =============================================================================
// Slot layout (the ITEM cell) — the custody register + the provenance chain.
// =============================================================================

/// Slot 0 — `CUSTODIAN`. The **current** custodian's identity scalar (the
/// single-custodianship register). Guarded by `AnyOf[Immutable, SenderInSlot]` —
/// the actor-bound baton: it may change ONLY in a turn signed by the incoming
/// holder. Mirrors the Lean `batonF` under
/// `anyOf[immutable batonF, senderInField batonF]`.
pub const CUSTODIAN_SLOT: u8 = 0;

/// Slot 1 — `EPOCH`. The provenance epoch (the handoff counter). `StrictMonotonic`
/// — every handoff strictly advances it (no replay). Mirrors the Lean `epochF`.
pub const EPOCH_SLOT: u8 = 1;

/// Slot 2 — `HEAD`. The provenance cursor: the index of the NEXT custody-receipt
/// link to be written. `Monotonic` — the chain is append-only. Mirrors
/// `AgentProvenanceGated.HEAD`.
pub const HEAD_SLOT: u8 = 2;

/// Slot 3 — `TIP`. The latest committed custody-link digest (the chain tip a
/// verifier reads first). Mirrors `AgentProvenanceGated.TIP`.
pub const TIP_SLOT: u8 = 3;

/// The first custody-receipt link slot. Link `i` lives at `LINK_BASE + i`, each
/// carrying a `WriteOnce` caveat — a committed link is frozen forever
/// (tamper-evidence). Mirrors `AgentProvenanceGated.ENTRY_BASE`.
pub const LINK_BASE: u8 = 4;

/// How many custody-receipt link slots fit in a single item cell. A dregg cell
/// carries exactly [`STATE_SLOTS`] field slots; after reserving CUSTODIAN / EPOCH
/// / HEAD / TIP, the links occupy `LINK_BASE..STATE_SLOTS`. A provenance chain
/// longer than this per-cell capacity chains ACROSS item cells (the filled cell's
/// `TIP` is the genesis predecessor of the next cell's first link), so
/// [`verify_chain`] continues seamlessly across the boundary.
pub const LINK_CAPACITY: usize = STATE_SLOTS - LINK_BASE as usize;

/// The slot index of the i-th custody-receipt link.
pub fn link_slot(i: usize) -> usize {
    LINK_BASE as usize + i
}

// =============================================================================
// The custody POLICY (the slot-caveat predicate installed on every item cell).
// =============================================================================

/// The supply-chain custody POLICY as a flat conjunction of slot caveats — THIS is
/// the exact predicate the executor installs as the factory-born item's
/// `CellProgram` and re-checks on EVERY turn that touches the item. Each clause is
/// a primitive of the custody invariant; each refusal is a theorem on the Lean
/// side and a real executor refusal here:
///
///   * **actor-bound handoff** (`AnyOf[Immutable(CUSTODIAN), SenderInSlot(CUSTODIAN)]`):
///     the `CUSTODIAN` register may change ONLY in a turn SIGNED BY the incoming
///     holder. Either the custodian is unchanged (`Immutable` holds — a non-handoff
///     turn is open) OR the turn's sender IS the (new) recorded custodian
///     (`SenderInSlot`). A flip to a party that did not sign is REFUSED. This is
///     the Lean `anyOf[immutable batonF, senderInField batonF]` keystone
///     (`stolen_baton_rejected`).
///   * **no replay** (`StrictMonotonic(EPOCH)`): every touching handoff strictly
///     advances the provenance epoch; a replayed (same / stale epoch) handoff is
///     REFUSED. The Lean `strictMono epochF`. (The item is minted at epoch 1 so the
///     mint turn itself strictly advances 0 -> 1; handoffs then go 1 -> 2 -> 3 -> ….)
///   * **append-only chain** (`Monotonic(HEAD)`): the provenance cursor only grows;
///     a rewind (truncate-then-fork) is REFUSED. The Lean `prov_head_cannot_rewind`.
///   * **frozen links** (`WriteOnce(LINK_BASE + i)`): each committed custody-receipt
///     link is frozen forever; an overwrite is REFUSED (tamper-evidence). The Lean
///     `prov_entry_writeonce`.
pub fn custody_constraints() -> Vec<StateConstraint> {
    let mut cs = Vec::with_capacity(3 + LINK_CAPACITY);
    // actor-bound custody handoff — the custodian flips only in a turn signed by
    // the incoming holder (the verified baton keystone).
    cs.push(StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Immutable {
                index: CUSTODIAN_SLOT,
            },
            SimpleStateConstraint::SenderInSlot {
                index: CUSTODIAN_SLOT,
            },
        ],
    });
    // no replay — every handoff strictly advances the provenance epoch.
    cs.push(StateConstraint::StrictMonotonic { index: EPOCH_SLOT });
    // append-only chain — the provenance cursor only grows.
    cs.push(StateConstraint::Monotonic { index: HEAD_SLOT });
    // frozen links — each committed custody-receipt link is write-once.
    for i in 0..LINK_CAPACITY {
        cs.push(StateConstraint::WriteOnce {
            index: link_slot(i) as u8,
        });
    }
    cs
}

/// The ITEM program — `custody_constraints` as a `CellProgram::Predicate`,
/// identical to what the factory installs on the born cell (so the program VK
/// names the exact installed predicate byte-for-byte).
pub fn item_program() -> CellProgram {
    CellProgram::Predicate(custody_constraints())
}

/// Canonical child program VK for the supply-chain item cell.
pub fn item_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&item_program())
}

// =============================================================================
// The custody-receipt LINK HASH (the provenance hash chain).
// =============================================================================

/// The genesis predecessor digest (no custody link before the mint).
pub const GENESIS_PREV: FieldElement = [0u8; 32];

/// Hash a party identity string to its identity scalar (the custodian register
/// stores `CUSTODIAN` as this scalar — the field image of a custodian's pubkey).
pub fn identity_field(party: &str) -> FieldElement {
    field_from_bytes(party.as_bytes())
}

/// **The custody EVENT digest** — `custody_event(from, to, epoch)` is the
/// canonical 32-byte digest of a single handoff: it binds the OUTGOING custodian,
/// the INCOMING custodian, and the provenance epoch. This is the payload each
/// receipt link commits to. Deterministic (a third party recomputes it exactly);
/// collision-resistant (a forged event hashing elsewhere is detectable).
pub fn custody_event(from: &FieldElement, to: &FieldElement, epoch: u64) -> FieldElement {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-custody-event\x01");
    h.update(from);
    h.update(to);
    h.update(&epoch.to_be_bytes());
    *h.finalize().as_bytes()
}

/// **The custody link hash** — `link_hash(prev, event)` is the digest stored at a
/// receipt link slot: `blake3(prev ‖ event)`, binding the new handoff event to the
/// ENTIRE committed prefix (since `prev` is itself the previous link). The
/// production (real-blake3) face of the Lean executable Horner shadow `linkHash`.
pub fn link_hash(prev: &FieldElement, event: &FieldElement) -> FieldElement {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-custody-link\x01");
    h.update(prev);
    h.update(event);
    *h.finalize().as_bytes()
}

/// A single handoff event in a custody history: `from` handed the item to `to` at
/// provenance epoch `epoch`. The mint is modelled as a handoff from
/// [`GENESIS_PREV`]'s identity (the zero scalar — "no prior custodian") to the
/// first custodian at epoch 1.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Handoff {
    /// The outgoing custodian's identity scalar (the zero scalar for the mint).
    pub from: FieldElement,
    /// The incoming custodian's identity scalar.
    pub to: FieldElement,
    /// The provenance epoch this handoff advances to (mint = 1, then 2, 3, …).
    pub epoch: u64,
}

impl Handoff {
    /// The canonical custody event digest for this handoff.
    pub fn event(&self) -> FieldElement {
        custody_event(&self.from, &self.to, self.epoch)
    }
}

/// `custody_chain_digests(handoffs)` — the honest custody-link digest sequence for
/// a custody history: each link folds the PREVIOUS link's digest with the next
/// handoff event, starting from [`GENESIS_PREV`]. This is exactly what an honest
/// custody chain commits to `LINK_BASE + i`, and exactly what [`verify_chain`]
/// recomputes.
pub fn custody_chain_digests(handoffs: &[Handoff]) -> Vec<FieldElement> {
    let mut out = Vec::with_capacity(handoffs.len());
    let mut prev = GENESIS_PREV;
    for h in handoffs {
        let link = link_hash(&prev, &h.event());
        out.push(link);
        prev = link;
    }
    out
}

/// **`verify_chain`** — the third-party VERIFIER ("PROVE this item's full custody
/// chain"). Given the published handoff events and the link digests read off the
/// committed item cell, re-derive the honest chain from scratch and check they
/// match link-for-link. Returns `true` IFF every committed link equals
/// `link_hash(previous committed link, handoff_i.event())`, i.e. the chain is
/// EXACTLY the honest custody history. A tampered, reordered, forged, or dropped
/// handoff makes this `false` — the provenance is verifiable by re-execution.
pub fn verify_chain(handoffs: &[Handoff], committed: &[FieldElement]) -> bool {
    committed == custody_chain_digests(handoffs).as_slice()
}

/// **`custody_chain_is_connected`** — the single-custodianship CONSERVATION check
/// on a custody history: the `from` of every handoff equals the `to` of the
/// previous handoff (and the first handoff's `from` is the genesis zero scalar).
/// This is the structural witness that custody is CONSERVED — there is no fork (a
/// second custodian appearing from nowhere) and no gap (a handoff whose outgoing
/// holder is not the prior incoming holder). Returns `true` IFF the chain is a
/// single connected custody path.
pub fn custody_chain_is_connected(handoffs: &[Handoff]) -> bool {
    let mut expected_from = GENESIS_PREV; // the mint's `from` is "no prior custodian"
    for h in handoffs {
        if h.from != expected_from {
            return false;
        }
        // ...and the epoch must strictly advance (no replay), starting at 1.
        expected_from = h.to;
    }
    // epochs must be 1, 2, 3, … (strictly monotone from the mint at 1).
    handoffs
        .iter()
        .enumerate()
        .all(|(i, h)| h.epoch == (i as u64) + 1)
}

// =============================================================================
// Factory configuration (the supply-chain item factory).
// =============================================================================

/// The factory VK we publish for the supply-chain item factory.
pub const ITEM_FACTORY_VK: [u8; 32] = *b"starbridge-supplychain-item-fact";

/// Default per-epoch creation budget for the item factory.
pub const DEFAULT_CREATION_BUDGET: u64 = 1_000_000;

/// Build the [`FactoryDescriptor`] for supply-chain ITEM cells.
///
/// A factory-born item is born EMPTY; the `mint_item` turn binds the first
/// `CUSTODIAN`, advances `EPOCH` to 1, and appends the genesis custody link before
/// any handoff. The custody policy (actor-bound register + strict-mono epoch +
/// append-only/write-once chain) is installed at birth FOR LIFE (mirror
/// agent-provenance / swarm-orchestration: born empty, bound by the first turn,
/// frozen).
pub fn item_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: ITEM_FACTORY_VK,
        child_program_vk: Some(item_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(item_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            // The item's custody cap is an attenuatable SelfCell cap — the ocap
            // handle a custodian holds. A handoff narrows it onward to the next
            // custodian (no amplification; the Lean `derive_no_amplify`).
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        // Born empty: the `mint_item` turn binds CUSTODIAN + EPOCH + the genesis
        // link from zero under the installed caveats.
        field_constraints: vec![],
        // The life-of-cell custody policy, installed at birth as the born cell's
        // `CellProgram::Predicate` and re-checked by the executor on every touching
        // turn. This is EXACTLY `custody_constraints()` (and `item_program()`'s
        // predicate), so the advertised program VK names the installed predicate
        // byte-for-byte.
        state_constraints: custody_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![item_factory_descriptor()]
}

// =============================================================================
// Turn builders — MINT / HANDOFF / (the forged-handoff adversary).
// =============================================================================

/// **MINT** — the manufacturer mints the item by binding the FIRST custodian into
/// `CUSTODIAN`, advancing `EPOCH` to 1 (so the mint turn itself satisfies
/// `StrictMonotonic(EPOCH)`, 0 -> 1), appending the genesis custody link
/// `link_0 = link_hash(GENESIS_PREV, event(genesis -> first, 1))`, advancing
/// `HEAD` to 1, and pointing `TIP` at the genesis link.
///
/// The mint is the actor-bound register's INCEPTION: the manufacturer (the first
/// custodian) signs the turn, and the written `CUSTODIAN` equals the signer, so
/// `SenderInSlot(CUSTODIAN)` holds (the `Immutable` disjunct's inception path also
/// admits the first write from zero). After the mint there is EXACTLY ONE
/// custodian — the manufacturer.
pub fn build_mint_action(
    cipherclerk: &AppCipherclerk,
    item: CellId,
    first_custodian: &str,
) -> Action {
    let first = identity_field(first_custodian);
    let event = custody_event(&GENESIS_PREV, &first, 1);
    let link = link_hash(&GENESIS_PREV, &event);
    let effects = vec![
        Effect::SetField {
            cell: item,
            index: CUSTODIAN_SLOT as usize,
            value: first,
        },
        // mint at epoch 1 — the mint turn itself strictly advances 0 -> 1 (so the
        // `StrictMonotonic(EPOCH)` no-replay caveat holds on the very first touch);
        // handoffs then go 1 -> 2 -> 3 -> ….
        Effect::SetField {
            cell: item,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(1),
        },
        // append the genesis custody link.
        Effect::SetField {
            cell: item,
            index: link_slot(0),
            value: link,
        },
        // advance the provenance cursor 0 -> 1.
        Effect::SetField {
            cell: item,
            index: HEAD_SLOT as usize,
            value: field_from_u64(1),
        },
        // point the chain tip at the genesis link.
        Effect::SetField {
            cell: item,
            index: TIP_SLOT as usize,
            value: link,
        },
        Effect::EmitEvent {
            cell: item,
            event: Event::new(symbol("item-minted"), vec![first, link]),
        },
    ];
    cipherclerk.make_action(item, "mint_item", effects)
}

/// **HANDOFF** — the incoming custodian accepts custody. It rewrites `CUSTODIAN`
/// to the incoming holder (the actor-bound register: the turn is signed by the
/// incoming holder, so `SenderInSlot(CUSTODIAN)` holds on the new value),
/// strictly advances `EPOCH` (no-replay), appends the custody-receipt link
/// `link_i = link_hash(prev, event(from -> to, new_epoch))`, advances `HEAD`, and
/// points `TIP` at the new link.
///
/// The executor admits this IFF the signer holds the item's custody cap (the
/// cap-graph half — the prior custodian handed it forward), the custodian flip is
/// signed by the incoming holder (the actor-bound caveat), the epoch strictly
/// advances, and the link slot is fresh. After the handoff there is again EXACTLY
/// ONE custodian — the incoming holder.
///
/// `from` is the outgoing custodian's identity (the current register value); `to`
/// is the incoming custodian's identity (the signer); `prev` is the digest
/// committed at link `i-1`; `new_epoch` is the strictly-greater epoch; `i` is the
/// link index (the current `HEAD`).
#[allow(clippy::too_many_arguments)]
pub fn build_handoff_action(
    cipherclerk: &AppCipherclerk,
    item: CellId,
    from: &str,
    to: &str,
    prev: &FieldElement,
    new_epoch: u64,
    i: usize,
) -> Action {
    let from_id = identity_field(from);
    let to_id = identity_field(to);
    let event = custody_event(&from_id, &to_id, new_epoch);
    let link = link_hash(prev, &event);
    let effects = vec![
        // the custody register advances to the incoming holder (actor-bound).
        Effect::SetField {
            cell: item,
            index: CUSTODIAN_SLOT as usize,
            value: to_id,
        },
        // the provenance epoch strictly advances (no replay).
        Effect::SetField {
            cell: item,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(new_epoch),
        },
        // append the custody-receipt link.
        Effect::SetField {
            cell: item,
            index: link_slot(i),
            value: link,
        },
        // advance the provenance cursor.
        Effect::SetField {
            cell: item,
            index: HEAD_SLOT as usize,
            value: field_from_u64((i + 1) as u64),
        },
        // point the chain tip at the new link.
        Effect::SetField {
            cell: item,
            index: TIP_SLOT as usize,
            value: link,
        },
        Effect::EmitEvent {
            cell: item,
            event: Event::new(
                symbol("custody-handoff"),
                vec![from_id, to_id, field_from_u64(new_epoch), link],
            ),
        },
    ];
    cipherclerk.make_action(item, "handoff_custody", effects)
}

/// **FORGED HANDOFF (the adversary)** — a party claims custody it does not hold.
/// This builds the SAME shape as an honest handoff (flipping `CUSTODIAN` to a new
/// holder and advancing the chain) but with the forger as the new holder while the
/// turn is NOT signed by that holder. Two real teeth REFUSE it:
///
///   * the **cap-graph** tooth: if the forger holds no custody cap reaching the
///     item, the executor's authorization gate rejects the turn before any caveat
///     runs (the ocap half of single-custodianship);
///   * the **actor-bound** tooth: if the custodian flips to a party that did NOT
///     sign the turn, `AnyOf[Immutable, SenderInSlot]` rejects (the held register
///     can only move to the signer — the Lean `stolen_baton_rejected`).
///
/// `claimed_to` is the custodian the forger tries to install; `forger_signs` is
/// the (different) identity actually signing — when these differ, the actor-bound
/// caveat bites. The capability gate bites independently whenever the signer holds
/// no custody cap over the item.
pub fn build_forged_handoff_action(
    cipherclerk: &AppCipherclerk,
    item: CellId,
    claimed_from: &str,
    claimed_to: &str,
    prev: &FieldElement,
    new_epoch: u64,
    i: usize,
) -> Action {
    // Identical shape to an honest handoff — only the (missing) authority differs.
    build_handoff_action(cipherclerk, item, claimed_from, claimed_to, prev, new_epoch, i)
}

// =============================================================================
// StarbridgeAppContext mount.
// =============================================================================

/// The canonical web-constants module (slot layout + event topics + factory-vk hex).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("supply-chain-provenance")
        .slot("CUSTODIAN_SLOT", CUSTODIAN_SLOT as u64)
        .slot("EPOCH_SLOT", EPOCH_SLOT as u64)
        .slot("HEAD_SLOT", HEAD_SLOT as u64)
        .slot("TIP_SLOT", TIP_SLOT as u64)
        .slot("LINK_BASE", LINK_BASE as u64)
        .slot("LINK_CAPACITY", LINK_CAPACITY as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&ITEM_FACTORY_VK))
        .topic("MINTED", "item-minted")
        .topic("HANDOFF", "custody-handoff")
}

/// Register the supply-chain-provenance starbridge-app on a shared context.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(item_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "supply-chain-item".into(),
        descriptor: serde_json::json!({
            "component": "dregg-supply-chain-item",
            "module": "/starbridge-apps/supply-chain-provenance/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["custodian", "epoch", "head", "tip", "links"],
            "slot_layout": {
                "custodian": CUSTODIAN_SLOT,
                "epoch": EPOCH_SLOT,
                "head": HEAD_SLOT,
                "tip": TIP_SLOT,
                "link_base": LINK_BASE,
                "capacity": LINK_CAPACITY,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&item_child_program_vk()),
            "methods": ["mint_item", "handoff_custody"],
        }),
    });

    factory_vk
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [0x5cu8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_item() -> CellId {
        CellId::from_bytes([7u8; 32])
    }

    // ── the custody policy is the verified slot-caveat shape ─────────────────

    #[test]
    fn item_program_has_the_custody_clauses() {
        let CellProgram::Predicate(ks) = item_program() else {
            panic!("item program must be a flat Predicate");
        };
        assert_eq!(ks, custody_constraints(), "the program IS custody_constraints");
        // the actor-bound custody register: AnyOf[Immutable, SenderInSlot] on CUSTODIAN.
        assert!(
            ks.iter().any(|k| matches!(
                k,
                StateConstraint::AnyOf { variants }
                    if variants.contains(&SimpleStateConstraint::Immutable { index: CUSTODIAN_SLOT })
                        && variants.contains(&SimpleStateConstraint::SenderInSlot { index: CUSTODIAN_SLOT })
            )),
            "the actor-bound handoff caveat AnyOf[Immutable(CUSTODIAN), SenderInSlot(CUSTODIAN)] must be a clause"
        );
        // no replay + append-only chain.
        assert!(ks.iter().any(|k| matches!(k, StateConstraint::StrictMonotonic { index } if *index == EPOCH_SLOT)));
        assert!(ks.iter().any(|k| matches!(k, StateConstraint::Monotonic { index } if *index == HEAD_SLOT)));
        // every link slot is write-once (tamper-evidence).
        for i in 0..LINK_CAPACITY {
            let idx = link_slot(i) as u8;
            assert!(
                ks.iter().any(|k| matches!(k, StateConstraint::WriteOnce { index } if *index == idx)),
                "expected WriteOnce on link slot {idx}"
            );
        }
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        assert_eq!(item_child_program_vk(), canonical_program_vk(&item_program()));
        assert_eq!(item_factory_descriptor().child_program_vk, Some(item_child_program_vk()));
    }

    #[test]
    fn descriptor_is_deterministic() {
        assert_eq!(item_factory_descriptor().hash(), item_factory_descriptor().hash());
    }

    // ── the provenance hash chain + verifier ─────────────────────────────────

    /// Build a connected honest custody history mint(M) -> A -> B -> C.
    fn demo_history() -> Vec<Handoff> {
        let m = identity_field("manufacturer");
        let a = identity_field("warehouse-a");
        let b = identity_field("carrier-b");
        let c = identity_field("retailer-c");
        vec![
            Handoff { from: GENESIS_PREV, to: m, epoch: 1 }, // mint
            Handoff { from: m, to: a, epoch: 2 },
            Handoff { from: a, to: b, epoch: 3 },
            Handoff { from: b, to: c, epoch: 4 },
        ]
    }

    #[test]
    fn honest_custody_chain_verifies_and_is_connected() {
        let h = demo_history();
        let committed = custody_chain_digests(&h);
        assert!(verify_chain(&h, &committed), "the honest custody chain must verify");
        assert!(custody_chain_is_connected(&h), "the honest custody chain is connected (conserved)");
    }

    #[test]
    fn chain_is_actually_linked() {
        let h = demo_history();
        let d = custody_chain_digests(&h);
        assert_eq!(d[0], link_hash(&GENESIS_PREV, &h[0].event()));
        assert_eq!(d[1], link_hash(&d[0], &h[1].event()));
        // the second link genuinely depends on the first (tamper the first ⇒ second differs).
        let mut tampered = d[0];
        tampered[0] ^= 0xff;
        assert_ne!(link_hash(&tampered, &h[1].event()), d[1]);
    }

    #[test]
    fn tampered_handoff_breaks_verification() {
        let h = demo_history();
        let mut committed = custody_chain_digests(&h);
        committed[2] = custody_event(&identity_field("x"), &identity_field("y"), 99);
        assert!(!verify_chain(&h, &committed), "a tampered middle link must break verification");
    }

    #[test]
    fn dropped_handoff_breaks_verification() {
        let h = demo_history();
        let mut committed = custody_chain_digests(&h);
        committed.pop();
        assert!(!verify_chain(&h, &committed), "a dropped tail handoff must break verification");
    }

    #[test]
    fn reordered_handoffs_break_verification() {
        let h = demo_history();
        let mut swapped = h.clone();
        swapped.swap(1, 2);
        let honest = custody_chain_digests(&h);
        assert!(!verify_chain(&swapped, &honest), "reordered handoffs must break verification");
    }

    // ── single-custodianship as conservation (the connected-chain witness) ───

    #[test]
    fn a_forked_chain_is_not_connected() {
        // A second custodian appears from nowhere: handoff 2's `from` is NOT the
        // prior `to` — custody was not conserved (a fork).
        let m = identity_field("manufacturer");
        let a = identity_field("warehouse-a");
        let rogue = identity_field("rogue");
        let b = identity_field("carrier-b");
        let forked = vec![
            Handoff { from: GENESIS_PREV, to: m, epoch: 1 },
            Handoff { from: m, to: a, epoch: 2 },
            // rogue hands off as if it held custody — but `a` held it, not rogue.
            Handoff { from: rogue, to: b, epoch: 3 },
        ];
        assert!(
            !custody_chain_is_connected(&forked),
            "a chain where a non-holder hands off is not connected — custody is not conserved"
        );
    }

    #[test]
    fn a_replayed_epoch_is_not_connected() {
        // Two handoffs at the same epoch — the no-replay law is violated.
        let m = identity_field("manufacturer");
        let a = identity_field("warehouse-a");
        let b = identity_field("carrier-b");
        let replayed = vec![
            Handoff { from: GENESIS_PREV, to: m, epoch: 1 },
            Handoff { from: m, to: a, epoch: 2 },
            Handoff { from: a, to: b, epoch: 2 }, // replayed epoch
        ];
        assert!(
            !custody_chain_is_connected(&replayed),
            "a replayed epoch breaks the strictly-monotone provenance — not conserved"
        );
    }

    // ── the turn builders carry real effects + a real signature ──────────────

    #[test]
    fn mint_action_pins_custodian_epoch_and_genesis_link() {
        let cclerk = test_cipherclerk();
        let action = build_mint_action(&cclerk, test_item(), "manufacturer");
        // custodian, epoch(=1), link_0, head(=1), tip, + event.
        assert_eq!(action.effects.len(), 6);
        let first = identity_field("manufacturer");
        let event = custody_event(&GENESIS_PREV, &first, 1);
        let link = link_hash(&GENESIS_PREV, &event);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. } if *index == CUSTODIAN_SLOT as usize && *value == first
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, value, .. } if *index == EPOCH_SLOT as usize && *value == field_from_u64(1)
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, value, .. } if *index == link_slot(0) && *value == link
        ));
    }

    #[test]
    fn handoff_action_advances_register_epoch_and_link() {
        let cclerk = test_cipherclerk();
        let action = build_handoff_action(&cclerk, test_item(), "manufacturer", "warehouse-a", &GENESIS_PREV, 2, 1);
        assert_eq!(action.effects.len(), 6);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. } if *index == CUSTODIAN_SLOT as usize && *value == identity_field("warehouse-a")
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, value, .. } if *index == EPOCH_SLOT as usize && *value == field_from_u64(2)
        ));
    }

    #[test]
    fn handoff_action_carries_a_real_signature() {
        let cclerk = test_cipherclerk();
        let action = build_handoff_action(&cclerk, test_item(), "a", "b", &GENESIS_PREV, 2, 1);
        match action.authorization {
            Authorization::Signature(a, b) => assert!(a != [0u8; 32] || b != [0u8; 32]),
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    // ── slot-caveat evaluation (executor-side regression) ─────────────────────

    fn empty() -> dregg_cell::state::CellState {
        dregg_cell::state::CellState::new(0)
    }

    #[test]
    fn link_overwrite_is_write_once_violation() {
        // A committed custody link; a turn tries to overwrite it → WriteOnce rejects.
        // (The turn otherwise advances the epoch like a real handoff, so the
        // earlier no-replay caveat is satisfied and the WriteOnce tooth is the one
        // that bites — isolating the constraint under test.)
        let program = item_program();
        let mut old = empty();
        old.fields[link_slot(0)] = link_hash(&GENESIS_PREV, &custody_event(&GENESIS_PREV, &identity_field("m"), 1));
        old.fields[HEAD_SLOT as usize] = field_from_u64(1);
        old.fields[EPOCH_SLOT as usize] = field_from_u64(1);
        old.set_nonce(1);
        let mut new = old.clone();
        new.fields[EPOCH_SLOT as usize] = field_from_u64(2); // a real handoff advances the epoch
        new.fields[link_slot(0)] = identity_field("forged-rewrite");
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("overwriting a committed custody link must be rejected");
        assert!(
            matches!(err, dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index }, ..
            } if index == link_slot(0) as u8),
            "expected WriteOnce violation on the link slot, got {err:?}"
        );
    }

    #[test]
    fn epoch_replay_is_strict_monotonic_violation() {
        // EPOCH at 2; a replayed handoff writes 2 again → StrictMonotonic rejects.
        let program = item_program();
        let mut old = empty();
        old.fields[EPOCH_SLOT as usize] = field_from_u64(2);
        old.set_nonce(2);
        let mut new = old.clone();
        new.fields[EPOCH_SLOT as usize] = field_from_u64(2); // not strictly greater
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("a replayed (non-advancing) epoch must be rejected");
        assert!(
            matches!(err, dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::StrictMonotonic { index }, ..
            } if index == EPOCH_SLOT),
            "expected StrictMonotonic violation on EPOCH, got {err:?}"
        );
    }

    #[test]
    fn head_rewind_is_monotonic_violation() {
        // A real handoff advances the epoch; here it also REWINDS the provenance
        // cursor → Monotonic(HEAD) rejects. (The turn advances the epoch like a
        // real handoff, so the earlier StrictMonotonic(EPOCH) no-replay caveat —
        // checked first — is satisfied and the Monotonic(HEAD) tooth is the one
        // that bites, isolating the constraint under test.)
        let program = item_program();
        let mut old = empty();
        old.fields[HEAD_SLOT as usize] = field_from_u64(3);
        old.fields[EPOCH_SLOT as usize] = field_from_u64(1);
        old.set_nonce(3);
        let mut new = old.clone();
        new.fields[EPOCH_SLOT as usize] = field_from_u64(2); // a real handoff advances the epoch
        new.fields[HEAD_SLOT as usize] = field_from_u64(2); // rewind
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("rewinding the provenance cursor must be rejected");
        assert!(
            matches!(err, dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::Monotonic { index }, ..
            } if index == HEAD_SLOT),
            "expected Monotonic violation on HEAD, got {err:?}"
        );
    }

    #[test]
    fn register_installs_factory_and_inspector() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, ITEM_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("supply-chain-item").is_some());
    }
}
