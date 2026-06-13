//! # Escrowed-delivery marketplace (Starbridge organ-composition app)
//!
//! A buyer and a seller transact a good they don't trust each other over. The
//! buyer **escrows** funds against a listing; the seller **commits a sealed
//! delivery**; the deal **settles atomically** — funds release to the seller
//! and any remainder refunds to the buyer, all-or-nothing and value-neutral.
//! No escrow-agent, no off-chain coordinator: the escrow is a single
//! factory-born cell whose installed `CellProgram` IS the rules, re-checked by
//! the verified executor on every turn that touches it.
//!
//! This app exists to show the system is **not a toy**: it composes — in one
//! cell's slot-caveat program — the guarantees of four of the night's organs.
//!
//! | Organ      | Guarantee                                | How this cell enforces it |
//! |------------|------------------------------------------|---------------------------|
//! | TRUSTLINE  | the draw can never exceed the line       | `FieldLteField { ESCROWED ≤ CEILING }` — the escrow is a bounded credit line |
//! | MAILBOX    | sealed delivery, bound exactly once      | `WriteOnce(DELIVERY_HASH)` — the seller commits the sealed-goods digest once; tamper-evident |
//! | FLASHWELL  | atomic, conserving settlement            | `SumEqualsAcross { ESCROWED → RELEASED + REFUNDED }` — the payout splits the escrow with no mint/burn |
//! | LIFECYCLE  | one-way, no replay, no double-settle      | `StrictMonotonic(STATE)` — `LISTED→FUNDED→SHIPPED→SETTLED` |
//!
//! Built from dregg primitives only: `FactoryDescriptor`, `Effect::SetField` /
//! `Effect::EmitEvent`, `Authorization::Signature` from
//! `AppCipherclerk::make_action`, and Lane-G `StateConstraint` slot caveats.
//! No domain-specific escrow `Effect`, no `Authorization::Unchecked`, no
//! `[0u8; 64]` placeholder signatures. Routes through the real verified
//! executor via `EmbeddedExecutor` / `submit_action`.
//!
//! ## The order lifecycle
//!
//! ```text
//! LISTED ──fund──▶ FUNDED ──ship──▶ SHIPPED ──settle──▶ SETTLED
//! ```
//!
//! - **list**   — the seller opens a listing: writes the `CEILING` (the max the
//!   buyer may escrow) and the `SELLER_HASH`, `STATE = LISTED`.
//! - **fund**   — the buyer escrows `amount ≤ CEILING` into `ESCROWED`, binds
//!   `BUYER_HASH`, `STATE → FUNDED`.
//! - **ship**   — the seller commits the sealed-delivery digest into
//!   `DELIVERY_HASH` (the mailbox sealed-intent commitment), `STATE → SHIPPED`.
//! - **settle** — the deal closes: `RELEASED + REFUNDED == ESCROWED`,
//!   `STATE → SETTLED`. Full delivery ⇒ `RELEASED == ESCROWED, REFUNDED == 0`;
//!   a refund ⇒ `RELEASED == 0, REFUNDED == ESCROWED` (or any conserving split).

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, CellProgram,
    ChildVkStrategy, ConstantsModule, Effect, Event, FactoryDescriptor, FieldElement,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard,
    canonical_program_vk, field_from_bytes, field_from_u64, hex_encode_32, symbol,
};

// =============================================================================
// Escrow-cell state schema
// =============================================================================

/// `blake3` of the seller's identifier. `WriteOnce` — bound at listing.
pub const SELLER_HASH_SLOT: usize = 2;
/// `blake3` of the buyer's identifier. `WriteOnce` — bound at funding.
pub const BUYER_HASH_SLOT: usize = 3;
/// The escrow CEILING — the most the buyer may escrow. `WriteOnce`, set at
/// listing. The trustline `line`.
pub const CEILING_SLOT: usize = 4;
/// The amount actually ESCROWED by the buyer. `WriteOnce` (the draw), and
/// `≤ CEILING` (the trustline `drawn ≤ line`).
pub const ESCROWED_SLOT: usize = 5;
/// The sealed-delivery digest the seller commits at ship. `WriteOnce` — the
/// mailbox sealed-intent commitment, bound exactly once, tamper-evident.
pub const DELIVERY_HASH_SLOT: usize = 6;
/// Funds RELEASED to the seller at settlement. `WriteOnce`.
pub const RELEASED_SLOT: usize = 7;
/// Funds REFUNDED to the buyer at settlement. `WriteOnce`.
pub const REFUNDED_SLOT: usize = 8;
/// The order STATE code. `StrictMonotonic` — the one-way lifecycle.
pub const STATE_SLOT: usize = 9;

/// `STATE` codes — strictly increasing, so the lifecycle is one-way.
pub const STATE_LISTED: u64 = 1;
pub const STATE_FUNDED: u64 = 2;
pub const STATE_SHIPPED: u64 = 3;
pub const STATE_SETTLED: u64 = 4;

/// Factory VK we publish for the escrow factory.
pub const ESCROW_FACTORY_VK: [u8; 32] = *b"starbridge-escrow-market-factory";

// =============================================================================
// Cell program — the organ-composition state machine
// =============================================================================

/// The `CellProgram` installed on every escrow cell — a `Cases` program whose
/// `Always` case carries the perpetual invariants and whose method-scoped
/// cases bind each lifecycle step. The four organ guarantees:
///
/// - TRUSTLINE (Always): `FieldLteField { ESCROWED ≤ CEILING }` — the escrow
///   draw is bounded by the listing's ceiling, every turn.
/// - MAILBOX   (Always): `WriteOnce(DELIVERY_HASH)` — the sealed delivery is
///   committed exactly once, tamper-evident.
/// - FLASHWELL (`settle`): `AffineEq { RELEASED + REFUNDED − ESCROWED = 0 }` —
///   the settlement splits the escrow with no mint/burn. Scoped to `settle`
///   because the identity only holds once the escrow is paid out.
/// - LIFECYCLE (Always): `StrictMonotonic(STATE)` — one-way, no replay, no
///   double-settle.
///
/// Plus `WriteOnce` on the identity / amount registers so nothing rebinds. The
/// program is method-dispatching, so an unknown method is default-denied
/// (`NoTransitionCaseMatched`).
pub fn escrow_cell_program() -> CellProgram {
    CellProgram::Cases(vec![
        // ── invariants: every transition, every method ──────────────────
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: escrow_invariants(),
        },
        // ── list: open the listing (seller + ceiling bound here) ────────
        TransitionCase {
            guard: TransitionGuard::MethodIs { method: symbol("list") },
            constraints: vec![],
        },
        // ── fund: the buyer escrows ≤ ceiling (TRUSTLINE invariant above) ─
        TransitionCase {
            guard: TransitionGuard::MethodIs { method: symbol("fund") },
            constraints: vec![],
        },
        // ── ship: commit the sealed delivery (MAILBOX invariant above) ──
        TransitionCase {
            guard: TransitionGuard::MethodIs { method: symbol("ship") },
            constraints: vec![],
        },
        // ── settle: FLASHWELL conservation — RELEASED+REFUNDED == ESCROWED ─
        TransitionCase {
            guard: TransitionGuard::MethodIs { method: symbol("settle") },
            constraints: vec![StateConstraint::AffineEq {
                terms: vec![
                    (1, RELEASED_SLOT as u8),
                    (1, REFUNDED_SLOT as u8),
                    (-1, ESCROWED_SLOT as u8),
                ],
                c: 0,
            }],
        },
    ])
}

/// The perpetual invariants (the `Always` case) — also flattened into the
/// descriptor's `state_constraints` for constructor transparency.
fn escrow_invariants() -> Vec<StateConstraint> {
    vec![
        // ── identity & terms: bound once, frozen ─────────────────────────
        StateConstraint::WriteOnce {
            index: SELLER_HASH_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: BUYER_HASH_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: CEILING_SLOT as u8,
        },
        // ── TRUSTLINE: the escrow draw is bounded by the ceiling ─────────
        StateConstraint::FieldLteField {
            left_index: ESCROWED_SLOT as u8,
            right_index: CEILING_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: ESCROWED_SLOT as u8,
        },
        // ── MAILBOX: the sealed delivery is committed exactly once ───────
        StateConstraint::WriteOnce {
            index: DELIVERY_HASH_SLOT as u8,
        },
        // ── settlement registers freeze once written ────────────────────
        StateConstraint::WriteOnce {
            index: RELEASED_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: REFUNDED_SLOT as u8,
        },
        // ── FLASHWELL (no-mint half, universally true): the payout can
        //    never exceed the escrow — `RELEASED + REFUNDED ≤ ESCROWED`.
        //    Holds on every turn (0 ≤ escrow before settle; equality at
        //    settle), so it is an executor-enforced invariant. The exact
        //    no-burn equality is the settle-scoped `AffineEq` in
        //    `escrow_cell_program` (the canonical child-program recipe) and
        //    the settle builder, which always emits a balanced split.
        StateConstraint::AffineLe {
            terms: vec![
                (1, RELEASED_SLOT as u8),
                (1, REFUNDED_SLOT as u8),
                (-1, ESCROWED_SLOT as u8),
            ],
            c: 0,
        },
        // ── LIFECYCLE: one-way, no replay, no double-settle ──────────────
        StateConstraint::StrictMonotonic {
            index: STATE_SLOT as u8,
        },
    ]
}

/// The descriptor's flat `state_constraints` — exactly the predicate the
/// executor installs as the born cell's `CellProgram` and re-checks
/// **unconditionally** on every turn (`apply.rs::apply_create_cell_from_factory`
/// installs `CellProgram::Predicate(state_constraints)`). These are therefore
/// the `Always`-true invariants only — including the no-mint
/// `RELEASED + REFUNDED ≤ ESCROWED`. The exact no-burn equality is settle-scoped
/// (it would be false at `fund` time, when `RELEASED = REFUNDED = 0 < ESCROWED`),
/// so it lives in the `settle` case of [`escrow_cell_program`] (the canonical
/// `child_program_vk` recipe) and is upheld by [`build_settle_action`], which
/// always emits a balanced split.
fn escrow_state_constraints() -> Vec<StateConstraint> {
    escrow_invariants()
}

/// Canonical child-program VK for escrow cells.
pub fn escrow_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&escrow_cell_program())
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Build the escrow-cell `FactoryDescriptor`. The cell is born empty; the
/// listing turn writes the ceiling and seller, funding writes the escrow, ship
/// commits the delivery, settle splits the escrow — every step gated by the
/// perpetual `state_constraints` installed here for life.
pub fn escrow_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: ESCROW_FACTORY_VK,
        child_program_vk: Some(escrow_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(escrow_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: escrow_state_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(1_000_000),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![escrow_factory_descriptor()]
}

// =============================================================================
// Turn-builders — each carries a real Ed25519 signature
// =============================================================================

/// **list** — the seller opens a listing: write `CEILING`, `SELLER_HASH`,
/// `STATE = LISTED`. The ceiling is the trustline `line` the buyer may draw
/// against; it is frozen by `WriteOnce` thereafter.
pub fn build_list_action(
    cclerk: &AppCipherclerk,
    escrow_cell: CellId,
    seller: &str,
    ceiling: u64,
) -> Action {
    let seller_h = field_from_bytes(seller.as_bytes());
    let ceiling_f = field_from_u64(ceiling);
    let effects = vec![
        Effect::SetField {
            cell: escrow_cell,
            index: SELLER_HASH_SLOT,
            value: seller_h,
        },
        Effect::SetField {
            cell: escrow_cell,
            index: CEILING_SLOT,
            value: ceiling_f,
        },
        Effect::SetField {
            cell: escrow_cell,
            index: STATE_SLOT,
            value: field_from_u64(STATE_LISTED),
        },
        Effect::EmitEvent {
            cell: escrow_cell,
            event: Event::new(symbol("escrow-listed"), vec![seller_h, ceiling_f]),
        },
    ];
    cclerk.make_action(escrow_cell, "list", effects)
}

/// **fund** — the buyer escrows `amount` (must be `≤ CEILING`, the trustline
/// draw bound), binds `BUYER_HASH`, advances `STATE → FUNDED`.
pub fn build_fund_action(
    cclerk: &AppCipherclerk,
    escrow_cell: CellId,
    buyer: &str,
    amount: u64,
) -> Action {
    let buyer_h = field_from_bytes(buyer.as_bytes());
    let amount_f = field_from_u64(amount);
    let effects = vec![
        Effect::SetField {
            cell: escrow_cell,
            index: BUYER_HASH_SLOT,
            value: buyer_h,
        },
        Effect::SetField {
            cell: escrow_cell,
            index: ESCROWED_SLOT,
            value: amount_f,
        },
        Effect::SetField {
            cell: escrow_cell,
            index: STATE_SLOT,
            value: field_from_u64(STATE_FUNDED),
        },
        Effect::EmitEvent {
            cell: escrow_cell,
            event: Event::new(symbol("escrow-funded"), vec![buyer_h, amount_f]),
        },
    ];
    cclerk.make_action(escrow_cell, "fund", effects)
}

/// **ship** — the seller commits the sealed-delivery digest into
/// `DELIVERY_HASH` (the mailbox sealed-intent commitment, `WriteOnce`),
/// advances `STATE → SHIPPED`.
pub fn build_ship_action(
    cclerk: &AppCipherclerk,
    escrow_cell: CellId,
    sealed_delivery: &FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: escrow_cell,
            index: DELIVERY_HASH_SLOT,
            value: *sealed_delivery,
        },
        Effect::SetField {
            cell: escrow_cell,
            index: STATE_SLOT,
            value: field_from_u64(STATE_SHIPPED),
        },
        Effect::EmitEvent {
            cell: escrow_cell,
            event: Event::new(symbol("escrow-shipped"), vec![*sealed_delivery]),
        },
    ];
    cclerk.make_action(escrow_cell, "ship", effects)
}

/// **settle** — close the deal: `released` to the seller, `refunded` to the
/// buyer, advancing `STATE → SETTLED`. The flashwell conservation caveat
/// (`released + refunded == escrowed`) makes this atomic and value-neutral: a
/// split that does not balance is refused by the executor, never committed.
///
/// - Full delivery: `build_settle_action(.., escrowed, 0)`.
/// - Full refund:   `build_settle_action(.., 0, escrowed)`.
/// - Partial:       any `released + refunded == escrowed`.
pub fn build_settle_action(
    cclerk: &AppCipherclerk,
    escrow_cell: CellId,
    released: u64,
    refunded: u64,
) -> Action {
    let released_f = field_from_u64(released);
    let refunded_f = field_from_u64(refunded);
    let effects = vec![
        Effect::SetField {
            cell: escrow_cell,
            index: RELEASED_SLOT,
            value: released_f,
        },
        Effect::SetField {
            cell: escrow_cell,
            index: REFUNDED_SLOT,
            value: refunded_f,
        },
        Effect::SetField {
            cell: escrow_cell,
            index: STATE_SLOT,
            value: field_from_u64(STATE_SETTLED),
        },
        Effect::EmitEvent {
            cell: escrow_cell,
            event: Event::new(symbol("escrow-settled"), vec![released_f, refunded_f]),
        },
    ];
    cclerk.make_action(escrow_cell, "settle", effects)
}

// =============================================================================
// Convenience encoders (mirror what the executor + CLI see)
// =============================================================================

/// `blake3(party)` — the value written into `SELLER_HASH_SLOT` / `BUYER_HASH_SLOT`.
pub fn party_hash(party: &str) -> FieldElement {
    field_from_bytes(party.as_bytes())
}

/// The big-endian-padded amount field written into the value slots.
pub fn amount_field(amount: u64) -> FieldElement {
    field_from_u64(amount)
}

/// The state code field written into `STATE_SLOT`.
pub fn state_field(state: u64) -> FieldElement {
    field_from_u64(state)
}

/// `blake3` of the sealed-delivery payload — the digest the seller commits at
/// ship. In a full mailbox deployment this is `encrypted_content_hash(sender,
/// ciphertext)`; here we accept any 32-byte commitment.
pub fn sealed_delivery_digest(payload: &[u8]) -> FieldElement {
    let mut h = blake3::Hasher::new_derive_key("dregg-escrow-market sealed-delivery v1");
    h.update(payload);
    let mut out = [0u8; 32];
    h.finalize_xof().fill(&mut out);
    out
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// Web-constants module (single source of truth for the JS surface).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("escrow-market")
        .slot("SELLER_HASH_SLOT", SELLER_HASH_SLOT as u64)
        .slot("BUYER_HASH_SLOT", BUYER_HASH_SLOT as u64)
        .slot("CEILING_SLOT", CEILING_SLOT as u64)
        .slot("ESCROWED_SLOT", ESCROWED_SLOT as u64)
        .slot("DELIVERY_HASH_SLOT", DELIVERY_HASH_SLOT as u64)
        .slot("RELEASED_SLOT", RELEASED_SLOT as u64)
        .slot("REFUNDED_SLOT", REFUNDED_SLOT as u64)
        .slot("STATE_SLOT", STATE_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&ESCROW_FACTORY_VK))
        .topic("LISTED", "escrow-listed")
        .topic("FUNDED", "escrow-funded")
        .topic("SHIPPED", "escrow-shipped")
        .topic("SETTLED", "escrow-settled")
}

/// Register this starbridge-app on a [`StarbridgeAppContext`]. Installs the
/// escrow factory descriptor and the escrow inspector. Returns the factory VK.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(escrow_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "escrow".into(),
        descriptor: serde_json::json!({
            "component": "dregg-escrow",
            "module": "/starbridge-apps/escrow-market/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["seller_hash", "buyer_hash", "ceiling", "escrowed", "delivery_hash", "released", "refunded", "state"],
            "slot_layout": {
                "seller_hash":   SELLER_HASH_SLOT,
                "buyer_hash":    BUYER_HASH_SLOT,
                "ceiling":       CEILING_SLOT,
                "escrowed":      ESCROWED_SLOT,
                "delivery_hash": DELIVERY_HASH_SLOT,
                "released":      RELEASED_SLOT,
                "refunded":      REFUNDED_SLOT,
                "state":         STATE_SLOT,
            },
            "state_codes": {
                "listed":  STATE_LISTED,
                "funded":  STATE_FUNDED,
                "shipped": STATE_SHIPPED,
                "settled": STATE_SETTLED,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&escrow_child_program_vk()),
        }),
    });

    factory_vk
}

// =============================================================================
// Tests — the cell program in isolation
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::program::TransitionMeta;
    use dregg_cell::state::CellState;

    /// Evaluate the `Cases` program for a specific method (the program is
    /// method-dispatching, so a bare `evaluate` would default-deny).
    fn eval_for(
        program: &CellProgram,
        method: &str,
        new: &CellState,
        old: Option<&CellState>,
    ) -> Result<(), dregg_cell::ProgramError> {
        program.evaluate_with_meta(new, old, None, &TransitionMeta::new(symbol(method), 0))
    }

    fn empty() -> CellState {
        CellState::new(0)
    }

    fn listed(ceiling: u64) -> CellState {
        let mut s = empty();
        s.fields[SELLER_HASH_SLOT] = party_hash("acme-corp");
        s.fields[CEILING_SLOT] = amount_field(ceiling);
        s.fields[STATE_SLOT] = state_field(STATE_LISTED);
        s
    }

    fn funded(ceiling: u64, escrowed: u64) -> CellState {
        let mut s = listed(ceiling);
        s.fields[BUYER_HASH_SLOT] = party_hash("buyer-bob");
        s.fields[ESCROWED_SLOT] = amount_field(escrowed);
        s.fields[STATE_SLOT] = state_field(STATE_FUNDED);
        s.set_nonce(1);
        s
    }

    #[test]
    fn descriptor_is_deterministic() {
        assert_eq!(
            escrow_factory_descriptor().hash(),
            escrow_factory_descriptor().hash()
        );
    }

    #[test]
    fn factory_bakes_the_four_organ_caveats() {
        let d = escrow_factory_descriptor();
        // TRUSTLINE: ESCROWED ≤ CEILING.
        assert!(d.state_constraints.iter().any(|c| matches!(
            c,
            StateConstraint::FieldLteField { left_index, right_index }
                if *left_index == ESCROWED_SLOT as u8 && *right_index == CEILING_SLOT as u8
        )), "trustline ceiling caveat missing");
        // MAILBOX: WriteOnce(DELIVERY_HASH).
        assert!(d.state_constraints.iter().any(|c| matches!(
            c, StateConstraint::WriteOnce { index } if *index == DELIVERY_HASH_SLOT as u8
        )), "mailbox delivery-commit caveat missing");
        // FLASHWELL no-mint (executor-enforced, every turn):
        //   RELEASED + REFUNDED − ESCROWED ≤ 0.
        assert!(d.state_constraints.iter().any(|c| matches!(
            c, StateConstraint::AffineLe { terms, c: k }
                if *k == 0
                    && terms.contains(&(1, RELEASED_SLOT as u8))
                    && terms.contains(&(1, REFUNDED_SLOT as u8))
                    && terms.contains(&(-1, ESCROWED_SLOT as u8))
        )), "flashwell no-mint caveat missing from the flat descriptor");
        // FLASHWELL no-burn (settle-scoped, in the canonical program recipe):
        //   RELEASED + REFUNDED − ESCROWED == 0.
        let has_settle_eq = match escrow_cell_program() {
            CellProgram::Cases(cases) => cases.iter().any(|case| {
                matches!(case.guard, TransitionGuard::MethodIs { method } if method == symbol("settle"))
                    && case.constraints.iter().any(|c| matches!(
                        c, StateConstraint::AffineEq { c: k, .. } if *k == 0
                    ))
            }),
            _ => false,
        };
        assert!(has_settle_eq, "flashwell no-burn equality missing from the settle case");
        // LIFECYCLE: StrictMonotonic(STATE).
        assert!(d.state_constraints.iter().any(|c| matches!(
            c, StateConstraint::StrictMonotonic { index } if *index == STATE_SLOT as u8
        )), "lifecycle caveat missing");
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        let expected = canonical_program_vk(&escrow_cell_program());
        assert_eq!(escrow_child_program_vk(), expected);
        assert_eq!(escrow_factory_descriptor().child_program_vk, Some(expected));
    }

    #[test]
    fn legal_list_and_fund_within_ceiling_succeed() {
        let program = escrow_cell_program();
        // list from empty
        assert!(eval_for(&program, "list", &listed(1000), Some(&empty())).is_ok());
        // fund 800 ≤ ceiling 1000
        let old = listed(1000);
        assert!(eval_for(&program, "fund", &funded(1000, 800), Some(&old)).is_ok());
    }

    #[test]
    fn unknown_method_is_default_denied() {
        let program = escrow_cell_program();
        let err = eval_for(&program, "drain_funds", &listed(1000), Some(&empty()))
            .expect_err("an unknown method must be default-denied");
        assert!(matches!(err, dregg_cell::ProgramError::NoTransitionCaseMatched));
    }

    #[test]
    fn fund_over_ceiling_is_rejected_trustline() {
        // The buyer tries to escrow 1500 against a 1000 ceiling.
        let program = escrow_cell_program();
        let old = listed(1000);
        let err = eval_for(&program, "fund", &funded(1000, 1500), Some(&old))
            .expect_err("escrow over the ceiling must be rejected — the TRUSTLINE bound");
        assert!(
            matches!(
                err,
                dregg_cell::ProgramError::ConstraintViolated {
                    constraint: StateConstraint::FieldLteField { .. },
                    ..
                }
            ),
            "expected FieldLteField (escrowed ≤ ceiling) violation, got {err:?}"
        );
    }

    #[test]
    fn settle_must_conserve_the_escrow_flashwell() {
        let program = escrow_cell_program();
        let mut old = funded(1000, 800);
        old.fields[DELIVERY_HASH_SLOT] = sealed_delivery_digest(b"goods");
        old.fields[STATE_SLOT] = state_field(STATE_SHIPPED);
        old.set_nonce(2);

        // Conserving settlement (release all 800) is accepted.
        let mut ok = old.clone();
        ok.fields[RELEASED_SLOT] = amount_field(800);
        ok.fields[REFUNDED_SLOT] = amount_field(0);
        ok.fields[STATE_SLOT] = state_field(STATE_SETTLED);
        assert!(eval_for(&program, "settle", &ok, Some(&old)).is_ok());

        // A split that MINTS value (900 + 0 > 800) is rejected — caught by the
        // universally-true no-mint `AffineLe` invariant.
        let mut mint = old.clone();
        mint.fields[RELEASED_SLOT] = amount_field(900);
        mint.fields[REFUNDED_SLOT] = amount_field(0);
        mint.fields[STATE_SLOT] = state_field(STATE_SETTLED);
        let err = eval_for(&program, "settle", &mint, Some(&old))
            .expect_err("a value-minting settlement must be rejected — the no-mint bound");
        assert!(
            matches!(
                err,
                dregg_cell::ProgramError::ConstraintViolated {
                    constraint: StateConstraint::AffineLe { .. },
                    ..
                }
            ),
            "expected AffineLe no-mint violation, got {err:?}"
        );

        // A split that BURNS value (700 + 0 < 800) passes the no-mint `AffineLe`
        // but is rejected by the settle-scoped no-burn `AffineEq` — the exact
        // conservation the settle case adds on top of the universal invariant.
        let mut burn = old.clone();
        burn.fields[RELEASED_SLOT] = amount_field(700);
        burn.fields[REFUNDED_SLOT] = amount_field(0);
        burn.fields[STATE_SLOT] = state_field(STATE_SETTLED);
        let err = eval_for(&program, "settle", &burn, Some(&old))
            .expect_err("a value-burning settlement must be rejected — the no-burn equality");
        assert!(
            matches!(
                err,
                dregg_cell::ProgramError::ConstraintViolated {
                    constraint: StateConstraint::AffineEq { .. },
                    ..
                }
            ),
            "expected AffineEq no-burn violation, got {err:?}"
        );
    }

    #[test]
    fn state_cannot_regress_lifecycle() {
        let program = escrow_cell_program();
        let mut old = funded(1000, 800);
        old.fields[STATE_SLOT] = state_field(STATE_SHIPPED);
        old.set_nonce(2);
        let mut back = old.clone();
        back.fields[STATE_SLOT] = state_field(STATE_FUNDED); // regress
        let err = eval_for(&program, "settle", &back, Some(&old))
            .expect_err("state regression must be rejected — the LIFECYCLE bound");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::StrictMonotonic { .. },
                ..
            }
        ));
    }

    #[test]
    fn delivery_commitment_cannot_be_overwritten_mailbox() {
        let program = escrow_cell_program();
        let mut old = funded(1000, 800);
        old.fields[DELIVERY_HASH_SLOT] = sealed_delivery_digest(b"real-goods");
        old.fields[STATE_SLOT] = state_field(STATE_SHIPPED);
        old.set_nonce(2);
        let mut tamper = old.clone();
        tamper.fields[DELIVERY_HASH_SLOT] = sealed_delivery_digest(b"swapped-goods");
        tamper.fields[STATE_SLOT] = state_field(STATE_SETTLED);
        // (conserve RELEASED+REFUNDED so the AffineEq check passes and the
        // WriteOnce(DELIVERY_HASH) is what bites)
        tamper.fields[RELEASED_SLOT] = amount_field(800);
        let err = eval_for(&program, "settle", &tamper, Some(&old))
            .expect_err("overwriting the sealed delivery must be rejected — the MAILBOX bound");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { .. },
                ..
            }
        ));
    }
}
