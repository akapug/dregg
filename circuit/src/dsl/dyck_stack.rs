//! `dregg-dyck-parse-v1`: the FIRST SLICE of the *parse-as-derivation* circuit
//! (`docs/DESIGN-parse-as-derivation.md`, the zk-succinct path).
//!
//! This is the depth-bounded pushdown-stack extension of the deployed inter-row
//! chain pattern. It is authored **line-for-line on the template**
//! `crate::dsl::dfa_routing` (`dfa_routing_descriptor`): a threaded state column via
//! `ConstraintExpr::Transition`, a `ChainedHash2to1` running commitment PI-seeded
//! with `SeedHash2to1`, and a rule-membership check. The generalization the design
//! names is: **thread `D` stack cells instead of one `CURRENT_STATE`, and let the
//! "transition table" be the grammar's rule table.**
//!
//! # What it proves
//!
//! A trace satisfying this descriptor IS an accepting **leftmost pushdown replay**
//! (`Dregg2.Crypto.CfgCompact.Replay`) of the one-bracket **Dyck** grammar
//! `S → [ S ] | ε` (`CfgCompact.lean` `Reference`: `dyck`, rules `rBracket`/`rEmpty`)
//! on its input word, with the parse's per-step commitments folded into a public
//! `route_commitment`. The bundled witness proves acceptance of `"[]"` — the exact
//! word `CfgCompact.Reference.brackets_replays` accepts via `[rBracket, rEmpty]`.
//!
//! # The stack discipline (honest sizing)
//!
//! The design's §5 sketch says "`D = 2` stack". The **faithful** pushdown run for
//! `"[]"` peaks at stack `[op, S, cl]` — depth **3** — the instant `rBracket` fires
//! (`S ⟹ [ S ]` pushes three symbols). So the spike carries `D = 3` stack cells
//! (`STACK0` = top). This is a real correction to the design's undercount, recorded
//! so slice 2 sizes `D` to the true max stack depth (bracket-nesting `k` ⇒ depth
//! `2k + 1`), not to the nesting number.
//!
//! Likewise the run is **five action rows** (`rule, term, rule, term, done`), padded
//! to a power of two with `done` self-loops — not the "2–3 rows" the sketch names.
//!
//! # Symbol / rule encoding
//!
//! Stack cells hold **symbol ids**; `0` is the reserved EMPTY cell.
//! `S = 1` (the sole nonterminal), `op = '[' = 2`, `cl = ']' = 3`.
//! Rule ids: `0 = none` (term/done rows), `rBracket = 1` (`S → [ S ]`),
//! `rEmpty = 2` (`S → ε`).
//!
//! # The bound this slice accepts (documented, not hidden)
//!
//! `rBracket`'s push writes `next.STACK[0..3] = (op, S, cl)` and **ignores the stack
//! below the popped `S`** — sound only while that remainder is empty (which it is for
//! `"[]"`, and for any input whose live prefix never nests a bracket under un-consumed
//! stack). The general variable-length RHS push over a `W`-wide buffer with a
//! remainder shift (`docs/DESIGN-parse-as-derivation.md` §2, hard-part #3) is slice-2
//! work. This slice de-risks the *threading + tamper-bite* on the deployed primitives.

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_4_to_1};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Symbol / rule alphabet
// ============================================================================

/// Reserved EMPTY stack-cell marker (a cell holding no symbol).
pub const SYM_EMPTY: u32 = 0;
/// The sole nonterminal `S` (`CfgCompact.Reference.NTs.S`).
pub const SYM_S: u32 = 1;
/// Terminal `op` = `'['` (`CfgCompact.Reference.Brk.op`).
pub const SYM_OP: u32 = 2;
/// Terminal `cl` = `']'` (`CfgCompact.Reference.Brk.cl`).
pub const SYM_CL: u32 = 3;

/// No rule fires on this row (term / done rows).
pub const RULE_NONE: u32 = 0;
/// `rBracket : S → [ S ]` (`CfgCompact.Reference.rBracket`).
pub const RULE_BRACKET: u32 = 1;
/// `rEmpty : S → ε` (`CfgCompact.Reference.rEmpty`).
pub const RULE_EMPTY: u32 = 2;

/// Bounded stack depth carried in columns (top at `STACK0`). See the module header
/// for why the `"[]"` spike needs `3`, not the design sketch's `2`.
pub const STACK_D: usize = 3;

// ============================================================================
// Column / public-input indices
// ============================================================================

/// Column indices for the Dyck-parse trace.
pub mod col {
    /// `STACK[0]` — the stack top (the symbol a `rule`/`term` step reads).
    pub const STACK0: usize = 0;
    /// `STACK[1]`.
    pub const STACK1: usize = 1;
    /// `STACK[2]` — the deepest cell the `D = 3` spike carries.
    pub const STACK2: usize = 2;
    /// Current stack depth (pointer), pinned `0` at `done`, `1` at the first row.
    pub const STACK_DEPTH: usize = 3;
    /// The stack depth AFTER this row's action (witness helper; threaded into
    /// `next.STACK_DEPTH` by a `Transition`). Constrained per action selector.
    pub const DEPTH_NEXT: usize = 4;
    /// `STEP_KIND = rule` selector (binary).
    pub const IS_RULE: usize = 5;
    /// `STEP_KIND = term` selector (binary).
    pub const IS_TERM: usize = 6;
    /// `STEP_KIND = done` selector (binary).
    pub const IS_DONE: usize = 7;
    /// The production id this row fires (`RULE_*`); `RULE_NONE` on term/done rows.
    pub const RULE_ID: usize = 8;
    /// The input token read on a `term` step (the tape symbol at `INPUT_POS`).
    pub const INPUT_TOKEN: usize = 9;
    /// Input-tape pointer.
    pub const INPUT_POS: usize = 10;
    /// `INPUT_POS + 1` (witness helper; threaded into `next.INPUT_POS` on a `term`).
    pub const INPUT_POS_P1: usize = 11;
    /// Rule selector: `1` iff this row fires `rBracket` (binary, `⊆ IS_RULE`).
    pub const SEL_BRACKET: usize = 12;
    /// Rule selector: `1` iff this row fires `rEmpty` (binary, `⊆ IS_RULE`).
    pub const SEL_EMPTY: usize = 13;
    /// Per-step commitment `hash_4_to_1(RULE_ID, STACK0, INPUT_TOKEN, 0)`.
    pub const ENTRY_HASH: usize = 14;
    /// Rolling parse commitment up to and including this row.
    pub const RUNNING_HASH: usize = 15;
    /// First-row selector (gates the running-hash seed).
    pub const IS_FIRST: usize = 16;
    /// Fixed lane `= op` (a `Transition` source for pushing the constant `op`).
    pub const LANE_OP: usize = 17;
    /// Fixed lane `= cl`.
    pub const LANE_CL: usize = 18;
    /// Fixed lane `= S`.
    pub const LANE_S: usize = 19;
    /// Fixed lane `= 0` (the EMPTY push source + the 4th entry-hash lane).
    pub const LANE_ZERO: usize = 20;
}

/// Public-input indices.
pub mod pi {
    /// The grammar's initial nonterminal (`S`) — pins the first row's stack top.
    pub const INITIAL_SYMBOL: usize = 0;
    /// The input word length (the `done` step pins `INPUT_POS == INPUT_LEN`).
    pub const INPUT_LEN: usize = 1;
    /// The rule-table commitment (the running-hash seed; ties the parse to `dyck`).
    pub const TABLE_COMMITMENT: usize = 2;
    /// The parse `route_commitment` (last row's `RUNNING_HASH`).
    pub const ROUTE_COMMITMENT: usize = 3;
}

/// Trace width.
pub const DYCK_WIDTH: usize = 21;

/// Number of public inputs.
pub const DYCK_PI_COUNT: usize = 4;

// ============================================================================
// Small constraint builders (local — read `local` only)
// ============================================================================

/// `col - constant == 0` as a `Polynomial` (reads `local[col]`).
fn eq_const(c: usize, k: u32) -> ConstraintExpr {
    ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![c],
            },
            PolyTerm {
                coeff: -BabyBear::new(k),
                col_indices: vec![],
            },
        ],
    }
}

/// `a - b - k == 0` as a `Polynomial` (reads `local[a]`, `local[b]`).
fn diff_is(a: usize, b: usize, k: i64) -> ConstraintExpr {
    let kf = if k >= 0 {
        -BabyBear::new(k as u32)
    } else {
        BabyBear::new((-k) as u32)
    };
    ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![a],
            },
            PolyTerm {
                coeff: -BabyBear::ONE,
                col_indices: vec![b],
            },
            PolyTerm {
                coeff: kf,
                col_indices: vec![],
            },
        ],
    }
}

/// `sel * (rule_id - r) == 0` (a rule selector is pinned to its rule id).
fn sel_pins_rule(sel: usize, r: u32) -> ConstraintExpr {
    ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![sel, col::RULE_ID],
            },
            PolyTerm {
                coeff: -BabyBear::new(r),
                col_indices: vec![sel],
            },
        ],
    }
}

fn gated(selector_col: usize, inner: ConstraintExpr) -> ConstraintExpr {
    ConstraintExpr::Gated {
        selector_col,
        inner: Box::new(inner),
    }
}

/// A gated push/shift: `next[next_col] == local[local_col]` fires under `sel`.
fn gated_thread(sel: usize, next_col: usize, local_col: usize) -> ConstraintExpr {
    gated(
        sel,
        ConstraintExpr::Transition {
            next_col,
            local_col,
        },
    )
}

// ============================================================================
// Descriptor
// ============================================================================

/// Build the `dregg-dyck-parse-v1` descriptor for the one-bracket Dyck grammar.
///
/// The constraints (all deployed `ConstraintExpr` variants; the `dfa_routing`
/// template is cited per group):
///
/// - **selectors** — `IS_RULE`/`IS_TERM`/`IS_DONE` binary and partition (exactly one);
///   the rule sub-selectors `SEL_BRACKET`/`SEL_EMPTY` binary, partition `IS_RULE`, and
///   are pinned to their rule ids.
/// - **rule membership** (`r ∈ g.rules`) — on a `rule` row, `RULE_ID ∈ {1, 2}` via a
///   gated vanishing polynomial `(RULE_ID − 1)(RULE_ID − 2) == 0`. This is the
///   spike's rule-table check, the analogue of `dfa_routing`'s `TableFunction`
///   transition-table lookup (`dfa_routing.rs:164`) at 2 rules.
/// - **top match** — `rule`: `STACK0 == S`; `term`: `STACK0 == INPUT_TOKEN` (both
///   `Gated` equalities, the shape of the design §2 `rule`/`term` teeth).
/// - **stack threading** (the heart) — the multi-cell generalization of
///   `dfa_routing`'s single `Transition{CURRENT_STATE ← NEXT_STATE}`
///   (`dfa_routing.rs:173`): `rBracket` pushes `(op, S, cl)`; `rEmpty` and `term`
///   shift the stack down one cell. Depth threads through `DEPTH_NEXT`.
/// - **input tape** — `term` advances `INPUT_POS` by one; every non-`term` step
///   holds it (`Transition`s on the pointer).
/// - **running commitment** — `ENTRY_HASH == hash_4_to_1(RULE_ID, STACK0,
///   INPUT_TOKEN, 0)` (C1 shape), folded by `ChainedHash2to1` (`dfa_routing.rs:178`)
///   and seeded on row 0 by `SeedHash2to1` against `pi[TABLE_COMMITMENT]`
///   (`dfa_routing.rs:185`).
pub fn dyck_parse_descriptor(name: &str) -> CircuitDescriptor {
    let column = |name: &str, index: usize, kind: ColumnKind| ColumnDef {
        name: name.to_string(),
        index,
        kind,
    };

    let constraints = vec![
        // ---- selector booleans -------------------------------------------
        ConstraintExpr::Binary { col: col::IS_RULE },
        ConstraintExpr::Binary { col: col::IS_TERM },
        ConstraintExpr::Binary { col: col::IS_DONE },
        ConstraintExpr::Binary { col: col::IS_FIRST },
        ConstraintExpr::Binary {
            col: col::SEL_BRACKET,
        },
        ConstraintExpr::Binary {
            col: col::SEL_EMPTY,
        },
        // exactly one action kind: IS_RULE + IS_TERM + IS_DONE == 1.
        ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::IS_RULE],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::IS_TERM],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::IS_DONE],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![],
                },
            ],
        },
        // the rule sub-selectors partition IS_RULE: SEL_BRACKET + SEL_EMPTY == IS_RULE.
        ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::SEL_BRACKET],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::SEL_EMPTY],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![col::IS_RULE],
                },
            ],
        },
        // rule sub-selectors pinned to their ids.
        sel_pins_rule(col::SEL_BRACKET, RULE_BRACKET),
        sel_pins_rule(col::SEL_EMPTY, RULE_EMPTY),
        // ---- rule membership: on a rule row, RULE_ID ∈ {rBracket, rEmpty} --
        // (RULE_ID - 1)(RULE_ID - 2) = RULE_ID^2 - 3 RULE_ID + 2 == 0, gated on IS_RULE.
        gated(
            col::IS_RULE,
            ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![col::RULE_ID, col::RULE_ID],
                    },
                    PolyTerm {
                        coeff: -BabyBear::new(3),
                        col_indices: vec![col::RULE_ID],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(2),
                        col_indices: vec![],
                    },
                ],
            },
        ),
        // ---- top match ----------------------------------------------------
        // rule step: the popped stack top is the nonterminal S.
        gated(col::IS_RULE, eq_const(col::STACK0, SYM_S)),
        // term step: the stack top is the terminal equal to the input token.
        gated(
            col::IS_TERM,
            ConstraintExpr::Equality {
                col_a: col::STACK0,
                col_b: col::INPUT_TOKEN,
            },
        ),
        // done step: stack empty (top == 0) and depth == 0.
        gated(col::IS_DONE, eq_const(col::STACK0, SYM_EMPTY)),
        gated(col::IS_DONE, eq_const(col::STACK_DEPTH, 0)),
        // ---- lane fixes (constant push sources) ---------------------------
        eq_const(col::LANE_OP, SYM_OP),
        eq_const(col::LANE_CL, SYM_CL),
        eq_const(col::LANE_S, SYM_S),
        eq_const(col::LANE_ZERO, 0),
        // ---- input-pointer helper -----------------------------------------
        diff_is(col::INPUT_POS_P1, col::INPUT_POS, 1), // INPUT_POS_P1 == INPUT_POS + 1
        // ---- depth-delta helper (per action) ------------------------------
        // rBracket: depth += 2 (pop 1, push 3).
        gated(
            col::SEL_BRACKET,
            diff_is(col::DEPTH_NEXT, col::STACK_DEPTH, 2),
        ),
        // rEmpty: depth -= 1 (pop 1, push 0).
        gated(
            col::SEL_EMPTY,
            diff_is(col::DEPTH_NEXT, col::STACK_DEPTH, -1),
        ),
        // term: depth -= 1 (pop 1).
        gated(col::IS_TERM, diff_is(col::DEPTH_NEXT, col::STACK_DEPTH, -1)),
        // done: depth unchanged.
        gated(col::IS_DONE, diff_is(col::DEPTH_NEXT, col::STACK_DEPTH, 0)),
        // ---- per-step commitment ------------------------------------------
        // ENTRY_HASH == hash_4_to_1(RULE_ID, STACK0, INPUT_TOKEN, 0).
        ConstraintExpr::Hash4to1 {
            output_col: col::ENTRY_HASH,
            input_cols: [col::RULE_ID, col::STACK0, col::INPUT_TOKEN, col::LANE_ZERO],
        },
        // seed row 0: RUNNING_HASH == hash_2_to_1(pi[TABLE_COMMITMENT], ENTRY_HASH).
        gated(
            col::IS_FIRST,
            ConstraintExpr::SeedHash2to1 {
                output_col: col::RUNNING_HASH,
                seed_pi_index: pi::TABLE_COMMITMENT,
                input_col: col::ENTRY_HASH,
            },
        ),
        // ================= cross-row (transition) constraints ==============
        // running-hash accumulation: next.running == hash(this.running, next.entry).
        ConstraintExpr::ChainedHash2to1 {
            output_next_col: col::RUNNING_HASH,
            seed_local_col: col::RUNNING_HASH,
            input_next_col: col::ENTRY_HASH,
        },
        // depth threading: next.STACK_DEPTH == this.DEPTH_NEXT.
        ConstraintExpr::Transition {
            next_col: col::STACK_DEPTH,
            local_col: col::DEPTH_NEXT,
        },
        // input-pointer threading: term advances by 1, every other step holds.
        gated_thread(col::IS_TERM, col::INPUT_POS, col::INPUT_POS_P1),
        ConstraintExpr::InvertedGated {
            selector_col: col::IS_TERM,
            inner: Box::new(ConstraintExpr::Transition {
                next_col: col::INPUT_POS,
                local_col: col::INPUT_POS,
            }),
        },
        // ---- stack threading: rBracket push (op, S, cl) -------------------
        gated_thread(col::SEL_BRACKET, col::STACK0, col::LANE_OP),
        gated_thread(col::SEL_BRACKET, col::STACK1, col::LANE_S),
        gated_thread(col::SEL_BRACKET, col::STACK2, col::LANE_CL),
        // ---- stack threading: rEmpty pop (shift down one cell) ------------
        gated_thread(col::SEL_EMPTY, col::STACK0, col::STACK1),
        gated_thread(col::SEL_EMPTY, col::STACK1, col::STACK2),
        gated_thread(col::SEL_EMPTY, col::STACK2, col::LANE_ZERO),
        // ---- stack threading: term pop (shift down one cell) --------------
        gated_thread(col::IS_TERM, col::STACK0, col::STACK1),
        gated_thread(col::IS_TERM, col::STACK1, col::STACK2),
        gated_thread(col::IS_TERM, col::STACK2, col::LANE_ZERO),
    ];

    // Degree: the gated rule-membership polynomial is degree 3 (selector · quadratic);
    // everything else is ≤ 2. Keep headroom to match the derivation descriptor envelope.
    let max_degree = 4usize;

    let boundaries = vec![
        // first row starts at [initial]: STACK0 == pi[INITIAL_SYMBOL], depth 1.
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::STACK0,
            pi_index: pi::INITIAL_SYMBOL,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::STACK_DEPTH,
            value: BabyBear::ONE,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::INPUT_POS,
            value: BabyBear::ZERO,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::IS_FIRST,
            value: BabyBear::ONE,
        },
        // last row is an accepting `done`: depth 0, input fully consumed,
        // route_commitment bound.
        BoundaryDef::Fixed {
            row: BoundaryRow::Last,
            col: col::IS_DONE,
            value: BabyBear::ONE,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::Last,
            col: col::STACK_DEPTH,
            value: BabyBear::ZERO,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::INPUT_POS,
            pi_index: pi::INPUT_LEN,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::RUNNING_HASH,
            pi_index: pi::ROUTE_COMMITMENT,
        },
    ];

    CircuitDescriptor {
        name: name.to_string(),
        trace_width: DYCK_WIDTH,
        max_degree,
        columns: vec![
            column("stack0", col::STACK0, ColumnKind::Value),
            column("stack1", col::STACK1, ColumnKind::Value),
            column("stack2", col::STACK2, ColumnKind::Value),
            column("stack_depth", col::STACK_DEPTH, ColumnKind::Value),
            column("depth_next", col::DEPTH_NEXT, ColumnKind::Value),
            column("is_rule", col::IS_RULE, ColumnKind::Selector),
            column("is_term", col::IS_TERM, ColumnKind::Selector),
            column("is_done", col::IS_DONE, ColumnKind::Selector),
            column("rule_id", col::RULE_ID, ColumnKind::Value),
            column("input_token", col::INPUT_TOKEN, ColumnKind::Value),
            column("input_pos", col::INPUT_POS, ColumnKind::Value),
            column("input_pos_p1", col::INPUT_POS_P1, ColumnKind::Value),
            column("sel_bracket", col::SEL_BRACKET, ColumnKind::Selector),
            column("sel_empty", col::SEL_EMPTY, ColumnKind::Selector),
            column("entry_hash", col::ENTRY_HASH, ColumnKind::Hash),
            column("running_hash", col::RUNNING_HASH, ColumnKind::Hash),
            column("is_first", col::IS_FIRST, ColumnKind::Selector),
            column("lane_op", col::LANE_OP, ColumnKind::Value),
            column("lane_cl", col::LANE_CL, ColumnKind::Value),
            column("lane_s", col::LANE_S, ColumnKind::Value),
            column("lane_zero", col::LANE_ZERO, ColumnKind::Value),
        ],
        constraints,
        boundaries,
        public_input_count: DYCK_PI_COUNT,
        lookup_tables: vec![],
    }
}

/// Create a `DslCircuit` from the Dyck-parse descriptor.
pub fn dyck_parse_circuit(name: &str) -> DslCircuit {
    DslCircuit::new(dyck_parse_descriptor(name))
}

/// The rule-table commitment: `hash_2_to_1(enc(rBracket), enc(rEmpty))`, where each
/// rule is encoded `hash_4_to_1(rule_id, lhs, rhs0, rhs1)`. This is the `pi[2]`
/// running-hash seed — it ties the parse to *this* grammar (analogue of
/// `dfa_routing::compute_table_commitment`).
pub fn dyck_rule_table_commitment() -> BabyBear {
    // rBracket: S → [ S ] ; encode (id, lhs=S, rhs head = op, rhs next = S).
    let e_bracket = hash_4_to_1(&[
        BabyBear::new(RULE_BRACKET),
        BabyBear::new(SYM_S),
        BabyBear::new(SYM_OP),
        BabyBear::new(SYM_S),
    ]);
    // rEmpty: S → ε ; encode (id, lhs=S, empty, empty).
    let e_empty = hash_4_to_1(&[
        BabyBear::new(RULE_EMPTY),
        BabyBear::new(SYM_S),
        BabyBear::new(SYM_EMPTY),
        BabyBear::new(SYM_EMPTY),
    ]);
    hash_2_to_1(e_bracket, e_empty)
}

// ============================================================================
// Trace generation — the honest accepting run of "[]"
// ============================================================================

/// One machine action, before power-of-two padding.
#[derive(Clone, Copy)]
pub enum Action {
    Rule(u32), // fire production `rule_id`
    Term(u32), // match terminal `token` on top against the input tape
    Done,
}

/// Build the accepting-parse trace + public inputs for the word `"[]"` (`[op, cl]`),
/// the exact word `CfgCompact.Reference.brackets_replays` accepts.
///
/// The rows are the faithful pushdown replay:
///   `rule rBracket · term '[' · rule rEmpty · term ']' · done`,
/// padded to a power of two with `done` self-loops. Returns the row-major trace
/// (width [`DYCK_WIDTH`]) and the public inputs
/// `[initial_symbol, input_len, table_commitment, route_commitment]`.
pub fn build_brackets_witness() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let input: Vec<u32> = vec![SYM_OP, SYM_CL];
    let actions = vec![
        Action::Rule(RULE_BRACKET),
        Action::Term(SYM_OP),
        Action::Rule(RULE_EMPTY),
        Action::Term(SYM_CL),
        Action::Done,
    ];
    build_witness(&input, &actions)
}

/// General trace builder: fold `actions` over the pushdown machine, laying out one
/// row per action and padding to a power of two with `done`. Used by
/// [`build_brackets_witness`] and by the tamper test's honest baseline.
///
/// This is the prover-side companion of the descriptor: it fills every witness
/// helper column (`DEPTH_NEXT`, `INPUT_POS_P1`, `SEL_*`, the lanes, the running
/// hash) so the honest run satisfies the descriptor.
pub fn build_witness(input: &[u32], actions: &[Action]) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let table_commitment = dyck_rule_table_commitment();

    // Live machine state.
    let mut stack: Vec<u32> = vec![SYM_S]; // starts at [initial]
    let mut input_pos: u32 = 0;

    let n_pad = actions.len().next_power_of_two().max(2);
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(n_pad);
    let mut running = table_commitment;

    let emit = |stack: &[u32],
                depth_next: u32,
                input_pos: u32,
                kind: (bool, bool, bool),
                rule_id: u32,
                input_token: u32,
                sel_bracket: u32,
                sel_empty: u32,
                is_first: u32,
                running: &mut BabyBear,
                first: bool|
     -> Vec<BabyBear> {
        let top = stack.first().copied().unwrap_or(SYM_EMPTY);
        let s1 = stack.get(1).copied().unwrap_or(SYM_EMPTY);
        let s2 = stack.get(2).copied().unwrap_or(SYM_EMPTY);
        let depth = stack.len() as u32;
        let entry = hash_4_to_1(&[
            BabyBear::new(rule_id),
            BabyBear::new(top),
            BabyBear::new(input_token),
            BabyBear::ZERO,
        ]);
        if first {
            *running = hash_2_to_1(table_commitment_of(), entry);
        } else {
            *running = hash_2_to_1(*running, entry);
        }
        let mut row = vec![BabyBear::ZERO; DYCK_WIDTH];
        row[col::STACK0] = BabyBear::new(top);
        row[col::STACK1] = BabyBear::new(s1);
        row[col::STACK2] = BabyBear::new(s2);
        row[col::STACK_DEPTH] = BabyBear::new(depth);
        row[col::DEPTH_NEXT] = BabyBear::new(depth_next);
        row[col::IS_RULE] = BabyBear::new(kind.0 as u32);
        row[col::IS_TERM] = BabyBear::new(kind.1 as u32);
        row[col::IS_DONE] = BabyBear::new(kind.2 as u32);
        row[col::RULE_ID] = BabyBear::new(rule_id);
        row[col::INPUT_TOKEN] = BabyBear::new(input_token);
        row[col::INPUT_POS] = BabyBear::new(input_pos);
        row[col::INPUT_POS_P1] = BabyBear::new(input_pos + 1);
        row[col::SEL_BRACKET] = BabyBear::new(sel_bracket);
        row[col::SEL_EMPTY] = BabyBear::new(sel_empty);
        row[col::ENTRY_HASH] = entry;
        row[col::RUNNING_HASH] = *running;
        row[col::IS_FIRST] = BabyBear::new(is_first);
        row[col::LANE_OP] = BabyBear::new(SYM_OP);
        row[col::LANE_CL] = BabyBear::new(SYM_CL);
        row[col::LANE_S] = BabyBear::new(SYM_S);
        row[col::LANE_ZERO] = BabyBear::ZERO;
        row
    };

    for (i, action) in actions.iter().enumerate() {
        let is_first = if i == 0 { 1 } else { 0 };
        let first = i == 0;
        match *action {
            Action::Rule(rule_id) => {
                // depth after: pop 1, push |rhs|.
                let (sel_bracket, sel_empty, new_stack) = match rule_id {
                    RULE_BRACKET => {
                        // pop S, push [op, S, cl] (rest below assumed empty — the D=3 bound).
                        (1u32, 0u32, vec![SYM_OP, SYM_S, SYM_CL])
                    }
                    RULE_EMPTY => {
                        // pop S, push nothing → shift down.
                        (0u32, 1u32, stack[1..].to_vec())
                    }
                    _ => (0, 0, stack.clone()),
                };
                let depth_next = new_stack.len() as u32;
                rows.push(emit(
                    &stack,
                    depth_next,
                    input_pos,
                    (true, false, false),
                    rule_id,
                    /*token*/ 0,
                    sel_bracket,
                    sel_empty,
                    is_first,
                    &mut running,
                    first,
                ));
                stack = new_stack;
            }
            Action::Term(token) => {
                let depth_next = (stack.len() as u32).saturating_sub(1);
                rows.push(emit(
                    &stack,
                    depth_next,
                    input_pos,
                    (false, true, false),
                    RULE_NONE,
                    token,
                    0,
                    0,
                    is_first,
                    &mut running,
                    first,
                ));
                // pop the matched terminal, advance the tape.
                stack.remove(0);
                input_pos += 1;
            }
            Action::Done => {
                let depth_next = stack.len() as u32; // 0, unchanged
                rows.push(emit(
                    &stack,
                    depth_next,
                    input_pos,
                    (false, false, true),
                    RULE_NONE,
                    0,
                    0,
                    0,
                    is_first,
                    &mut running,
                    first,
                ));
            }
        }
    }

    // Pad to a power of two with `done` self-loops (stack empty, tape at end).
    while rows.len() < n_pad {
        let i = rows.len();
        let _ = i;
        rows.push(emit(
            &stack,
            0,
            input_pos,
            (false, false, true),
            RULE_NONE,
            0,
            0,
            0,
            0,
            &mut running,
            false,
        ));
    }

    let route_commitment = rows.last().unwrap()[col::RUNNING_HASH];
    let public_inputs = vec![
        BabyBear::new(SYM_S), // initial nonterminal
        BabyBear::new(input.len() as u32),
        dyck_rule_table_commitment(),
        route_commitment,
    ];
    (rows, public_inputs)
}

/// The rule-table commitment as a plain function (used inside the row emitter's
/// seed step). Kept separate so the closure captures nothing borrow-conflicting.
fn table_commitment_of() -> BabyBear {
    dyck_rule_table_commitment()
}

// ============================================================================
// Satisfaction predicate — the Rust `Satisfied2` driver
// ============================================================================

/// Does `expr` read the `next` row (a cross-row / transition constraint)? Such
/// constraints are enforced only on the transition domain (rows `0..n-1`), matching
/// the STARK transition vanishing polynomial that excludes the last row.
fn references_next(expr: &ConstraintExpr) -> bool {
    match expr {
        ConstraintExpr::Transition { .. } | ConstraintExpr::ChainedHash2to1 { .. } => true,
        ConstraintExpr::Gated { inner, .. }
        | ConstraintExpr::InvertedGated { inner, .. }
        | ConstraintExpr::Squared { inner } => references_next(inner),
        _ => false,
    }
}

/// **The descriptor-satisfaction predicate** — the Rust analogue of Lean `Satisfied2`:
/// every constraint evaluates to zero across the trace domain, and every boundary
/// holds. This DRIVES the deployed evaluator
/// [`ConstraintExpr::evaluate_with_tables`] (it does not re-implement the constraint
/// semantics), so a `true`/`false` here is the same accept/reject the audited
/// prover's per-row check computes.
///
/// - transition constraints (`references_next`) are checked on rows `0..n-1` with
///   `next = trace[i+1]`;
/// - per-row constraints are checked on every row (`next` unused);
/// - boundaries resolve `First`/`Last`/`Index` and check the pinned cell against
///   the public input (`PiBinding`) or the literal (`Fixed`).
pub fn dyck_satisfied(desc: &CircuitDescriptor, trace: &[Vec<BabyBear>], pi: &[BabyBear]) -> bool {
    let n = trace.len();
    if n == 0 {
        return false;
    }
    for c in &desc.constraints {
        if references_next(c) {
            for i in 0..n - 1 {
                if c.evaluate(&trace[i], &trace[i + 1], pi) != BabyBear::ZERO {
                    return false;
                }
            }
        } else {
            for i in 0..n {
                let next = &trace[(i + 1).min(n - 1)];
                if c.evaluate(&trace[i], next, pi) != BabyBear::ZERO {
                    return false;
                }
            }
        }
    }
    for b in &desc.boundaries {
        let (row, value) = match b {
            BoundaryDef::PiBinding { row, col, pi_index } => {
                let r = resolve_row(row, n);
                (trace[r][*col], pi[*pi_index])
            }
            BoundaryDef::Fixed { row, col, value } => {
                let r = resolve_row(row, n);
                (trace[r][*col], *value)
            }
        };
        if row != value {
            return false;
        }
    }
    true
}

fn resolve_row(row: &BoundaryRow, n: usize) -> usize {
    match row {
        BoundaryRow::First => 0,
        BoundaryRow::Last => n - 1,
        BoundaryRow::Index(i) => *i,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const NAME: &str = "dregg-dyck-parse-v1";

    #[test]
    fn descriptor_is_deployable() {
        let desc = dyck_parse_descriptor(NAME);
        desc.validate().expect("dyck descriptor must validate");
    }

    #[test]
    fn brackets_accepts() {
        let desc = dyck_parse_descriptor(NAME);
        let (trace, pi) = build_brackets_witness();
        assert!(
            dyck_satisfied(&desc, &trace, &pi),
            "the honest '[]' parse must satisfy the descriptor"
        );
    }
}
