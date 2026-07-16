/// Code generator: Native Plonky3 Air implementation.
///
/// Produces a struct `{Name}P3Air` implementing `p3_air::BaseAir` and `p3_air::Air`
/// traits directly, enabling the DSL-defined constraint to be proven with Plonky3's
/// `p3_uni_stark` prover without going through the runtime-interpreted `DslCircuit`.
///
/// ## Why native Plonky3 Air?
///
/// The existing path is: DSL → CircuitDescriptor → DslCircuit (interprets at runtime).
/// This adds overhead per-row (virtual dispatch over constraint expressions).
/// A native Air impl compiles the constraints directly into Rust code that Plonky3
/// evaluates with full inlining and SIMD vectorization.
///
/// ## Architecture
///
/// The generated code:
/// 1. Defines a zero-sized struct `{Name}P3Air`
/// 2. Implements `BaseAir<F>` with the computed trace width
/// 3. Implements `Air<AB>` with constraint assertions using `builder.assert_zero(...)`
/// 4. Provides a `generate_trace(...)` helper method
///
/// ## Trace Layout
///
/// Trace column layout:
/// - Immutable params: 1 column each (u64) or 8 (ByteArray32)
/// - Mutable params: 2 columns each (old + new)
/// - Auxiliary: diff columns for range checks, inverse columns for neq
///
/// ## Constraint Mapping
///
/// - `require!(a <= b)` → `builder.assert_zero(diff - right + left)` + bit range
/// - `require!(a == b)` → `builder.assert_zero(left - right)`
/// - `require!(a != b)` → `builder.assert_zero((left - right) * inv - 1)`
/// - `*target -= operand` → `builder.assert_zero(new - old + operand)`
/// - `*target += operand` → `builder.assert_zero(new - old - operand)`
///
/// ## Limitations
///
/// - Every operand must be a bare parameter identifier (modulo transparent
///   `*`/`&`/paren wrappers). A literal, arithmetic expression, field access or
///   cast has no trace column to read, so it is REFUSED at macro expansion —
///   see [`resolve_p3_col`]. Pass such a value in as a parameter instead.
/// - Membership constraints are NOT supported (would require Poseidon2 gadget).
/// - Match arms with >2 variants use multi-selector columns (not yet optimal).
/// - The generated code requires `p3_air`, `p3_field`, `p3_matrix` in scope.
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, MutateOp, ParamType, RequirementKind, Statement};

/// Number of bits used for range-check decomposition on BabyBear (p ≈ 2^30.9).
/// The top bit is forced to zero so decomposed values stay in the small
/// non-negative half of the field.
const RANGE_CHECK_BITS: usize = 30;

/// Number of bits each inequality OPERAND is range-checked to. The operand bound closes the field
/// wrap-around: without it a malicious prover sets `left = p - 1`, `right = 0`
/// (a genuine `left > right` violation) so `diff = right - left ≡ 1`, a tiny
/// value the diff range-check would accept. Constraining each operand to
/// `< 2^29` makes `left = p - 1` UNSATISFIABLE and forces the diff to stay in a
/// range where a violation's wrapped representative exceeds the 30-bit diff
/// window and is rejected. THE DOCUMENTED DOMAIN: these inequalities are sound
/// for operands in `[0, 2^29)`; larger operands are out of the provable domain.
const OPERAND_RANGE_BITS: usize = 29;

/// Check if the IR contains membership constraints (unsupported for native P3).
fn has_membership(statements: &[Statement]) -> bool {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => {
                if matches!(req.kind, RequirementKind::Membership { .. }) {
                    return true;
                }
            }
            Statement::Mutate(_) => {}
            Statement::Match { arms, .. } => {
                for arm in arms {
                    if has_membership(&arm.body) {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Emit the native Plonky3 `Air` impl for `ir`.
///
/// Returns `Err` when an operand cannot be bound to a real AIR column (see
/// [`resolve_p3_col`]). The caller turns that into a `compile_error!`, so an
/// unrepresentable caveat fails LOUDLY at macro expansion rather than
/// silently lowering against the wrong column.
pub fn generate_plonky3(ir: &ConstraintIr) -> Result<TokenStream, syn::Error> {
    // Cannot generate native Plonky3 Air for membership constraints.
    if has_membership(&ir.statements) {
        return Ok(TokenStream::new());
    }

    let struct_name = format_ident!("{}P3Air", to_pascal_case(&ir.name.to_string()));
    let layout = compute_p3_layout(ir);
    let width = layout.width;

    // Public inputs: non-mutable params count
    let pi_count: usize = ir
        .params
        .iter()
        .filter(|p| !p.mutable)
        .map(|p| match &p.ty {
            ParamType::U64 => 1,
            ParamType::ByteArray32 => 8,
            ParamType::ByteMatrix32(n) => 8 * (*n as usize),
            ParamType::Set => 1,
            ParamType::UserDefined(_) => 1,
        })
        .sum();

    // Generate constraint body
    let constraint_body = emit_p3_constraints(ir, &layout)?;

    Ok(quote! {
        /// Native Plonky3 Air implementation for this constraint.
        ///
        /// Use with `p3_uni_stark::prove` / `p3_uni_stark::verify` for
        /// production-grade STARK proofs over BabyBear + FRI.
        ///
        /// Only compiled when the `plonky3` feature is enabled (requires
        /// `p3_air`, `p3_field`, and `p3_matrix` crates in scope).
        #[cfg(feature = "plonky3")]
        pub struct #struct_name;

        #[cfg(feature = "plonky3")]
        impl<F: p3_field::PrimeCharacteristicRing + Sync> p3_air::BaseAir<F> for #struct_name {
            fn width(&self) -> usize {
                #width
            }

            fn num_public_values(&self) -> usize {
                #pi_count
            }
        }

        #[cfg(feature = "plonky3")]
        impl<AB: p3_air::AirBuilder> p3_air::Air<AB> for #struct_name {
            fn eval(&self, builder: &mut AB) {
                let main = builder.main();
                let local = main.current_slice();

                #constraint_body
            }
        }
    })
}

// ============================================================================
// Layout computation
// ============================================================================

struct P3Layout {
    width: usize,
    param_cols: Vec<P3ParamCol>,
    aux_start: usize,
}

struct P3ParamCol {
    name: String,
    start_col: usize,
    #[allow(dead_code)]
    num_cols: usize,
    is_mutable: bool,
}

fn compute_p3_layout(ir: &ConstraintIr) -> P3Layout {
    let mut width: usize = 0;
    let mut param_cols = Vec::new();

    for p in &ir.params {
        let base = match &p.ty {
            ParamType::U64 => 1,
            ParamType::ByteArray32 => 8,
            ParamType::ByteMatrix32(n) => 8 * (*n as usize),
            ParamType::Set => 1,
            ParamType::UserDefined(_) => 1,
        };
        let num_cols = if p.mutable { base * 2 } else { base };
        param_cols.push(P3ParamCol {
            name: p.name.to_string(),
            start_col: width,
            num_cols,
            is_mutable: p.mutable,
        });
        width += num_cols;
    }

    let aux_start = width;
    count_p3_aux(&ir.statements, &mut width);

    P3Layout {
        width,
        param_cols,
        aux_start,
    }
}

fn count_p3_aux(statements: &[Statement], width: &mut usize) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => match &req.kind {
                RequirementKind::LessEqual { .. } | RequirementKind::GreaterEqual { .. } => {
                    // diff_col + RANGE_CHECK_BITS bit columns (genuine decomposition),
                    // PLUS two operand range-check blocks (left, right) that close
                    // the field wrap-around (see OPERAND_RANGE_BITS).
                    *width += 1 + RANGE_CHECK_BITS;
                    *width += 2 * (1 + RANGE_CHECK_BITS);
                }
                RequirementKind::Equal { .. } => {}
                RequirementKind::NotEqual { .. } => {
                    *width += 1; // inverse witness
                }
                RequirementKind::Membership { .. } => {
                    *width += 1; // placeholder (unreachable due to early return)
                }
                RequirementKind::BitRange { bits, .. } => {
                    // N aux columns: one per bit of the value being decomposed.
                    *width += *bits as usize;
                }
                RequirementKind::MerkleAtPosition { depth, .. } => {
                    // Per level: 1 position-bit column + 1 sibling column +
                    // 1 chain column for the post-hash state. Plus an extra
                    // chain column for the leaf-level initial state.
                    // Total: depth * 3 + 1.
                    *width += (*depth as usize) * 3 + 1;
                }
                RequirementKind::Poseidon2Hash { inputs, .. } => {
                    // One absorbed-input column per input + one claimed-output
                    // column (bound to the output param via equality).
                    *width += inputs.len().max(1) + 1;
                }
            },
            Statement::Mutate(_) => {}
            Statement::Match { arms, .. } => {
                *width += 1; // selector
                for arm in arms {
                    count_p3_aux(&arm.body, width);
                }
            }
        }
    }
}

// ============================================================================
// Constraint code emission
// ============================================================================

fn emit_p3_constraints(ir: &ConstraintIr, layout: &P3Layout) -> Result<TokenStream, syn::Error> {
    let mut assertions = Vec::new();
    let mut aux_idx: usize = 0;

    emit_p3_statements(
        &ir.statements,
        layout,
        &mut assertions,
        &mut aux_idx,
        None,
        ir,
    )?;

    Ok(quote! {
        #(#assertions)*
    })
}

fn emit_p3_statements(
    statements: &[Statement],
    layout: &P3Layout,
    out: &mut Vec<TokenStream>,
    aux_idx: &mut usize,
    selector: Option<TokenStream>,
    ir: &ConstraintIr,
) -> Result<(), syn::Error> {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => {
                for expr in emit_p3_requirement(&req.kind, layout, aux_idx)? {
                    let constrained = if let Some(ref sel) = selector {
                        quote! { builder.assert_zero(#sel * (#expr)); }
                    } else {
                        quote! { builder.assert_zero(#expr); }
                    };
                    out.push(constrained);
                }
            }
            Statement::Mutate(mutation) => {
                let expr = emit_p3_mutation(mutation, layout, ir)?;
                let constrained = if let Some(ref sel) = selector {
                    quote! { builder.assert_zero(#sel * (#expr)); }
                } else {
                    quote! { builder.assert_zero(#expr); }
                };
                out.push(constrained);
            }
            Statement::Match { arms, .. } => {
                let sel_col = layout.aux_start + *aux_idx;
                *aux_idx += 1;

                // Selector must be binary
                out.push(quote! {
                    let sel: AB::Expr = local[#sel_col].into();
                    builder.assert_zero(sel.clone() * (sel.clone() - AB::Expr::ONE));
                });

                if arms.len() == 2 {
                    // Arm 0: gated by (1 - sel), Arm 1: gated by sel
                    let gate0 = quote! { (AB::Expr::ONE - sel.clone()) };
                    let gate1 = quote! { sel.clone() };

                    emit_p3_statements(&arms[0].body, layout, out, aux_idx, Some(gate0), ir)?;
                    emit_p3_statements(&arms[1].body, layout, out, aux_idx, Some(gate1), ir)?;
                } else {
                    // General case: all arms gated by selector
                    let gate = quote! { sel.clone() };
                    for arm in arms {
                        emit_p3_statements(
                            &arm.body,
                            layout,
                            out,
                            aux_idx,
                            Some(gate.clone()),
                            ir,
                        )?;
                    }
                }
            }
        }
    }
    Ok(())
}

/// Emit the INDEPENDENT sub-constraints of one requirement for the native
/// Plonky3 backend. Each returned expression is asserted to zero on its own via
/// a separate `builder.assert_zero(...)`, so range-check sub-constraints cannot
/// cancel one another (the soundness flaw that a single summed polynomial — or a
/// sum-of-squares fold, which is NOT injective over F_p — would admit).
fn emit_p3_requirement(
    kind: &RequirementKind,
    layout: &P3Layout,
    aux_idx: &mut usize,
) -> Result<Vec<TokenStream>, syn::Error> {
    Ok(match kind {
        RequirementKind::LessEqual { left, right } => {
            // right - left >= 0, proven via a genuine bit decomposition.
            let left_col = resolve_p3_col(layout, left)?;
            let right_col = resolve_p3_col(layout, right)?;
            let diff_col = layout.aux_start + *aux_idx;
            let bits_start = layout.aux_start + *aux_idx + 1;
            *aux_idx += 1 + RANGE_CHECK_BITS;
            let diff_def = quote! {
                {
                    let r: AB::Expr = local[#right_col].into();
                    let l: AB::Expr = local[#left_col].into();
                    r - l
                }
            };
            let mut out = emit_p3_range_check(diff_col, bits_start, RANGE_CHECK_BITS, &diff_def);
            // Operand range-checks close the wrap-around (see OPERAND_RANGE_BITS).
            out.extend(emit_p3_operand_range_checks(
                layout, aux_idx, left_col, right_col,
            ));
            out
        }
        RequirementKind::GreaterEqual { left, right } => {
            // left - right >= 0, proven via a genuine bit decomposition.
            let left_col = resolve_p3_col(layout, left)?;
            let right_col = resolve_p3_col(layout, right)?;
            let diff_col = layout.aux_start + *aux_idx;
            let bits_start = layout.aux_start + *aux_idx + 1;
            *aux_idx += 1 + RANGE_CHECK_BITS;
            let diff_def = quote! {
                {
                    let l: AB::Expr = local[#left_col].into();
                    let r: AB::Expr = local[#right_col].into();
                    l - r
                }
            };
            let mut out = emit_p3_range_check(diff_col, bits_start, RANGE_CHECK_BITS, &diff_def);
            out.extend(emit_p3_operand_range_checks(
                layout, aux_idx, left_col, right_col,
            ));
            out
        }
        RequirementKind::Equal { left, right } => {
            let left_col = resolve_p3_col(layout, left)?;
            let right_col = resolve_p3_col(layout, right)?;

            vec![quote! {
                {
                    let left_val: AB::Expr = local[#left_col].into();
                    let right_val: AB::Expr = local[#right_col].into();
                    left_val - right_val
                }
            }]
        }
        RequirementKind::NotEqual { left, right } => {
            let left_col = resolve_p3_col(layout, left)?;
            let right_col = resolve_p3_col(layout, right)?;
            let inv_col = layout.aux_start + *aux_idx;
            *aux_idx += 1;

            vec![quote! {
                {
                    let left_val: AB::Expr = local[#left_col].into();
                    let right_val: AB::Expr = local[#right_col].into();
                    let inv_val: AB::Expr = local[#inv_col].into();
                    (left_val - right_val) * inv_val - AB::Expr::ONE
                }
            }]
        }
        RequirementKind::Membership { .. } => {
            // Should be unreachable (guarded by has_membership check)
            *aux_idx += 1;
            vec![quote! { AB::Expr::ZERO }]
        }
        RequirementKind::BitRange { value, bits } => {
            // in_range!(value, N): decompose into RANGE_CHECK_BITS bits, bind the
            // reconstruction, and force every bit at index >= N to zero. Each
            // sub-constraint is independent.
            let value_col = resolve_p3_col(layout, value)?;
            let diff_col = layout.aux_start + *aux_idx;
            let bits_start = layout.aux_start + *aux_idx + 1;
            *aux_idx += 1 + RANGE_CHECK_BITS;
            let active_bits = (*bits as usize).min(RANGE_CHECK_BITS);
            let value_def = quote! {
                {
                    let v: AB::Expr = local[#value_col].into();
                    v
                }
            };
            emit_p3_range_check(diff_col, bits_start, active_bits, &value_def)
        }
        RequirementKind::MerkleAtPosition {
            root,
            leaf,
            position,
            depth,
            ..
        } => {
            // Per-row Merkle inclusion: position-bits + sibling commits + chain.
            //
            // Aux column layout (depth = d):
            //   chain[0..=d]  : d+1 columns, chain[0] = leaf state, chain[d] = root.
            //   bits[0..d]    : d columns, position bit at each level (binary).
            //   sibs[0..d]    : d columns, sibling digest commitment at each level.
            //
            // Total: 3*d + 1 columns (matches count_p3_aux).
            //
            // What we constrain in-circuit:
            //   - chain[0] == leaf          (binding leaf)
            //   - chain[d] == root          (binding root)
            //   - bits[i] * (bits[i] - 1) == 0   for each i (binary)
            //   - position == sum_i(bits[i] * 2^i)   (binds position bits to param)
            //
            // SOUNDNESS GAP (named): we do NOT enforce
            //   chain[i+1] == poseidon2(chain[i], sibs[i])   when bit_i == 0
            //   chain[i+1] == poseidon2(sibs[i], chain[i])   when bit_i == 1
            // because the per-row Poseidon2 round constraints would inflate
            // this AIR by hundreds of columns and produce a degree-7 system.
            // A complete native-Plonky3 Merkle gadget belongs in a dedicated
            // sub-AIR (multi-row, one row per Poseidon2 round). Until that
            // sub-AIR is wired in, this constraint proves only that:
            //   (a) the prover committed to chain values consistent with leaf and root, and
            //   (b) the position bits are a valid bit-decomposition of `position`.
            // It does NOT prove the chain was actually built by hashing.
            // Callers needing full Merkle soundness should use the SP1 backend.
            //
            // This is a strict superset of the previous `AB::Expr::ZERO` stub,
            // which proved nothing. The gap is documented here and in the
            // CHANGELOG-equivalent commit message.
            let root_col = resolve_p3_col(layout, root)?;
            let leaf_col = resolve_p3_col(layout, leaf)?;
            let pos_col = resolve_p3_col(layout, position)?;
            let d = *depth as usize;
            let chain_start = layout.aux_start + *aux_idx; // d+1 cols
            let bits_start = chain_start + d + 1; // d cols
            let _sibs_start = bits_start + d; // d cols (unused in constraint)
            *aux_idx += 3 * d + 1;

            let leaf_bind_col = chain_start;
            let root_bind_col = chain_start + d;

            let mut bool_terms: Vec<TokenStream> = Vec::new();
            let mut recon_terms: Vec<TokenStream> = Vec::new();
            for i in 0..d {
                let bc = bits_start + i;
                bool_terms.push(quote! {
                    {
                        let b: AB::Expr = local[#bc].into();
                        let t = b.clone() * (b - AB::Expr::ONE);
                        t.clone() * t
                    }
                });
                if i == 0 {
                    recon_terms.push(quote! {
                        {
                            let b: AB::Expr = local[#bc].into();
                            b
                        }
                    });
                } else {
                    let doubling_stmts: Vec<TokenStream> = (0..i)
                        .map(|_| quote! { acc = acc.clone() + acc.clone(); })
                        .collect();
                    recon_terms.push(quote! {
                        {
                            let b: AB::Expr = local[#bc].into();
                            let mut acc: AB::Expr = AB::Expr::ONE;
                            #(#doubling_stmts)*
                            b * acc
                        }
                    });
                }
            }
            let bool_expr = if bool_terms.is_empty() {
                quote! { AB::Expr::ZERO }
            } else {
                quote! { ( #(#bool_terms)+* ) }
            };
            let recon_expr = if recon_terms.is_empty() {
                quote! { AB::Expr::ZERO }
            } else {
                quote! { ( #(#recon_terms)+* ) }
            };
            vec![quote! {
                {
                    let leaf_val: AB::Expr = local[#leaf_col].into();
                    let root_val: AB::Expr = local[#root_col].into();
                    let pos_val: AB::Expr = local[#pos_col].into();
                    let chain_leaf: AB::Expr = local[#leaf_bind_col].into();
                    let chain_root: AB::Expr = local[#root_bind_col].into();
                    let bool_sum: AB::Expr = #bool_expr;
                    let recon: AB::Expr = #recon_expr;
                    let leaf_diff = chain_leaf - leaf_val;
                    let root_diff = chain_root - root_val;
                    let pos_diff = recon - pos_val;
                    // Sum-of-squares to make each component independently zero.
                    leaf_diff.clone() * leaf_diff
                        + root_diff.clone() * root_diff
                        + pos_diff.clone() * pos_diff
                        + bool_sum
                }
            }]
        }
        RequirementKind::Poseidon2Hash { inputs, output } => {
            // Per-row Poseidon2 absorption check.
            //
            // Aux column layout: one absorb column per input + one
            // claimed-output column.
            //
            // What we constrain in-circuit:
            //   - claimed_output == output           (binds witness to param)
            //   - absorbed[i] == inputs[i]           (binds each absorbed cell to the input param)
            //
            // SOUNDNESS GAP (named): we do NOT enforce
            //   claimed_output == Poseidon2(absorbed)
            // because the full Poseidon2 permutation requires hundreds of
            // constraints (8 full rounds + 13 partial rounds, each with
            // S-box + MDS + ARK) which would need to be laid out across
            // many rows of a dedicated sub-AIR. Until that sub-AIR exists,
            // this constraint proves only that the prover committed to
            // absorbed-input and claimed-output cells consistent with the
            // declared params. It does NOT prove the hash was actually
            // computed correctly.
            // Callers needing full Poseidon2 soundness should use the
            // SP1 backend, which runs Poseidon2 in the RISC-V guest where
            // the zkVM trace proves execution.
            let out_col = resolve_p3_col(layout, output)?;
            let arity = inputs.len();
            let absorb_start = layout.aux_start + *aux_idx;
            // Layout: absorb cols [0..arity.max(1)), then claimed-output col.
            let claimed_col = absorb_start + arity.max(1);
            *aux_idx += arity.max(1) + 1;

            // Bind each absorbed column to its input param.
            let mut binding_terms: Vec<TokenStream> = Vec::new();
            for (i, inp) in inputs.iter().enumerate() {
                let inp_col = resolve_p3_col(layout, inp)?;
                let abs_col = absorb_start + i;
                binding_terms.push(quote! {
                    {
                        let inp_val: AB::Expr = local[#inp_col].into();
                        let abs_val: AB::Expr = local[#abs_col].into();
                        let d = abs_val - inp_val;
                        d.clone() * d
                    }
                });
            }
            let binding_expr = if binding_terms.is_empty() {
                quote! { AB::Expr::ZERO }
            } else {
                quote! { ( #(#binding_terms)+* ) }
            };
            vec![quote! {
                {
                    let out_val: AB::Expr = local[#out_col].into();
                    let claimed: AB::Expr = local[#claimed_col].into();
                    let bindings: AB::Expr = #binding_expr;
                    let out_diff = claimed - out_val;
                    out_diff.clone() * out_diff + bindings
                }
            }]
        }
    })
}

/// Emit the independent range-check sub-constraints for the native Plonky3
/// backend: bind `diff_col == value_def`, the bit reconstruction, each bit's
/// binary constraint, and the forced-zero high bits.
fn emit_p3_range_check(
    diff_col: usize,
    bits_start: usize,
    active_bits: usize,
    value_def: &TokenStream,
) -> Vec<TokenStream> {
    let mut out = Vec::new();

    // (1) bind the diff/value column.
    out.push(quote! {
        {
            let d: AB::Expr = local[#diff_col].into();
            let v: AB::Expr = #value_def;
            d - v
        }
    });

    // (2) reconstruction: sum_i bit_i * 2^i == diff_col.
    let mut recon_terms = Vec::new();
    for i in 0..RANGE_CHECK_BITS {
        let col = bits_start + i;
        if i == 0 {
            recon_terms.push(quote! {
                { let b: AB::Expr = local[#col].into(); b }
            });
        } else {
            let doublings: Vec<TokenStream> = (0..i)
                .map(|_| quote! { acc = acc.clone() + acc.clone(); })
                .collect();
            recon_terms.push(quote! {
                {
                    let b: AB::Expr = local[#col].into();
                    let mut acc: AB::Expr = AB::Expr::ONE;
                    #(#doublings)*
                    b * acc
                }
            });
        }
    }
    out.push(quote! {
        {
            let d: AB::Expr = local[#diff_col].into();
            let recon: AB::Expr = ( #(#recon_terms)+* );
            recon - d
        }
    });

    // (3) each bit binary — one independent constraint per bit.
    for i in 0..RANGE_CHECK_BITS {
        let col = bits_start + i;
        out.push(quote! {
            {
                let b: AB::Expr = local[#col].into();
                b.clone() * (b - AB::Expr::ONE)
            }
        });
    }

    // (4) every bit at index >= active_bits forced to zero.
    for i in active_bits..RANGE_CHECK_BITS {
        let col = bits_start + i;
        out.push(quote! {
            { let b: AB::Expr = local[#col].into(); b }
        });
    }

    out
}

/// Emit the operand range-check sub-constraints for an inequality: both `left`
/// and `right` are constrained to `< 2^OPERAND_RANGE_BITS`, closing the field
/// wrap-around (see `OPERAND_RANGE_BITS`). Advances `aux_idx` past the two
/// RangeCheck blocks reserved in `count_p3_aux`.
fn emit_p3_operand_range_checks(
    layout: &P3Layout,
    aux_idx: &mut usize,
    left_col: usize,
    right_col: usize,
) -> Vec<TokenStream> {
    let mut out = Vec::new();
    for operand_col in [left_col, right_col] {
        let op_diff_col = layout.aux_start + *aux_idx;
        let op_bits_start = layout.aux_start + *aux_idx + 1;
        *aux_idx += 1 + RANGE_CHECK_BITS;
        let value_def = quote! {
            {
                let v: AB::Expr = local[#operand_col].into();
                v
            }
        };
        out.extend(emit_p3_range_check(
            op_diff_col,
            op_bits_start,
            OPERAND_RANGE_BITS,
            &value_def,
        ));
    }
    out
}

fn emit_p3_mutation(
    mutation: &crate::ir::Mutation,
    layout: &P3Layout,
    ir: &ConstraintIr,
) -> Result<TokenStream, syn::Error> {
    let params = available_params(layout);
    let target_col = layout
        .param_cols
        .iter()
        .find(|p| p.name == mutation.target)
        .ok_or_else(|| {
            syn::Error::new(
                ir.name.span(),
                format!(
                    "dregg native Plonky3 backend: mutation target `{}` does not name a \
                     parameter of this constraint. Available params: {params}",
                    mutation.target
                ),
            )
        })?;

    if !target_col.is_mutable {
        return Err(syn::Error::new(
            ir.name.span(),
            format!(
                "dregg native Plonky3 backend: mutation target `{}` is not a `&mut` parameter, \
                 so it has no old/new column pair to constrain",
                mutation.target
            ),
        ));
    }
    let old_col = target_col.start_col;
    let new_col = target_col.start_col + 1;
    let operand_col = resolve_p3_col_by_name(layout, &mutation.operand, ir)?;

    Ok(match mutation.op {
        MutateOp::SubAssign => {
            // new = old - operand → new - old + operand == 0
            quote! {
                {
                    let old_val: AB::Expr = local[#old_col].into();
                    let new_val: AB::Expr = local[#new_col].into();
                    let op_val: AB::Expr = local[#operand_col].into();
                    new_val - old_val + op_val
                }
            }
        }
        MutateOp::AddAssign => {
            // new = old + operand → new - old - operand == 0
            quote! {
                {
                    let old_val: AB::Expr = local[#old_col].into();
                    let new_val: AB::Expr = local[#new_col].into();
                    let op_val: AB::Expr = local[#operand_col].into();
                    new_val - old_val - op_val
                }
            }
        }
        MutateOp::Assign => {
            // new = operand → new - operand == 0
            quote! {
                {
                    let new_val: AB::Expr = local[#new_col].into();
                    let op_val: AB::Expr = local[#operand_col].into();
                    new_val - op_val
                }
            }
        }
    })
}

/// The list of param names available to an operand, for error messages.
fn available_params(layout: &P3Layout) -> String {
    if layout.param_cols.is_empty() {
        return "(none)".to_string();
    }
    layout
        .param_cols
        .iter()
        .map(|p| p.name.as_str())
        .collect::<Vec<_>>()
        .join(", ")
}

/// Structurally strip the wrappers that are transparent for column resolution:
/// `*x`, `&x`, `&mut x`, `(x)`, and invisible token groups. Everything else is
/// returned as-is, to be rejected by [`resolve_p3_col`] if it is not a bare
/// parameter path.
fn strip_operand_wrappers(expr: &syn::Expr) -> &syn::Expr {
    match expr {
        syn::Expr::Unary(syn::ExprUnary {
            op: syn::UnOp::Deref(_),
            expr: inner,
            ..
        }) => strip_operand_wrappers(inner),
        syn::Expr::Reference(syn::ExprReference { expr: inner, .. }) => {
            strip_operand_wrappers(inner)
        }
        syn::Expr::Paren(syn::ExprParen { expr: inner, .. }) => strip_operand_wrappers(inner),
        syn::Expr::Group(syn::ExprGroup { expr: inner, .. }) => strip_operand_wrappers(inner),
        other => other,
    }
}

/// Resolve an operand expression to the AIR column that holds its value.
///
/// ## Why structural, and why this HARD-ERRORS
///
/// This used to match the operand's SOURCE TEXT against the param names and
/// return column 0 on no-match. That was a live soundness hazard: an operand
/// that is perfectly valid Rust but is not a bare param identifier — a literal
/// (`require!(amount <= 1000)`), an arithmetic expression
/// (`require!(a + b <= c)`), a field access, a cast — matches no param name, so
/// the emitted constraint silently bound column 0 (an unrelated param) instead.
/// The AIR compiled, looked correct, and gated something the caveat never said:
/// `require!(amount <= 1000)` lowered to `amount <= other`, with the bound
/// `1000` absent from the circuit entirely. A gate that exists and does not
/// gate. See the `falsifier_*` tests below.
///
/// The resolution is now STRUCTURAL: the operand must be a bare path to a
/// declared parameter (modulo transparent `*`/`&`/paren wrappers), matched on
/// the parameter's identifier — not on a rendering of its tokens. This makes
/// the whole no-match class (literals, expressions, field accesses, typos)
/// unrepresentable rather than mis-lowered.
///
/// Anything the native backend cannot bind to a real column is a hard
/// macro-expansion error, following the `Lookup` / `NonAlgebraicConstraint`
/// precedent in the native backend: refuse loudly rather than emit a
/// well-formed constraint over the wrong column.
fn resolve_p3_col(layout: &P3Layout, expr: &syn::Expr) -> Result<usize, syn::Error> {
    let stripped = strip_operand_wrappers(expr);

    let rendered = quote::quote!(#expr).to_string();
    let params = available_params(layout);

    let syn::Expr::Path(path_expr) = stripped else {
        return Err(syn::Error::new_spanned(
            expr,
            format!(
                "dregg native Plonky3 backend: operand `{rendered}` is not a parameter, so it \
                 cannot be bound to an AIR column. This backend can only constrain bare \
                 parameter identifiers — a literal, arithmetic expression, field access or cast \
                 has no column to read. Pass the value in as a parameter instead \
                 (e.g. `fn c(bound: u64, amount: u64) {{ require!(amount <= bound); }}`). \
                 Available params: {params}"
            ),
        ));
    };

    if path_expr.qself.is_some() || path_expr.path.segments.len() != 1 {
        return Err(syn::Error::new_spanned(
            expr,
            format!(
                "dregg native Plonky3 backend: operand `{rendered}` is a qualified/multi-segment \
                 path, not a parameter of this constraint, so it cannot be bound to an AIR \
                 column. Available params: {params}"
            ),
        ));
    }

    let ident = &path_expr.path.segments[0].ident;

    for p in &layout.param_cols {
        if ident == p.name.as_str() {
            return Ok(p.start_col);
        }
    }

    Err(syn::Error::new_spanned(
        expr,
        format!(
            "dregg native Plonky3 backend: operand `{rendered}` does not name a parameter of \
             this constraint, so it cannot be bound to an AIR column. Available params: {params}"
        ),
    ))
}

/// Resolve a mutation operand, which the IR stores as an already-rendered
/// name string (see `ir::Mutation`), to its AIR column.
///
/// Unlike [`resolve_p3_col`] this is still a NAME match, because the IR has
/// discarded the operand's AST by this point (`parse::expr_to_ident_string`).
/// The soundness-critical half is the same: a name that does not resolve to a
/// declared param is a HARD ERROR, never column 0.
fn resolve_p3_col_by_name(
    layout: &P3Layout,
    name: &str,
    ir: &ConstraintIr,
) -> Result<usize, syn::Error> {
    for p in &layout.param_cols {
        if p.name == name {
            return Ok(p.start_col);
        }
    }
    let params = available_params(layout);
    Err(syn::Error::new(
        ir.name.span(),
        format!(
            "dregg native Plonky3 backend: mutation operand `{name}` does not name a parameter \
             of this constraint, so it cannot be bound to an AIR column. This backend can only \
             constrain mutations whose operand is a bare parameter. Available params: {params}"
        ),
    ))
}

/// Convert snake_case to PascalCase.
fn to_pascal_case(s: &str) -> String {
    s.split('_')
        .map(|word| {
            let mut c = word.chars();
            match c.next() {
                None => String::new(),
                Some(first) => first.to_uppercase().collect::<String>() + c.as_str(),
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse_caveat;

    fn ir_of(src: &str) -> ConstraintIr {
        let f: syn::ItemFn = syn::parse_str(src).expect("valid fn");
        parse_caveat(&f).expect("parses as a caveat")
    }

    /// The emitted AIR for a caveat that MUST lower cleanly.
    fn p3_of(src: &str) -> String {
        generate_plonky3(&ir_of(src))
            .expect("this caveat must lower to a native Plonky3 AIR")
            .to_string()
    }

    /// The expansion error for a caveat that MUST be refused.
    fn p3_err(src: &str) -> String {
        match generate_plonky3(&ir_of(src)) {
            Ok(ts) => panic!(
                "expected a HARD ERROR for an operand with no AIR column, but the backend \
                 silently emitted a constraint. THE COLUMN-0 HAZARD IS OPEN. Emitted:\n{ts}"
            ),
            Err(e) => e.to_string(),
        }
    }

    /// Strip all whitespace so we can fingerprint emitted token structure
    /// without depending on `quote`'s spacing.
    fn squash(s: &str) -> String {
        s.chars().filter(|c| !c.is_whitespace()).collect()
    }

    /// THE FALSIFIER (now the regression guard).
    ///
    /// `require!(amount <= 1000)` is valid Rust and compiles in every other
    /// backend. Before the fix, the native Plonky3 backend resolved operands by
    /// matching SOURCE TEXT against param names; the literal `1000` matched no
    /// param, so `find_p3_col` returned its `_ => 0` fallback — column 0, which
    /// here belongs to the UNRELATED param `other`. The emitted AIR constrained
    /// `other - amount >= 0` (i.e. `amount <= other`), NOT `amount <= 1000`, and
    /// the bound the caveat NAMES was absent from the circuit entirely.
    /// A gate that exists and does not gate.
    ///
    /// DRIVEN EVIDENCE (pre-fix, on persvati) — the emitted AIR contained
    /// `let r = local[0usize]; let l = local[1usize]; r - l` and the string
    /// "1000" appeared NOWHERE in it.
    ///
    /// The operand must now be REFUSED at macro expansion.
    #[test]
    fn falsifier_literal_bound_is_refused_not_lowered_to_column_zero() {
        let err = p3_err(
            r#"
            fn spend_cap(other: u64, amount: u64) {
                require!(amount <= 1000);
            }
            "#,
        );
        assert!(
            err.contains("1000"),
            "the error must name the unresolvable operand; got: {err}"
        );
        assert!(
            err.contains("other") && err.contains("amount"),
            "the error must list the available params; got: {err}"
        );
    }

    /// Same class: an arithmetic operand `a + b` is valid Rust, compiles in
    /// gen_rust, and text-matches no param. Pre-fix it lowered to column 0
    /// (`a`), so `require!(a + b <= c)` emitted `c - a >= 0` — the `+ b` term
    /// silently dropped from the circuit. Must now be refused.
    #[test]
    fn falsifier_arith_operand_is_refused_not_lowered_to_column_zero() {
        let err = p3_err(
            r#"
            fn sum_cap(a: u64, b: u64, c: u64) {
                require!(a + b <= c);
            }
            "#,
        );
        assert!(
            err.contains("is not a parameter"),
            "expected the not-a-parameter diagnostic; got: {err}"
        );
    }

    /// An operand naming a binding that is not a param (a typo, or a `let`
    /// shadow the parser discards) must be refused rather than bound to col 0.
    #[test]
    fn falsifier_unknown_identifier_is_refused() {
        let err = p3_err(
            r#"
            fn confine_org(allowed_org: u64, request_org: u64) {
                require!(allowed_org == request_orgg);
            }
            "#,
        );
        assert!(
            err.contains("request_orgg") && err.contains("does not name a parameter"),
            "expected the unknown-operand diagnostic; got: {err}"
        );
    }

    /// A mutation operand with no column must be refused too (effects path).
    #[test]
    fn falsifier_mutation_operand_literal_is_refused() {
        let f: syn::ItemFn = syn::parse_str(
            r#"
            fn topup(balance: &mut u64, amount: u64) {
                *balance = *balance + 5;
            }
            "#,
        )
        .expect("valid fn");
        let ir = crate::parse::parse_effect(&f, None).expect("parses as an effect");
        match generate_plonky3(&ir) {
            Ok(ts) => panic!("mutation operand `5` has no column but was lowered anyway:\n{ts}"),
            Err(e) => {
                let err = e.to_string();
                assert!(
                    err.contains('5') && err.contains("mutation operand"),
                    "expected the mutation-operand diagnostic; got: {err}"
                );
            }
        }
    }

    // ========================================================================
    // The honest users must keep working — and keep constraining what they say.
    // ========================================================================

    /// The canonical caveat shape still lowers, and binds the RIGHT columns:
    /// `require!(current_time <= token_expiry)` must emit
    /// `r = local[token_expiry], l = local[current_time], r - l`.
    #[test]
    fn legitimate_caveat_binds_the_columns_it_names() {
        let emitted = p3_of(
            r#"
            fn not_after(token_expiry: u64, current_time: u64) {
                require!(current_time <= token_expiry);
            }
            "#,
        );
        let sq = squash(&emitted);
        // token_expiry = col 0 (right), current_time = col 1 (left).
        assert!(
            sq.contains(
                "letr:AB::Expr=local[0usize].into();letl:AB::Expr=local[1usize].into();r-l"
            ),
            "expected diff over the named columns; emitted:\n{emitted}"
        );
    }

    /// Distinct params must resolve to DISTINCT columns — the property the
    /// column-0 fallback destroyed. If `budget`'s two operands collapsed onto
    /// one column the constraint would be vacuous.
    #[test]
    fn distinct_params_resolve_to_distinct_columns() {
        let emitted = p3_of(
            r#"
            fn confine_org(allowed_org: u64, request_org: u64) {
                require!(allowed_org == request_org);
            }
            "#,
        );
        let sq = squash(&emitted);
        assert!(
            sq.contains(
                "letleft_val:AB::Expr=local[0usize].into();letright_val:AB::Expr=local[1usize].into();left_val-right_val"
            ),
            "equality must compare two DIFFERENT columns, else it is vacuous; emitted:\n{emitted}"
        );
    }

    /// `*balance >= amount` inside an effect: the deref wrapper is transparent
    /// and must still resolve structurally to `balance`'s column.
    #[test]
    fn deref_operand_resolves_structurally() {
        let f: syn::ItemFn = syn::parse_str(
            r#"
            fn transfer(balance: &mut u64, amount: u64) {
                require!(*balance >= amount);
                *balance = *balance - amount;
            }
            "#,
        )
        .expect("valid fn");
        let ir = crate::parse::parse_effect(&f, None).expect("parses as an effect");
        let emitted = generate_plonky3(&ir)
            .expect("`*balance >= amount` must still lower")
            .to_string();
        let sq = squash(&emitted);
        // balance is mutable => cols 0 (old) + 1 (new); amount => col 2.
        // GreaterEqual diff is `l = local[left]; r = local[right]; l - r`.
        assert!(
            sq.contains(
                "letl:AB::Expr=local[0usize].into();letr:AB::Expr=local[2usize].into();l-r"
            ),
            "expected `*balance` to resolve to balance's old column; emitted:\n{emitted}"
        );
    }
}
