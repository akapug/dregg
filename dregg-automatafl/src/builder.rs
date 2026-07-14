//! A co-build harness: it emits the DSL `CircuitDescriptor` constraints AND the
//! single-row witness in lockstep, so columns and witness values can never drift.
//! Every gadget records the honest witness value it computed from the reference,
//! then `air_accepts` evaluates the emitted constraints over that row — accept iff
//! every constraint vanishes. Forgery tests `tamper` a named column and re-check.
//!
//! Only PURE-LOCAL algebraic `ConstraintExpr` kinds are used (Polynomial / Binary),
//! which lower one-to-one to IR-v2 `Base(Gate(..))` bodies in
//! `cellprogram_to_descriptor2` and are checked identically by the DSL evaluator
//! here and by the real STARK quotient/FRI on the prove path — so `air_accepts`
//! is a faithful shadow of "the leaf proves".

use std::collections::HashMap;

use dregg_circuit::dsl::circuit::{
    CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};

/// Canonical `BabyBear` of a signed integer (handles negatives, e.g. `-1 -> p-1`).
pub fn fb(x: i128) -> BabyBear {
    let p = BABYBEAR_P as i128;
    BabyBear::new((((x % p) + p) % p) as u32)
}

/// A linear (or product) head: `Σ (coeff, cols) + constant`. `cols` empty = constant term.
#[derive(Clone, Debug, Default)]
pub struct Head {
    pub terms: Vec<(i128, Vec<usize>)>,
    pub constant: i128,
}

impl Head {
    pub fn zero() -> Self {
        Head {
            terms: vec![],
            constant: 0,
        }
    }
    pub fn c(constant: i128) -> Self {
        Head {
            terms: vec![],
            constant,
        }
    }
    /// `coeff * col`.
    pub fn lin(coeff: i128, col: usize) -> Self {
        Head {
            terms: vec![(coeff, vec![col])],
            constant: 0,
        }
    }
    pub fn add_lin(mut self, coeff: i128, col: usize) -> Self {
        self.terms.push((coeff, vec![col]));
        self
    }
    pub fn add_prod(mut self, coeff: i128, cols: Vec<usize>) -> Self {
        self.terms.push((coeff, cols));
        self
    }
    pub fn add_const(mut self, k: i128) -> Self {
        self.constant += k;
        self
    }
    pub fn scale(mut self, k: i128) -> Self {
        for t in &mut self.terms {
            t.0 *= k;
        }
        self.constant *= k;
        self
    }
    pub fn append(mut self, other: &Head) -> Self {
        self.terms.extend(other.terms.iter().cloned());
        self.constant += other.constant;
        self
    }
}

pub struct Builder {
    pub name: String,
    columns: Vec<ColumnDef>,
    values: Vec<BabyBear>, // parallel to columns; the single-row witness
    names: Vec<String>,
    constraints: Vec<ConstraintExpr>,
    pub public_input_count: usize,
    pub pis: Vec<BabyBear>,
}

impl Builder {
    pub fn new(name: impl Into<String>) -> Self {
        Builder {
            name: name.into(),
            columns: Vec::new(),
            values: Vec::new(),
            names: Vec::new(),
            constraints: Vec::new(),
            public_input_count: 0,
            pis: Vec::new(),
        }
    }

    pub fn width(&self) -> usize {
        self.columns.len()
    }

    pub fn value(&self, col: usize) -> BabyBear {
        self.values[col]
    }

    pub fn col_by_name(&self, name: &str) -> Option<usize> {
        self.names.iter().position(|n| n == name)
    }

    /// Allocate a fresh column with a witness value (signed integer, reduced mod p).
    pub fn alloc(&mut self, name: impl Into<String>, kind: ColumnKind, value: i128) -> usize {
        let idx = self.columns.len();
        let name = name.into();
        self.columns.push(ColumnDef {
            name: name.clone(),
            index: idx,
            kind,
        });
        self.values.push(fb(value));
        self.names.push(name);
        idx
    }

    pub fn add_pi(&mut self, value: i128) {
        self.pis.push(fb(value));
        self.public_input_count = self.pis.len();
    }

    fn push(&mut self, c: ConstraintExpr) {
        self.constraints.push(c);
    }

    /// Assert `Σ head == 0` (a `Polynomial` gate).
    pub fn assert_zero(&mut self, head: &Head) {
        let mut terms: Vec<PolyTerm> = head
            .terms
            .iter()
            .filter(|(c, _)| *c % (BABYBEAR_P as i128) != 0 || true) // keep all; coeff may be 0 only if intended
            .map(|(c, cols)| PolyTerm {
                coeff: fb(*c),
                col_indices: cols.clone(),
            })
            .collect();
        if head.constant % (BABYBEAR_P as i128) != 0 {
            terms.push(PolyTerm {
                coeff: fb(head.constant),
                col_indices: vec![],
            });
        }
        self.push(ConstraintExpr::Polynomial { terms });
    }

    /// Boolean pin (`col*(col-1) == 0`).
    pub fn assert_binary(&mut self, col: usize) {
        self.push(ConstraintExpr::Binary { col });
    }

    /// `∏_{s in set} (col - s) == 0` (membership; degree |set|).
    pub fn assert_member(&mut self, col: usize, set: &[i128]) {
        // Expand the product into a Polynomial.
        let mut poly: Vec<PolyTerm> = vec![PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![],
        }];
        for &s in set {
            let mut next: Vec<PolyTerm> = Vec::new();
            for t in &poly {
                let mut with_col = t.col_indices.clone();
                with_col.push(col);
                next.push(PolyTerm {
                    coeff: t.coeff,
                    col_indices: with_col,
                });
                next.push(PolyTerm {
                    coeff: t.coeff * fb(-s),
                    col_indices: t.col_indices.clone(),
                });
            }
            poly = next;
        }
        self.push(ConstraintExpr::Polynomial { terms: poly });
    }

    /// A one-hot selector vector of `k` bits, witnessed one at `hot`, pinned so that
    /// `Σ j*sel_j == index_head`. Returns the selector column indices. (Does NOT bind
    /// a read value; use [`Self::one_hot_read`] for the full read.)
    pub fn one_hot(&mut self, tag: &str, k: usize, hot: usize, index_head: &Head) -> Vec<usize> {
        let mut sel = Vec::with_capacity(k);
        for j in 0..k {
            let v = if j == hot { 1 } else { 0 };
            let c = self.alloc(format!("{tag}_sel{j}"), ColumnKind::Binary, v);
            self.assert_binary(c);
            sel.push(c);
        }
        // Σ sel == 1.
        let mut sum = Head::c(-1);
        for &c in &sel {
            sum = sum.add_lin(1, c);
        }
        self.assert_zero(&sum);
        // Σ j*sel_j - index_head == 0.
        let mut idx = Head::zero();
        for (j, &c) in sel.iter().enumerate() {
            idx = idx.add_lin(j as i128, c);
        }
        idx = idx.append(&index_head.clone().scale(-1));
        self.assert_zero(&idx);
        sel
    }

    /// Random-access board read: `value_col == board[index]`, where `index` is pinned
    /// to `index_head` by a one-hot selector. `board_cols[index_val]` must equal the
    /// witnessed value of `value_col` (the caller computed both from the reference).
    /// Degree 2 (the `Σ sel_j*board_j` product).
    pub fn one_hot_read(
        &mut self,
        tag: &str,
        board_cols: &[usize],
        index_val: usize,
        index_head: &Head,
        value_col: usize,
    ) {
        let sel = self.one_hot(tag, board_cols.len(), index_val, index_head);
        // Σ sel_j * board_j - value_col == 0.
        let mut rd = Head::zero();
        for (j, &s) in sel.iter().enumerate() {
            rd = rd.add_prod(1, vec![s, board_cols[j]]);
        }
        rd = rd.add_lin(-1, value_col);
        self.assert_zero(&rd);
    }

    /// THE RANGE GADGET (bit-decomposition non-negativity, per `compiler.rs`).
    /// Emit `rbits` boolean columns and the recomposition `head - Σ 2^k b_k == 0`.
    /// The honest `head_val` (which must be `0 <= head_val < 2^rbits`) fills the bits;
    /// a negative/over-range head cannot be recomposed by any bits, so the leaf is
    /// UNSAT — a genuine non-negativity proof sound through the STARK/FRI quotient.
    pub fn range_nonneg(&mut self, tag: &str, head: &Head, head_val: i128, rbits: usize) {
        let canon = {
            let p = BABYBEAR_P as i128;
            (((head_val % p) + p) % p) as u128
        };
        let mut recomp = head.clone();
        for k in 0..rbits {
            let bit = ((canon >> k) & 1) as i128;
            let b = self.alloc(format!("{tag}_rb{k}"), ColumnKind::Binary, bit);
            self.assert_binary(b);
            recomp = recomp.add_lin(-(1i128 << k), b);
        }
        self.assert_zero(&recomp);
    }

    /// A boolean column FORCED to equal `[d >= 0]` for the signed head `d`. Enforced
    /// by `range_nonneg(2*ib*d + ib - d - 1)`: when `d >= 0` only `ib = 1` keeps the
    /// term `>= 0` (`= d`); when `d < 0` only `ib = 0` does (`= -d-1`). So the bit is
    /// pinned to the true comparison — a forged bit makes the range gadget UNSAT.
    pub fn forced_ge0(&mut self, tag: &str, d: &Head, d_val: i128, rbits: usize) -> usize {
        let ib_val = if d_val >= 0 { 1 } else { 0 };
        let ib = self.alloc(format!("{tag}_ib"), ColumnKind::Binary, ib_val);
        self.assert_binary(ib);
        // term = 2*ib*d + ib - d - 1
        let mut term = Head::zero();
        for (coeff, cols) in &d.terms {
            let mut c2 = vec![ib];
            c2.extend(cols.iter().copied());
            term = term.add_prod(2 * coeff, c2);
        }
        term = term.add_prod(2 * d.constant, vec![ib]);
        term = term.add_lin(1, ib);
        term = term.append(&d.clone().scale(-1));
        term = term.add_const(-1);
        let term_val = if d_val >= 0 { d_val } else { -d_val - 1 };
        self.range_nonneg(&format!("{tag}_t"), &term, term_val, rbits);
        ib
    }

    /// `ConditionalNonzero`: when `selector != 0`, require `value != 0` (via a witnessed
    /// inverse). `value_val` is the honest value (used to fill the inverse; `0` if the
    /// selector is off so `value` may legitimately be zero).
    pub fn cond_nonzero(
        &mut self,
        tag: &str,
        selector_col: usize,
        value_col: usize,
        value_val: i128,
    ) {
        let inv_val: i128 = if self.values[selector_col] != BabyBear::ZERO {
            // value must be nonzero; witness its inverse.
            fb(value_val).inverse().map(|x| x.0 as i128).unwrap_or(0)
        } else {
            0
        };
        let inv = self.alloc(format!("{tag}_inv"), ColumnKind::Value, inv_val);
        self.push(ConstraintExpr::ConditionalNonzero {
            selector_col,
            value_col,
            inverse_col: inv,
        });
    }

    /// A one-hot selector gated by `gate_col` (a bit): the selectors sum to `gate`
    /// (all zero when the gate is off), and when on they one-hot at `index_head`.
    /// Returns the selector columns. `hot` is the honest hot index (ignored if the
    /// gate is off in the witness).
    pub fn one_hot_gated(
        &mut self,
        tag: &str,
        k: usize,
        gate_col: usize,
        hot: usize,
        index_head: &Head,
    ) -> Vec<usize> {
        let on = self.values[gate_col] != BabyBear::ZERO;
        let mut sel = Vec::with_capacity(k);
        for j in 0..k {
            let v = if on && j == hot { 1 } else { 0 };
            let c = self.alloc(format!("{tag}_sel{j}"), ColumnKind::Binary, v);
            self.assert_binary(c);
            sel.push(c);
        }
        // Σ sel - gate == 0.
        let mut s = Head::lin(-1, gate_col);
        for &c in &sel {
            s = s.add_lin(1, c);
        }
        self.assert_zero(&s);
        // Σ j*sel_j - gate*index_head == 0.
        let mut idx = Head::zero();
        for (j, &c) in sel.iter().enumerate() {
            idx = idx.add_lin(j as i128, c);
        }
        for (coeff, cols) in &index_head.terms {
            let mut cc = vec![gate_col];
            cc.extend(cols.iter().copied());
            idx = idx.add_prod(-coeff, cc);
        }
        idx = idx.add_prod(-index_head.constant, vec![gate_col]);
        self.assert_zero(&idx);
        sel
    }

    /// Gated random-access read: `value_col == board[index]` when `gate` is on, else
    /// `value_col == 0` (the OOB/wall convention). Selectors sum to `gate`.
    pub fn one_hot_read_gated(
        &mut self,
        tag: &str,
        board_cols: &[usize],
        gate_col: usize,
        index_val: usize,
        index_head: &Head,
        value_col: usize,
    ) {
        let sel = self.one_hot_gated(tag, board_cols.len(), gate_col, index_val, index_head);
        // Σ sel_j*board_j - value_col == 0.
        let mut rd = Head::zero();
        for (j, &s) in sel.iter().enumerate() {
            rd = rd.add_prod(1, vec![s, board_cols[j]]);
        }
        rd = rd.add_lin(-1, value_col);
        self.assert_zero(&rd);
    }

    /// A fresh column pinned to the product of two columns (`out == a*b`).
    pub fn alloc_prod(&mut self, name: &str, a: usize, b: usize) -> usize {
        let v = (self.values[a] * self.values[b]).0 as i128;
        let out = self.alloc(name, ColumnKind::Value, v);
        self.assert_zero(&Head::lin(-1, out).add_prod(1, vec![a, b]));
        out
    }

    // -------- witness self-evaluation (the `air_accepts` shadow) --------

    /// Evaluate every emitted constraint over the single witness row; return the list
    /// of `(constraint_index, residual)` that do NOT vanish. Empty => the AIR accepts.
    pub fn failing(&self) -> Vec<(usize, BabyBear)> {
        let row = &self.values;
        let mut out = Vec::new();
        for (i, c) in self.constraints.iter().enumerate() {
            let r = c.evaluate(row, row, &self.pis);
            if r != BabyBear::ZERO {
                out.push((i, r));
            }
        }
        out
    }

    /// The AIR accepts the current witness iff no constraint has a nonzero residual.
    pub fn air_accepts(&self) -> bool {
        self.failing().is_empty()
    }

    /// Overwrite a column's witness value (a forgery), returning the previous value.
    pub fn tamper(&mut self, col: usize, value: i128) -> BabyBear {
        let prev = self.values[col];
        self.values[col] = fb(value);
        prev
    }

    pub fn set_value(&mut self, col: usize, value: BabyBear) {
        self.values[col] = value;
    }

    // -------- lowering to the prove path --------

    pub fn max_degree(&self) -> usize {
        self.constraints
            .iter()
            .map(|c| c.degree())
            .max()
            .unwrap_or(1)
    }

    pub fn descriptor(&self) -> CircuitDescriptor {
        CircuitDescriptor {
            name: self.name.clone(),
            trace_width: self.columns.len(),
            max_degree: self.max_degree().max(1),
            columns: self.columns.clone(),
            constraints: self.constraints.clone(),
            boundaries: vec![],
            public_input_count: self.public_input_count,
            lookup_tables: vec![],
        }
    }

    pub fn cellprogram(&self) -> CellProgram {
        CellProgram::new(self.descriptor(), 1)
    }

    /// The trace witness (`col name -> per-row values`, constant across `num_rows`).
    pub fn trace_witness(&self, num_rows: usize) -> HashMap<String, Vec<BabyBear>> {
        let mut w = HashMap::new();
        for (i, col) in self.columns.iter().enumerate() {
            w.insert(col.name.clone(), vec![self.values[i]; num_rows]);
        }
        w
    }

    pub fn constraint_count(&self) -> usize {
        self.constraints.len()
    }
}
