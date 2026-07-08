//! `R_q = ℤ_q[X]/(Xⁿ+1)` — the negacyclic polynomial quotient ring the Lean
//! spec's abstract `CommRing R` is instantiated at for this reference.
//!
//! Small concrete parameters (`N = 8`, `Q = 3329`, the Kyber prime) and
//! schoolbook negacyclic convolution: this is a REFERENCE, not a performant
//! or constant-time implementation.

/// Ring dimension `n` in `Xⁿ + 1`.
pub const N: usize = 8;

/// The coefficient modulus `q` (prime; 3329 = 13·2⁸ + 1, the Kyber prime).
pub const Q: u64 = 3329;

/// An element of `R_q`: coefficients of `1, X, …, X^{N-1}`, each in `[0, Q)`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Poly {
    /// Coefficient of `X^i` at position `i`, reduced mod [`Q`].
    pub coeffs: [u64; N],
}

impl Poly {
    /// The zero element.
    pub const ZERO: Poly = Poly { coeffs: [0; N] };

    /// The constant polynomial `v mod q` (the image of `ℤ_q ↪ R_q`).
    pub fn constant(v: u64) -> Self {
        let mut coeffs = [0u64; N];
        coeffs[0] = v % Q;
        Poly { coeffs }
    }

    /// Ring addition, coefficientwise mod `q`.
    pub fn add(&self, other: &Self) -> Self {
        let mut coeffs = [0u64; N];
        for i in 0..N {
            coeffs[i] = (self.coeffs[i] + other.coeffs[i]) % Q;
        }
        Poly { coeffs }
    }

    /// Ring subtraction, coefficientwise mod `q`.
    pub fn sub(&self, other: &Self) -> Self {
        let mut coeffs = [0u64; N];
        for i in 0..N {
            coeffs[i] = (self.coeffs[i] + Q - other.coeffs[i]) % Q;
        }
        Poly { coeffs }
    }

    /// Additive inverse.
    pub fn neg(&self) -> Self {
        Poly::ZERO.sub(self)
    }

    /// Ring multiplication: schoolbook NEGACYCLIC convolution — the index
    /// wraparound `X^N = -1` is the quotient by `Xⁿ + 1`.
    pub fn mul(&self, other: &Self) -> Self {
        // |acc| ≤ N · (Q-1)² ≈ 8.9e7 — comfortably inside i64.
        let mut acc = [0i64; N];
        for i in 0..N {
            for j in 0..N {
                let p = (self.coeffs[i] * other.coeffs[j]) as i64;
                let k = i + j;
                if k < N {
                    acc[k] += p;
                } else {
                    acc[k - N] -= p; // X^{k} = X^{k-N} · X^N = -X^{k-N}
                }
            }
        }
        let mut coeffs = [0u64; N];
        for i in 0..N {
            coeffs[i] = acc[i].rem_euclid(Q as i64) as u64;
        }
        Poly { coeffs }
    }

    /// Is this the image of a base-ring constant?
    pub fn is_constant(&self) -> bool {
        self.coeffs[1..].iter().all(|&c| c == 0)
    }

    /// Inverse of a CONSTANT unit polynomial (`c ∈ ℤ_q^*` embedded in `R_q`).
    ///
    /// The Lean `FieldModel` extractor divides by `c - c'`; in the deployed
    /// ring the challenge set is chosen so challenge differences are units.
    /// This reference exposes inversion only on the constant subring (where
    /// `q` prime makes every nonzero element a unit), enough to realize
    /// `extractPreimage` on constant-challenge forks. General `R_q` inversion
    /// is intentionally out of scope.
    pub fn inverse_constant(&self) -> Option<Self> {
        if !self.is_constant() {
            return None;
        }
        inv_mod_q(self.coeffs[0]).map(Poly::constant)
    }
}

/// `a⁻¹ mod q` by Fermat (q prime), or `None` for `a ≡ 0`.
pub fn inv_mod_q(a: u64) -> Option<u64> {
    let a = a % Q;
    if a == 0 {
        return None;
    }
    // a^(q-2) mod q by square-and-multiply.
    let mut base = a;
    let mut exp = Q - 2;
    let mut result = 1u64;
    while exp > 0 {
        if exp & 1 == 1 {
            result = result * base % Q;
        }
        base = base * base % Q;
        exp >>= 1;
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x_to(k: usize) -> Poly {
        let mut coeffs = [0u64; N];
        coeffs[k] = 1;
        Poly { coeffs }
    }

    #[test]
    fn negacyclic_wraparound_x_n_is_minus_one() {
        // X^{N-1} · X = X^N ≡ -1 in ℤ_q[X]/(Xⁿ+1).
        let prod = x_to(N - 1).mul(&x_to(1));
        assert_eq!(prod, Poly::constant(Q - 1));
    }

    #[test]
    fn ring_laws_spot_checks() {
        let a = Poly {
            coeffs: [1, 7, 0, 3328, 12, 0, 5, 900],
        };
        let b = Poly {
            coeffs: [3300, 2, 2, 2, 0, 0, 1, 1],
        };
        let c = Poly {
            coeffs: [17, 0, 0, 0, 0, 4, 0, 2500],
        };
        // Commutativity and associativity of mul; distributivity over add.
        assert_eq!(a.mul(&b), b.mul(&a));
        assert_eq!(a.mul(&b).mul(&c), a.mul(&b.mul(&c)));
        assert_eq!(a.mul(&b.add(&c)), a.mul(&b).add(&a.mul(&c)));
        // Additive group.
        assert_eq!(a.add(&a.neg()), Poly::ZERO);
        assert_eq!(a.sub(&b), a.add(&b.neg()));
        // Multiplicative identity.
        assert_eq!(a.mul(&Poly::constant(1)), a);
    }

    #[test]
    fn constant_inversion() {
        for v in [1u64, 2, 13, 256, 3328] {
            let p = Poly::constant(v);
            let inv = p.inverse_constant().unwrap();
            assert_eq!(p.mul(&inv), Poly::constant(1));
        }
        assert!(Poly::constant(0).inverse_constant().is_none());
        assert!(x_to(1).inverse_constant().is_none());
    }
}
