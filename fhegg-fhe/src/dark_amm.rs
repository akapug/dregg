//! The Dark Pool — an AMM `x·y=k` with HIDDEN reserves (THE-DARK-BAZAAR.md, the walk stone).
//!
//! Hidden reserves need a product of two SECRETS, so this rides ct×ct multiply (`crate::bfv_mul`, oracle-
//! anchored to fhe.rs Multiplicator). OWNED by the `dark-amm` lane. Signatures frozen here; implement bodies.
//!
//! # What this stone IS (scoped honestly)
//!
//! **Verify-not-find.** Under FHE nobody can *compute* the swap output `dy = ⌊y·dx/(x+dx)⌋` from the
//! encrypted reserves — that is a division by an encrypted quantity, a deep circuit far past the depth-1
//! budget. But the constant-product invariant is *verifiable* with exactly ONE ct×ct multiply:
//!
//! ```text
//!   Enc(x) --(+ dx, plaintext add, EXACT)--> Enc(x+dx)   ┐
//!                                                        ├── bfv_mul ──> Enc((x+dx)·(y−dy))
//!   Enc(y) --(− dy, plaintext sub, EXACT)--> Enc(y−dy)   ┘
//! ```
//!
//! and the decrypt boundary opens ONLY that product, accepting iff it equals the public invariant
//! target `k`. So the roles are:
//!
//! * the **LP** (pool creator) initialized the reserves, so it legitimately knows them and — because
//!   `dx`/`dy` are public in this first stone — can track them and QUOTE `dy` (the "finder");
//! * the **house** holds only ciphertexts + the public `k` and ENFORCES the invariant homomorphically
//!   (the "verifier") — it can never see the reserves it is enforcing the curve on;
//! * the **decrypt boundary** (modeled here as an injected decrypted scalar; the real n-of-n threshold
//!   committee is the `threshold.rs` lane) opens the single invariant product, which for an honest exact
//!   swap equals the already-public `k` — one bit of information (pass/fail).
//!
//! Reserve ciphertexts are only ever touched by PLAINTEXT ops (`ct ± Plaintext` — exact in BFV, zero
//! noise growth), so repeated swaps do NOT accumulate noise on the pool state; the ct×ct product is a
//! per-swap ephemeral. The 3-swap chain test validates this by execution.
//!
//! # What stays OUT OF SCOPE (named, not hidden)
//!
//! * **Private `dx`** — here `dx` and `dy` are public, so every swap reveals the marginal price
//!   `dy/dx ≈ y/(x+dx)`; an observer of the full swap stream can progressively infer the reserves.
//!   The claim of THIS stone is the *machinery* (invariant enforcement by ct×ct on encrypted state);
//!   the full dark pool needs encrypted trade amounts + encrypted balances (a later stone).
//! * **Floor-division swaps.** Acceptance here is EXACT: the product must decrypt to exactly `k`, so
//!   only swaps where `(x+dx) | y·dx` are accepted (`NoExactQuote` otherwise). Generic floor swaps
//!   satisfy `k ≤ (x+dx)(y−dy) < k + (x+dx)`, and checking that upper bound against an ENCRYPTED
//!   `x+dx` is a homomorphic comparison this stone does not have (the MPC-boundary machinery).
//! * **The mod-t forgery margin.** Acceptance is equality mod t. An adversary who already KNOWS the
//!   reserves may be able to craft a wrapped `dy` whose junk product lands on `k mod t`; a blind
//!   adversary hits a ~1/t window. Range proofs at ingest + a blinded-residual decrypt (open
//!   `r·(P−k)` for random `r`, so a refused swap reveals nothing but "≠") are the named hardenings —
//!   today a refused proposal's decrypt reveals `P = k + r` itself.
//! * **Noise-budget proof.** The single multiply rides `bfv_mul`'s measured budget
//!   (`noise_growth_measured`) and the Lean bound (`metatheory/Bfv/Mul.lean`); no new Lean here.
//! * **Threshold relin-key generation** — `RelinearizationKey` is sk-adjacent material; who generates
//!   it in a no-viewer deployment is the same open point `bfv_mul` names.
//! * **Scale.** The wrap guard demands `bound_x'·bound_y' < t ≈ 2^20`, so reserves live in a small
//!   universe (≲1015·1015). Bigger pools need a larger t or CRT limbs. Also: declared caps are PUBLIC
//!   — an LP must declare loose caps, not the exact reserves.
//! * **Fees / slippage curve** — none; pure constant-product.

use std::fmt;
use std::sync::Arc;

use fhe::bfv::{BfvParameters, Encoding, Plaintext, PublicKey, RelinearizationKey};
use fhe_traits::{FheEncoder, FheEncrypter};

use crate::bfv_mul::{BfvMulError, BoundedCiphertext, MulEngine};

/// Errors — every refusal is loud and NAMES what was refused.
#[derive(Debug)]
pub enum DarkAmmError {
    /// A zero dx (or a quoted zero dy) is not a swap.
    ZeroAmount,
    /// This pool object has no LP view (house-side copy) — it can VERIFY a
    /// proposed swap but cannot QUOTE one. Use `try_swap_proposed`.
    QuoteUnavailable,
    /// The constant-product quote for this dx is not exact: `(x+dx) ∤ y·dx`.
    /// Floor swaps are the named out-of-scope; the floor quote and remainder
    /// are reported so the refusal is informative.
    NoExactQuote {
        dx: u64,
        dy_floor: u64,
        remainder: u64,
    },
    /// The proposed dy exceeds the pool's PUBLIC reserve cap — refused before
    /// touching any ciphertext.
    DyExceedsCap { dy: u64, cap_y: u64 },
    /// A bound/cap computation left the plaintext domain (≥ t or u64 overflow).
    CapOverflow { detail: &'static str },
    /// Pool construction rejected.
    InvalidInit { reason: &'static str },
    /// The wrapped `bfv_mul` engine refused (wrap guard) or fhe.rs failed.
    Mul(BfvMulError),
    /// The decrypt boundary opened the invariant product and it was NOT k:
    /// the proposed swap does not lie on the constant-product curve.
    InvariantViolated { decrypted: u64, k: u64 },
    /// The frozen `swap()` entry point was handed a plaintext modulus that is
    /// not the engine's.
    ParamMismatch { expected_t: u64, got_t: u64 },
    /// A fhe.rs encode operation failed (its error text carried through).
    Fhe(String),
}

impl fmt::Display for DarkAmmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroAmount => write!(f, "zero-amount swap refused"),
            Self::QuoteUnavailable => write!(
                f,
                "no LP view on this pool object: it can verify a proposed swap, not quote one"
            ),
            Self::NoExactQuote {
                dx,
                dy_floor,
                remainder,
            } => write!(
                f,
                "no exact constant-product quote for dx={dx}: floor dy={dy_floor} leaves remainder \
                 {remainder}; floor swaps are out of scope for the exact-acceptance stone"
            ),
            Self::DyExceedsCap { dy, cap_y } => {
                write!(f, "proposed dy={dy} exceeds the public reserve cap {cap_y}")
            }
            Self::CapOverflow { detail } => write!(f, "cap arithmetic left the domain: {detail}"),
            Self::InvalidInit { reason } => write!(f, "pool init refused: {reason}"),
            Self::Mul(e) => write!(f, "ct×ct multiply refused/failed: {e}"),
            Self::InvariantViolated { decrypted, k } => write!(
                f,
                "invariant violated: (x+dx)·(y−dy) decrypted to {decrypted}, expected k={k}; \
                 swap refused"
            ),
            Self::ParamMismatch { expected_t, got_t } => write!(
                f,
                "plaintext modulus mismatch: engine t={expected_t}, caller passed t={got_t}"
            ),
            Self::Fhe(e) => write!(f, "fhe.rs operation failed: {e}"),
        }
    }
}

impl std::error::Error for DarkAmmError {}

impl From<BfvMulError> for DarkAmmError {
    fn from(e: BfvMulError) -> Self {
        Self::Mul(e)
    }
}

/// The PLAINTEXT constant-product AMM — the differential oracle AND the LP's
/// quoting view. Deliberately boring: this is the cleartext truth the FHE path
/// must match exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlainAmm {
    pub x: u64,
    pub y: u64,
    pub k: u64,
}

impl PlainAmm {
    pub fn new(x0: u64, y0: u64) -> Self {
        Self {
            x: x0,
            y: y0,
            k: x0 * y0,
        }
    }

    /// The canonical floor quote: `dy = ⌊y·dx/(x+dx)⌋` and the division
    /// remainder `r = y·dx − dy·(x+dx)`, so `(x+dx)(y−dy) = k + r`.
    pub fn quote_floor(&self, dx: u64) -> (u64, u64) {
        let num = (self.y as u128) * (dx as u128);
        let den = (self.x as u128) + (dx as u128);
        let dy = num / den;
        let r = num % den;
        (dy as u64, r as u64)
    }

    /// The exact quote: `Some(dy)` iff the floor quote has remainder 0, i.e.
    /// the post-swap product is EXACTLY k.
    pub fn quote_exact(&self, dx: u64) -> Option<u64> {
        let (dy, r) = self.quote_floor(dx);
        (r == 0 && dy > 0).then_some(dy)
    }

    /// Apply a swap to the plaintext view.
    pub fn apply(&mut self, dx: u64, dy: u64) {
        self.x += dx;
        self.y -= dy;
    }
}

/// The house-visible encrypted pool state: two `BoundedCiphertext` reserves.
/// Bounds are PUBLIC declared caps (loose, never the exact reserves).
#[derive(Clone, Debug)]
pub struct PoolCiphertexts {
    pub ct_x: BoundedCiphertext,
    pub ct_y: BoundedCiphertext,
}

/// A pool with encrypted reserves (x, y) and the public invariant target k = x·y.
pub struct DarkPool {
    params: Arc<BfvParameters>,
    engine: MulEngine,
    state: PoolCiphertexts,
    /// The public constant-product target. Public by design: acceptance is
    /// "the product ciphertext decrypts to exactly this".
    pub k: u64,
    /// The LP's plaintext tracking view (quoting leg). `None` on a house-side
    /// object: the house can verify, never quote — and never sees reserves.
    lp_view: Option<PlainAmm>,
}

impl fmt::Debug for DarkPool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // MulEngine (fhe.rs Multiplicator) has no Debug; print the public face.
        f.debug_struct("DarkPool")
            .field("k", &self.k)
            .field("cap_x", &self.state.ct_x.plain_bound)
            .field("cap_y", &self.state.ct_y.plain_bound)
            .field("has_lp_view", &self.lp_view.is_some())
            .finish_non_exhaustive()
    }
}

/// A swap: dx in of asset X, dy out of asset Y, priced by the invariant on ENCRYPTED reserves.
/// `outcome` is `Ok(AppliedSwap)` — the candidate post-state plus the encrypted invariant product
/// the decrypt boundary must check — or the loud, named refusal.
pub struct SwapResult {
    pub outcome: Result<AppliedSwap, DarkAmmError>,
}

/// A verified-shape swap candidate. NOT yet committed: the decrypt boundary
/// must open `invariant` and see exactly `k` (`check_invariant`), then the
/// pool owner calls `DarkPool::commit`.
#[derive(Debug)]
pub struct AppliedSwap {
    pub dx: u64,
    pub dy: u64,
    /// The public invariant target the product must decrypt to.
    pub k: u64,
    /// Enc((x+dx)·(y−dy)) — the ct×ct product (relinearized, wrap-guarded).
    /// This is the ONLY ciphertext the decrypt boundary opens.
    pub invariant: BoundedCiphertext,
    /// Candidate post-swap encrypted reserves (plaintext-op descendants of the
    /// current state; committed only after the invariant check passes).
    pub state_after: PoolCiphertexts,
}

impl AppliedSwap {
    /// The acceptance rule at the decrypt boundary: the opened slot-0 value of
    /// `invariant` must be EXACTLY k. The caller supplies the decrypted value
    /// (test: sk decrypt; production: threshold combine) — this module never
    /// holds key material.
    pub fn check_invariant(&self, decrypted_slot0: u64) -> Result<(), DarkAmmError> {
        if decrypted_slot0 != self.k {
            return Err(DarkAmmError::InvariantViolated {
                decrypted: decrypted_slot0,
                k: self.k,
            });
        }
        Ok(())
    }
}

impl DarkPool {
    /// LP-side pool creation: encrypt the initial reserves under the pool's
    /// public key, declare PUBLIC loose caps, publish k = x0·y0.
    ///
    /// Refuses loudly when: a reserve is 0; a reserve exceeds its declared cap
    /// (the cap must actually bound the ciphertext slot or the wrap guard is
    /// unsound); or the cap product already reaches t (no swap could ever be
    /// verified).
    #[allow(clippy::too_many_arguments)]
    pub fn init<R: rand_09::RngCore + rand_09::CryptoRng>(
        params: &Arc<BfvParameters>,
        pk: &PublicKey,
        rk: &RelinearizationKey,
        x0: u64,
        y0: u64,
        cap_x: u64,
        cap_y: u64,
        rng: &mut R,
    ) -> Result<Self, DarkAmmError> {
        let engine = MulEngine::new(rk, params)?;
        let t = engine.plaintext_modulus();
        if x0 == 0 || y0 == 0 {
            return Err(DarkAmmError::InvalidInit {
                reason: "empty reserve",
            });
        }
        if x0 > cap_x || y0 > cap_y {
            return Err(DarkAmmError::InvalidInit {
                reason: "reserve exceeds its declared public cap (cap would be an unsound bound)",
            });
        }
        if (cap_x as u128) * (cap_y as u128) >= t as u128 {
            return Err(DarkAmmError::InvalidInit {
                reason: "cap_x·cap_y >= t: the invariant product could wrap; no swap verifiable",
            });
        }
        // caps < t ⇒ k = x0·y0 ≤ cap_x·cap_y < t: representable, exact.
        let k = x0 * y0;
        let encrypt = |v: u64, rng: &mut R| -> Result<_, DarkAmmError> {
            let pt = Plaintext::try_encode(&[v], Encoding::simd(), params)
                .map_err(|e| DarkAmmError::Fhe(e.to_string()))?;
            pk.try_encrypt(&pt, rng)
                .map_err(|e| DarkAmmError::Fhe(e.to_string()))
        };
        let ct_x = BoundedCiphertext::new(encrypt(x0, rng)?, cap_x);
        let ct_y = BoundedCiphertext::new(encrypt(y0, rng)?, cap_y);
        Ok(Self {
            params: params.clone(),
            engine,
            state: PoolCiphertexts { ct_x, ct_y },
            k,
            lp_view: Some(PlainAmm::new(x0, y0)),
        })
    }

    /// Drop the LP view — what the HOUSE holds: ciphertexts, caps, k. It can
    /// verify proposed swaps but cannot quote (and cannot see reserves).
    pub fn strip_lp_view(&mut self) {
        self.lp_view = None;
    }

    /// The encrypted reserves (for the decrypt boundary / differential tests).
    pub fn reserve_cts(&self) -> &PoolCiphertexts {
        &self.state
    }

    pub fn plaintext_modulus(&self) -> u64 {
        self.engine.plaintext_modulus()
    }

    fn scalar_pt(&self, v: u64) -> Result<Plaintext, DarkAmmError> {
        Plaintext::try_encode(&[v], Encoding::simd(), &self.params)
            .map_err(|e| DarkAmmError::Fhe(e.to_string()))
    }

    /// HOUSE-side verification leg: given a public (dx, dy) proposal, compute
    /// the candidate post-state by EXACT plaintext ops and the invariant
    /// product by ONE wrap-guarded ct×ct multiply. Touches no plaintext
    /// reserve. Refusals: zero amounts, dy over the public cap, cap overflow,
    /// wrap guard.
    pub fn try_swap_proposed(&self, dx: u64, dy: u64) -> Result<AppliedSwap, DarkAmmError> {
        let t = self.engine.plaintext_modulus();
        if dx == 0 || dy == 0 {
            return Err(DarkAmmError::ZeroAmount);
        }
        let cap_y = self.state.ct_y.plain_bound;
        if dy > cap_y {
            return Err(DarkAmmError::DyExceedsCap { dy, cap_y });
        }
        let cap_x_after = self
            .state
            .ct_x
            .plain_bound
            .checked_add(dx)
            .filter(|&b| b < t)
            .ok_or(DarkAmmError::CapOverflow {
                detail: "cap_x + dx >= t",
            })?;
        // dy ≤ cap_y checked above; honest reserves y ≤ cap_y give y−dy ≤ cap_y−dy.
        // (A dishonest dy > y wraps the slot mod t, the declared bound is then
        // unsound, the product is junk, and the invariant check refuses — the
        // residual mod-t forgery margin is named in the module doc.)
        let cap_y_after = cap_y - dy;

        // The public legs: EXACT plaintext add/sub on the ciphertexts.
        let new_x = BoundedCiphertext::new(&self.state.ct_x.ct + &self.scalar_pt(dx)?, cap_x_after);
        let new_y = BoundedCiphertext::new(&self.state.ct_y.ct - &self.scalar_pt(dy)?, cap_y_after);

        // The secret×secret leg: ONE wrap-guarded ct×ct multiply (fhe.rs
        // Multiplicator underneath — the oracle-anchored engine).
        let invariant = self.engine.multiply(&new_x, &new_y)?;

        Ok(AppliedSwap {
            dx,
            dy,
            k: self.k,
            invariant,
            state_after: PoolCiphertexts {
                ct_x: new_x,
                ct_y: new_y,
            },
        })
    }

    /// LP-side full leg: quote dy from the LP view (EXACT quotes only), then
    /// run the house verification leg on it.
    pub fn try_swap(&self, dx: u64) -> Result<AppliedSwap, DarkAmmError> {
        if dx == 0 {
            return Err(DarkAmmError::ZeroAmount);
        }
        let lp = self
            .lp_view
            .as_ref()
            .ok_or(DarkAmmError::QuoteUnavailable)?;
        let (dy_floor, remainder) = lp.quote_floor(dx);
        let dy = lp.quote_exact(dx).ok_or(DarkAmmError::NoExactQuote {
            dx,
            dy_floor,
            remainder,
        })?;
        self.try_swap_proposed(dx, dy)
    }

    /// Commit a checked swap: the caller passes the decrypt boundary's opened
    /// slot-0 value of `swap.invariant`; iff it is exactly k, the encrypted
    /// state advances (and the LP view, if any, tracks).
    pub fn commit(
        &mut self,
        swap: &AppliedSwap,
        decrypted_invariant_slot0: u64,
    ) -> Result<(), DarkAmmError> {
        swap.check_invariant(decrypted_invariant_slot0)?;
        self.state = swap.state_after.clone();
        if let Some(lp) = self.lp_view.as_mut() {
            lp.apply(swap.dx, swap.dy);
        }
        Ok(())
    }
}

/// Price a swap on hidden reserves: enforce (x+dx)·(y−dy) == k homomorphically (the ct×ct multiply is the
/// point — reserves never revealed). Returns dy (or the encrypted price), plus the updated encrypted pool.
pub fn swap(pool: &DarkPool, dx_plain: u64, t: u64) -> SwapResult {
    let expected_t = pool.plaintext_modulus();
    if t != expected_t {
        return SwapResult {
            outcome: Err(DarkAmmError::ParamMismatch {
                expected_t,
                got_t: t,
            }),
        };
    }
    SwapResult {
        outcome: pool.try_swap(dx_plain),
    }
}

// ---------------------------------------------------------------------------
// THE TEETH — fhe.rs is the oracle: encrypt with real fhe.rs, swap through the
// engine, decrypt with real fhe.rs, and DIFFERENTIALLY match the plaintext
// constant-product AMM exactly. If the homomorphic invariant or the state
// update is wrong in any way, fhe.rs decrypts a different number and the test
// is RED — agreement with a real BFV library cannot be faked.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;
    use fhe::bfv::{Ciphertext, SecretKey};
    use fhe_traits::{FheDecoder, FheDecrypter};
    use rand_09::rngs::StdRng;
    use rand_09::SeedableRng;

    use crate::additive::pick_params;
    use crate::bfv_lean::{FOLD_DEGREE, FOLD_MODULI};

    struct Fixture {
        params: Arc<BfvParameters>,
        sk: SecretKey,
        pk: PublicKey,
        rk: RelinearizationKey,
        rng: StdRng,
        t: u64,
    }

    fn fixture(seed: u64) -> Fixture {
        let params = pick_params(20);
        // Pin the parameter facts (same discipline as bfv_mul_oracle): if the
        // default set drifts we fail LOUDLY instead of testing another scheme.
        assert_eq!(params.degree(), FOLD_DEGREE, "degree drifted");
        assert_eq!(params.moduli(), &FOLD_MODULI, "RNS moduli drifted");
        let t = params.plaintext();
        assert_eq!(t, 1_032_193, "plaintext modulus drifted");
        let mut rng = StdRng::seed_from_u64(seed);
        let sk = SecretKey::random(&params, &mut rng);
        let pk = PublicKey::new(&sk, &mut rng);
        let rk = RelinearizationKey::new(&sk, &mut rng).expect("relin key");
        Fixture {
            params,
            sk,
            pk,
            rk,
            rng,
            t,
        }
    }

    /// The modeled decrypt boundary: open slot 0 with the real fhe.rs sk.
    /// (Production: the threshold committee — the `threshold.rs` lane.)
    fn open_slot0(fx: &Fixture, ct: &Ciphertext) -> u64 {
        let pt = fx.sk.try_decrypt(ct).expect("fhe.rs decrypt");
        Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("simd decode")[0]
    }

    fn pool(fx: &mut Fixture, x0: u64, y0: u64, cap_x: u64, cap_y: u64) -> DarkPool {
        let mut rng = StdRng::seed_from_u64(0xDA12_0000 ^ x0 ^ (y0 << 20));
        let _ = &mut fx.rng; // fixture rng reserved for key material
        DarkPool::init(&fx.params, &fx.pk, &fx.rk, x0, y0, cap_x, cap_y, &mut rng)
            .expect("pool init")
    }

    /// THE LOAD-BEARING TOOTH: one exact swap through the frozen `swap()`
    /// entry point, DIFFERENTIALLY validated against the plaintext
    /// constant-product AMM: the quoted dy, the decrypted invariant product,
    /// and the decrypted post-swap reserves all match the cleartext x·y=k
    /// computation exactly.
    #[test]
    fn oracle_exact_swap_matches_plaintext_amm() {
        let mut fx = fixture(0xDA1);
        let (x0, y0) = (100u64, 900u64);
        let mut p = pool(&mut fx, x0, y0, 400, 1000);
        assert_eq!(p.k, 90_000);

        // The plaintext oracle.
        let mut plain = PlainAmm::new(x0, y0);
        let dx = 50u64;
        let (dy_floor, r) = plain.quote_floor(dx);
        assert_eq!((dy_floor, r), (300, 0), "chosen dx must be an exact case");

        // The FHE swap through the FROZEN entry point.
        let res = swap(&p, dx, fx.t);
        let applied = res.outcome.expect("exact swap must verify in shape");
        assert_eq!(
            applied.dy, dy_floor,
            "quoted dy differs from the plaintext AMM"
        );

        // The decrypt boundary opens ONLY the invariant product: exactly k.
        let opened = open_slot0(&fx, &applied.invariant.ct);
        assert_eq!(opened, p.k, "(x+dx)·(y−dy) decrypted off the invariant");
        applied.check_invariant(opened).expect("acceptance");
        p.commit(&applied, opened).expect("commit");

        // Differential: decrypted post-swap reserves == plaintext AMM's.
        plain.apply(dx, dy_floor);
        assert_eq!((plain.x, plain.y), (150, 600));
        let st = p.reserve_cts();
        assert_eq!(open_slot0(&fx, &st.ct_x.ct), plain.x, "post-swap x differs");
        assert_eq!(open_slot0(&fx, &st.ct_y.ct), plain.y, "post-swap y differs");
        // And the plaintext invariant really is preserved.
        assert_eq!(plain.x * plain.y, p.k);
    }

    /// REPEATED SWAPS: a 3-swap exact chain (100,900)→(150,600)→(180,500)→
    /// (300,300). Every hop: invariant decrypts to exactly k; final reserves
    /// decrypt to the plaintext AMM's. This also witnesses by execution that
    /// plaintext-op-only state updates do not accumulate decrypt-breaking
    /// noise across swaps.
    #[test]
    fn oracle_multi_swap_chain() {
        let mut fx = fixture(0xDA2);
        let (x0, y0) = (100u64, 900u64);
        let mut p = pool(&mut fx, x0, y0, 400, 1000);
        let mut plain = PlainAmm::new(x0, y0);

        for dx in [50u64, 30, 120] {
            let dy = plain.quote_exact(dx).expect("chain chosen exact");
            let applied = p.try_swap(dx).expect("swap shape");
            assert_eq!(applied.dy, dy, "dx={dx}: dy differs from plaintext AMM");
            let opened = open_slot0(&fx, &applied.invariant.ct);
            assert_eq!(opened, p.k, "dx={dx}: invariant product != k");
            p.commit(&applied, opened).expect("commit");
            plain.apply(dx, dy);
        }
        assert_eq!((plain.x, plain.y), (300, 300));
        let st = p.reserve_cts();
        assert_eq!(open_slot0(&fx, &st.ct_x.ct), 300);
        assert_eq!(open_slot0(&fx, &st.ct_y.ct), 300);
    }

    /// FAILING SIDE — the invariant check BITES: dy off by ±1 decrypts to a
    /// value ≠ k and is REFUSED; the pool state does not advance. This is the
    /// tooth that a faked/trivial invariant cannot pass.
    #[test]
    fn wrong_dy_is_refused_and_state_holds() {
        let mut fx = fixture(0xDA3);
        let mut p = pool(&mut fx, 100, 900, 400, 1000);
        let k = p.k;

        for bad_dy in [299u64, 301] {
            let applied = p.try_swap_proposed(50, bad_dy).expect("shape passes");
            let opened = open_slot0(&fx, &applied.invariant.ct);
            assert_ne!(opened, k, "bad dy={bad_dy} must not satisfy the invariant");
            // 150·(900−299)=90150, 150·(900−301)=89850 — well-formed WRONG products.
            let expected = 150 * (900 - bad_dy);
            assert_eq!(opened, expected, "the oracle sees the exact wrong product");
            let err = p.commit(&applied, opened).expect_err("must refuse");
            assert!(
                matches!(err, DarkAmmError::InvariantViolated { decrypted, k: kk }
                    if decrypted == expected && kk == k),
                "wrong refusal: {err}"
            );
        }
        // State held: reserves unchanged.
        let st = p.reserve_cts();
        assert_eq!(open_slot0(&fx, &st.ct_x.ct), 100);
        assert_eq!(open_slot0(&fx, &st.ct_y.ct), 900);
    }

    /// FAILING SIDE — a dy > y (overdraw under the public cap) wraps the slot
    /// mod t; the junk product cannot decrypt to k and the swap is refused.
    #[test]
    fn overdraw_dy_wraps_and_is_refused() {
        let mut fx = fixture(0xDA4);
        let mut p = pool(&mut fx, 100, 900, 400, 1000);
        // dy=950 ≤ cap_y=1000 passes the public cap check, but y−dy = −50
        // wraps to t−50 in plaintext space.
        let applied = p.try_swap_proposed(50, 950).expect("shape passes");
        let opened = open_slot0(&fx, &applied.invariant.ct);
        // 150·(t−50) mod t = (150·1032143) mod 1032193 — junk, and ≠ k.
        let expected = ((150u128 * (fx.t as u128 - 50)) % fx.t as u128) as u64;
        assert_eq!(opened, expected, "wrap arithmetic witness");
        assert_ne!(opened, p.k);
        assert!(
            p.commit(&applied, opened).is_err(),
            "overdraw must be refused"
        );
    }

    /// The wrap-guard DISCIPLINE is inherited from bfv_mul: a swap whose
    /// declared post-swap cap product reaches t is refused BEFORE any
    /// ciphertext math (loud, named), and pool init refuses caps that could
    /// never verify a swap.
    #[test]
    fn wrap_guard_and_init_refusals() {
        let mut fx = fixture(0xDA5);
        // init: caps whose product reaches t are refused outright.
        let mut rng = StdRng::seed_from_u64(7);
        let err = DarkPool::init(&fx.params, &fx.pk, &fx.rk, 100, 900, 1016, 1016, &mut rng)
            .expect_err("cap product >= t must be refused at init");
        assert!(
            matches!(err, DarkAmmError::InvalidInit { .. }),
            "wrong refusal: {err}"
        );

        // swap: cap_x grows with dx until the multiply guard trips.
        let p = pool(&mut fx, 100, 900, 700, 1000);
        // (700+600)·(1000−300) = 910000 < t would pass, so push dy small:
        // (700+600)·(1000−1) = 1298700 ≥ t → WrapRefused from bfv_mul.
        let err = p.try_swap_proposed(600, 1).expect_err("guard must refuse");
        assert!(
            matches!(err, DarkAmmError::Mul(BfvMulError::WrapRefused { .. })),
            "wrong refusal: {err}"
        );
    }

    /// Quoting refusals: non-exact dx is NAMED (floor quote + remainder
    /// reported), zero amounts are refused, and a house-side pool (LP view
    /// stripped) can verify but not quote.
    #[test]
    fn quote_refusals_are_loud_and_named() {
        let mut fx = fixture(0xDA6);
        let mut p = pool(&mut fx, 100, 900, 400, 1000);

        // dx=7: y·dx = 6300, x+dx = 107 → floor 58 r 94: not exact.
        let err = p.try_swap(7).expect_err("inexact dx must be refused");
        assert!(
            matches!(
                err,
                DarkAmmError::NoExactQuote {
                    dx: 7,
                    dy_floor: 58,
                    remainder: 94
                }
            ),
            "wrong refusal: {err}"
        );

        assert!(matches!(
            swap(&p, 0, fx.t).outcome,
            Err(DarkAmmError::ZeroAmount)
        ));
        assert!(matches!(
            swap(&p, 50, fx.t + 1).outcome,
            Err(DarkAmmError::ParamMismatch { .. })
        ));

        // House-side: verify works, quote does not.
        p.strip_lp_view();
        assert!(matches!(
            p.try_swap(50),
            Err(DarkAmmError::QuoteUnavailable)
        ));
        let applied = p
            .try_swap_proposed(50, 300)
            .expect("house can still verify");
        assert_eq!(open_slot0(&fx, &applied.invariant.ct), p.k);
    }

    /// The plaintext reference itself: floor-quote arithmetic pins (the
    /// oracle must be right before it can judge the FHE path).
    #[test]
    fn plain_amm_quote_pins() {
        let amm = PlainAmm::new(100, 900);
        assert_eq!(amm.quote_floor(50), (300, 0));
        assert_eq!(amm.quote_exact(50), Some(300));
        assert_eq!(amm.quote_floor(7), (58, 94)); // 6300 = 58·107 + 94
        assert_eq!(amm.quote_exact(7), None);
        // Constant-product identity: (x+dx)(y−dy) = k + r, for both cases.
        for dx in [50u64, 7] {
            let (dy, r) = amm.quote_floor(dx);
            assert_eq!((amm.x + dx) * (amm.y - dy), amm.k + r);
        }
        // dy=0 quotes are not swaps.
        let tiny = PlainAmm::new(1000, 1);
        assert_eq!(tiny.quote_exact(1), None);
    }
}
