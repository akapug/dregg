//! [`JupiterSwap`] — the deferred pile→fuel **swap execution**: convert the treasury's
//! illiquid `$DREGG` pile into USDC fuel over the `$DREGG`→SOL→USDC Jupiter route,
//! **behind an operator-held [`Signer`]** and **authorized by a governance vote**.
//!
//! # Who authorizes, who signs — the two independent gates
//!
//! A swap moves treasury value, so it is gated twice and NEITHER gate is automated:
//!
//! * **The vote authorizes.** A [`SwapAuthorization`] is minted ONLY by a passed
//!   liquidity-event vote ([`crate::governance`]). It is stamped by the operator's
//!   [`GovernanceAuthority`] key (a certification of the tally outcome) and binds the
//!   exact `amount`, `min_out`, and the two mints. [`JupiterSwap::execute`] REFUSES
//!   any authorization it cannot verify against the configured authority public key —
//!   a forged or wrong-authority authorization is [`SwapError::Unauthorized`]. There is
//!   no `execute`-without-authorization path: the value type is required.
//! * **The operator signs.** The on-chain swap transaction is signed by an
//!   operator-held [`Signer`]. `dregg-pay` NEVER holds the key: [`MockSigner`] is the
//!   throwaway test signer (real ed25519, no network); the production path injects the
//!   operator's secured signer (KMS/HSM). [`JupiterSwap::build_unsigned`] builds the
//!   exact bytes the operator signs, so a real deployment can hand the operator an
//!   unsigned transaction and take the signature back — the key stays with the operator.
//!
//! # Scope — devnet/mock by default
//!
//! The [`SwapVenue`] seam is injected exactly like the watcher's RPC / the sweeper's
//! [`TxSubmitter`](crate::sweeper::TxSubmitter): [`MockSwapVenue`] fills at a fixed rate
//! with no network; the real path quotes + submits through Jupiter. On a (mock) success
//! the treasury pile ([`Treasury::dregg_balance`]) moves DOWN by `amount` and the fuel
//! tank ([`Treasury::usdc_balance`]) moves UP by the realized USDC — the whole point of
//! the swap. Mainnet is a config flip on ember's go; custody remains the signer.

use ed25519_dalek::{Signature, Signer as _, SigningKey, Verifier as _, VerifyingKey};

use crate::treasury::{Treasury, TreasuryStore};

// ─────────────────────────────────────────────────────────────────────────────
// The operator signer seam — dregg-pay NEVER holds a key
// ─────────────────────────────────────────────────────────────────────────────

/// Why a signer backend failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SignerError {
    /// The signing backend (HSM / KMS / local key) failed to produce a signature.
    Backend(String),
}

impl std::fmt::Display for SignerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SignerError::Backend(e) => write!(f, "signer backend error: {e}"),
        }
    }
}

impl std::error::Error for SignerError {}

/// An **operator-held** transaction signer. The key lives with the operator (a local
/// secured key, a KMS, an HSM) — `dregg-pay` only ever calls [`Signer::sign`] and reads
/// [`Signer::public_key`]; it holds no key itself. This is the seam that keeps
/// settlement a deliberate operator action, never an automated key-in-code.
pub trait Signer {
    /// The signer's ed25519 public key (32 bytes) — the operator authority whose
    /// signature the venue / chain verifies.
    fn public_key(&self) -> [u8; 32];

    /// Sign `message`, returning a 64-byte ed25519 signature. On the real path this is
    /// the operator's secured backend; in tests [`MockSigner`] signs with a throwaway
    /// key (real crypto, no network).
    fn sign(&self, message: &[u8]) -> Result<[u8; 64], SignerError>;
}

/// A throwaway ed25519 signer for driven tests. NEVER a real operator key — built from
/// a fixed test seed. It performs REAL ed25519 signing so the driven tests exercise the
/// genuine signature path (the same shape a KMS/HSM signer satisfies), with no funds and
/// no network.
pub struct MockSigner {
    key: SigningKey,
}

impl MockSigner {
    /// A mock signer from a throwaway 32-byte seed. Never a real operator key.
    pub fn from_seed(seed: [u8; 32]) -> Self {
        MockSigner {
            key: SigningKey::from_bytes(&seed),
        }
    }
}

impl Signer for MockSigner {
    fn public_key(&self) -> [u8; 32] {
        self.key.verifying_key().to_bytes()
    }

    fn sign(&self, message: &[u8]) -> Result<[u8; 64], SignerError> {
        Ok(self.key.sign(message).to_bytes())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The governance authority — certifies a passed vote into a SwapAuthorization
// ─────────────────────────────────────────────────────────────────────────────

/// The operator-held **governance authority**: the key that certifies a passed
/// liquidity-event vote into a [`SwapAuthorization`] the swap executor can verify without
/// re-running the vote. It is operator config (throwaway in tests), never a compiled-in
/// mainnet secret — the same custody law as [`Seed`](crate::config::Seed). The vote is
/// the decision; this key is only the attestation that binds the decision to an exact
/// swap so [`JupiterSwap`] can trust it at a distance.
pub struct GovernanceAuthority {
    key: SigningKey,
}

impl GovernanceAuthority {
    /// A governance authority from a throwaway 32-byte seed (tests) or the operator's
    /// configured certification key (prod). Never hardcoded to a mainnet value.
    pub fn from_seed(seed: [u8; 32]) -> Self {
        GovernanceAuthority {
            key: SigningKey::from_bytes(&seed),
        }
    }

    /// The authority public key — what [`JupiterSwap`] is configured with to verify a
    /// [`SwapAuthorization`].
    pub fn public_key(&self) -> [u8; 32] {
        self.key.verifying_key().to_bytes()
    }

    /// Certify a passed vote into a signed [`SwapAuthorization`]. Called by
    /// [`crate::governance`] ONLY once a real quorum has been reached — this method
    /// does not itself check the vote (that is governance's job); it binds the swap
    /// params so the executor can verify the outcome.
    pub(crate) fn authorize(
        &self,
        amount: u64,
        min_out: u64,
        dregg_mint: [u8; 32],
        usdc_mint: [u8; 32],
        poll_id: [u8; 32],
    ) -> SwapAuthorization {
        let msg = authorization_message(amount, min_out, &dregg_mint, &usdc_mint, &poll_id);
        let signature = self.key.sign(&msg).to_bytes();
        SwapAuthorization {
            amount,
            min_out,
            dregg_mint,
            usdc_mint,
            poll_id,
            signature,
        }
    }
}

/// The canonical bytes a [`SwapAuthorization`] is signed over — binds every field so a
/// signature can never be replayed onto a different amount, floor, mint pair, or poll.
fn authorization_message(
    amount: u64,
    min_out: u64,
    dregg_mint: &[u8; 32],
    usdc_mint: &[u8; 32],
    poll_id: &[u8; 32],
) -> Vec<u8> {
    let mut m = Vec::with_capacity(18 + 8 + 8 + 32 * 3);
    m.extend_from_slice(b"dregg-pay/swap-auth/v1");
    m.extend_from_slice(&amount.to_le_bytes());
    m.extend_from_slice(&min_out.to_le_bytes());
    m.extend_from_slice(dregg_mint);
    m.extend_from_slice(usdc_mint);
    m.extend_from_slice(poll_id);
    m
}

/// A governance-issued **authorization** for exactly one pile→fuel swap. Minted ONLY by
/// [`GovernanceAuthority::authorize`] (i.e. by a passed vote in [`crate::governance`]);
/// its `signature` is verified by [`JupiterSwap::execute`] against the configured
/// authority public key, so a hand-rolled / wrong-authority authorization is refused.
/// The `signature` field is private: no external code can forge one.
#[derive(Clone, Debug)]
pub struct SwapAuthorization {
    /// Atomic `$DREGG` authorized to swap out of the pile.
    pub amount: u64,
    /// The minimum atomic USDC the swap must realize (the slippage floor). A fill below
    /// this fails closed.
    pub min_out: u64,
    /// The `$DREGG` mint this authorization is bound to.
    pub dregg_mint: [u8; 32],
    /// The USDC mint this authorization is bound to.
    pub usdc_mint: [u8; 32],
    /// The liquidity-event poll whose passed vote authorized this swap (provenance).
    pub poll_id: [u8; 32],
    /// The governance authority's ed25519 signature over
    /// [`authorization_message`]. Private — only [`GovernanceAuthority::authorize`]
    /// produces a valid value, so a [`SwapAuthorization`] cannot be forged outside a vote.
    signature: [u8; 64],
}

impl SwapAuthorization {
    /// Verify this authorization against `authority_pk` — the real gate: recompute the
    /// canonical bytes and check the governance signature. A forged or wrong-authority
    /// authorization returns `false`.
    pub fn verify(&self, authority_pk: &[u8; 32]) -> bool {
        let Ok(vk) = VerifyingKey::from_bytes(authority_pk) else {
            return false;
        };
        let Ok(sig) = Signature::from_slice(&self.signature) else {
            return false;
        };
        let msg = authorization_message(
            self.amount,
            self.min_out,
            &self.dregg_mint,
            &self.usdc_mint,
            &self.poll_id,
        );
        vk.verify(&msg, &sig).is_ok()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The swap route + the venue seam
// ─────────────────────────────────────────────────────────────────────────────

/// The `$DREGG`→SOL→USDC route a swap realizes. The SOL leg is implicit in the Jupiter
/// route (Jupiter finds the best path through SOL); this records the endpoints and the
/// slippage floor the swap must clear.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SwapRoute {
    /// Atomic `$DREGG` sold into the route (out of the pile).
    pub dregg_in: u64,
    /// The minimum atomic USDC the route must return (the slippage floor).
    pub min_usdc_out: u64,
    /// The `$DREGG` mint (input).
    pub dregg_mint: [u8; 32],
    /// The USDC mint (output).
    pub usdc_mint: [u8; 32],
}

/// The canonical bytes the operator SIGNS to execute a swap — binds the route so an
/// operator signature can't be replayed onto a different swap. A production submitter
/// signs the assembled Solana/Jupiter transaction message; this is the minimal binding
/// the driven tests prove custody over.
pub fn swap_message(route: &SwapRoute) -> Vec<u8> {
    let mut m = Vec::with_capacity(18 + 8 + 8 + 32 * 2);
    m.extend_from_slice(b"dregg-pay/swap-tx/v1");
    m.extend_from_slice(&route.dregg_in.to_le_bytes());
    m.extend_from_slice(&route.min_usdc_out.to_le_bytes());
    m.extend_from_slice(&route.dregg_mint);
    m.extend_from_slice(&route.usdc_mint);
    m
}

/// An unsigned swap transaction: the exact bytes the operator signs, plus the route it
/// realizes. The real deployment hands this to the operator's secured signer and takes
/// back a signature — `dregg-pay` never holds the key.
#[derive(Clone, Debug)]
pub struct UnsignedSwapTx {
    /// The message the operator signs (see [`swap_message`]).
    pub message: Vec<u8>,
    /// The route the signed transaction realizes.
    pub route: SwapRoute,
}

/// The swap-execution seam. Injected (not baked-in reqwest/tokio) exactly like the
/// watcher's RPC fetcher and the sweeper's [`TxSubmitter`](crate::sweeper::TxSubmitter):
///
/// * [`MockSwapVenue`] fills at a fixed `$DREGG`/USDC rate — driven, no network.
/// * A production impl calls the Jupiter quote API, builds the swap transaction, has the
///   operator sign it (the passed-in `signature`), submits it, and returns the realized
///   USDC. The pricing seam it quotes against is the same public Jupiter API the
///   [`JupiterPriceOracle`](crate::pricing::JupiterPriceOracle) reads.
pub trait SwapVenue {
    /// Quote the atomic USDC a `route.dregg_in` sale would realize (best-effort — the
    /// realized amount is what [`SwapVenue::submit`] returns and the swap floors on).
    fn quote(&self, route: &SwapRoute) -> Result<u64, SwapError>;

    /// Submit the operator-signed swap, returning `(realized_usdc, tx_reference)`. The
    /// `signature` is the operator's signature over [`swap_message`]; a production venue
    /// binds it into the on-chain transaction.
    fn submit(&self, route: &SwapRoute, signature: &[u8; 64]) -> Result<(u64, String), SwapError>;
}

/// A mock swap venue: fills `$DREGG`→USDC at a fixed rate, no network. `usdc_per_dregg_bps`
/// is the realized USDC (atomic) per whole `$DREGG` in basis-point resolution against the
/// `$DREGG` decimals — but to keep the driven tests exact, it simply multiplies
/// `dregg_in` by `num` and divides by `den` (a fixed rational rate).
pub struct MockSwapVenue {
    num: u128,
    den: u128,
}

impl MockSwapVenue {
    /// A venue that realizes `dregg_in * num / den` atomic USDC (a fixed rational rate).
    /// e.g. `num = 5, den = 1000` models `$0.005`/`$DREGG` at equal (6,6) decimals.
    pub fn new(num: u128, den: u128) -> Self {
        MockSwapVenue { num, den }
    }

    fn fill(&self, dregg_in: u64) -> u64 {
        u64::try_from((dregg_in as u128) * self.num / self.den).unwrap_or(u64::MAX)
    }
}

impl SwapVenue for MockSwapVenue {
    fn quote(&self, route: &SwapRoute) -> Result<u64, SwapError> {
        Ok(self.fill(route.dregg_in))
    }

    fn submit(&self, route: &SwapRoute, _signature: &[u8; 64]) -> Result<(u64, String), SwapError> {
        let usdc = self.fill(route.dregg_in);
        Ok((usdc, format!("mock-swap:{}:{usdc}", route.dregg_in)))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The swap executor
// ─────────────────────────────────────────────────────────────────────────────

/// Why a swap was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SwapError {
    /// The [`SwapAuthorization`] did not verify against the configured governance
    /// authority — a forged / wrong-authority / tampered authorization (the vote gate).
    Unauthorized,
    /// The authorization is for a different mint pair than this swap executor is
    /// configured for (a bound-authorization mismatch).
    MintMismatch,
    /// The pile cannot cover the authorized `amount` — fail closed (need vs have).
    PileShort {
        /// Atomic `$DREGG` the swap needs.
        needed: u64,
        /// Atomic `$DREGG` in the pile.
        available: u64,
    },
    /// The realized USDC was below the authorization's `min_out` — the slippage floor
    /// bit. Fail closed: no treasury move happens.
    SlippageExceeded {
        /// The realized atomic USDC.
        realized: u64,
        /// The authorized floor.
        min_out: u64,
    },
    /// The operator signer failed.
    Signer(SignerError),
    /// The venue (Jupiter / mock) failed to quote or submit.
    Venue(String),
}

impl std::fmt::Display for SwapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SwapError::Unauthorized => {
                write!(
                    f,
                    "swap refused: authorization did not verify (no passed vote)"
                )
            }
            SwapError::MintMismatch => {
                write!(
                    f,
                    "swap refused: authorization bound to a different mint pair"
                )
            }
            SwapError::PileShort { needed, available } => write!(
                f,
                "swap refused: pile short — need {needed} atomic $DREGG, have {available}"
            ),
            SwapError::SlippageExceeded { realized, min_out } => write!(
                f,
                "swap refused: realized {realized} atomic USDC below floor {min_out}"
            ),
            SwapError::Signer(e) => write!(f, "swap refused: {e}"),
            SwapError::Venue(e) => write!(f, "swap venue error: {e}"),
        }
    }
}

impl std::error::Error for SwapError {}

impl From<SignerError> for SwapError {
    fn from(e: SignerError) -> Self {
        SwapError::Signer(e)
    }
}

/// The result of an executed swap.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SwapOutcome {
    /// Atomic `$DREGG` sold out of the pile.
    pub dregg_in: u64,
    /// Atomic USDC realized into the fuel tank.
    pub usdc_out: u64,
    /// The new pile balance (atomic `$DREGG`) after the swap.
    pub pile_after: u64,
    /// The new fuel balance (atomic USDC) after the swap.
    pub fuel_after: u64,
    /// The venue transaction reference (a Jupiter tx signature on the real path; a
    /// synthetic id on the mock path).
    pub tx_reference: String,
}

/// The pile→fuel swap executor over an injected [`SwapVenue`]. Configured with the mint
/// pair (so it can reject a mis-bound authorization) and the governance authority public
/// key (so it can verify the vote gate). Holds NO key.
pub struct JupiterSwap<V: SwapVenue> {
    venue: V,
    dregg_mint: [u8; 32],
    usdc_mint: [u8; 32],
    authority_pk: [u8; 32],
}

impl<V: SwapVenue> JupiterSwap<V> {
    /// Build a swap executor: the venue seam, the mint pair from
    /// [`PayConfig`](crate::config::PayConfig), and the governance authority public key a
    /// [`SwapAuthorization`] must verify against.
    pub fn new(
        venue: V,
        dregg_mint: [u8; 32],
        usdc_mint: [u8; 32],
        authority_pk: [u8; 32],
    ) -> Self {
        JupiterSwap {
            venue,
            dregg_mint,
            usdc_mint,
            authority_pk,
        }
    }

    /// Verify an authorization and build the UNSIGNED swap transaction — the exact bytes
    /// the operator signs. A real deployment calls this, hands `UnsignedSwapTx::message`
    /// to the operator's secured signer, and passes the returned signature to
    /// [`JupiterSwap::submit_signed`]. `dregg-pay` never holds the key.
    ///
    /// Refuses ([`SwapError::Unauthorized`] / [`SwapError::MintMismatch`]) before building
    /// anything if the authorization does not verify — the vote gate comes first.
    pub fn build_unsigned(&self, auth: &SwapAuthorization) -> Result<UnsignedSwapTx, SwapError> {
        self.check_auth(auth)?;
        let route = self.route_for(auth);
        Ok(UnsignedSwapTx {
            message: swap_message(&route),
            route,
        })
    }

    /// Execute the authorized swap: verify the authorization (the vote gate), check the
    /// pile covers it, have the operator [`Signer`] sign the swap tx, submit it through
    /// the venue, enforce the slippage floor, and — on success — move the treasury
    /// (pile DOWN by `amount`, fuel UP by the realized USDC).
    ///
    /// REFUSES without a valid authorization ([`SwapError::Unauthorized`]) — there is no
    /// unauthorized path — and fails closed on a short pile, a blown slippage floor, or a
    /// signer/venue error, with NO treasury move on any refusal.
    pub fn execute<S: TreasuryStore>(
        &self,
        auth: &SwapAuthorization,
        signer: &dyn Signer,
        treasury: &Treasury<S>,
    ) -> Result<SwapOutcome, SwapError> {
        // Gate 1 — THE VOTE: the authorization must verify against the governance
        // authority. A forged / wrong-authority / tampered authorization is refused here.
        self.check_auth(auth)?;

        // Fail closed if the pile cannot cover the authorized amount — before signing.
        let pile = treasury.dregg_balance();
        if auth.amount > pile {
            return Err(SwapError::PileShort {
                needed: auth.amount,
                available: pile,
            });
        }

        // Gate 2 — THE OPERATOR SIGNER: build the unsigned tx and have the operator sign
        // it. dregg-pay holds no key; it only calls `signer.sign`.
        let route = self.route_for(auth);
        let message = swap_message(&route);
        let signature = signer.sign(&message)?;

        // The operator's signature is genuine ed25519 — verify it (a custody sanity
        // tooth; the real chain also verifies it). A production signer's key is the
        // operator's; this proves the signer path is real crypto, not a stub.
        if let Ok(vk) = VerifyingKey::from_bytes(&signer.public_key()) {
            if let Ok(sig) = Signature::from_slice(&signature) {
                if vk.verify(&message, &sig).is_err() {
                    return Err(SwapError::Signer(SignerError::Backend(
                        "operator signature failed to verify".into(),
                    )));
                }
            }
        }

        // Submit through the venue (Jupiter on the real path; a fixed-rate fill on mock).
        let (usdc_out, tx_reference) = self.venue.submit(&route, &signature)?;

        // The slippage floor bites: a fill below the authorized `min_out` fails closed,
        // with NO treasury move.
        if usdc_out < auth.min_out {
            return Err(SwapError::SlippageExceeded {
                realized: usdc_out,
                min_out: auth.min_out,
            });
        }

        // On success, realize the swap in the treasury: pile DOWN, fuel UP.
        let pile_after =
            treasury
                .withdraw_dregg(auth.amount)
                .map_err(|_| SwapError::PileShort {
                    needed: auth.amount,
                    available: treasury.dregg_balance(),
                })?;
        let fuel_after = treasury.deposit_usdc(usdc_out);

        Ok(SwapOutcome {
            dregg_in: auth.amount,
            usdc_out,
            pile_after,
            fuel_after,
            tx_reference,
        })
    }

    /// A best-effort USDC quote for an authorization's amount (does not move funds).
    pub fn quote(&self, auth: &SwapAuthorization) -> Result<u64, SwapError> {
        self.check_auth(auth)?;
        self.venue.quote(&self.route_for(auth))
    }

    fn check_auth(&self, auth: &SwapAuthorization) -> Result<(), SwapError> {
        if !auth.verify(&self.authority_pk) {
            return Err(SwapError::Unauthorized);
        }
        if auth.dregg_mint != self.dregg_mint || auth.usdc_mint != self.usdc_mint {
            return Err(SwapError::MintMismatch);
        }
        Ok(())
    }

    fn route_for(&self, auth: &SwapAuthorization) -> SwapRoute {
        SwapRoute {
            dregg_in: auth.amount,
            min_usdc_out: auth.min_out,
            dregg_mint: self.dregg_mint,
            usdc_mint: self.usdc_mint,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::treasury::InMemoryTreasuryStore;

    const DREGG_MINT: [u8; 32] = [0x11u8; 32];
    const USDC_MINT: [u8; 32] = [0x22u8; 32];

    fn treasury(pile: u64, fuel: u64) -> Treasury<InMemoryTreasuryStore> {
        let t = Treasury::new(InMemoryTreasuryStore::new(), 6);
        t.deposit_dregg(pile);
        t.deposit_usdc(fuel);
        t
    }

    #[test]
    fn authorized_swap_moves_pile_to_fuel_mock_signed() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        // $0.005/$DREGG at (6,6) decimals: 100_000_000 atomic $DREGG → 500_000 atomic USDC.
        let venue = MockSwapVenue::new(5, 1000);
        let swap = JupiterSwap::new(venue, DREGG_MINT, USDC_MINT, authority.public_key());

        let t = treasury(100_000_000, 0);
        let auth = authority.authorize(100_000_000, 400_000, DREGG_MINT, USDC_MINT, [1u8; 32]);
        let out = swap.execute(&auth, &signer, &t).unwrap();
        assert_eq!(out.dregg_in, 100_000_000);
        assert_eq!(out.usdc_out, 500_000);
        assert_eq!(out.pile_after, 0, "pile drained by the swap");
        assert_eq!(out.fuel_after, 500_000, "fuel filled by the swap");
        assert_eq!(t.dregg_balance(), 0);
        assert_eq!(t.usdc_balance(), 500_000);
    }

    #[test]
    fn swap_without_valid_authorization_is_refused() {
        // An ATTACKER authority (different key) mints a validly-self-signed authorization,
        // but the swap is configured with the REAL authority pk → refused. Non-vacuous.
        let real = GovernanceAuthority::from_seed([7u8; 32]);
        let attacker = GovernanceAuthority::from_seed([0x99u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 1000),
            DREGG_MINT,
            USDC_MINT,
            real.public_key(),
        );
        let t = treasury(100_000_000, 0);
        let forged = attacker.authorize(100_000_000, 400_000, DREGG_MINT, USDC_MINT, [1u8; 32]);
        assert_eq!(
            swap.execute(&forged, &signer, &t),
            Err(SwapError::Unauthorized)
        );
        // Nothing moved.
        assert_eq!(t.dregg_balance(), 100_000_000);
        assert_eq!(t.usdc_balance(), 0);
    }

    #[test]
    fn tampered_authorization_is_refused() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 1000),
            DREGG_MINT,
            USDC_MINT,
            authority.public_key(),
        );
        let t = treasury(100_000_000, 0);
        let mut auth = authority.authorize(1_000_000, 4_000, DREGG_MINT, USDC_MINT, [1u8; 32]);
        // Tamper: bump the amount after signing. The signature no longer matches.
        auth.amount = 100_000_000;
        assert_eq!(
            swap.execute(&auth, &signer, &t),
            Err(SwapError::Unauthorized)
        );
        assert_eq!(t.dregg_balance(), 100_000_000);
    }

    #[test]
    fn swap_fails_closed_when_pile_short() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 1000),
            DREGG_MINT,
            USDC_MINT,
            authority.public_key(),
        );
        // Pile has only 10; authorization asks for 100_000_000.
        let t = treasury(10, 0);
        let auth = authority.authorize(100_000_000, 1, DREGG_MINT, USDC_MINT, [1u8; 32]);
        assert_eq!(
            swap.execute(&auth, &signer, &t),
            Err(SwapError::PileShort {
                needed: 100_000_000,
                available: 10
            })
        );
        assert_eq!(t.dregg_balance(), 10, "short pile untouched");
    }

    #[test]
    fn slippage_floor_fails_closed_with_no_move() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        // Venue realizes only 500_000 but the floor is 600_000 → refused.
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 1000),
            DREGG_MINT,
            USDC_MINT,
            authority.public_key(),
        );
        let t = treasury(100_000_000, 0);
        let auth = authority.authorize(100_000_000, 600_000, DREGG_MINT, USDC_MINT, [1u8; 32]);
        assert_eq!(
            swap.execute(&auth, &signer, &t),
            Err(SwapError::SlippageExceeded {
                realized: 500_000,
                min_out: 600_000
            })
        );
        assert_eq!(
            t.dregg_balance(),
            100_000_000,
            "no move on slippage refusal"
        );
        assert_eq!(t.usdc_balance(), 0);
    }

    #[test]
    fn mint_mismatch_is_refused() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let signer = MockSigner::from_seed([8u8; 32]);
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 1000),
            DREGG_MINT,
            USDC_MINT,
            authority.public_key(),
        );
        let t = treasury(100_000_000, 0);
        // Authorization bound to a DIFFERENT $DREGG mint.
        let auth = authority.authorize(1, 1, [0xAB; 32], USDC_MINT, [1u8; 32]);
        assert_eq!(
            swap.execute(&auth, &signer, &t),
            Err(SwapError::MintMismatch)
        );
    }

    #[test]
    fn build_unsigned_binds_the_route_for_the_operator() {
        let authority = GovernanceAuthority::from_seed([7u8; 32]);
        let swap = JupiterSwap::new(
            MockSwapVenue::new(5, 1000),
            DREGG_MINT,
            USDC_MINT,
            authority.public_key(),
        );
        let auth = authority.authorize(100_000_000, 400_000, DREGG_MINT, USDC_MINT, [1u8; 32]);
        let unsigned = swap.build_unsigned(&auth).unwrap();
        assert_eq!(unsigned.route.dregg_in, 100_000_000);
        assert_eq!(unsigned.route.min_usdc_out, 400_000);
        assert_eq!(unsigned.message, swap_message(&unsigned.route));
        // The operator signs `unsigned.message` externally; the key stays with them.
    }
}
