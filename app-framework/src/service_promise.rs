//! # Service-promise exchange — the spine of the agent service economy.
//!
//! The ring ([`crate::ring_trade::RingCoordinator`]) and the [`crate::payable`]
//! DSI exchange ASSETS atomically: a party offers an asset, wants an asset, the
//! verified [`RingSolver`] matches a conserving cycle and the legs settle
//! all-or-nothing. That is a *spot* market — value-for-value, both sides on the
//! table at once.
//!
//! A service economy needs more: a provider promises to PERFORM a service later,
//! and a consumer pays for it now. The danger is the half-open deal — the
//! consumer pays and the provider never performs, or the provider performs and
//! the consumer never pays. This module closes that gap with the SAME pieces the
//! ring already trusts, composed into a service-for-payment leg:
//!
//!  1. **Match** — a provider posts a [`ServicePromise`] ("I will perform service
//!     `S` for `price`"); a consumer posts a [`ServiceRequest`] ("I want `S`,
//!     offering `P`"). The match is found by the SAME [`RingSolver`] the asset
//!     ring uses: the service is encoded as a synthetic "promise-token" asset, so
//!     a provider↔consumer pair is exactly a 2-cycle (provider offers the
//!     promise-token + wants payment; consumer offers payment + wants the
//!     promise-token). [`ServicePromiseExchange::match_one`].
//!
//!  2. **Escrow** — the matched payment leg is not paid straight to the provider;
//!     it is HELD. The payment moves consumer → escrow through the verified
//!     executor ([`settle_ring_verified`], per-asset Σδ=0), exactly the
//!     conserving move the ring already proves. [`ServicePromiseExchange::fund`].
//!
//!  3. **Fulfill** — the promise is a guarded hole. The provider commits, at
//!     match time, to performing a specific verified turn (the service effect);
//!     its hash is the hole. The held payment is bound by a
//!     [`ProofCondition::TurnExecuted`] naming that hash — the exact promise-hole
//!     shape `turn/src/{eventual,conditional}.rs` defines (a one-shot
//!     continuation whose fill is the receipt the service turn executed). When the
//!     provider performs the turn it presents the signed [`TurnReceipt`]; the
//!     receipt FILLS the hole ([`resolve_condition`] → `Resolved`) and the escrow
//!     RELEASES the payment escrow → provider, again through the verified executor.
//!     [`ServicePromiseExchange::fulfill`].
//!
//!  4. **Refund** — if the promise lapses (the timeout passes with no conforming
//!     receipt) the held payment REFUNDS escrow → consumer.
//!     [`ServicePromiseExchange::refund`].
//!
//! Every value move is a single-leg [`settle_ring_verified`] fold, so each is
//! atomic and per-asset conserving on its own, and the whole lifecycle conserves
//! the payment asset end-to-end (consumer's `price` ends up wholly with the
//! provider on fulfillment, or wholly back with the consumer on refund — never
//! split). Release and refund are mutually-exclusive one-shot terminals, the same
//! consumed-once discipline `cell/src/escrow_sealed.rs` binds into a cell's
//! commitment; here the holder is the verified ledger rather than a heap leaf, but
//! the invariant is identical: a held leg is taken exactly once, by exactly one of
//! its two exits.
//!
//! ## What a "service" is, and how fulfillment is proven
//!
//! A [`ServiceId`] names a service as a `(target cell, method)` pair — a method/
//! effect the provider will exercise on a target. The provider's commitment to
//! perform it is the `service_turn_hash` it posts: the content-addressed
//! [`dregg_turn::Turn::hash`] of the exact verified turn that performs the
//! service. Fulfillment is proven the way the kernel already proves "a turn ran":
//! a [`TurnReceipt`] whose `turn_hash` matches AND whose `executor_signature`
//! verifies against a trusted executor key (the [`ProofCondition::TurnExecuted`]
//! resolution path). This module does NOT itself decide what counts as the
//! service being "done well" — it binds payment to the FACT that the named turn
//! executed under a trusted executor. Richer fulfillment (a STARK proof of an
//! outcome predicate) is the `ProofCondition::LocalProof` / `RemoteProof` path,
//! pluggable through the same [`ServiceEscrow::condition`] field.

use std::collections::HashSet;

use dregg_intent::CommitmentId;
use dregg_intent::exchange::AssetId;
use dregg_intent::solver::{ExchangeSpec, IntentNode, RingSolver, RingTrade};
use dregg_intent::verified_settle::{
    VerifiedLedger, VerifiedLeg, VerifiedSettleError, settle_ring_verified,
};
use dregg_turn::TurnReceipt;
use dregg_turn::conditional::{
    ConditionProof, ConditionalResult, ProofCondition, resolve_condition,
};
use dregg_types::CellId;

/// Names a service `S`: a method/effect the provider exercises on a target cell.
///
/// The id is the domain-separated hash of `(target, method)`, so two providers
/// promising the same `(target, method)` post the SAME [`ServiceId`] and the ring
/// matcher recognises them as offering one service. Inside the ring graph the
/// service trades as a synthetic "promise-token" asset (its bytes ARE the asset
/// id) — that is what lets the asset ring matcher find a provider↔consumer cycle
/// without a bespoke service matcher.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ServiceId(pub [u8; 32]);

impl ServiceId {
    /// The service "exercise `method` on `target`".
    pub fn of(target: CellId, method: &str) -> Self {
        let mut h = blake3::Hasher::new_derive_key("dregg.service-promise.service-id.v1");
        h.update(target.as_bytes());
        h.update(method.as_bytes());
        ServiceId(*h.finalize().as_bytes())
    }

    /// A service id from raw bytes (e.g. an externally agreed service tag).
    pub fn from_bytes(bytes: [u8; 32]) -> Self {
        ServiceId(bytes)
    }

    /// The raw 32-byte id.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// The synthetic promise-token asset this service trades as inside the ring
    /// graph. (It never settles as real value — it is the marker the ring matcher
    /// pairs provider↔consumer on; the only value that moves is the payment.)
    fn as_asset(&self) -> AssetId {
        self.0
    }
}

/// A provider's posted promise: "I will perform `service` for `price` of
/// `payment_asset`, paid to me (`provider`)."
#[derive(Clone, Debug)]
pub struct ServicePromise {
    /// The provider's ring identity (its low byte is its verified-ledger cell).
    pub provider: CommitmentId,
    /// The service promised.
    pub service: ServiceId,
    /// The content-addressed [`dregg_turn::Turn::hash`] of the exact verified turn
    /// the provider will perform to fulfill — the fulfillment hole. A
    /// [`TurnReceipt`] for THIS turn (signed by a trusted executor) fills it.
    pub service_turn_hash: [u8; 32],
    /// The asset the provider wants to be paid in.
    pub payment_asset: AssetId,
    /// The price the provider asks.
    pub price: u64,
    /// The block height after which an unfulfilled promise's escrow may be
    /// refunded to the consumer (the promise window).
    pub timeout_height: u64,
}

/// A consumer's posted request: "I want `service`, offering up to `offer` of
/// `payment_asset` from me (`consumer`)."
#[derive(Clone, Debug)]
pub struct ServiceRequest {
    /// The consumer's ring identity (its low byte is its verified-ledger cell).
    pub consumer: CommitmentId,
    /// The service wanted.
    pub service: ServiceId,
    /// The asset the consumer pays in.
    pub payment_asset: AssetId,
    /// The most the consumer will pay.
    pub offer: u64,
}

/// A matched provider/consumer pair — the service-for-payment leg the ring found.
#[derive(Clone, Debug)]
pub struct ServiceMatch {
    /// The provider being paid on fulfillment.
    pub provider: CommitmentId,
    /// The consumer whose payment is escrowed.
    pub consumer: CommitmentId,
    /// The service being exchanged.
    pub service: ServiceId,
    /// The fulfillment hole (the promised service turn's hash).
    pub service_turn_hash: [u8; 32],
    /// The asset payment settles in.
    pub payment_asset: AssetId,
    /// The matched price (the verified ring leg's amount).
    pub price: u64,
    /// The promise window (refund becomes available after this height).
    pub timeout_height: u64,
    /// The ring the solver matched (audit: the cycle these two formed).
    pub ring: RingTrade,
}

/// The lifecycle state of an escrowed promise. `Funded` is the only OPEN state;
/// `Released` and `Refunded` are one-shot terminals — a released escrow can never
/// refund and vice-versa (the held payment is taken exactly once).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EscrowStatus {
    /// Payment is held against the promise; awaiting fulfillment or lapse.
    Funded,
    /// Fulfillment was proven; payment was released to the provider.
    Released,
    /// The promise lapsed; payment was refunded to the consumer.
    Refunded,
}

/// A funded service escrow — the held payment plus the fulfillment condition that
/// gates its release.
#[derive(Clone, Debug)]
pub struct ServiceEscrow {
    /// The match this escrow was opened for.
    pub matched: ServiceMatch,
    /// The account holding the payment until release/refund.
    pub escrow: CommitmentId,
    /// The fulfillment condition (the promise hole): a [`ProofCondition::TurnExecuted`]
    /// naming the promised service turn. Swap this for a `LocalProof`/`RemoteProof`
    /// to gate release on an outcome predicate instead of mere execution.
    pub condition: ProofCondition,
    /// Lifecycle state.
    pub status: EscrowStatus,
}

impl ServiceEscrow {
    /// Whether the escrow is still open (payment held, not yet released/refunded).
    pub fn is_open(&self) -> bool {
        matches!(self.status, EscrowStatus::Funded)
    }
}

/// Why a service-promise operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ServicePromiseError {
    /// The promise and request name different services — nothing to match.
    ServiceMismatch,
    /// The promise and request settle in different payment assets.
    AssetMismatch,
    /// The consumer's offer does not cover the provider's price.
    Underfunded {
        /// What the consumer offered.
        offered: u64,
        /// What the provider asked.
        price: u64,
    },
    /// The ring matcher found no conserving cycle for the pair (e.g. a zero
    /// price, or the two share a verified-ledger cell index).
    NoMatch,
    /// A value move did not settle/conserve on the verified executor. Atomic: on
    /// this error no state changed.
    NotConserving(VerifiedSettleError),
    /// The escrow is already released or refunded — its one-shot exit was taken.
    AlreadySettled,
    /// Fulfillment was attempted but the presented proof did not resolve the
    /// promise (wrong/forged receipt, expired window, untrusted executor). No
    /// payment moved — the escrow stays funded.
    Unfulfilled(String),
    /// A refund was attempted before the promise window lapsed.
    NotYetRefundable {
        /// The height the refund was attempted at.
        current_height: u64,
        /// The height the promise window closes at.
        timeout_height: u64,
    },
}

impl std::fmt::Display for ServicePromiseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ServiceMismatch => write!(f, "promise and request name different services"),
            Self::AssetMismatch => write!(f, "promise and request use different payment assets"),
            Self::Underfunded { offered, price } => {
                write!(f, "consumer offers {offered} but provider asks {price}")
            }
            Self::NoMatch => write!(f, "no conserving service ring matched the pair"),
            Self::NotConserving(e) => write!(f, "value move did not conserve: {e}"),
            Self::AlreadySettled => write!(f, "escrow already released or refunded (one-shot)"),
            Self::Unfulfilled(d) => write!(f, "promise not fulfilled: {d}"),
            Self::NotYetRefundable {
                current_height,
                timeout_height,
            } => write!(
                f,
                "promise window still open: height {current_height} <= timeout {timeout_height}"
            ),
        }
    }
}

impl std::error::Error for ServicePromiseError {}

/// **The service-promise exchange.**
///
/// Holds the ring bound, the wall-clock `now` intents are judged against, the
/// escrow holding account, and the executor keys whose signatures count as proof
/// a service turn ran. It owns no value — value lives in the verified ledger; the
/// exchange MATCHES promises and drives the held-payment lifecycle through the
/// verified executor.
#[derive(Clone, Debug)]
pub struct ServicePromiseExchange {
    /// Largest cycle the ring matcher searches (≥ 2; a service pair is a 2-cycle).
    pub max_ring_size: usize,
    /// The wall-clock time posted intents are judged fresh against.
    pub now: u64,
    /// The account that holds escrowed payments between fund and release/refund.
    pub escrow: CommitmentId,
    /// Executor verifying-keys (32-byte ed25519) whose signature on a
    /// [`TurnReceipt`] proves the named service turn executed.
    pub trusted_executor_keys: Vec<[u8; 32]>,
    /// Maximum age (in blocks) a federation root may be for a `RemoteProof`
    /// fulfillment; unused by the default `TurnExecuted` path.
    pub max_root_age: u64,
}

impl ServicePromiseExchange {
    /// A new exchange holding escrowed payments in `escrow`, accepting fulfillment
    /// receipts signed by any of `trusted_executor_keys`.
    pub fn new(
        max_ring_size: usize,
        now: u64,
        escrow: CommitmentId,
        trusted_executor_keys: Vec<[u8; 32]>,
    ) -> Self {
        Self {
            max_ring_size,
            now,
            escrow,
            trusted_executor_keys,
            max_root_age: u64::MAX,
        }
    }

    /// **Match** a posted promise with a posted request, through the SAME ring
    /// matcher the asset ring uses.
    ///
    /// Encodes the provider and consumer as ring intents — the service as a
    /// synthetic promise-token asset, the payment as the real asset — and asks the
    /// [`RingSolver`] for a cycle. A compatible pair is exactly a 2-cycle; the
    /// matched payment leg (consumer → provider, in the payment asset) carries the
    /// price the escrow will hold.
    pub fn match_one(
        &self,
        promise: &ServicePromise,
        request: &ServiceRequest,
    ) -> Result<ServiceMatch, ServicePromiseError> {
        if promise.service != request.service {
            return Err(ServicePromiseError::ServiceMismatch);
        }
        if promise.payment_asset != request.payment_asset {
            return Err(ServicePromiseError::AssetMismatch);
        }
        if request.offer < promise.price {
            return Err(ServicePromiseError::Underfunded {
                offered: request.offer,
                price: promise.price,
            });
        }

        let expiry = self.now.saturating_add(3600);
        let service_asset = promise.service.as_asset();

        // The provider offers the promise-token, wants payment.
        let provider_node = IntentNode {
            intent_id: intent_id(
                &promise.provider,
                b"provider",
                &service_asset,
                promise.price,
            ),
            exchange: ExchangeSpec {
                offer_asset: service_asset,
                offer_amount: 1,
                want_asset: promise.payment_asset,
                want_min_amount: promise.price,
                min_rate: None,
                max_rate: None,
            },
            creator: promise.provider,
            expiry,
        };
        // The consumer offers payment, wants the promise-token.
        let consumer_node = IntentNode {
            intent_id: intent_id(
                &request.consumer,
                b"consumer",
                &request.payment_asset,
                request.offer,
            ),
            exchange: ExchangeSpec {
                offer_asset: request.payment_asset,
                offer_amount: request.offer,
                want_asset: service_asset,
                want_min_amount: 1,
                min_rate: None,
                max_rate: None,
            },
            creator: request.consumer,
            expiry,
        };

        let solver = RingSolver::new(self.max_ring_size);
        let ring = solver
            .solve_best(&[provider_node, consumer_node], self.now)
            .ok_or(ServicePromiseError::NoMatch)?;

        // The payment leg is the matched settlement in the payment asset
        // (consumer → provider). Its amount is the verified matched price.
        let pay = ring
            .settlements
            .iter()
            .find(|s| s.asset == promise.payment_asset)
            .ok_or(ServicePromiseError::NoMatch)?;
        if pay.from != request.consumer || pay.to != promise.provider {
            return Err(ServicePromiseError::NoMatch);
        }

        Ok(ServiceMatch {
            provider: promise.provider,
            consumer: request.consumer,
            service: promise.service,
            service_turn_hash: promise.service_turn_hash,
            payment_asset: promise.payment_asset,
            price: pay.amount,
            timeout_height: promise.timeout_height,
            ring,
        })
    }

    /// **Fund** the escrow: move the matched payment from the consumer into the
    /// escrow account through the verified executor (per-asset Σδ=0), and open the
    /// escrow bound by the fulfillment condition. Returns the funded escrow and the
    /// post-ledger. Atomic: if the move does not conserve/settle, nothing changes.
    pub fn fund(
        &self,
        matched: &ServiceMatch,
        ledger: &VerifiedLedger,
    ) -> Result<(ServiceEscrow, VerifiedLedger), ServicePromiseError> {
        let leg = VerifiedLeg {
            from: matched.consumer.0[0],
            to: self.escrow.0[0],
            asset: matched.payment_asset,
            amount: matched.price as i128,
        };
        let post =
            settle_ring_verified(ledger, &[leg]).map_err(ServicePromiseError::NotConserving)?;
        let escrow = ServiceEscrow {
            matched: matched.clone(),
            escrow: self.escrow,
            condition: ProofCondition::TurnExecuted {
                turn_hash: matched.service_turn_hash,
            },
            status: EscrowStatus::Funded,
        };
        Ok((escrow, post))
    }

    /// **Fulfill**: the provider presents the proof its promised service turn ran
    /// (a signed [`TurnReceipt`], as a [`ConditionProof::Receipt`]). The receipt
    /// FILLS the promise hole via [`resolve_condition`]; on `Resolved` the held
    /// payment RELEASES escrow → provider through the verified executor and the
    /// escrow becomes [`EscrowStatus::Released`].
    ///
    /// If the proof does not resolve (wrong receipt, untrusted executor, expired
    /// window) NOTHING moves and the escrow stays funded — there is no half-settle.
    /// A released or refunded escrow refuses ([`ServicePromiseError::AlreadySettled`]).
    pub fn fulfill(
        &self,
        escrow: &mut ServiceEscrow,
        ledger: &VerifiedLedger,
        proof: &ConditionProof,
        current_height: u64,
    ) -> Result<VerifiedLedger, ServicePromiseError> {
        if !escrow.is_open() {
            return Err(ServicePromiseError::AlreadySettled);
        }

        // Fill the hole: does the presented proof resolve the promise condition?
        let mut used_proof_hashes: HashSet<[u8; 32]> = HashSet::new();
        let result = resolve_condition(
            &escrow.condition,
            proof,
            current_height,
            escrow.matched.timeout_height,
            &[], // no federation roots needed for the TurnExecuted path
            self.max_root_age,
            &mut used_proof_hashes,
            &self.trusted_executor_keys,
        );
        if result != ConditionalResult::Resolved {
            return Err(ServicePromiseError::Unfulfilled(format!("{result:?}")));
        }

        // Promise fulfilled — release the held payment to the provider. Atomic.
        let leg = VerifiedLeg {
            from: escrow.escrow.0[0],
            to: escrow.matched.provider.0[0],
            asset: escrow.matched.payment_asset,
            amount: escrow.matched.price as i128,
        };
        let post =
            settle_ring_verified(ledger, &[leg]).map_err(ServicePromiseError::NotConserving)?;
        escrow.status = EscrowStatus::Released;
        Ok(post)
    }

    /// **Refund**: once the promise window has lapsed (`current_height >
    /// timeout_height`) with no fulfillment, return the held payment to the
    /// consumer through the verified executor and mark the escrow
    /// [`EscrowStatus::Refunded`]. A released or refunded escrow refuses; a refund
    /// before the window closes refuses ([`ServicePromiseError::NotYetRefundable`]).
    pub fn refund(
        &self,
        escrow: &mut ServiceEscrow,
        ledger: &VerifiedLedger,
        current_height: u64,
    ) -> Result<VerifiedLedger, ServicePromiseError> {
        if !escrow.is_open() {
            return Err(ServicePromiseError::AlreadySettled);
        }
        if current_height <= escrow.matched.timeout_height {
            return Err(ServicePromiseError::NotYetRefundable {
                current_height,
                timeout_height: escrow.matched.timeout_height,
            });
        }
        let leg = VerifiedLeg {
            from: escrow.escrow.0[0],
            to: escrow.matched.consumer.0[0],
            asset: escrow.matched.payment_asset,
            amount: escrow.matched.price as i128,
        };
        let post =
            settle_ring_verified(ledger, &[leg]).map_err(ServicePromiseError::NotConserving)?;
        escrow.status = EscrowStatus::Refunded;
        Ok(post)
    }

    /// Seed a verified ledger with the three accounts a single service-for-payment
    /// touches (consumer, provider, escrow), funding the consumer with
    /// `consumer_balance` of the payment asset. The conserved reference the
    /// lifecycle settles against.
    pub fn seed_ledger(&self, matched: &ServiceMatch, consumer_balance: u64) -> VerifiedLedger {
        let mut k = VerifiedLedger::new();
        for cell in [
            matched.consumer.0[0],
            matched.provider.0[0],
            self.escrow.0[0],
        ] {
            k.add_account(cell);
        }
        k.set(
            matched.consumer.0[0],
            &matched.payment_asset,
            consumer_balance as i128,
        );
        k
    }
}

/// A content-addressed ring-intent id for one side of a service promise (binds the
/// party, its role, and its exchange terms). Distinct roles/parties get distinct
/// ids, in the same spirit as `ring_trade::intent_id_for`.
fn intent_id(creator: &CommitmentId, role: &[u8], asset: &AssetId, amount: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("dregg.service-promise.intent-id.v1");
    h.update(&creator.0);
    h.update(role);
    h.update(asset);
    h.update(&amount.to_le_bytes());
    *h.finalize().as_bytes()
}

/// Build a fulfillment proof from a service turn's hash + a signed executor
/// receipt — the [`ConditionProof::Receipt`] the provider presents to fill the
/// promise hole. The receipt's `turn_hash` must equal the promised
/// `service_turn_hash`, and `executor_signature` must be a 64-byte signature (by a
/// trusted executor) over `receipt.receipt_hash()`. Exposed as a helper because
/// "the provider performed the turn, here is the receipt" is the whole fulfillment
/// gesture.
pub fn fulfillment_proof(receipt: TurnReceipt) -> ConditionProof {
    ConditionProof::Receipt(receipt)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CommitmentId {
        CommitmentId([b; 32])
    }
    fn asset(b: u8) -> AssetId {
        let mut a = [0u8; 32];
        a[0] = b;
        a
    }

    fn sample() -> (
        ServicePromiseExchange,
        ServicePromise,
        ServiceRequest,
        [u8; 32],
    ) {
        let service = ServiceId::of(CellId::from_bytes([0x5e; 32]), "render-report");
        let service_turn_hash = [0xAB; 32];
        let promise = ServicePromise {
            provider: cid(2),
            service,
            service_turn_hash,
            payment_asset: asset(7),
            price: 100,
            timeout_height: 50,
        };
        let request = ServiceRequest {
            consumer: cid(1),
            service,
            payment_asset: asset(7),
            offer: 100,
        };
        let exchange = ServicePromiseExchange::new(4, 0, cid(9), vec![]);
        (exchange, promise, request, service_turn_hash)
    }

    #[test]
    fn match_pairs_provider_and_consumer_through_the_ring() {
        let (exchange, promise, request, _) = sample();
        let m = exchange
            .match_one(&promise, &request)
            .expect("pair must match");
        assert_eq!(m.provider, cid(2));
        assert_eq!(m.consumer, cid(1));
        assert_eq!(m.price, 100);
        assert_eq!(m.payment_asset, asset(7));
        // The match was found by the real ring solver (the cycle is recorded).
        assert_eq!(m.ring.participants.len(), 2);
    }

    #[test]
    fn mismatched_service_or_asset_or_underfunded_refuses() {
        let (exchange, promise, request, _) = sample();

        let mut wrong_service = request.clone();
        wrong_service.service = ServiceId::from_bytes([0xFF; 32]);
        assert!(matches!(
            exchange.match_one(&promise, &wrong_service),
            Err(ServicePromiseError::ServiceMismatch)
        ));

        let mut wrong_asset = request.clone();
        wrong_asset.payment_asset = asset(8);
        assert!(matches!(
            exchange.match_one(&promise, &wrong_asset),
            Err(ServicePromiseError::AssetMismatch)
        ));

        let mut poor = request.clone();
        poor.offer = 1;
        assert!(matches!(
            exchange.match_one(&promise, &poor),
            Err(ServicePromiseError::Underfunded {
                offered: 1,
                price: 100
            })
        ));
    }

    #[test]
    fn fund_escrows_the_payment_conserved() {
        let (exchange, promise, request, _) = sample();
        let m = exchange.match_one(&promise, &request).unwrap();
        let k0 = exchange.seed_ledger(&m, 100);
        assert_eq!(k0.get(m.consumer.0[0], &m.payment_asset), 100);

        let (escrow, k1) = exchange.fund(&m, &k0).expect("fund must settle");
        // Payment left the consumer and is held in escrow; provider untouched.
        assert_eq!(k1.get(m.consumer.0[0], &m.payment_asset), 0);
        assert_eq!(k1.get(exchange.escrow.0[0], &m.payment_asset), 100);
        assert_eq!(k1.get(m.provider.0[0], &m.payment_asset), 0);
        assert_eq!(escrow.status, EscrowStatus::Funded);
        // Conserved.
        assert_eq!(k1.total_asset(&m.payment_asset), 100);
    }
}
