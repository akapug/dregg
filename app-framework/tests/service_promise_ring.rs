//! End-to-end prototype: two cells exchange a SERVICE for PAYMENT via the ring.
//!
//! A provider promises a service for payment; a consumer pays for it. The ring
//! matches them, the payment is ESCROWED against the promise, and then either the
//! provider FULFILLS (proves its service turn ran → payment released) or the
//! promise LAPSES (→ payment refunded). This test proves the four contracts:
//!
//!   1. HAPPY PATH   — service performed (a signed receipt fills the hole) → paid.
//!   2. REFUND PATH  — unfulfilled past the window → refunded to the consumer.
//!   3. ATOMICITY    — a forged/absent fulfillment never half-pays; release and
//!                     refund are mutually-exclusive one-shots.
//!   4. CONSERVATION — the payment asset's total is preserved across every path.

use dregg_app_framework::service_promise::{
    EscrowStatus, ServiceId, ServicePromise, ServicePromiseError, ServicePromiseExchange,
    ServiceRequest, fulfillment_proof,
};
use dregg_intent::CommitmentId;
use dregg_intent::exchange::AssetId;
use dregg_turn::TurnReceipt;
use dregg_turn::conditional::ConditionProof;
use dregg_types::CellId;
use ed25519_dalek::{Signer, SigningKey};

fn cid(b: u8) -> CommitmentId {
    CommitmentId([b; 32])
}
fn asset(b: u8) -> AssetId {
    let mut a = [0u8; 32];
    a[0] = b;
    a
}

/// The provider cell, the consumer cell, the escrow cell — distinct verified-ledger
/// indices (the ledger projects each commitment to its low byte).
const CONSUMER: u8 = 1;
const PROVIDER: u8 = 2;
const ESCROW: u8 = 9;
const PRICE: u64 = 100;

/// Build a signed receipt that the named service turn executed, by a trusted
/// executor — the proof the provider presents to FILL the promise hole.
fn signed_receipt(service_turn_hash: [u8; 32], executor: &SigningKey) -> ConditionProof {
    let mut receipt = TurnReceipt {
        turn_hash: service_turn_hash,
        agent: CellId::from_bytes([PROVIDER; 32]),
        ..Default::default()
    };
    let sig = executor.sign(&receipt.receipt_hash());
    receipt.executor_signature = Some(sig.to_bytes().to_vec());
    fulfillment_proof(receipt)
}

fn setup() -> (
    ServicePromiseExchange,
    ServicePromise,
    ServiceRequest,
    [u8; 32],
    SigningKey,
) {
    let executor = SigningKey::from_bytes(&[7u8; 32]);
    let trusted = vec![executor.verifying_key().to_bytes()];
    let exchange = ServicePromiseExchange::new(4, 0, cid(ESCROW), trusted);

    let service = ServiceId::of(CellId::from_bytes([0x5e; 32]), "render-report");
    let service_turn_hash = [0xAB; 32];
    let promise = ServicePromise {
        provider: cid(PROVIDER),
        service,
        service_turn_hash,
        payment_asset: asset(7),
        price: PRICE,
        timeout_height: 50,
    };
    let request = ServiceRequest {
        consumer: cid(CONSUMER),
        service,
        payment_asset: asset(7),
        offer: PRICE,
    };
    (exchange, promise, request, service_turn_hash, executor)
}

/// (1) HAPPY PATH + (4) CONSERVATION.
/// match → escrow → fulfill (signed receipt) → payment released to provider; the
/// payment asset is conserved at every step.
#[test]
fn happy_path_service_performed_then_paid() {
    let (exchange, promise, request, service_turn_hash, executor) = setup();
    let pay = asset(7);

    let m = exchange
        .match_one(&promise, &request)
        .expect("ring matches the pair");
    assert_eq!(m.price, PRICE);

    let k0 = exchange.seed_ledger(&m, PRICE);
    assert_eq!(k0.total_asset(&pay), PRICE as i128);

    // Escrow the payment.
    let (mut escrow, k1) = exchange.fund(&m, &k0).expect("payment escrows");
    assert_eq!(k1.get(CONSUMER, &pay), 0);
    assert_eq!(k1.get(ESCROW, &pay), PRICE as i128);
    assert_eq!(
        k1.total_asset(&pay),
        PRICE as i128,
        "conserved after escrow"
    );

    // The provider performs the service turn and presents the signed receipt.
    let proof = signed_receipt(service_turn_hash, &executor);
    let k2 = exchange
        .fulfill(&mut escrow, &k1, &proof, 10)
        .expect("a conforming receipt releases the payment");

    assert_eq!(escrow.status, EscrowStatus::Released);
    assert_eq!(k2.get(PROVIDER, &pay), PRICE as i128, "provider is paid");
    assert_eq!(k2.get(ESCROW, &pay), 0, "escrow drained");
    assert_eq!(k2.get(CONSUMER, &pay), 0);
    assert_eq!(k2.total_asset(&pay), PRICE as i128, "conserved end-to-end");
}

/// (2) REFUND PATH + (4) CONSERVATION.
/// match → escrow → window lapses with no fulfillment → payment refunded whole to
/// the consumer; conserved throughout.
#[test]
fn refund_path_unfulfilled_then_refunded() {
    let (exchange, promise, request, _, _) = setup();
    let pay = asset(7);

    let m = exchange.match_one(&promise, &request).unwrap();
    let k0 = exchange.seed_ledger(&m, PRICE);
    let (mut escrow, k1) = exchange.fund(&m, &k0).expect("payment escrows");

    // Refund before the window closes is refused.
    assert_eq!(
        exchange.refund(&mut escrow, &k1, 10),
        Err(ServicePromiseError::NotYetRefundable {
            current_height: 10,
            timeout_height: 50
        })
    );
    assert_eq!(escrow.status, EscrowStatus::Funded, "still held");

    // After the window lapses, the unfulfilled payment refunds to the consumer.
    let k2 = exchange
        .refund(&mut escrow, &k1, 51)
        .expect("lapsed promise refunds");
    assert_eq!(escrow.status, EscrowStatus::Refunded);
    assert_eq!(k2.get(CONSUMER, &pay), PRICE as i128, "consumer made whole");
    assert_eq!(k2.get(ESCROW, &pay), 0, "escrow drained");
    assert_eq!(k2.get(PROVIDER, &pay), 0, "provider got nothing");
    assert_eq!(k2.total_asset(&pay), PRICE as i128, "conserved end-to-end");
}

/// (3) ATOMICITY — no half-settle.
/// A forged fulfillment (a receipt NOT signed by a trusted executor) does not
/// release the payment: the escrow stays fully funded, nothing splits, and the
/// consumer can still refund the WHOLE amount once the window lapses.
#[test]
fn forged_fulfillment_never_half_pays() {
    let (exchange, promise, request, service_turn_hash, _trusted_executor) = setup();
    let pay = asset(7);

    let m = exchange.match_one(&promise, &request).unwrap();
    let k0 = exchange.seed_ledger(&m, PRICE);
    let (mut escrow, k1) = exchange.fund(&m, &k0).unwrap();

    // An UNTRUSTED party signs a receipt for the right turn hash.
    let impostor = SigningKey::from_bytes(&[42u8; 32]);
    let forged = signed_receipt(service_turn_hash, &impostor);
    let err = exchange
        .fulfill(&mut escrow, &k1, &forged, 10)
        .expect_err("an untrusted receipt must not release payment");
    assert!(matches!(err, ServicePromiseError::Unfulfilled(_)));

    // No half-settle: every felt is still held in escrow, status unchanged.
    assert_eq!(escrow.status, EscrowStatus::Funded);
    assert_eq!(k1.get(ESCROW, &pay), PRICE as i128);
    assert_eq!(k1.get(PROVIDER, &pay), 0);
    assert_eq!(k1.total_asset(&pay), PRICE as i128);

    // A receipt for the WRONG turn also fails to fill the hole.
    let trusted = SigningKey::from_bytes(&[7u8; 32]);
    let wrong_turn = signed_receipt([0x00; 32], &trusted);
    assert!(matches!(
        exchange.fulfill(&mut escrow, &k1, &wrong_turn, 10),
        Err(ServicePromiseError::Unfulfilled(_))
    ));

    // The consumer can still refund the whole payment after the window.
    let k2 = exchange
        .refund(&mut escrow, &k1, 51)
        .expect("still refundable");
    assert_eq!(k2.get(CONSUMER, &pay), PRICE as i128);
    assert_eq!(k2.total_asset(&pay), PRICE as i128);
}

/// (3) ATOMICITY — release and refund are mutually-exclusive one-shots.
/// Once released, refund is refused; once a (separate) escrow is refunded, fulfill
/// is refused. The held payment is taken by exactly one exit, exactly once.
#[test]
fn release_and_refund_are_one_shot_exclusive() {
    let (exchange, promise, request, service_turn_hash, executor) = setup();

    // Released escrow cannot also refund.
    let m = exchange.match_one(&promise, &request).unwrap();
    let k0 = exchange.seed_ledger(&m, PRICE);
    let (mut escrow, k1) = exchange.fund(&m, &k0).unwrap();
    let proof = signed_receipt(service_turn_hash, &executor);
    let k2 = exchange.fulfill(&mut escrow, &k1, &proof, 10).unwrap();
    assert_eq!(escrow.status, EscrowStatus::Released);
    assert_eq!(
        exchange.refund(&mut escrow, &k2, 51),
        Err(ServicePromiseError::AlreadySettled),
        "a released escrow cannot refund"
    );
    // And it cannot release twice.
    assert_eq!(
        exchange.fulfill(&mut escrow, &k2, &proof, 11),
        Err(ServicePromiseError::AlreadySettled),
        "a released escrow cannot release again"
    );

    // Refunded escrow cannot also fulfill.
    let m2 = exchange.match_one(&promise, &request).unwrap();
    let k0b = exchange.seed_ledger(&m2, PRICE);
    let (mut escrow2, k1b) = exchange.fund(&m2, &k0b).unwrap();
    let _ = exchange.refund(&mut escrow2, &k1b, 51).unwrap();
    assert_eq!(escrow2.status, EscrowStatus::Refunded);
    let proof2 = signed_receipt(service_turn_hash, &executor);
    assert_eq!(
        exchange.fulfill(&mut escrow2, &k1b, &proof2, 10),
        Err(ServicePromiseError::AlreadySettled),
        "a refunded escrow cannot release"
    );
}
