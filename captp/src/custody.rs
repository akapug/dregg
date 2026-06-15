//! Store-and-forward CUSTODY ACCOUNTABILITY: a signed receipt makes a relay that
//! ACCEPTED custody and then DROPPED a message convictable, while an honest relay
//! (one that delivered or refunded) is provably safe.
//!
//! # The gap this closes
//!
//! [`crate::store_forward`] proves the relay is a delay/drop channel that cannot read,
//! forge, or re-address a box (X25519 + ChaCha20-Poly1305 AEAD). But the relay's whole
//! sanctioned power is to **drop** ([`crate::store_forward::MessageRelay::expire`],
//! [`crate::store_forward::MessageRelay::drain`]'s reorder) — and a drop produced **no
//! evidence**: the relay signed NOTHING. `QueuedMessage` carried no relay commitment;
//! `StoreForwardClient.acknowledge` only mutated the *sender's* own local bookkeeping.
//! So a dropped message could not be proven *against the relay*, and nothing proved an
//! honest relay could not be slashed by a fabricated dispute. Accountability — "a
//! dropped message is convictable, an honest relay is safe" — was the missing calculus.
//!
//! This module is the Rust realization of the verified Lean model
//! `Dregg2.Exec.Custody` (`metatheory/Dregg2/Exec/CustodyReceipt.lean`). The
//! structures mirror it field-for-field; the two headline theorems
//! (`accepted_and_dropped_is_convictable`, `honest_relay_not_slashable`) are the
//! both-polarity teeth in the test module below.
//!
//! # The §8 seam, DISCHARGED here
//!
//! In the Lean model the receipt carries `sig : Bool` — the *carrier* for "the relay's
//! Ed25519 signature over the receipt preimage verifies" — and unforgeability is the
//! named obligation `receiptUnforgeable` routed to the crypto portal. This module is
//! exactly that portal: the receipt carries a real [`Signature`], and
//! [`CustodyReceipt::well_formed`] checks it against the relay's [`PublicKey`] over the
//! canonical, domain-separated preimage. `sig = true` becomes "verify_strict succeeds";
//! the EUF-CMA unforgeability of Ed25519 (only the relay's key can produce a verifying
//! signature) is supplied by `ed25519-dalek`, the vetted crate — never re-proved.
//!
//! # The adjudicator reads the CELL, not the disputant
//!
//! Per `CustodyReceipt.lean` §7.5: the verdict is a pure function of the inbox's own
//! authenticated, MONOTONE root (the `CapInbox`/`MerkleQueue` head root, which only ever
//! advances) plus a refund bit — never the disputant's claim. A malicious disputant
//! cannot manufacture a conviction by lying about the outcome, and an honest disputant
//! need not be believed. [`adjudicate_from_inbox`] is the realizable decision procedure
//! the dispute path runs against the inbox cell's root.

use dregg_types::{PublicKey, Signature, SigningKey, sign};
use serde::{Deserialize, Serialize};

use crate::FederationId;

// =============================================================================
// §1 — The signed CustodyReceipt and the custody outcome
// =============================================================================

/// Domain-separation tag for the custody-receipt signing preimage. Bump on any
/// wire-format change to the preimage. Distinct tag ⇒ a receipt signature can never be
/// replayed as a handoff cert or any other signed object (cross-protocol confusion).
pub const CUSTODY_RECEIPT_DOMAIN: &[u8] = b"dregg-custody-receipt-v1";

/// **`CustodyReceipt`** — the relay's SIGNED promise of custody, returned when it accepts
/// a box for store-and-forward. Mirrors `Dregg2.Exec.Custody.CustodyReceipt`. It binds:
///
///   * `relay`        — the operator identity that signed it (the party held accountable);
///   * `content_hash` — the content-address of the box the relay accepted (binds the
///     receipt to a specific message; a receipt for a different `content_hash` does not
///     cover this box);
///   * `inbox_owner`  — the destination the box is held FOR (binds custody to the right
///     inbox);
///   * `old_root` / `new_root` — the inbox-root transition the relay PROMISES to effect
///     on delivery (`old_root` = the inbox root at accept time, `new_root` = the root
///     after the box is appended);
///   * `accept_by`    — the deadline height: the relay must DELIVER or REFUND by this
///     height, else it has DROPPED (the accept-or-refund-by clause);
///   * `signature`    — the §8 carrier MADE REAL: the relay's Ed25519 signature over the
///     domain-separated preimage. In the Lean model this is the `sig : Bool` carrier;
///     here it is the actual signature, verified by [`Self::well_formed`].
///
/// The relay's [`PublicKey`] is *not* stored inline — it is `relay` interpreted as a key
/// ([`Self::relay_pubkey`]): a `FederationId` in the unified lace model is the operator's
/// committee commitment / pubkey. This is what makes a valid conviction bind exactly the
/// signer (`conviction_binds_the_signer`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CustodyReceipt {
    /// The operator identity that signed this receipt (the accountable party).
    pub relay: FederationId,
    /// Content-address of the accepted box (BLAKE3 of the ciphertext envelope).
    pub content_hash: [u8; 32],
    /// The inbox owner the box is held FOR.
    pub inbox_owner: FederationId,
    /// The inbox root at accept time (the transition's source).
    pub old_root: [u8; 32],
    /// The inbox root the relay PROMISES to effect on delivery (the transition's target).
    pub new_root: [u8; 32],
    /// Deadline height: deliver or refund by here, else dropped.
    pub accept_by: u64,
    /// §8 carrier: the relay's Ed25519 signature over [`Self::signing_preimage`].
    pub signature: Signature,
}

impl CustodyReceipt {
    /// The canonical, domain-separated preimage the relay signs. Includes every binding
    /// field EXCEPT the signature itself, so two receipts differing in any bound field
    /// produce distinct preimages (and thus distinct signatures — no field can be swapped
    /// post-hoc without invalidating the signature).
    pub fn signing_preimage(
        relay: &FederationId,
        content_hash: &[u8; 32],
        inbox_owner: &FederationId,
        old_root: &[u8; 32],
        new_root: &[u8; 32],
        accept_by: u64,
    ) -> Vec<u8> {
        let mut msg = Vec::with_capacity(CUSTODY_RECEIPT_DOMAIN.len() + 32 * 4 + 32 + 8);
        msg.extend_from_slice(CUSTODY_RECEIPT_DOMAIN);
        msg.extend_from_slice(&relay.0);
        msg.extend_from_slice(content_hash);
        msg.extend_from_slice(&inbox_owner.0);
        msg.extend_from_slice(old_root);
        msg.extend_from_slice(new_root);
        msg.extend_from_slice(&accept_by.to_le_bytes());
        msg
    }

    /// The preimage for THIS receipt's bound fields.
    fn preimage(&self) -> Vec<u8> {
        Self::signing_preimage(
            &self.relay,
            &self.content_hash,
            &self.inbox_owner,
            &self.old_root,
            &self.new_root,
            self.accept_by,
        )
    }

    /// **The relay signs a custody receipt** — the object `POST /relay/send` (or
    /// [`crate::store_forward::MessageRelay::accept_custody`]) returns. The relay's
    /// `SigningKey` produces an Ed25519 signature over the canonical preimage; the
    /// `relay` id MUST be the public key matching `relay_key` (else the receipt will not
    /// be well-formed and convicts nobody — exactly the binding the model demands).
    pub fn sign(
        relay: FederationId,
        relay_key: &SigningKey,
        content_hash: [u8; 32],
        inbox_owner: FederationId,
        old_root: [u8; 32],
        new_root: [u8; 32],
        accept_by: u64,
    ) -> Self {
        let preimage = Self::signing_preimage(
            &relay,
            &content_hash,
            &inbox_owner,
            &old_root,
            &new_root,
            accept_by,
        );
        let signature = sign(relay_key, &preimage);
        Self {
            relay,
            content_hash,
            inbox_owner,
            old_root,
            new_root,
            accept_by,
            signature,
        }
    }

    /// The relay identity interpreted as an Ed25519 public key (the unified-lace
    /// equivalence: a `FederationId` IS the operator's pubkey/committee commitment).
    pub fn relay_pubkey(&self) -> PublicKey {
        PublicKey(self.relay.0)
    }

    /// **`sig` made real** — the §8 carrier: does the relay's signature over the canonical
    /// preimage verify against the `relay` public key? This is the discharge of the Lean
    /// `sig : Bool` and the `receiptUnforgeable` obligation: only the holder of the
    /// `relay` secret key can make this return `true` (Ed25519 EUF-CMA, by `ed25519-dalek`
    /// `verify_strict`). A forged receipt (no relay key) yields `false`.
    pub fn sig_verifies(&self) -> bool {
        self.relay_pubkey().verify(&self.preimage(), &self.signature)
    }
}

/// **`CustodyOutcome`** — what the relay actually DID with the accepted box, observed
/// at/after the deadline. Mirrors `Dregg2.Exec.Custody.CustodyOutcome`: two honest fates,
/// one dishonest.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CustodyOutcome {
    /// The recipient drained the box and the inbox root advanced to `root` (HONEST iff
    /// `root` is the promised `new_root`); the recipient's drain witnesses delivery.
    Delivered {
        /// The inbox root after delivery (the cell's authenticated head).
        root: [u8; 32],
    },
    /// The relay returned the fee and released custody before the deadline. HONEST: the
    /// accept-OR-refund-by half — it could not deliver but did not silently keep custody.
    Refunded,
    /// The deadline passed with the box neither delivered nor refunded. DISHONEST: the
    /// relay took custody (and the fee) and silently lost the message.
    Dropped,
}

impl CustodyOutcome {
    /// **`outcome_honest`** — the relay HONORED the receipt: delivered the box to the
    /// PROMISED root, or refunded before the deadline. `Dropped` is dishonest; a
    /// `Delivered` to the WRONG root is also dishonest (the relay effected a different
    /// inbox transition than it signed for — caught here, not papered over). Mirrors
    /// `outcomeHonest`.
    pub fn is_honest_for(&self, receipt: &CustodyReceipt) -> bool {
        match self {
            CustodyOutcome::Delivered { root } => *root == receipt.new_root,
            CustodyOutcome::Refunded => true,
            CustodyOutcome::Dropped => false,
        }
    }
}

// =============================================================================
// §2 — EvidenceOfDrop: the conviction object, and the adjudicator's verdict
// =============================================================================

/// **`EvidenceOfDrop`** — the conviction object submitted by the inbox owner against a
/// relay (the `POST /relay/dispute` body). Mirrors `Dregg2.Exec.Custody.EvidenceOfDrop`:
///
///   * `receipt`         — the relay's OWN signed [`CustodyReceipt`] (binds the dispute to
///     a specific relay, content, owner, and promised transition);
///   * `claimed_outcome` — the outcome the disputant CLAIMS holds at the deadline. NOTE:
///     this is the disputant's *assertion*; the realizable adjudicator
///     ([`adjudicate_from_inbox`]) does NOT trust it — it reads the inbox cell. Carried so
///     a dispute is self-describing and to prove the claim is inert
///     (`disputant_claim_irrelevant`);
///   * `at_height`       — the height the dispute is raised at (must be ≥ `accept_by`:
///     the deadline must have PASSED for a non-delivery to be a drop, not pending custody).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceOfDrop {
    /// The relay's own signed receipt (the binding to a specific accountable party).
    pub receipt: CustodyReceipt,
    /// The outcome the disputant claims (an assertion; the cell read overrides it).
    pub claimed_outcome: CustodyOutcome,
    /// The height the dispute is raised at (must be ≥ `receipt.accept_by`).
    pub at_height: u64,
}

impl EvidenceOfDrop {
    /// **`well_formed`** — the evidence is admissible: the receipt's signature verifies
    /// (binding it to `receipt.relay`) AND the dispute is raised at or after the deadline
    /// (`at_height ≥ accept_by`, so the relay has actually defaulted). A forged receipt or
    /// a premature dispute is NOT admissible — the two non-malleability gates. Mirrors
    /// `wellFormed`.
    pub fn well_formed(&self) -> bool {
        self.receipt.sig_verifies() && self.at_height >= self.receipt.accept_by
    }

    /// **`adjudicate`** — the verdict given the TRUE custody outcome (what the relay
    /// actually did, established by the inbox cell's authenticated state — see
    /// [`true_outcome_from_inbox`]). Returns `slash` (`true`) IFF the evidence is
    /// well-formed AND the true outcome is `Dropped`; otherwise `acquit`. It does NOT take
    /// the disputant's `claimed_outcome` on faith. Mirrors `adjudicate`.
    pub fn adjudicate(&self, true_outcome: CustodyOutcome) -> bool {
        self.well_formed() && matches!(true_outcome, CustodyOutcome::Dropped)
    }

    /// **`evidence_of_drop`** — the canonical evidence the inbox owner assembles from a
    /// relay's receipt once the deadline has passed (`at_height = accept_by`, the earliest
    /// admissible height), claiming the box was `Dropped`. Mirrors `evidenceOfDrop`.
    pub fn from_receipt(receipt: CustodyReceipt) -> Self {
        let at_height = receipt.accept_by;
        Self {
            receipt,
            claimed_outcome: CustodyOutcome::Dropped,
            at_height,
        }
    }
}

// =============================================================================
// §7.5 — The REALIZABLE adjudicator: the true outcome is DERIVED from the inbox's
// authenticated monotone root, not TAKEN from the disputant
// =============================================================================

/// **`InboxState`** — exactly what the adjudication path READS to establish the true
/// custody outcome: the inbox's authenticated, MONOTONE root (the `CapInbox` /
/// [`crate::store_forward`] queue head root, which only ever advances) at the dispute
/// height, plus `refund_recorded` — the bit set by the relay's authenticated refund move
/// (the accept-OR-refund-by other half). The disputant's claim is NOT here. Mirrors
/// `Dregg2.Exec.Custody.InboxState`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InboxState {
    /// The inbox's authenticated root at the dispute height. MONOTONE: once it reaches a
    /// value it never retreats (the cursor discipline of the FIFO inbox).
    pub root: [u8; 32],
    /// The relay recorded a refund before the deadline (an authenticated cell event).
    pub refund_recorded: bool,
}

impl InboxState {
    /// **`root_reached`** — the inbox's authenticated root has reached (or, by monotonicity,
    /// passed) the `promised` root. Once delivery advances the root to `new_root`,
    /// subsequent activity only pushes it FURTHER, so a later root that still EQUALS the
    /// promise witnesses delivery; an unrelated advance that never equals the promise does
    /// not. Because roots are opaque content-addresses (not ordered), "reached" is
    /// equality with the promised root OR a recorded witness that this exact transition
    /// occurred. We model the authenticated cell as exposing the promised root directly:
    /// the queue's delivery event sets `root == new_root`. Mirrors `rootReached` (with the
    /// content-address equality reading of the monotone cursor).
    pub fn root_reached(&self, promised: &[u8; 32]) -> bool {
        self.root == *promised
    }

    /// **`true_outcome_from_inbox`** — the custody outcome DERIVED from this authenticated
    /// inbox state for `receipt`. NOT the disputant's claim: a verified fact read off the
    /// cell. Mirrors `trueOutcomeFromInbox`:
    ///
    ///   * authenticated root reached the promised `new_root` → `Delivered { new_root }`
    ///     (HONEST);
    ///   * else if a refund was recorded → `Refunded` (HONEST);
    ///   * else → `Dropped` (the deadline passed, the root never reached the promise, no
    ///     refund — established WITHOUT trusting anyone's word).
    pub fn true_outcome(&self, receipt: &CustodyReceipt) -> CustodyOutcome {
        if self.root_reached(&receipt.new_root) {
            CustodyOutcome::Delivered {
                root: receipt.new_root,
            }
        } else if self.refund_recorded {
            CustodyOutcome::Refunded
        } else {
            CustodyOutcome::Dropped
        }
    }
}

/// **`adjudicate_from_inbox`** — the REALIZABLE adjudicator the dispute path runs: it
/// derives the true outcome from the inbox's authenticated state and feeds it to
/// [`EvidenceOfDrop::adjudicate`]. No disputant claim is consulted. Returns `slash`
/// (`true`) IFF the dispute is well-formed AND the authenticated root fell short of the
/// promise AND no refund was recorded. Mirrors `adjudicateFromInbox` and is governed by
/// the `conviction_iff_root_short` keystone. This is the function `POST /relay/dispute`
/// evaluates against the inbox cell's root.
pub fn adjudicate_from_inbox(evidence: &EvidenceOfDrop, inbox: &InboxState) -> bool {
    let true_outcome = inbox.true_outcome(&evidence.receipt);
    evidence.adjudicate(true_outcome)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_types::generate_keypair;

    // A relay identity whose FederationId IS its Ed25519 public key (unified-lace
    // equivalence). We construct a real keypair and use the public key bytes as the id.
    fn relay_identity() -> (FederationId, SigningKey) {
        let (sk, pk) = generate_keypair();
        (FederationId(pk.0), sk)
    }

    fn owner() -> FederationId {
        FederationId([0x03; 32])
    }

    fn h(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    /// Build the demo receipt of `CustodyReceipt.lean` §7: relay accepts box `0xAB..`,
    /// for the owner, promising the root to advance `old → new` by deadline 500.
    fn demo_receipt() -> (CustodyReceipt, SigningKey) {
        let (relay, sk) = relay_identity();
        let r = CustodyReceipt::sign(
            relay,
            &sk,
            h(0xAB), // content_hash
            owner(),
            h(0x64), // old_root
            h(0x8E), // new_root (the promised transition target)
            500,     // accept_by
        );
        (r, sk)
    }

    // ── §3 KEYSTONE (a): an accepted-and-dropped relay is CONVICTABLE ──────────────

    #[test]
    fn accepted_and_dropped_is_convictable() {
        // Mirrors theorem `accepted_and_dropped_is_convictable`: a relay that signed a
        // valid receipt and DROPPED is convictable by its OWN signature.
        let (r, _sk) = demo_receipt();
        assert!(r.sig_verifies(), "the relay's real signature must verify");

        let evidence = EvidenceOfDrop::from_receipt(r);
        assert!(evidence.well_formed(), "own signature + deadline reached");
        assert!(
            evidence.adjudicate(CustodyOutcome::Dropped),
            "verdict on a true drop must be SLASH"
        );
    }

    // ── §4 KEYSTONE (b): an HONEST relay is NOT slashable (no false conviction) ─────

    #[test]
    fn honest_relay_not_slashable() {
        // Mirrors theorem `honest_relay_not_slashable`: if the relay HONORED the receipt
        // (delivered to the promised root, or refunded), NO claim convicts it — the
        // adjudicator decides on the verified TRUE outcome, not the disputant's claim.
        let (r, _sk) = demo_receipt();
        let new_root = r.new_root;
        let evidence = EvidenceOfDrop::from_receipt(r);

        // Honest delivery to the promised root: acquit even on the disputant's drop-claim.
        let delivered = CustodyOutcome::Delivered { root: new_root };
        assert!(delivered.is_honest_for(&evidence.receipt));
        assert!(
            !evidence.adjudicate(delivered),
            "an honestly-delivered relay must be ACQUITTED"
        );

        // Honest refund: acquit.
        assert!(CustodyOutcome::Refunded.is_honest_for(&evidence.receipt));
        assert!(
            !evidence.adjudicate(CustodyOutcome::Refunded),
            "an honestly-refunded relay must be ACQUITTED"
        );
    }

    #[test]
    fn wrong_root_delivery_is_not_honest() {
        // Mirrors the §7 #guard `outcomeHonest demoReceipt (.delivered 999) == false`:
        // the relay effected a DIFFERENT inbox transition than it signed for ⇒ dishonest.
        let (r, _sk) = demo_receipt();
        let wrong = CustodyOutcome::Delivered { root: h(0xFF) };
        assert!(
            !wrong.is_honest_for(&r),
            "delivery to the wrong root is NOT honest (caught, not excused)"
        );
    }

    // ── §5 non-malleability / binding teeth ────────────────────────────────────────

    #[test]
    fn forged_receipt_no_conviction() {
        // Mirrors `forged_receipt_no_conviction`: a receipt fabricated WITHOUT the relay's
        // key convicts nobody. We forge by signing the preimage with the WRONG key (an
        // attacker who does not hold the relay's secret) — `verify_strict` against the
        // relay's pubkey then fails, so the evidence is not well-formed.
        let (r, _sk) = demo_receipt();
        let (attacker_sk, _attacker_pk) = generate_keypair();
        let bad_sig = sign(&attacker_sk, &r.preimage());
        let forged = CustodyReceipt {
            signature: bad_sig,
            ..r
        };
        assert!(
            !forged.sig_verifies(),
            "a signature by a non-relay key must NOT verify against the relay pubkey"
        );
        let evidence = EvidenceOfDrop::from_receipt(forged);
        assert!(!evidence.well_formed());
        assert!(
            !evidence.adjudicate(CustodyOutcome::Dropped),
            "a forged receipt convicts nobody even on a true drop"
        );
    }

    #[test]
    fn tampered_field_breaks_signature() {
        // Sharper than the Lean Bool model: a relay-signed receipt whose bound field is
        // mutated post-hoc no longer verifies (the preimage covers every field). This is
        // the real-crypto strengthening of the `sig : Bool` carrier.
        let (r, _sk) = demo_receipt();
        assert!(r.sig_verifies());
        // Swap the promised new_root while keeping the original signature.
        let tampered = CustodyReceipt {
            new_root: h(0x99),
            ..r.clone()
        };
        assert!(
            !tampered.sig_verifies(),
            "mutating a bound field must invalidate the relay's signature"
        );
        // Swapping the content_hash likewise.
        let tampered2 = CustodyReceipt {
            content_hash: h(0x11),
            ..r
        };
        assert!(!tampered2.sig_verifies());
    }

    #[test]
    fn premature_dispute_inadmissible() {
        // Mirrors `premature_dispute_inadmissible`: a drop-claim raised BEFORE the deadline
        // (height < accept_by) is inadmissible — the relay has not yet defaulted.
        let (r, _sk) = demo_receipt();
        let accept_by = r.accept_by;
        let early = EvidenceOfDrop {
            receipt: r,
            claimed_outcome: CustodyOutcome::Dropped,
            at_height: accept_by - 1,
        };
        assert!(!early.well_formed(), "a premature dispute is not well-formed");
        assert!(!early.adjudicate(CustodyOutcome::Dropped));
    }

    #[test]
    fn conviction_binds_the_signer() {
        // Mirrors `conviction_binds_the_signer` under the `receiptUnforgeable` seam: a
        // well-formed conviction can only be against the relay that signed. The relay
        // pubkey recovered from a verifying receipt IS the accountable party, and no other
        // identity could have produced a verifying signature (Ed25519 EUF-CMA).
        let (r, _sk) = demo_receipt();
        let evidence = EvidenceOfDrop::from_receipt(r.clone());
        assert!(evidence.well_formed());
        // The signer named in the receipt is exactly the relay whose pubkey verifies it.
        assert_eq!(evidence.receipt.relay.0, evidence.receipt.relay_pubkey().0);
        // A DIFFERENT relay id (different pubkey) on the same signature does not verify —
        // the conviction cannot be re-pointed at an innocent party.
        let (other_id, _other_sk) = relay_identity();
        let mispointed = CustodyReceipt {
            relay: other_id,
            ..r
        };
        assert!(
            !mispointed.sig_verifies(),
            "a receipt cannot be re-pointed at an innocent relay"
        );
    }

    // ── §7.5 the REALIZABLE adjudicator: verdict from the inbox cell, claim inert ───

    #[test]
    fn conviction_from_inbox_when_root_short() {
        // Mirrors `conviction_iff_root_short` (slash direction) + the §7.5(d) #guard
        // `adjudicateFromInbox (evidenceOfDrop demoReceipt) droppedInbox == true`: the
        // authenticated root FELL SHORT of the promise and no refund ⇒ the realizable
        // adjudicator SLASHES — established from the cell, NOT the disputant.
        let (r, _sk) = demo_receipt();
        let new_root = r.new_root;
        let evidence = EvidenceOfDrop::from_receipt(r);
        // Dropped inbox: root is the OLD root (never advanced to the promise), no refund.
        let dropped_inbox = InboxState {
            root: h(0x64), // old_root != new_root
            refund_recorded: false,
        };
        assert_eq!(
            dropped_inbox.true_outcome(&evidence.receipt),
            CustodyOutcome::Dropped
        );
        assert!(
            adjudicate_from_inbox(&evidence, &dropped_inbox),
            "a genuine drop (root short, no refund) convicts from the cell"
        );
        // Sanity: the promised root differs from the dropped root.
        assert_ne!(new_root, dropped_inbox.root);
    }

    #[test]
    fn acquit_from_inbox_when_delivered_or_refunded() {
        // Mirrors `honest_relay_not_slashable_from_inbox` + the §7.5(d) acquit #guards: if
        // the authenticated root reached the promise (delivered) OR a refund was recorded,
        // the realizable adjudicator ACQUITS for ANY evidence, regardless of the claim.
        let (r, _sk) = demo_receipt();
        let new_root = r.new_root;
        let evidence = EvidenceOfDrop::from_receipt(r);

        // Delivered inbox: root reached the promise.
        let delivered_inbox = InboxState {
            root: new_root,
            refund_recorded: false,
        };
        assert!(matches!(
            delivered_inbox.true_outcome(&evidence.receipt),
            CustodyOutcome::Delivered { .. }
        ));
        assert!(
            !adjudicate_from_inbox(&evidence, &delivered_inbox),
            "delivery witnessed in the cell ⇒ acquit even on the drop-claim"
        );

        // Refunded inbox: root short, but refund recorded.
        let refunded_inbox = InboxState {
            root: h(0x64),
            refund_recorded: true,
        };
        assert_eq!(
            refunded_inbox.true_outcome(&evidence.receipt),
            CustodyOutcome::Refunded
        );
        assert!(
            !adjudicate_from_inbox(&evidence, &refunded_inbox),
            "a recorded refund ⇒ acquit (accept-or-refund-by half, read off the cell)"
        );
    }

    #[test]
    fn disputant_claim_irrelevant() {
        // Mirrors `disputant_claim_irrelevant`: the verdict does NOT depend on the
        // disputant's claimed_outcome AT ALL — two evidences with the same receipt + height
        // but arbitrarily different claims adjudicate identically against the same inbox.
        let (r, _sk) = demo_receipt();
        let dropped_inbox = InboxState {
            root: h(0x64),
            refund_recorded: false,
        };
        let claim_drop = EvidenceOfDrop {
            receipt: r.clone(),
            claimed_outcome: CustodyOutcome::Dropped,
            at_height: 500,
        };
        let claim_delivered = EvidenceOfDrop {
            receipt: r.clone(),
            claimed_outcome: CustodyOutcome::Delivered { root: h(0xFF) },
            at_height: 500,
        };
        let claim_refunded = EvidenceOfDrop {
            receipt: r,
            claimed_outcome: CustodyOutcome::Refunded,
            at_height: 500,
        };
        // All three adjudicate identically against the genuine-drop inbox (all convict).
        let v1 = adjudicate_from_inbox(&claim_drop, &dropped_inbox);
        let v2 = adjudicate_from_inbox(&claim_delivered, &dropped_inbox);
        let v3 = adjudicate_from_inbox(&claim_refunded, &dropped_inbox);
        assert_eq!(v1, v2);
        assert_eq!(v2, v3);
        assert!(v1, "the cell shows a drop ⇒ all convict regardless of the claim");
    }

    #[test]
    fn forged_receipt_acquits_even_against_drop_inbox() {
        // Mirrors the §7.5(d) #guard: a forged receipt convicts nobody even against a
        // genuine-drop inbox (the §5 binding tooth composes with the cell-read adjudicator).
        let (r, _sk) = demo_receipt();
        let (attacker_sk, _pk) = generate_keypair();
        let forged = CustodyReceipt {
            signature: sign(&attacker_sk, &r.preimage()),
            ..r
        };
        let evidence = EvidenceOfDrop::from_receipt(forged);
        let dropped_inbox = InboxState {
            root: h(0x64),
            refund_recorded: false,
        };
        assert!(
            !adjudicate_from_inbox(&evidence, &dropped_inbox),
            "not well-formed ⇒ acquit regardless of the cell"
        );
    }

    #[test]
    fn full_lifecycle_honest_custody_then_deliver() {
        // End-to-end: an HONEST custody+deliver verifies (the recipient drained, the root
        // reached the promise) — the headline scenario named in the recovered keystone.
        let (relay, relay_sk) = relay_identity();
        let promised_root = h(0x8E);
        // 1. Relay accepts custody and signs a receipt.
        let receipt = CustodyReceipt::sign(
            relay,
            &relay_sk,
            h(0xAB),
            owner(),
            h(0x64),
            promised_root,
            500,
        );
        assert!(receipt.sig_verifies());
        // 2. Recipient comes online; the inbox root advances to the promised root.
        let inbox = InboxState {
            root: promised_root,
            refund_recorded: false,
        };
        // 3. Even if SOMEONE files a drop dispute, the cell shows delivery ⇒ acquit.
        let dispute = EvidenceOfDrop::from_receipt(receipt);
        assert!(
            !adjudicate_from_inbox(&dispute, &inbox),
            "honest custody+deliver: relay is provably safe"
        );
    }

    #[test]
    fn full_lifecycle_accepted_then_withheld_is_at_fault() {
        // End-to-end: a relay that ACCEPTED-but-WITHHELD is provably at fault — the other
        // headline scenario. The relay signed (it accepted), the deadline passed, the root
        // never reached the promise, no refund ⇒ the cell-read adjudicator convicts.
        let (relay, relay_sk) = relay_identity();
        let promised_root = h(0x8E);
        let receipt = CustodyReceipt::sign(
            relay,
            &relay_sk,
            h(0xAB),
            owner(),
            h(0x64),
            promised_root,
            500,
        );
        // Deadline passed; inbox never advanced (the relay withheld), no refund.
        let inbox = InboxState {
            root: h(0x64),
            refund_recorded: false,
        };
        let dispute = EvidenceOfDrop::from_receipt(receipt);
        assert!(dispute.well_formed());
        assert!(
            adjudicate_from_inbox(&dispute, &inbox),
            "accepted-then-withheld: the relay is provably at fault"
        );
    }
}
