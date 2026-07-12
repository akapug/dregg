//! Owner-anchored, BILATERAL fraud proofs: compose an operator's SIGNED promise with a
//! contradicting fact drawn from the grain's OWN authenticated history, so that any owner
//! (or any light client) can convict the operator WITHOUT global consensus.
//!
//! # The shape of a fraud proof (the M1 composition)
//!
//! A fraud proof is the pairing of two things an owner already holds:
//!
//!   1. **the signed operator promise** — a [`CustodyReceipt`]: the operator (the relay /
//!      store-and-forward custodian) put its Ed25519 signature over a specific commitment
//!      `X` — *"this box (`content_hash`), held for this owner, WILL be delivered to
//!      `new_root` or refunded, by height `accept_by`."* Only the operator's key can
//!      produce it ([`CustodyReceipt::sig_verifies`], EUF-CMA via `ed25519-dalek`);
//!   2. **the owner-anchored contradicting fact** — [`OwnerAnchoredFact`]: the grain's
//!      OWN authenticated inbox-cell state ([`InboxState`], the sticky content-addressed
//!      delivery-witness). This is a fact the owner reads off its own cell — or that a
//!      light client reads off the grain's finalized WHOLE-CHAIN history (see
//!      *Provenance* below). It establishes the TRUE outcome, `not-X`.
//!
//! [`FraudProof::verify`] convicts IFF the operator signed `X`, the deadline has passed,
//! and the owner-anchored fact shows `not-X` (the box was neither delivered nor refunded).
//! A promise that was HONORED acquits; a FORGED (unsigned / wrong-key) promise convicts
//! nobody; a PREMATURE proof (deadline not yet reached) acquits. Both polarities are teeth
//! in the test module.
//!
//! # Why this is DREGGIC — no global ledger, no global state
//!
//! The verdict is a PURE FUNCTION of two owner-held inputs: the operator's own signature
//! and the owner's own cell. There is:
//!
//!   * **no global-owned adjudicator** — the owner (or any light client the owner hands the
//!     proof to) runs [`FraudProof::verify`] locally;
//!   * **no global ledger / no consensus round** — nothing is looked up in a world state;
//!     the contradiction is BILATERAL (operator ⇄ owner), per-grain, owner-anchored;
//!   * **no ACL** — the operator is bound by a *capability it signed itself* (the receipt),
//!     not by an entry in someone's access list.
//!
//! That is the whole point of the M1 primitive: the market rides on convictions any party
//! can check offline, so a defaulting operator is convictable without asking a global
//! authority for permission or for the truth.
//!
//! # Provenance of the fact (the WholeChainProof edge)
//!
//! [`OwnerAnchoredFact::InboxWitness`] carries an [`InboxState`] — the sticky
//! delivery-witness bit + refund bit + live root the adjudicator reads. This crate takes
//! that state as an owner-anchored INPUT; it deliberately does NOT re-derive it here (the
//! circuit/prover machinery lives in the `dregg-lightclient` / `dregg-circuit-prove`
//! crates, whose heavy prover deps must not leak into the CapTP data plane). The honest
//! link: the very same `(delivered_content_hashes, root, refund)` an owner passes to
//! [`InboxState::from_dequeue`] is what a light client obtains from a VERIFIED read of the
//! grain's own finalized history — `dregg_lightclient::verify_finalized_history` attests a
//! whole-chain fold `AttestedHistory` (every finalized turn of the grain's inbox cell,
//! correctly ordered, finalized by the grain's committee quorum), and the delivered
//! content-hashes + head root fall out of that attested cell. So the fact is owner-anchored
//! whether the owner reads its raw authenticated cell or a peer light-verifies the grain's
//! `WholeChainProof`; the fraud proof consumes the projection either way.
//!
//! # Relationship to `custody`
//!
//! [`crate::custody`] already realizes the drop-specific referee
//! ([`adjudicate_from_inbox`]). This module is the GENERAL bilateral wrapper around it: it
//! names the two halves (signed promise, owner-anchored fact), reports a structured
//! [`Verdict`] (who is convicted and why, or why not), and REUSES
//! [`adjudicate_from_inbox`] as the outcome-deriving core rather than re-implementing the
//! calculus. The `verdict_agrees_with_referee` test pins the two to agree — this is a lens
//! over the verified referee, not a divergent second implementation.

use crate::FederationId;
use crate::custody::{
    CustodyOutcome, CustodyReceipt, EvidenceOfDrop, InboxState, adjudicate_from_inbox,
};

// =============================================================================
// §1 — The owner-anchored fact
// =============================================================================

/// **`OwnerAnchoredFact`** — a fact drawn from the grain's OWN authenticated state that can
/// CONTRADICT an operator's signed promise. Owner-anchored: it is read off the owner's own
/// cell (or a light-verified read of the grain's finalized history — see the module docs on
/// *Provenance*), never taken from the operator or from a global ledger.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OwnerAnchoredFact {
    /// The grain inbox cell's delivery-witness state: the sticky, content-addressed record
    /// of whether THIS box left the queue toward the recipient (plus the refund bit and the
    /// live monotone root). This is the realizable, overshoot/reorg-robust fact the custody
    /// referee reads ([`InboxState`]).
    InboxWitness(InboxState),
}

impl OwnerAnchoredFact {
    /// Build the inbox-witness fact content-address-HONESTLY from the grain's authenticated
    /// delivery evidence — the set of dequeued box `content_hash`es the inbox emitted, the
    /// live head `root`, and whether a refund was recorded. Delegates to
    /// [`InboxState::from_dequeue`], so the witness bit is set IFF some dequeue carried
    /// `receipt.content_hash` (sticky, order-free, root-movement-robust).
    pub fn from_dequeue(
        receipt: &CustodyReceipt,
        delivered_content_hashes: &[[u8; 32]],
        root: [u8; 32],
        refund_recorded: bool,
    ) -> Self {
        OwnerAnchoredFact::InboxWitness(InboxState::from_dequeue(
            receipt,
            delivered_content_hashes,
            root,
            refund_recorded,
        ))
    }

    /// The TRUE custody outcome this fact establishes for `receipt` — delegated to the
    /// verified derivation [`InboxState::true_outcome`] (delivered / refunded / dropped).
    fn true_outcome(&self, receipt: &CustodyReceipt) -> CustodyOutcome {
        match self {
            OwnerAnchoredFact::InboxWitness(inbox) => inbox.true_outcome(receipt),
        }
    }
}

// =============================================================================
// §2 — The verdict
// =============================================================================

/// **`Conviction`** — the outcome of a fraud proof that CONVICTS: the operator's own signed
/// promise is contradicted by the owner-anchored fact. Binds exactly the signer (the party
/// whose key produced the receipt), the box, and the inbox it was held for — the data a
/// market/slashing path needs, all derived from the operator's OWN commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conviction {
    /// The convicted operator — the party bound by the signature it produced
    /// (`promise.relay`; equal to the pubkey that verifies the receipt).
    pub operator: FederationId,
    /// The content-address of the box the operator promised to deliver-or-refund.
    pub content_hash: [u8; 32],
    /// The inbox owner the box was held FOR (the party the promise ran to).
    pub inbox_owner: FederationId,
}

/// **`Acquittal`** — why a fraud proof did NOT convict. Distinguishing the reasons keeps
/// the both-polarity guarantee legible (an honest operator is safe; a forged or premature
/// proof convicts nobody) rather than collapsing every non-conviction into one bit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Acquittal {
    /// The promise's signature does NOT verify against `promise.relay` — a forged /
    /// wrong-key / unsigned commitment. It binds no operator, so it convicts nobody
    /// (the §5 binding tooth: a conviction can only run against the actual signer).
    PromiseUnsigned,
    /// The proof was raised BEFORE the promise's deadline (`at_height < accept_by`): the
    /// operator has not yet defaulted, so non-delivery is pending custody, not a drop.
    PromisePending,
    /// The owner-anchored fact shows the promise was HONORED — the box was delivered
    /// (witnessed in the cell, robust to overshoot) or a refund was recorded. `X` holds;
    /// there is no contradiction.
    PromiseHonored,
}

/// **`Verdict`** — the result of adjudicating a [`FraudProof`]. Either the operator is
/// convictable (with the binding data) or it is acquitted (with the reason).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The operator signed `X`, the deadline passed, and the owner-anchored fact shows
    /// `not-X` — CONVICTABLE without global consensus.
    Convict(Conviction),
    /// No conviction, with the reason (honored / premature / forged).
    Acquit(Acquittal),
}

impl Verdict {
    /// Does this verdict convict? Convenience for the common boolean check.
    pub fn convicts(&self) -> bool {
        matches!(self, Verdict::Convict(_))
    }
}

impl core::fmt::Display for Verdict {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Verdict::Convict(c) => write!(
                f,
                "CONVICT operator {} — signed promise contradicted by the owner-anchored fact \
                 (box {} held for owner {} was neither delivered nor refunded by the deadline)",
                hex16(&c.operator.0),
                hex16(&c.content_hash),
                hex16(&c.inbox_owner.0),
            ),
            Verdict::Acquit(Acquittal::PromiseUnsigned) => write!(
                f,
                "ACQUIT — the promise signature does not verify (forged/unsigned): binds no operator"
            ),
            Verdict::Acquit(Acquittal::PromisePending) => write!(
                f,
                "ACQUIT — the proof is premature (deadline not yet reached): custody still pending"
            ),
            Verdict::Acquit(Acquittal::PromiseHonored) => write!(
                f,
                "ACQUIT — the owner-anchored fact shows the promise was honored (delivered or refunded)"
            ),
        }
    }
}

/// A short hex rendering of the first 4 bytes of a 32-byte id, for diagnostics only.
fn hex16(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(11);
    for b in &bytes[..4] {
        s.push_str(&format!("{b:02x}"));
    }
    s.push_str("..");
    s
}

// =============================================================================
// §3 — The fraud proof
// =============================================================================

/// **`FraudProof`** — the bilateral, owner-anchored conviction object: an operator's signed
/// promise paired with a contradicting fact from the grain's own authenticated history.
///
/// An owner assembles this once its operator has defaulted; ANY party the owner hands it to
/// (a market, a peer, a light client) re-checks it offline via [`Self::verify`] — no global
/// ledger, no consensus, no trusted third party. The proof is self-describing and
/// self-contained: the operator's key is `promise.relay`, and the fact is the owner's cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FraudProof {
    /// The operator's SIGNED promise `X` (a [`CustodyReceipt`] — the accept-or-refund-by
    /// commitment the operator put its key over).
    pub promise: CustodyReceipt,
    /// The owner-anchored fact establishing the true outcome (`not-X` on a conviction).
    pub fact: OwnerAnchoredFact,
    /// The height at which the fact is read / the proof is raised. Must be `>= accept_by`
    /// for a non-delivery to be a DROP (default) rather than pending custody.
    pub at_height: u64,
}

impl FraudProof {
    /// Assemble the canonical fraud proof an owner raises the MOMENT the deadline passes
    /// (`at_height = promise.accept_by`, the earliest admissible height), pairing the
    /// operator's receipt with the owner-anchored fact.
    pub fn at_deadline(promise: CustodyReceipt, fact: OwnerAnchoredFact) -> Self {
        let at_height = promise.accept_by;
        Self {
            promise,
            fact,
            at_height,
        }
    }

    /// **THE BILATERAL, OWNER-ANCHORED CHECK.** Convicts IFF the operator signed the
    /// promise, the deadline has passed, and the owner-anchored fact shows the promise was
    /// NOT honored (`not-X`). Runs with NO global consensus — a pure function of the
    /// operator's own signature and the owner's own cell.
    ///
    /// The decision is delegated to the verified custody referee: the promise + a canonical
    /// `Dropped` claim form an [`EvidenceOfDrop`], and [`adjudicate_from_inbox`] derives the
    /// TRUE outcome from the fact's [`InboxState`] and returns the slash bit. This method's
    /// only added value over that referee is the STRUCTURED verdict: it first inspects the
    /// two admissibility gates (signature, deadline) to name WHY a non-conviction occurred,
    /// then defers the honored-vs-dropped decision to the referee.
    pub fn verify(&self) -> Verdict {
        // Gate 1 — the binding tooth: a promise whose signature does not verify against
        // `promise.relay` binds no operator (forged/unsigned/wrong-key). Convicts nobody.
        if !self.promise.sig_verifies() {
            return Verdict::Acquit(Acquittal::PromiseUnsigned);
        }
        // Gate 2 — admissibility: the deadline must have passed for non-delivery to be a
        // default rather than pending custody.
        if self.at_height < self.promise.accept_by {
            return Verdict::Acquit(Acquittal::PromisePending);
        }

        // The outcome decision — delegated to the verified referee. With gates 1+2 already
        // satisfied, `adjudicate_from_inbox` returns `true` IFF the true outcome is Dropped.
        match &self.fact {
            OwnerAnchoredFact::InboxWitness(inbox) => {
                let evidence = EvidenceOfDrop {
                    receipt: self.promise.clone(),
                    claimed_outcome: CustodyOutcome::Dropped,
                    at_height: self.at_height,
                };
                if adjudicate_from_inbox(&evidence, inbox) {
                    Verdict::Convict(Conviction {
                        operator: self.promise.relay,
                        content_hash: self.promise.content_hash,
                        inbox_owner: self.promise.inbox_owner,
                    })
                } else {
                    Verdict::Acquit(Acquittal::PromiseHonored)
                }
            }
        }
    }

    /// Convenience: does this fraud proof convict its operator?
    pub fn convicts(&self) -> bool {
        self.verify().convicts()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_types::{SigningKey, generate_keypair, sign};

    // A relay/operator identity whose FederationId IS its Ed25519 public key.
    fn operator_identity() -> (FederationId, SigningKey) {
        let (sk, pk) = generate_keypair();
        (FederationId(pk.0), sk)
    }

    fn owner() -> FederationId {
        FederationId([0x03; 32])
    }

    fn h(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    /// The demo promise: operator accepts box `0xAB..` for the owner, promising the inbox
    /// root to advance `0x64 → 0x8E` by deadline 500.
    fn demo_promise() -> (CustodyReceipt, SigningKey) {
        let (op, sk) = operator_identity();
        let r = CustodyReceipt::sign(op, &sk, h(0xAB), owner(), h(0x64), h(0x8E), 500);
        (r, sk)
    }

    // ── The three REQUIRED teeth ────────────────────────────────────────────────────

    #[test]
    fn genuine_contradiction_convicts() {
        // Operator signed X (deliver-or-refund box 0xAB by height 500). The owner's OWN
        // cell shows the box was NEVER delivered (no dequeue carried its content_hash) and
        // no refund — not-X. At the deadline, this convicts, without any global consensus.
        let (promise, _sk) = demo_promise();
        let fact = OwnerAnchoredFact::from_dequeue(&promise, &[], h(0x64), false);
        let proof = FraudProof::at_deadline(promise.clone(), fact);

        let verdict = proof.verify();
        assert!(verdict.convicts(), "a genuine contradiction must convict");
        match verdict {
            Verdict::Convict(c) => {
                assert_eq!(c.operator, promise.relay, "conviction binds the SIGNER");
                assert_eq!(c.content_hash, promise.content_hash);
                assert_eq!(c.inbox_owner, promise.inbox_owner);
            }
            Verdict::Acquit(a) => panic!("expected a conviction, got acquittal {a:?}"),
        }
    }

    #[test]
    fn consistent_promise_and_fact_acquits() {
        // The operator HONORED the promise. Two honest fates, both acquit — the operator is
        // provably safe against a fabricated dispute (no false conviction).
        let (promise, _sk) = demo_promise();

        // (a) DELIVERED: the box's content_hash is among the dequeued (witness set).
        let delivered = OwnerAnchoredFact::from_dequeue(
            &promise,
            &[promise.content_hash],
            promise.new_root,
            false,
        );
        let proof_delivered = FraudProof::at_deadline(promise.clone(), delivered);
        assert_eq!(
            proof_delivered.verify(),
            Verdict::Acquit(Acquittal::PromiseHonored),
            "an honestly-delivered promise must acquit"
        );

        // (b) REFUNDED: box not delivered, but a refund was recorded (accept-or-refund-by).
        let refunded = OwnerAnchoredFact::from_dequeue(&promise, &[], h(0x64), true);
        let proof_refunded = FraudProof::at_deadline(promise, refunded);
        assert_eq!(
            proof_refunded.verify(),
            Verdict::Acquit(Acquittal::PromiseHonored),
            "an honestly-refunded promise must acquit"
        );
    }

    #[test]
    fn forged_unsigned_promise_rejected() {
        // A promise fabricated WITHOUT the operator's key convicts nobody, even against a
        // genuine-drop fact. We forge by signing the receipt preimage with a DIFFERENT key
        // (an attacker who does not hold the operator's secret).
        let (promise, _sk) = demo_promise();
        let (attacker_sk, _pk) = generate_keypair();
        // Reconstruct the preimage the operator would sign, then sign it with the wrong key.
        let bad_sig = sign(
            &attacker_sk,
            &CustodyReceipt::signing_preimage(
                &promise.relay,
                &promise.content_hash,
                &promise.inbox_owner,
                &promise.old_root,
                &promise.new_root,
                promise.accept_by,
            ),
        );
        let forged = CustodyReceipt {
            signature: bad_sig,
            ..promise
        };
        assert!(!forged.sig_verifies(), "the forgery must not verify");

        // Even paired with a genuine-drop fact, a forged promise binds no operator.
        let fact = OwnerAnchoredFact::from_dequeue(&forged, &[], h(0x64), false);
        let proof = FraudProof::at_deadline(forged, fact);
        assert_eq!(
            proof.verify(),
            Verdict::Acquit(Acquittal::PromiseUnsigned),
            "a forged/unsigned promise convicts nobody"
        );
        assert!(!proof.convicts());
    }

    // ── Admissibility / binding ──────────────────────────────────────────────────────

    #[test]
    fn premature_proof_acquits() {
        // A proof raised BEFORE the deadline is inadmissible: the operator has not defaulted.
        let (promise, _sk) = demo_promise();
        let fact = OwnerAnchoredFact::from_dequeue(&promise, &[], h(0x64), false);
        let accept_by = promise.accept_by;
        let proof = FraudProof {
            promise,
            fact,
            at_height: accept_by - 1,
        };
        assert_eq!(
            proof.verify(),
            Verdict::Acquit(Acquittal::PromisePending),
            "a premature proof must acquit (custody still pending)"
        );
    }

    #[test]
    fn conviction_binds_the_signing_operator() {
        // The convicted party is exactly the operator whose key produced the receipt — the
        // conviction cannot be re-pointed at an innocent party (the receipt would not verify
        // under a different relay id).
        let (promise, _sk) = demo_promise();
        assert_eq!(
            promise.relay.0,
            promise.relay_pubkey().0,
            "the signer id IS the verifying pubkey"
        );
        let fact = OwnerAnchoredFact::from_dequeue(&promise, &[], h(0x64), false);
        let proof = FraudProof::at_deadline(promise.clone(), fact);
        let Verdict::Convict(c) = proof.verify() else {
            panic!("expected conviction");
        };
        assert_eq!(c.operator, promise.relay);
    }

    // ── Overshoot / reorg robustness (composes with the sticky witness bit) ────────────

    #[test]
    fn overshoot_delivery_still_acquits() {
        // The box WAS delivered, but the live inbox root then grew PAST the promised
        // new_root (a later box / reorg / late block). The sticky content-addressed witness
        // acquits — no false conviction of a delivered operator on overshoot.
        let (promise, _sk) = demo_promise();
        let overshot_root = h(0x99);
        assert_ne!(overshot_root, promise.new_root);
        let fact = OwnerAnchoredFact::from_dequeue(
            &promise,
            &[promise.content_hash],
            overshot_root,
            false,
        );
        let proof = FraudProof::at_deadline(promise, fact);
        assert_eq!(
            proof.verify(),
            Verdict::Acquit(Acquittal::PromiseHonored),
            "overshoot must acquit a delivered operator"
        );
    }

    #[test]
    fn genuine_drop_survives_unrelated_root_growth() {
        // Dual polarity: the root grew by UNRELATED activity but THIS box was never
        // delivered and no refund — still convictable (overshoot robustness is not a
        // drop loophole).
        let (promise, _sk) = demo_promise();
        let grown = h(0x99);
        let fact = OwnerAnchoredFact::from_dequeue(&promise, &[], grown, false);
        let proof = FraudProof::at_deadline(promise, fact);
        assert!(
            proof.convicts(),
            "a genuine drop stays convictable even as the root grows"
        );
    }

    #[test]
    fn another_boxs_delivery_does_not_acquit() {
        // The witness is content-addressed: a dequeue of a DIFFERENT box does not witness
        // THIS box's delivery, so the operator is still convictable (no cross-box acquit).
        let (promise, _sk) = demo_promise();
        let other_box = h(0x77);
        let fact = OwnerAnchoredFact::from_dequeue(&promise, &[other_box], h(0x12), false);
        let proof = FraudProof::at_deadline(promise, fact);
        assert!(
            proof.convicts(),
            "another box's delivery must not acquit this operator"
        );
    }

    // ── The lens tooth: this wrapper AGREES with the verified referee ─────────────────

    #[test]
    fn verdict_agrees_with_referee() {
        // FraudProof::verify is a lens over adjudicate_from_inbox, not a divergent second
        // implementation: for every admissible (signed + deadline-reached) case, the
        // conviction bit must equal the referee's slash bit.
        let (promise, _sk) = demo_promise();
        let cases = [
            (vec![], h(0x64), false),                     // dropped
            (vec![promise.content_hash], h(0x8E), false), // delivered at promise
            (vec![promise.content_hash], h(0x99), false), // delivered, overshoot
            (vec![], h(0x64), true),                      // refunded
            (vec![h(0x77)], h(0x12), false),              // other box only -> dropped
        ];
        for (dequeued, root, refund) in cases {
            let inbox = InboxState::from_dequeue(&promise, &dequeued, root, refund);
            let evidence = EvidenceOfDrop::from_receipt(promise.clone());
            let referee = adjudicate_from_inbox(&evidence, &inbox);

            let fact = OwnerAnchoredFact::InboxWitness(inbox);
            let proof = FraudProof::at_deadline(promise.clone(), fact);
            assert_eq!(
                proof.convicts(),
                referee,
                "FraudProof must agree with the custody referee for {dequeued:?} / {root:?} / {refund}"
            );
        }
    }

    #[test]
    fn verdict_display_is_legible() {
        // The Display impls render without panicking and name the polarity — a small guard
        // that the diagnostic strings stay wired to the variants.
        let (promise, _sk) = demo_promise();
        let convict = FraudProof::at_deadline(
            promise.clone(),
            OwnerAnchoredFact::from_dequeue(&promise, &[], h(0x64), false),
        )
        .verify();
        assert!(format!("{convict}").starts_with("CONVICT"));

        let acquit = FraudProof::at_deadline(
            promise.clone(),
            OwnerAnchoredFact::from_dequeue(&promise, &[promise.content_hash], h(0x8E), false),
        )
        .verify();
        assert!(format!("{acquit}").starts_with("ACQUIT"));
    }
}
