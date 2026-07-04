//! # polis — the quorum auto-certifier as a `Reactor` (the reactive twin of
//! `invoke()`).
//!
//! The fifth axis (AX5) of a modern starbridge-app. Where the [`crate::service`]
//! face is the **command** front-door (a `propose` / `approve` / `certify` turn
//! comes *in*, caller-driven), this is the **reaction** front-door: a service
//! that WATCHES the council proposal cell and, when an `approve` commits that
//! crosses the council threshold, REACTS by emitting its own `certify` turn —
//! event-driven, the on-chain governance loop.
//!
//! [`CouncilCertifyReactor`] is the approve→certify step made reactive: the
//! propose → approve → certify lifecycle's threshold step is EVENT-DRIVEN (a
//! quorum of approvals triggers certification), which is exactly what a
//! [`Reactor`] models. It watches the proposal for committed
//! [`approve`](starbridge_polis::council::METHOD_APPROVE) ops and reacts by
//! [`certify`](starbridge_polis::council::METHOD_CERTIFY)-ing the proposal —
//! reading the running approval count off the `council-approved` event the same
//! turn emits.
//!
//! Both front-doors are **userspace**: there is NO kernel `Effect::React` (just
//! as there is no `Effect::Invoke`). The reaction desugars to ordinary [`Effect`]s
//! the kernel already enforces and the circuit already witnesses — here, the SAME
//! [`crate::service::certify_effects`] body a service `certify` desugars to. The
//! reaction's `certify` turn is re-enforced by the installed canonical council
//! program: the `AffineLe { M·flag − Σ approvals <= 0 }` threshold gate bites as
//! a REAL executor refusal, so a reaction can never arm the flag without a genuine
//! `Σ approvals >= M` quorum in the cell's committed state — the reactor's own
//! count is only a trigger; the verified tooth is the floor.
//!
//! Like the service face, this file is compiled INTO THE TEST BINARIES via
//! `#[path = "../src/reactor.rs"]` (it pulls `dregg-app-framework`, which polis can
//! only reach across the dev-dependency edge — see `Cargo.toml`).

use dregg_app_framework::{
    AuthRequired, CellId, Effect, FieldElement, ObservedReceipt, ReactionPlan, Reactor,
    ReceiptFilter, symbol,
};

use crate::service::certify_effects;

/// **A quorum auto-certifier reactor** — watches a council proposal cell for
/// committed `approve` ops and reacts by `certify`-ing once the running approval
/// count crosses the council `threshold`.
///
/// The reactive analogue of a [`crate::service::CouncilService`] certify: it
/// DECLARES its watch ([`ReceiptFilter`] over the proposal's `approve` method)
/// and how it reacts ([`Reactor::react`] → a `certify` [`ReactionPlan`]); the
/// framework wires the match → cap-gate → build → sign. An approval below quorum
/// produces no reaction.
#[derive(Clone, Debug)]
pub struct CouncilCertifyReactor {
    /// The council proposal cell this reactor watches (and certifies against).
    pub council: CellId,
    /// The council threshold — the running approval count must REACH this for
    /// certification to fire. Carried as reactor config (the same M the cell's
    /// `AffineLe` gate enforces); an approval whose observed count is below it
    /// does not react.
    pub threshold: u64,
}

impl CouncilCertifyReactor {
    /// A certify reactor watching `council`, firing certification at `threshold`
    /// distinct approving members.
    pub fn new(council: CellId, threshold: u64) -> Self {
        CouncilCertifyReactor { council, threshold }
    }
}

impl Reactor for CouncilCertifyReactor {
    fn filter(&self) -> ReceiptFilter {
        // What it watches: the proposal cell, for the `approve` op. The reactive
        // analogue of the service cell's interface descriptor.
        ReceiptFilter::cell_methods(self.council, &[starbridge_polis::council::METHOD_APPROVE])
    }

    fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan> {
        // Decode the running approval count off the observed turn's committed
        // effects: the `council-approved` event carries [member_index, count].
        let mut count: Option<u64> = None;
        for effect in &observed.effects {
            if let Effect::EmitEvent { event, .. } = effect {
                if event.topic == symbol("council-approved") && event.data.len() >= 2 {
                    count = Some(field_to_u64(&event.data[1]));
                }
            }
        }
        // Certification only fires once the running count REACHES the threshold —
        // an approval below quorum produces no reaction (fail-closed on missing
        // data).
        let count = count?;
        if count < self.threshold {
            return None;
        }
        Some(ReactionPlan {
            target: self.council,
            method: starbridge_polis::council::METHOD_CERTIFY.into(),
            args: vec![],
            // The reaction desugars to the ordinary certify body — the kernel /
            // circuit see only what they already know. The executor re-enforces
            // the `AffineLe` threshold gate on it.
            effects: certify_effects(self.council),
            auth_required: AuthRequired::Signature,
        })
    }
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse
/// of `field_from_u64` for the approval count the council stores in its event).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{
        AgentCipherclerk, AppCipherclerk, CellId as TyCellId, EmbeddedExecutor, InvokeAuthority,
        ReactRefused, field_from_u64, react_build,
    };

    use crate::service::{CouncilService, approve_effects, seed_council};
    use starbridge_polis::STATE_SLOT;
    use starbridge_polis::council::{APPROVED_FLAG_SLOT, CouncilCharter, STATE_APPROVED};

    const THRESHOLD: u64 = 2;

    fn charter_2of3() -> CouncilCharter {
        CouncilCharter::new(
            vec![
                TyCellId::from_bytes([0x11; 32]),
                TyCellId::from_bytes([0x22; 32]),
                TyCellId::from_bytes([0x33; 32]),
            ],
            THRESHOLD,
        )
    }

    /// A cipherclerk + an embedded executor whose agent cell IS the council
    /// proposal cell, seeded with the canonical council program (DRAFT genesis),
    /// then opened into PROPOSED via a real `propose` invocation.
    fn deploy(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, CouncilService) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        let charter = charter_2of3();
        seed_council(&executor, &charter);
        let service = CouncilService::new(cclerk.cell_id(), charter);
        let propose = service
            .propose(&cclerk, [0xAC; 32], InvokeAuthority::Signature)
            .expect("a Signature holder may open a proposal");
        executor.submit_turn(&propose).expect("propose commits");
        (cclerk, executor, service)
    }

    #[test]
    fn an_on_chain_quorum_approval_drives_the_reactor_to_auto_certify() {
        // THE END-TO-END event-driven loop: a committed quorum-crossing `approve`
        // → the reactor sees it via the observed receipt → its `certify` reaction
        // arms the threshold flag + steps the proposal to APPROVED, committed
        // through the real executor (the AffineLe gate re-enforces Σ >= M).
        let (cclerk, executor, service) = deploy(0x01);
        let council = service.cell;

        // Two distinct members approve; the SECOND crosses the threshold.
        executor
            .submit_turn(
                &service
                    .approve(&cclerk, 0, 1, InvokeAuthority::Signature)
                    .unwrap(),
            )
            .expect("member 0 approves");
        executor
            .submit_turn(
                &service
                    .approve(&cclerk, 1, 2, InvokeAuthority::Signature)
                    .unwrap(),
            )
            .expect("member 1 approves (quorum reached)");

        // The reactor OBSERVES the quorum-crossing approval and reacts.
        let observed = ObservedReceipt {
            cell: council,
            method: symbol(starbridge_polis::council::METHOD_APPROVE),
            effects: approve_effects(council, 1, THRESHOLD),
            turn_hash: [0u8; 32],
            signer: cclerk.public_key().0,
        };
        let reactor = CouncilCertifyReactor::new(council, THRESHOLD);
        let turn = react_build(&cclerk, &reactor, &observed, InvokeAuthority::Signature)
            .expect("a Signature-holding reactor is authorized")
            .expect("a quorum-crossing approval reacts");

        // The reaction IS the genuine certify turn — submit it; the flag arms.
        executor
            .submit_turn(&turn)
            .expect("the reaction certify turn commits (Σ approvals == M, AffineLe holds)");
        let state = executor.cell_state(council).unwrap();
        assert_eq!(
            state.fields[STATE_SLOT as usize],
            field_from_u64(STATE_APPROVED),
            "the reactor advanced the proposal to APPROVED"
        );
        assert_eq!(
            state.fields[APPROVED_FLAG_SLOT as usize],
            field_from_u64(1),
            "the reactor armed the threshold-certification flag"
        );
    }

    #[test]
    fn a_below_quorum_approval_produces_no_reaction() {
        let (cclerk, _executor, service) = deploy(0x02);
        let council = service.cell;
        let reactor = CouncilCertifyReactor::new(council, THRESHOLD);

        // An approval with count below threshold → no reaction.
        let observed = ObservedReceipt {
            cell: council,
            method: symbol(starbridge_polis::council::METHOD_APPROVE),
            effects: approve_effects(council, 0, THRESHOLD - 1),
            turn_hash: [0u8; 32],
            signer: cclerk.public_key().0,
        };
        assert!(matches!(
            react_build(&cclerk, &reactor, &observed, InvokeAuthority::Signature),
            Ok(None)
        ));
    }

    #[test]
    fn the_reactor_only_watches_approvals() {
        let (cclerk, _executor, service) = deploy(0x03);
        let council = service.cell;
        let reactor = CouncilCertifyReactor::new(council, THRESHOLD);

        // An observed `certify` (not the watched `approve`) → no reaction.
        let off = ObservedReceipt {
            cell: council,
            method: symbol(starbridge_polis::council::METHOD_CERTIFY),
            effects: vec![],
            turn_hash: [0u8; 32],
            signer: cclerk.public_key().0,
        };
        assert!(matches!(
            react_build(&cclerk, &reactor, &off, InvokeAuthority::Signature),
            Ok(None)
        ));
    }

    #[test]
    fn the_reaction_is_cap_gated_fail_closed() {
        let (cclerk, _executor, service) = deploy(0x04);
        let council = service.cell;
        let reactor = CouncilCertifyReactor::new(council, THRESHOLD);

        let observed = ObservedReceipt {
            cell: council,
            method: symbol(starbridge_polis::council::METHOD_APPROVE),
            effects: approve_effects(council, 1, THRESHOLD),
            turn_hash: [0u8; 32],
            signer: cclerk.public_key().0,
        };

        // A None-authority reactor cannot satisfy the Signature-required reaction.
        let refused = react_build(&cclerk, &reactor, &observed, InvokeAuthority::None)
            .expect_err("None authority cannot satisfy a Signature reaction");
        assert!(matches!(refused, ReactRefused::Unauthorized { .. }));
    }
}
