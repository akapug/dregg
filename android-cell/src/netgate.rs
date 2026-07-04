//! **Cap-gate the I/O.** The android app's outbound network bound to the held
//! [`SurfaceCapability`] through `Netlayer::dial` — the SAME discipline the webcell's
//! `NetcapConnector` enforces, android-side.
//!
//! Android grants an app the network ambiently (the `INET` permission lets its UID
//! open sockets to anything). The android-cell puts a **cap gate in front of every
//! egress**: an origin the held cap does not authorize is [`IoDecision::RefusedByCap`]
//! **before any socket** — `Netlayer::dial` is never called — and so reaches nothing
//! on the glass; an authorized origin is dialed through the audited netlayer. Every
//! decision, admit or deny, leaves an [`IoReceipt`].
//!
//! This is the android-cell's equivalent of `cap_gated_pipeline`'s load-bearing
//! property: **a denied I/O puts nothing on the glass** (the gate is IN FRONT of the
//! render, not after it). The depth here is the SHALLOW, real-today layer — on macOS
//! the emulator's egress is routed/refused at this connect decision (the host-proxy
//! leg is the deployment wiring); on Linux the redroid container adds netns +
//! iptables-by-UID so the refusal also bites at the kernel socket. The DEEP per-call
//! sensor/intent gate (HAL/binder interposition) is the named frontier, not claimed
//! (`ANDROID-CELL.md §5`).

use dregg_captp::netlayer::{Netlayer, NetlayerError, PeerId};
use starbridge_web_surface::SurfaceCapability;

/// Map an app's egress origin (`https://api.example.com`) to a federation [`PeerId`]
/// — the netlayer node the cap-admitted traffic dials. `blake3(origin)[..32]`, the
/// SAME derivation `servo-render`'s netcap connector uses, so an origin-scoped cap is
/// a peer-scoped cap and the two surfaces share one keyspace.
pub fn origin_to_peer(origin: &str) -> PeerId {
    *blake3::hash(origin.as_bytes()).as_bytes()
}

/// The three distinguishable ends an egress attempt can reach — the same trichotomy
/// the webcell's `ConnectOutcome` reports, named for the android-cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IoDecision {
    /// The held cap authorized the origin AND the netlayer dialed the peer: a real
    /// audited session opened.
    Dialed { origin: String, peer: PeerId },
    /// The held [`SurfaceCapability`] does NOT authorize this origin — refused AT the
    /// gate, before `Netlayer::dial`. The socket is never opened; nothing reaches the
    /// glass. THIS is the no-ambient-authority property.
    RefusedByCap { origin: String },
    /// The cap authorized the origin, but the netlayer could not reach the peer — the
    /// transport's own refusal, distinct from the cap's.
    RefusedByTransport { origin: String, reason: String },
}

impl IoDecision {
    pub fn dialed(&self) -> bool {
        matches!(self, IoDecision::Dialed { .. })
    }
    pub fn refused_by_cap(&self) -> bool {
        matches!(self, IoDecision::RefusedByCap { .. })
    }
}

/// **The receipt left by a gated egress decision.** Every act the gate decides — admit
/// or deny — produces one, so the android-cell's I/O is auditable end to end (the
/// `TurnReceipt`-shaped artifact `ANDROID-CELL.md §8 step 5` asks for, at the shallow
/// connect granularity that layer honestly provides — per-connection, not per-syscall).
///
/// The receipt is content-addressed: `decision_digest = blake3(origin ‖ tag ‖ peer?)`,
/// so a verifier can reconstruct and check it. It is deliberately lightweight (NOT the
/// full kernel `turn::TurnReceipt`, which records a state transition); a net-egress
/// decision is an authority check at a transport boundary, and this is its faithful
/// receipt — the analogue of the webcell's audited `ConnectOutcome`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IoReceipt {
    /// The cell whose held cap decided this egress (the authority lineage).
    pub cell: Option<dregg_firmament::CellId>,
    /// The origin the app tried to reach.
    pub origin: String,
    /// The decision reached.
    pub decision: IoDecision,
    /// `blake3(origin ‖ tag ‖ peer?)[..32]` — the content-addressed witness of this
    /// decision a verifier reconstructs.
    pub decision_digest: [u8; 32],
}

impl IoReceipt {
    fn digest(origin: &str, decision: &IoDecision) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(origin.as_bytes());
        match decision {
            IoDecision::Dialed { peer, .. } => {
                h.update(b"\x01dialed");
                h.update(peer);
            }
            IoDecision::RefusedByCap { .. } => {
                h.update(b"\x02refused-by-cap");
            }
            IoDecision::RefusedByTransport { reason, .. } => {
                h.update(b"\x03refused-by-transport");
                h.update(reason.as_bytes());
            }
        }
        *h.finalize().as_bytes()
    }

    /// A one-line audit truth for the cockpit status line — which end, named exactly.
    pub fn status_line(&self) -> String {
        match &self.decision {
            IoDecision::Dialed { origin, peer } => format!(
                "android-io: ✔ {origin} → dialed through captp Netlayer (peer {}…) — audited, not an ambient android socket",
                bs58::encode(&peer[..6]).into_string()
            ),
            IoDecision::RefusedByCap { origin } => format!(
                "android-io: ✖ {origin} REFUSED at the gate — the app's held SurfaceCapability does not authorize this origin (Netlayer::dial never called; nothing reaches the glass)"
            ),
            IoDecision::RefusedByTransport { origin, reason } => format!(
                "android-io: ⚠ {origin} cap-authorized but unreachable on the netlayer ({reason})"
            ),
        }
    }
}

/// The cap-gated net gate for one android-cell. Holds the audited transport
/// ([`Netlayer`]) and the cell whose cap decides; holds NO ambient authority — every
/// [`egress`](Self::egress) is a function of the `surface` cap argument.
pub struct AndroidNetGate<N: Netlayer> {
    netlayer: N,
    cell: Option<dregg_firmament::CellId>,
}

impl<N: Netlayer> AndroidNetGate<N> {
    /// Bind a gate to a netlayer (the audited transport leg) and the cell it speaks
    /// for (recorded on each receipt; the cap argument is what actually decides).
    pub fn new(netlayer: N, cell: Option<dregg_firmament::CellId>) -> Self {
        AndroidNetGate { netlayer, cell }
    }

    pub fn netlayer(&self) -> &N {
        &self.netlayer
    }

    /// **THE EGRESS GATE.** The app wants to reach `origin`. Decide against the held
    /// `surface` cap and, iff admitted, dial through the audited netlayer — returning
    /// the decision AND its [`IoReceipt`].
    ///
    /// A cap-denied origin returns [`IoDecision::RefusedByCap`] and **`Netlayer::dial`
    /// is never called** — the socket never opens, nothing reaches the glass. The gate
    /// bites at the transport, before a packet — exactly the webcell's property,
    /// android-side.
    pub async fn egress(&self, surface: &SurfaceCapability, origin: &str) -> IoReceipt
    where
        N: Netlayer<Addr = PeerId>,
    {
        // STEP 1 — THE CAP, BEFORE THE SOCKET. An origin the held cap does not
        // authorize is refused here; dial is never reached.
        if !surface.may_fetch(origin) {
            let decision = IoDecision::RefusedByCap {
                origin: origin.to_string(),
            };
            return self.receipt(origin, decision);
        }

        // STEP 2 — DIAL THROUGH THE AUDITED NETLAYER. The cap admitted the origin;
        // resolve it to its peer and dial. A real session over the netlayer's
        // byte-frame transport — not an ambient android socket.
        let peer = origin_to_peer(origin);
        let decision = match self.netlayer.dial(&peer).await {
            Ok(_session) => IoDecision::Dialed {
                origin: origin.to_string(),
                peer,
            },
            Err(NetlayerError::PeerUnreachable { .. }) => IoDecision::RefusedByTransport {
                origin: origin.to_string(),
                reason: "peer unreachable on this netlayer".to_string(),
            },
            Err(other) => IoDecision::RefusedByTransport {
                origin: origin.to_string(),
                reason: other.to_string(),
            },
        };
        self.receipt(origin, decision)
    }

    fn receipt(&self, origin: &str, decision: IoDecision) -> IoReceipt {
        let decision_digest = IoReceipt::digest(origin, &decision);
        IoReceipt {
            cell: self.cell,
            origin: origin.to_string(),
            decision,
            decision_digest,
        }
    }
}

/// Drive an [`AndroidNetGate::egress`] future to completion on the calling thread.
/// The in-memory netlayers never pend on external wakeups, so a no-op waker suffices
/// — the same single-future executor the webcell's `netcap_connector::block_on` uses.
pub fn block_on<F: std::future::Future>(fut: F) -> F::Output {
    use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
    fn raw() -> RawWaker {
        fn no_op(_: *const ()) {}
        fn clone(_: *const ()) -> RawWaker {
            raw()
        }
        RawWaker::new(
            std::ptr::null(),
            &RawWakerVTable::new(clone, no_op, no_op, no_op),
        )
    }
    let waker = unsafe { Waker::from_raw(raw()) };
    let mut cx = Context::from_waker(&waker);
    let mut fut = std::pin::pin!(fut);
    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(out) => return out,
            Poll::Pending => std::thread::yield_now(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_captp::netlayer::InProcessFabric;
    use dregg_firmament::cell_seed;
    use starbridge_web_surface::{AuthRequired, SurfaceCapability};

    fn gate_with_peers(
        origins: &[&str],
        cell: dregg_firmament::CellId,
    ) -> AndroidNetGate<dregg_captp::netlayer::InProcessNetlayer> {
        let fabric = InProcessFabric::new();
        let me = fabric.join([0x07; 32]);
        for o in origins {
            let _ = fabric.join(origin_to_peer(o));
        }
        AndroidNetGate::new(me, Some(cell))
    }

    /// **THE LOAD-BEARING TEST: an origin the app's cap does NOT authorize is refused
    /// at the gate — before any dial — and the receipt records the refusal.**
    #[test]
    fn uncapped_egress_is_refused_before_the_socket() {
        let cell = cell_seed(9);
        let gate = gate_with_peers(
            &["https://api.example.com", "https://tracker.evil.com"],
            cell,
        );
        let surface = SurfaceCapability::scoped(
            cell,
            AuthRequired::Either,
            [String::from("https://api.example.com")],
            [],
        );

        let receipt = block_on(gate.egress(&surface, "https://tracker.evil.com"));

        assert!(
            receipt.decision.refused_by_cap(),
            "the uncapped origin is refused by the cap"
        );
        assert_eq!(
            receipt.decision,
            IoDecision::RefusedByCap {
                origin: "https://tracker.evil.com".to_string()
            }
        );
        assert_eq!(receipt.cell, Some(cell));
        assert!(receipt.status_line().contains("REFUSED at the gate"));
        assert!(receipt.status_line().contains("nothing reaches the glass"));
        // The receipt is content-addressed and reconstructible.
        assert_eq!(
            receipt.decision_digest,
            IoReceipt::digest("https://tracker.evil.com", &receipt.decision)
        );
    }

    /// The other half: a cap-authorized origin dials through the audited netlayer and
    /// the receipt records the dialed peer.
    #[test]
    fn capped_egress_dials_through_the_netlayer() {
        let cell = cell_seed(9);
        let gate = gate_with_peers(&["https://api.example.com"], cell);
        let surface = SurfaceCapability::scoped(
            cell,
            AuthRequired::Either,
            [String::from("https://api.example.com")],
            [],
        );

        let receipt = block_on(gate.egress(&surface, "https://api.example.com"));

        assert!(receipt.decision.dialed(), "the cap-authorized origin dials");
        match &receipt.decision {
            IoDecision::Dialed { origin, peer } => {
                assert_eq!(origin, "https://api.example.com");
                assert_eq!(*peer, origin_to_peer("https://api.example.com"));
            }
            other => panic!("expected Dialed, got {other:?}"),
        }
        assert!(receipt
            .status_line()
            .contains("dialed through captp Netlayer"));
    }

    /// Cap and transport are DISTINCT teeth: a wildcard cap still defers to the
    /// netlayer's reachability.
    #[test]
    fn wildcard_cap_still_subject_to_transport() {
        let cell = cell_seed(9);
        let gate = gate_with_peers(&["https://api.example.com"], cell);
        let root = SurfaceCapability::root(cell, AuthRequired::Either);

        let ok = block_on(gate.egress(&root, "https://api.example.com"));
        assert!(ok.decision.dialed());

        let unreachable = block_on(gate.egress(&root, "https://nowhere.invalid"));
        assert!(matches!(
            unreachable.decision,
            IoDecision::RefusedByTransport { .. }
        ));
        assert!(!unreachable.decision.refused_by_cap());
    }
}
