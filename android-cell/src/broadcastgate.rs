//! **Cap-gate the BROADCAST.** The confined Android app's `sendBroadcast` reforged from
//! ambient device-wide fan-out into a **cap-scoped fan-out of receipted deliveries** to
//! registered receiver cells — `GRAPHIDEOS.md §1` (the intent row's broadcast half) made
//! real, in the same shape as the proven [`crate::intentgate`] / [`crate::contentgate`] /
//! [`crate::organgate`] / [`crate::permgate`] gates.
//!
//! # What Android does (the ambient mechanism deos replaces)
//!
//! In stock Android an app calls `context.sendBroadcast(intent)` (or `sendOrderedBroadcast`
//! / `sendStickyBroadcast`) and the framework's **`ActivityManagerService`** matches the
//! broadcast `Intent`'s action against **EVERY registered `BroadcastReceiver` on the
//! device** — both manifest-declared `<receiver><intent-filter>` components and
//! runtime-`registerReceiver`'d ones — and invokes `onReceive(context, intent)` on **all**
//! of them. This is the most purely **ambient** Android surface: a sender names an action
//! string and reaches the *whole device's* receiver set; a receiver marked
//! `android:exported="true"` accepts a broadcast from any app; a sticky broadcast is a
//! standing ambient value any later receiver re-reads. Unlike `startActivity` (one handler,
//! or a chooser), `sendBroadcast` is **one-to-many** — the fan-out is the point, and it is
//! unbounded by any cap.
//!
//! # What graphideOS does (the cap-bounded reforge)
//!
//! `GRAPHIDEOS.md §1`: *"an 'intent' is a turn targeting a cell you hold a cap to;
//! implicit resolution is the **spotter** over cells you can reach; no ambient
//! `startActivity`."* A **broadcast** is that same principle taken to the one-to-many case:
//! a fan-out of cap-bounded, receipted deliveries over the sender's **cap-reachable receiver
//! neighborhood**, NOT the device's global receiver set. This module is that:
//!
//! 1. **The fan-out ranges over the cap-reachable neighborhood, not the device.** The
//!    [`BroadcastRouter`] holds exactly the receiver cells the android-cell was *granted* a
//!    cap to reach — decidedly NOT `ActivityManagerService`'s global registration table. A
//!    receiver whose filter matches but is NOT in the cap-reachable set **never receives**:
//!    there is no ambient global broadcast. The fan-out is to a bounded set, by construction.
//! 2. **A delivery is a receipted event on the receiver cell.** Each matched, cap-admitted
//!    receiver gets a [`DeliveryOutcome::Delivered`] — `GRAPHIDEOS.md §1`'s "a notification
//!    is an `EmittedEvent` on a turn's receipt" generalised: a broadcast delivery is a
//!    receipted event landed on a named receiver cell, not an ambient `onReceive`. Multiple
//!    matches is **NORMAL** (the fan-out), never the intent gate's `Ambiguous` chooser.
//! 3. **Protected broadcasts are system-only.** Faithful to AOSP's protected-broadcast list
//!    (`BOOT_COMPLETED`, `PACKAGE_ADDED`, …): a protected action from a NON-system sender is
//!    [`BroadcastDecision::RefusedProtected`] — the whole fan-out is refused, nothing
//!    delivered. A confined app cannot forge a system broadcast.
//! 4. **Both permission legs are cap attenuations.** AOSP's `sendBroadcast(intent,
//!    receiverPermission)` (the sender requires receivers to hold a permission) and a
//!    `<receiver android:permission=…>` (the receiver requires the sender to hold one)
//!    become per-delivery teeth: a receiver lacking the sender-required permission is
//!    [`DeliveryOutcome::FilteredReceiverLacksPermission`]; a sender lacking the
//!    receiver-required permission is [`DeliveryOutcome::FilteredSenderLacksPermission`].
//!    Both are recorded (not silently dropped), so a filtered delivery is auditable.
//!
//! Every `sendBroadcast` leaves a content-addressed [`BroadcastReceipt`] enumerating the
//! delivered + filtered receivers, so the android-cell's broadcast traffic is auditable end
//! to end exactly like the intent / content / service / permission receipts.
//!
//! # The depth (honest, like the sibling gates')
//!
//! This is the **fan-out-and-authority** layer: the router decides, against the held
//! permissions + the granted receiver set, which receivers a broadcast reaches and how, and
//! records it. The remaining frontier — interposing the *actual* binder
//! `ActivityManagerService.broadcastIntent` transaction inside the confined runtime so the
//! device kernel itself fans a broadcast out only to cap-admitted receiver cells (the
//! HAL/binder leg the sibling gates also name), sticky-broadcast persistence as a receipted
//! cell value, and ordered-broadcast result propagation — is the same not-yet-claimed depth.
//! What IS real today: the fan-out algebra + the protected-broadcast tooth + the two
//! permission teeth + the receipt, testable on any node with no device.

use std::collections::BTreeSet;

use dregg_firmament::CellId;

use crate::appfactory::AndroidPermission;
use crate::intentgate::{AndroidIntent, IntentFilter};

/// **A broadcast the confined app fired** — the `Intent` payload plus the sender's optional
/// `receiverPermission` (AOSP's `sendBroadcast(intent, receiverPermission)`: the sender
/// requires every receiver to hold this permission to be delivered to). Reuses
/// [`AndroidIntent`] for the action/data/category payload (a broadcast IS an `Intent` in
/// AOSP) and [`IntentFilter`]'s match algorithm for receiver matching.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Broadcast {
    /// The broadcast `Intent` — its action is what receivers match on.
    pub intent: AndroidIntent,
    /// The permission the sender requires receivers to hold (`sendBroadcast(intent,
    /// receiverPermission)`). `None` = no sender-imposed receiver requirement.
    pub receiver_permission: Option<AndroidPermission>,
}

impl Broadcast {
    /// A bare action-only broadcast (the common `sendBroadcast(new Intent(ACTION))` shape).
    pub fn action(action: impl Into<String>) -> Self {
        Broadcast {
            intent: AndroidIntent {
                action: action.into(),
                data: None,
                mime_type: None,
                categories: BTreeSet::new(),
            },
            receiver_permission: None,
        }
    }

    /// A broadcast carrying an [`AndroidIntent`] payload.
    pub fn new(intent: AndroidIntent) -> Self {
        Broadcast {
            intent,
            receiver_permission: None,
        }
    }

    /// Require receivers to hold `permission` to be delivered to (`sendBroadcast(intent,
    /// receiverPermission)` — builder).
    pub fn requiring_receiver_permission(mut self, permission: AndroidPermission) -> Self {
        self.receiver_permission = Some(permission);
        self
    }

    /// A short tag for the receipt digest + status line.
    fn tag(&self) -> String {
        self.intent.action.clone()
    }
}

/// **The sender's authority context** — who fired the broadcast and what it holds. The
/// powerbox-style "you can only reach what you hold": a non-system sender cannot fire a
/// protected broadcast, and a sender that does not hold a receiver's required permission is
/// filtered from that receiver.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sender {
    /// The android-cell that fired the broadcast.
    pub cell: CellId,
    /// Whether the sender is the device/system principal (only the system may fire a
    /// protected broadcast — `BOOT_COMPLETED`, `PACKAGE_ADDED`, …). A confined foreign app
    /// is NOT system.
    pub is_system: bool,
    /// The permissions the sender holds — checked against a receiver's
    /// [`BroadcastReceiver::required_sender_permission`].
    pub holds: BTreeSet<AndroidPermission>,
}

impl Sender {
    /// A confined (non-system) app sender holding `holds`.
    pub fn app(cell: CellId, holds: impl IntoIterator<Item = AndroidPermission>) -> Self {
        Sender {
            cell,
            is_system: false,
            holds: holds.into_iter().collect(),
        }
    }

    /// The device/system principal (may fire protected broadcasts).
    pub fn system(cell: CellId) -> Self {
        Sender {
            cell,
            is_system: true,
            holds: BTreeSet::new(),
        }
    }
}

/// **A cap-reachable broadcast receiver in the android-cell's bounded neighborhood** — the
/// deos form of an AOSP `<receiver><intent-filter>` (or a runtime-`registerReceiver`'d one).
/// Held by the [`BroadcastRouter`] only for receivers the sender holds a cap to (NOT the
/// device's global registration table). A delivery to it is a receipted event on its cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BroadcastReceiver {
    /// The receiver cell — the named capability holder a delivery lands an event on.
    pub cell: CellId,
    /// A short human label for the status line / audit (e.g. "SyncReceiver").
    pub label: String,
    /// What this receiver answers — the `<intent-filter>` (reusing the intent match algebra).
    pub filter: IntentFilter,
    /// The permission this receiver requires the SENDER to hold (AOSP `<receiver
    /// android:permission=…>`). `None` = any cap-reachable sender may deliver.
    pub required_sender_permission: Option<AndroidPermission>,
    /// The permissions this receiver holds — checked against the sender's
    /// [`Broadcast::receiver_permission`] (AOSP `sendBroadcast(intent, receiverPermission)`).
    pub holds: BTreeSet<AndroidPermission>,
}

impl BroadcastReceiver {
    /// A receiver answering `filter`, requiring nothing of the sender and holding nothing —
    /// the common manifest `<receiver>` over a granted neighborhood (the cap to reach it is
    /// the only authority).
    pub fn new(cell: CellId, label: impl Into<String>, filter: IntentFilter) -> Self {
        BroadcastReceiver {
            cell,
            label: label.into(),
            filter,
            required_sender_permission: None,
            holds: BTreeSet::new(),
        }
    }

    /// Require the sender to hold `permission` to deliver here (`<receiver
    /// android:permission=…>` — builder).
    pub fn requiring_sender_permission(mut self, permission: AndroidPermission) -> Self {
        self.required_sender_permission = Some(permission);
        self
    }

    /// Declare the permissions this receiver holds (for the sender's `receiverPermission`
    /// check — builder).
    pub fn holding(mut self, holds: impl IntoIterator<Item = AndroidPermission>) -> Self {
        self.holds = holds.into_iter().collect();
        self
    }
}

/// **The outcome of a broadcast at ONE receiver** — delivered, or filtered by one of the two
/// permission legs. A filtered delivery is RECORDED (not silently dropped), so the
/// authority decision at each receiver is auditable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeliveryOutcome {
    /// The broadcast was delivered: a receipted event landed on this receiver cell.
    Delivered,
    /// FILTERED: the receiver does NOT hold the permission the SENDER required
    /// (`sendBroadcast(intent, receiverPermission)`) — it is excluded from the fan-out.
    FilteredReceiverLacksPermission,
    /// FILTERED: the SENDER does NOT hold the permission the RECEIVER required (`<receiver
    /// android:permission=…>`) — the delivery to this receiver is refused.
    FilteredSenderLacksPermission,
}

impl DeliveryOutcome {
    pub fn delivered(&self) -> bool {
        matches!(self, DeliveryOutcome::Delivered)
    }

    fn tag(&self) -> &'static str {
        match self {
            DeliveryOutcome::Delivered => "delivered",
            DeliveryOutcome::FilteredReceiverLacksPermission => "filtered-receiver-perm",
            DeliveryOutcome::FilteredSenderLacksPermission => "filtered-sender-perm",
        }
    }
}

/// **One receiver's result in a fan-out** — the receiver cell, its label, and the
/// [`DeliveryOutcome`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Delivery {
    /// The receiver cell.
    pub receiver: CellId,
    /// The receiver's label (for the status line).
    pub label: String,
    /// Delivered, or filtered by which leg.
    pub outcome: DeliveryOutcome,
}

/// **The decision a `sendBroadcast` reaches** — the broadcast-side analogue of
/// [`crate::intentgate::IntentDecision`], but the granted case is a **fan-out** (a set of
/// per-receiver [`Delivery`]s), not a single resolution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BroadcastDecision {
    /// The broadcast fanned out over the cap-reachable receiver neighborhood. Carries every
    /// matched receiver's [`Delivery`] (delivered or filtered). An EMPTY fan-out (no matched
    /// cap-reachable receiver) is this with no deliveries — faithful to AOSP, where a
    /// broadcast reaching no receiver simply drops; the no-ambient property is that an
    /// ungranted receiver is never a candidate in the first place.
    FannedOut { deliveries: Vec<Delivery> },
    /// REFUSED: a protected (system-only) action fired by a NON-system sender — the whole
    /// fan-out is refused, nothing delivered. A confined app cannot forge a system broadcast.
    RefusedProtected { action: String },
}

impl BroadcastDecision {
    pub fn fanned_out(&self) -> bool {
        matches!(self, BroadcastDecision::FannedOut { .. })
    }
    pub fn refused_protected(&self) -> bool {
        matches!(self, BroadcastDecision::RefusedProtected { .. })
    }

    /// The receiver cells the broadcast was actually DELIVERED to (the fan-out's reached
    /// set, excluding the filtered ones). Empty for a refused or fully-filtered broadcast.
    pub fn delivered_to(&self) -> Vec<CellId> {
        match self {
            BroadcastDecision::FannedOut { deliveries } => deliveries
                .iter()
                .filter(|d| d.outcome.delivered())
                .map(|d| d.receiver)
                .collect(),
            BroadcastDecision::RefusedProtected { .. } => Vec::new(),
        }
    }

    /// The receivers that MATCHED but were filtered out by a permission leg (the audit of
    /// who *would* have received it but lacked authority).
    pub fn filtered(&self) -> Vec<&Delivery> {
        match self {
            BroadcastDecision::FannedOut { deliveries } => deliveries
                .iter()
                .filter(|d| !d.outcome.delivered())
                .collect(),
            BroadcastDecision::RefusedProtected { .. } => Vec::new(),
        }
    }
}

/// **The AOSP protected-broadcast predicate.** A representative set of the actions only the
/// system may broadcast (a non-system `sendBroadcast` of one of these throws a
/// `SecurityException` in AOSP). graphideOS refuses the whole fan-out: a confined app cannot
/// forge a boot/package/connectivity system event. The long tail (the full
/// `<protected-broadcast>` list) extends this set; an unrecognised action is NOT protected
/// (any cap-reachable sender may fire an ordinary broadcast).
pub fn is_protected_action(action: &str) -> bool {
    matches!(
        action,
        "android.intent.action.BOOT_COMPLETED"
            | "android.intent.action.LOCKED_BOOT_COMPLETED"
            | "android.intent.action.PACKAGE_ADDED"
            | "android.intent.action.PACKAGE_REMOVED"
            | "android.intent.action.PACKAGE_REPLACED"
            | "android.intent.action.MY_PACKAGE_REPLACED"
            | "android.intent.action.PACKAGE_CHANGED"
            | "android.net.conn.CONNECTIVITY_CHANGE"
            | "android.intent.action.BATTERY_CHANGED"
            | "android.intent.action.BATTERY_LOW"
            | "android.intent.action.SCREEN_ON"
            | "android.intent.action.SCREEN_OFF"
            | "android.intent.action.AIRPLANE_MODE"
            | "android.intent.action.TIME_SET"
            | "android.intent.action.TIMEZONE_CHANGED"
    )
}

/// **The receipt left by a gated `sendBroadcast`.** Every broadcast produces one, so the
/// android-cell's broadcast fan-out is auditable end to end exactly like the intent /
/// content / service / permission receipts. Content-addressed:
/// `decision_digest = blake3(sender? ‖ action ‖ receiver_perm? ‖ outcome ‖ per-delivery…)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BroadcastReceipt {
    /// The android-cell that fired the broadcast.
    pub sender: Option<CellId>,
    /// The broadcast fired.
    pub broadcast: Broadcast,
    /// The decision reached (the fan-out, or the protected refusal).
    pub decision: BroadcastDecision,
    /// `blake3(…)[..32]` — the content-addressed witness a verifier reconstructs.
    pub decision_digest: [u8; 32],
}

impl BroadcastReceipt {
    fn digest(
        sender: Option<CellId>,
        broadcast: &Broadcast,
        decision: &BroadcastDecision,
    ) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"graphideos-broadcast-v1");
        if let Some(s) = sender {
            h.update(b"\x01sender");
            h.update(s.as_bytes());
        }
        h.update(broadcast.tag().as_bytes());
        h.update(b"\x00");
        if let Some(p) = &broadcast.receiver_permission {
            h.update(b"\x01recv-perm");
            h.update(p.android_name().as_bytes());
        }
        match decision {
            BroadcastDecision::FannedOut { deliveries } => {
                h.update(b"\x01fanned-out");
                // deliveries are sorted by cell in `send`, so the digest is stable.
                for d in deliveries {
                    h.update(d.receiver.as_bytes());
                    h.update(d.outcome.tag().as_bytes());
                }
            }
            BroadcastDecision::RefusedProtected { action } => {
                h.update(b"\x02refused-protected");
                h.update(action.as_bytes());
            }
        }
        *h.finalize().as_bytes()
    }

    /// A one-line audit truth for the cockpit status line — which end, named exactly.
    pub fn status_line(&self) -> String {
        match &self.decision {
            BroadcastDecision::FannedOut { deliveries } => {
                let delivered = deliveries.iter().filter(|d| d.outcome.delivered()).count();
                let filtered = deliveries.len() - delivered;
                format!(
                    "android-broadcast: ✔ {} → fanned out to {delivered} cap-reachable receiver cell(s) as receipted events ({filtered} filtered by permission) — a bounded neighborhood, not an ambient device-wide broadcast",
                    self.broadcast.tag()
                )
            }
            BroadcastDecision::RefusedProtected { action } => format!(
                "android-broadcast: ✖ {action} REFUSED — a protected (system-only) broadcast cannot be fired by a confined app (no forged system event)"
            ),
        }
    }
}

/// **The cap-gated broadcast router for one sender — the fan-out over the sender's bounded,
/// cap-reachable receiver neighborhood**, NOT `ActivityManagerService`'s global registration
/// table. Holds the granted receiver set + the sender cell it speaks for; holds NO ambient
/// authority — every [`send`](Self::send) is a pure function of its receivers + the sender
/// context.
pub struct BroadcastRouter {
    receivers: Vec<BroadcastReceiver>,
    sender: Option<CellId>,
}

impl BroadcastRouter {
    /// Build a router over the granted receiver neighborhood and the sender cell it speaks for.
    pub fn new(
        receivers: impl IntoIterator<Item = BroadcastReceiver>,
        sender: Option<CellId>,
    ) -> Self {
        BroadcastRouter {
            receivers: receivers.into_iter().collect(),
            sender,
        }
    }

    /// The granted receiver neighborhood (the cap-reachable set the fan-out ranges over).
    pub fn receivers(&self) -> &[BroadcastReceiver] {
        &self.receivers
    }

    /// **THE BROADCAST GATE.** The `sender` fired `broadcast`. Decide against the granted
    /// receiver set + both permission legs, and return the decision AND its
    /// [`BroadcastReceipt`].
    ///
    /// Order of teeth (fail-closed):
    /// 1. **The protected-broadcast tooth, first** — a protected (system-only) action fired
    ///    by a NON-system sender ⟹ [`BroadcastDecision::RefusedProtected`]; the fan-out never
    ///    runs (a confined app cannot forge a system broadcast).
    /// 2. **The fan-out over the cap-reachable set** — for each granted receiver whose filter
    ///    matches the broadcast `Intent` (AOSP action+category+data algorithm), decide its
    ///    [`DeliveryOutcome`]:
    ///    - the receiver requires a sender permission the sender lacks ⟹
    ///      [`DeliveryOutcome::FilteredSenderLacksPermission`];
    ///    - the sender requires a receiver permission the receiver lacks ⟹
    ///      [`DeliveryOutcome::FilteredReceiverLacksPermission`];
    ///    - otherwise ⟹ [`DeliveryOutcome::Delivered`] (a receipted event on the cell).
    ///
    /// A receiver NOT in the granted set is, by construction, never a candidate — the
    /// no-ambient-global-broadcast property.
    pub fn send(&self, sender: &Sender, broadcast: &Broadcast) -> BroadcastReceipt {
        // TOOTH 1 — THE PROTECTED-BROADCAST TOOTH. A confined app cannot forge a system event.
        if is_protected_action(&broadcast.intent.action) && !sender.is_system {
            let decision = BroadcastDecision::RefusedProtected {
                action: broadcast.intent.action.clone(),
            };
            return self.receipt(broadcast, decision);
        }

        // TOOTH 2 — THE FAN-OUT OVER THE CAP-REACHABLE NEIGHBORHOOD. Range ONLY over the
        // granted receivers; an unreachable receiver is not a candidate.
        let mut matched: Vec<&BroadcastReceiver> = self
            .receivers
            .iter()
            .filter(|r| r.filter.matches(&broadcast.intent))
            .collect();
        // Dedup + stable order by cell (a receiver granted twice is one capability holder,
        // and the digest must be stable).
        matched.sort_by(|a, b| a.cell.as_bytes().cmp(b.cell.as_bytes()));
        matched.dedup_by(|a, b| a.cell == b.cell);

        let deliveries = matched
            .into_iter()
            .map(|r| {
                let outcome = if r
                    .required_sender_permission
                    .as_ref()
                    .is_some_and(|p| !sender.holds.contains(p))
                {
                    DeliveryOutcome::FilteredSenderLacksPermission
                } else if broadcast
                    .receiver_permission
                    .as_ref()
                    .is_some_and(|p| !r.holds.contains(p))
                {
                    DeliveryOutcome::FilteredReceiverLacksPermission
                } else {
                    DeliveryOutcome::Delivered
                };
                Delivery {
                    receiver: r.cell,
                    label: r.label.clone(),
                    outcome,
                }
            })
            .collect();

        let decision = BroadcastDecision::FannedOut { deliveries };
        self.receipt(broadcast, decision)
    }

    fn receipt(&self, broadcast: &Broadcast, decision: BroadcastDecision) -> BroadcastReceipt {
        let decision_digest = BroadcastReceipt::digest(self.sender, broadcast, &decision);
        BroadcastReceipt {
            sender: self.sender,
            broadcast: broadcast.clone(),
            decision,
            decision_digest,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::cell_seed;

    fn sync_receiver() -> BroadcastReceiver {
        BroadcastReceiver::new(
            cell_seed(0x61),
            "SyncReceiver",
            IntentFilter::new(["com.example.SYNC"], Vec::<String>::new()),
        )
    }
    fn other_sync_receiver() -> BroadcastReceiver {
        BroadcastReceiver::new(
            cell_seed(0x62),
            "OtherSync",
            IntentFilter::new(["com.example.SYNC"], Vec::<String>::new()),
        )
    }

    /// **THE LOAD-BEARING TEST: a broadcast fans out ONLY over the cap-reachable receiver
    /// neighborhood — a receiver whose filter matches but was never granted a cap NEVER
    /// receives (no ambient device-wide broadcast).**
    #[test]
    fn fan_out_ranges_only_over_the_granted_neighborhood() {
        let me = cell_seed(9);
        // The neighborhood holds ONE sync receiver. A second sync receiver exists in the
        // "device" but is NOT in the router (the sender holds no cap to it).
        let router = BroadcastRouter::new([sync_receiver()], Some(me));
        let sender = Sender::app(me, []);
        let bc = Broadcast::action("com.example.SYNC");

        let receipt = router.send(&sender, &bc);
        assert!(receipt.decision.fanned_out());
        // Delivered to exactly the ONE granted receiver — not the ungranted one.
        assert_eq!(receipt.decision.delivered_to(), vec![cell_seed(0x61)]);
        assert!(
            !receipt.decision.delivered_to().contains(&cell_seed(0x62)),
            "the ungranted receiver never receives (no ambient broadcast)"
        );
        assert_eq!(
            receipt.decision_digest,
            BroadcastReceipt::digest(Some(me), &bc, &receipt.decision)
        );
    }

    /// **THE FAN-OUT (NOT A CHOOSER): two cap-reachable receivers matching one action both
    /// receive — multiple matches is NORMAL for a broadcast, never the intent gate's
    /// `Ambiguous`.**
    #[test]
    fn multiple_matches_all_receive_no_chooser() {
        let me = cell_seed(9);
        let router = BroadcastRouter::new([sync_receiver(), other_sync_receiver()], Some(me));
        let sender = Sender::app(me, []);
        let receipt = router.send(&sender, &Broadcast::action("com.example.SYNC"));

        let delivered = receipt.decision.delivered_to();
        assert_eq!(
            delivered.len(),
            2,
            "both matched receivers receive the fan-out"
        );
        assert!(delivered.contains(&cell_seed(0x61)));
        assert!(delivered.contains(&cell_seed(0x62)));
        assert!(receipt.status_line().contains("fanned out to 2"));
    }

    /// A broadcast no cap-reachable receiver matches delivers to nothing (an empty fan-out —
    /// faithful AOSP: a broadcast reaching no receiver simply drops).
    #[test]
    fn unmatched_broadcast_delivers_to_nothing() {
        let me = cell_seed(9);
        let router = BroadcastRouter::new([sync_receiver()], Some(me));
        let sender = Sender::app(me, []);
        let receipt = router.send(&sender, &Broadcast::action("com.example.OTHER"));
        assert!(receipt.decision.fanned_out());
        assert!(receipt.decision.delivered_to().is_empty());
    }

    /// **THE PROTECTED-BROADCAST TOOTH: a system-only action (BOOT_COMPLETED) fired by a
    /// confined (non-system) app is refused — the whole fan-out, nothing delivered.**
    #[test]
    fn protected_broadcast_from_a_confined_app_is_refused() {
        let me = cell_seed(9);
        // A receiver that WOULD match BOOT_COMPLETED, in the neighborhood.
        let boot_rx = BroadcastReceiver::new(
            cell_seed(0x63),
            "BootRx",
            IntentFilter::new(
                ["android.intent.action.BOOT_COMPLETED"],
                Vec::<String>::new(),
            ),
        );
        let router = BroadcastRouter::new([boot_rx], Some(me));
        let sender = Sender::app(me, []); // NOT system.
        let receipt = router.send(
            &sender,
            &Broadcast::action("android.intent.action.BOOT_COMPLETED"),
        );

        assert!(receipt.decision.refused_protected());
        assert!(
            receipt.decision.delivered_to().is_empty(),
            "a forged system broadcast reaches nothing"
        );
        assert!(receipt.status_line().contains("system-only"));

        // The SAME broadcast from the system principal fans out normally.
        let system = Sender::system(cell_seed(0x01));
        let sys_router = BroadcastRouter::new(
            [BroadcastReceiver::new(
                cell_seed(0x63),
                "BootRx",
                IntentFilter::new(
                    ["android.intent.action.BOOT_COMPLETED"],
                    Vec::<String>::new(),
                ),
            )],
            Some(cell_seed(0x01)),
        );
        let sys_receipt = sys_router.send(
            &system,
            &Broadcast::action("android.intent.action.BOOT_COMPLETED"),
        );
        assert!(sys_receipt.decision.fanned_out());
        assert_eq!(sys_receipt.decision.delivered_to(), vec![cell_seed(0x63)]);
    }

    /// **THE RECEIVER-PERMISSION TOOTH: a receiver requiring a sender permission the sender
    /// does NOT hold is filtered (FilteredSenderLacksPermission); holding it delivers.**
    #[test]
    fn receiver_required_sender_permission_filters() {
        let me = cell_seed(9);
        let guarded = BroadcastReceiver::new(
            cell_seed(0x64),
            "Guarded",
            IntentFilter::new(["com.example.SYNC"], Vec::<String>::new()),
        )
        .requiring_sender_permission(AndroidPermission::ReadContacts);
        let router = BroadcastRouter::new([guarded], Some(me));
        let bc = Broadcast::action("com.example.SYNC");

        // A sender lacking READ_CONTACTS is filtered from the guarded receiver.
        let weak = Sender::app(me, []);
        let r0 = router.send(&weak, &bc);
        assert!(
            r0.decision.delivered_to().is_empty(),
            "sender lacks the permission"
        );
        assert_eq!(r0.decision.filtered().len(), 1);
        assert_eq!(
            r0.decision.filtered()[0].outcome,
            DeliveryOutcome::FilteredSenderLacksPermission
        );

        // A sender holding it is delivered to.
        let strong = Sender::app(me, [AndroidPermission::ReadContacts]);
        let r1 = router.send(&strong, &bc);
        assert_eq!(r1.decision.delivered_to(), vec![cell_seed(0x64)]);
    }

    /// **THE SENDER-`receiverPermission` TOOTH: a sender's `sendBroadcast(intent,
    /// receiverPermission)` filters receivers that do NOT hold the required permission.**
    #[test]
    fn sender_required_receiver_permission_filters() {
        let me = cell_seed(9);
        // One receiver holds CAMERA, one does not.
        let cam_rx = BroadcastReceiver::new(
            cell_seed(0x65),
            "CamRx",
            IntentFilter::new(["com.example.SYNC"], Vec::<String>::new()),
        )
        .holding([AndroidPermission::Camera]);
        let plain_rx = BroadcastReceiver::new(
            cell_seed(0x66),
            "PlainRx",
            IntentFilter::new(["com.example.SYNC"], Vec::<String>::new()),
        );
        let router = BroadcastRouter::new([cam_rx, plain_rx], Some(me));
        let sender = Sender::app(me, []);

        // The sender requires receivers to hold CAMERA: only CamRx is delivered to.
        let bc = Broadcast::action("com.example.SYNC")
            .requiring_receiver_permission(AndroidPermission::Camera);
        let receipt = router.send(&sender, &bc);
        assert_eq!(receipt.decision.delivered_to(), vec![cell_seed(0x65)]);
        assert_eq!(receipt.decision.filtered().len(), 1);
        assert_eq!(receipt.decision.filtered()[0].receiver, cell_seed(0x66));
        assert_eq!(
            receipt.decision.filtered()[0].outcome,
            DeliveryOutcome::FilteredReceiverLacksPermission
        );
    }

    /// The receipt digest is stable + content-addressed across the fan-out (order-independent
    /// because deliveries are sorted by cell).
    #[test]
    fn receipt_is_content_addressed_and_stable() {
        let me = cell_seed(9);
        // Same receivers, different construction order ⟹ same digest (sorted by cell).
        let r1 = BroadcastRouter::new([sync_receiver(), other_sync_receiver()], Some(me));
        let r2 = BroadcastRouter::new([other_sync_receiver(), sync_receiver()], Some(me));
        let sender = Sender::app(me, []);
        let bc = Broadcast::action("com.example.SYNC");
        assert_eq!(
            r1.send(&sender, &bc).decision_digest,
            r2.send(&sender, &bc).decision_digest,
            "the fan-out digest is order-independent (deliveries sorted by cell)"
        );
    }

    /// The protected-action predicate is faithful (system events protected, ordinary custom
    /// actions not).
    #[test]
    fn protected_action_predicate_is_faithful() {
        assert!(is_protected_action("android.intent.action.BOOT_COMPLETED"));
        assert!(is_protected_action("android.intent.action.PACKAGE_ADDED"));
        assert!(is_protected_action("android.net.conn.CONNECTIVITY_CHANGE"));
        // An ordinary app-defined action is NOT protected.
        assert!(!is_protected_action("com.example.SYNC"));
        assert!(!is_protected_action("android.intent.action.VIEW"));
    }
}
