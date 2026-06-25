//! **Cap-gate the SYSTEM SERVICE.** The confined Android app's `getSystemService` reach
//! reforged from ambient device authority into a cap-bounded, spotter-resolved, receipted
//! reach to a **named organ cell** — `GRAPHIDEOS.md §1` (the system-services row) made real,
//! in the same shape as the proven [`crate::intentgate`] / [`crate::contentgate`] /
//! [`crate::netgate`] gates.
//!
//! # What Android does (the ambient mechanism deos replaces)
//!
//! In stock Android an app calls `context.getSystemService(Context.LOCATION_SERVICE)` (or
//! `getPackageManager()`, `getSystemService(ACTIVITY_SERVICE)`, …) and the framework's
//! **`ServiceManager`** hands back a binder proxy to a **privileged system-service process**
//! (`LocationManagerService`, `PackageManagerService`, `ActivityManagerService`, …). The app
//! then calls methods on that proxy — `getLastKnownLocation`, `requestLocationUpdates`,
//! `killBackgroundProcesses` — and the privileged backend acts on the *whole device's* state.
//! This is **ambient authority**: `getSystemService` is reachable from any context with no
//! cap in hand, the backend holds device-wide authority, and a manifest permission gates only
//! *some* methods (a `SecurityException` at the call, not at the reach) — `getSystemService`
//! itself is never refused, and the privileged service is the standing ambient backend.
//!
//! # What graphideOS does (the cap-bounded reforge)
//!
//! `GRAPHIDEOS.md §1`: *"each system service becomes a deos **organ/cell** exposing its
//! authority as caps, reached by turns, not a privileged backend (GrapheneOS's 'Play services
//! as an unprivileged app' taken to its conclusion: there is no privileged backend, there is
//! the cap graph)."* This module is that, in the same shape as the sibling gates and over the
//! [`crate::organs`](../../starbridge-v2/src/organs.rs)-style **organ-cell** vocabulary:
//!
//! 1. **The reach is over the cap-reachable organ neighborhood, not the device.** The
//!    [`ServiceResolver`] holds exactly the service-organ cells the android-cell was *granted*
//!    a cap to reach — it is decidedly NOT the framework's global `ServiceManager`. A
//!    `getSystemService` for a service no cap-reachable organ provides is
//!    [`ServiceDecision::RefusedNoOrgan`]: **the app cannot reach a system service it was
//!    never handed a cap to** (there is no ambient `getSystemService`). The cap to the organ
//!    *is* the permission — the AOSP "get the manager freely, throw at the call" loophole is
//!    closed: no cap-reachable organ, no reach at all.
//! 2. **A read is an authorized query; a state-changing call is a receipted turn.** Faithful
//!    AOSP service semantics: `getLastKnownLocation` / `getRunningAppProcesses` /
//!    `getPrimaryClip` are **queries** ([`ServiceCallKind::Query`] — an authorized read of the
//!    organ's state); `requestLocationUpdates` / `killBackgroundProcesses` / `setPrimaryClip`
//!    are **state changes** ([`ServiceCallKind::StateChange`] — a mutation that in deos
//!    commits as a **receipted turn against the organ cell**, needing a write-granting cap).
//!    [`SystemService::classify`] carries the per-service method classification.
//! 3. **Write authority is the attenuation tooth.** A *state-changing* call against an organ
//!    the holder was granted only **read** ([`ServiceGrant::ReadOnly`]) is
//!    [`ServiceDecision::RefusedReadOnly`] — a read cap does not amplify to a state change
//!    (the `granted ⊆ held` lattice, organ-side). AOSP's per-method `SecurityException` split
//!    becomes a cap attenuation checked at the gate, before the organ is touched.
//! 4. **Ambiguity is an explicit chooser, never a silent route.** Two cap-reachable organs
//!    answering one service ⟹ [`ServiceDecision::Ambiguous`] (the powerbox-style ceremony) —
//!    a device may hold, say, a real-location organ and a mock-location organ; deos refuses to
//!    silently pick.
//!
//! Every decision leaves a content-addressed [`ServiceReceipt`], so the android-cell's
//! system-service traffic is auditable end to end exactly like the intent / content / net /
//! input receipts.
//!
//! # The depth (honest, like the intent + content + net gates')
//!
//! This is the **reach-and-authority** layer: the gate decides, against the granted organ set
//! + its grants, whether (and how) a `getSystemService` call may proceed, and records it. The
//! remaining frontier — interposing the *actual* binder `ServiceManager.getService` /
//! `transact` transactions inside the confined runtime so the device kernel itself routes only
//! cap-admitted service calls (the HAL/binder leg the net + intent gates also name), and the
//! in-circuit constructor proof that a given organ cell IS the device's location/activity
//! organ — are the same not-yet-claimed depth the sibling gates name. What IS real today: the
//! reach-resolution algebra + the read/state-change attenuation teeth + the faithful AOSP
//! method classification + the receipt, testable on any node with no device.

use dregg_firmament::CellId;

/// A standard AOSP system service — a representative set of the device's privileged framework
/// services, plus an `Other` long-tail. Each becomes a deos **organ cell** (the device's
/// location/activity/package organ); the SET an android-cell holds a cap to is the entire
/// system authority it may ever reach (no ambient `getSystemService`).
///
/// The variants name the services GrapheneOS itself most scrutinises (location, the package
/// manager, the activity manager, connectivity) plus the common sensor/clipboard/notification
/// reaches; the long tail is carried by its `Context.*_SERVICE` key string.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SystemService {
    /// `LocationManager` (`Context.LOCATION_SERVICE`) — the device's position organ.
    Location,
    /// `PackageManager` (`Context.getPackageManager()`) — the install/component organ.
    Package,
    /// `ActivityManager` (`Context.ACTIVITY_SERVICE`) — the running-process/task organ.
    Activity,
    /// `ConnectivityManager` (`Context.CONNECTIVITY_SERVICE`) — the network-state organ.
    Connectivity,
    /// `SensorManager` (`Context.SENSOR_SERVICE`) — the device-sensor organ.
    Sensor,
    /// `CameraManager` (`Context.CAMERA_SERVICE`) — the camera-device organ.
    Camera,
    /// `AudioManager` (`Context.AUDIO_SERVICE`) — the audio-routing/volume organ.
    Audio,
    /// `PowerManager` (`Context.POWER_SERVICE`) — the wake-lock/power-state organ.
    Power,
    /// `ClipboardManager` (`Context.CLIPBOARD_SERVICE`) — the shared-clip organ.
    Clipboard,
    /// `NotificationManager` (`Context.NOTIFICATION_SERVICE`) — the notification organ.
    Notification,
    /// `WifiManager` (`Context.WIFI_SERVICE`) — the wifi-state organ.
    Wifi,
    /// `AlarmManager` (`Context.ALARM_SERVICE`) — the scheduled-wake organ.
    Alarm,
    /// Any other system service (the long tail), carried by its `Context.*_SERVICE` key.
    Other(String),
}

impl SystemService {
    /// The `Context.*_SERVICE` key string the app passes to `getSystemService` — the stable
    /// identity an organ answers on, lower-cased for matching (AOSP service keys are simple
    /// lower-case tokens). `PackageManager` is obtained via `getPackageManager()` rather than a
    /// `Context` constant; graphideOS gives it the synthetic key `"package"` so every service
    /// reach is one uniform organ-keyed lookup.
    pub fn key(&self) -> String {
        match self {
            SystemService::Location => "location",
            SystemService::Package => "package",
            SystemService::Activity => "activity",
            SystemService::Connectivity => "connectivity",
            SystemService::Sensor => "sensor",
            SystemService::Camera => "camera",
            SystemService::Audio => "audio",
            SystemService::Power => "power",
            SystemService::Clipboard => "clipboard",
            SystemService::Notification => "notification",
            SystemService::Wifi => "wifi",
            SystemService::Alarm => "alarm",
            SystemService::Other(s) => return s.to_ascii_lowercase(),
        }
        .to_string()
    }

    /// The AOSP manager class this service is reached through (`android.location.LocationManager`,
    /// …) — the human label the receipt + chooser name, and the class the in-runtime binder
    /// interposition would shim.
    pub fn manager_class(&self) -> String {
        match self {
            SystemService::Location => "android.location.LocationManager",
            SystemService::Package => "android.content.pm.PackageManager",
            SystemService::Activity => "android.app.ActivityManager",
            SystemService::Connectivity => "android.net.ConnectivityManager",
            SystemService::Sensor => "android.hardware.SensorManager",
            SystemService::Camera => "android.hardware.camera2.CameraManager",
            SystemService::Audio => "android.media.AudioManager",
            SystemService::Power => "android.os.PowerManager",
            SystemService::Clipboard => "android.content.ClipboardManager",
            SystemService::Notification => "android.app.NotificationManager",
            SystemService::Wifi => "android.net.wifi.WifiManager",
            SystemService::Alarm => "android.app.AlarmManager",
            SystemService::Other(s) => return s.clone(),
        }
        .to_string()
    }

    /// **The device's organ cell for this service** — derived deterministically from the
    /// service key, so distinct services (location vs activity) target distinct organs and a
    /// resolver's organ set distinguishes them. On a real device the boot resolves these to the
    /// actual reforged service-organ cells (`GRAPHIDEOS.md §1`); the key-derived id is the
    /// stable stand-in identity, in the SAME spirit as [`crate::appfactory`]'s `organ_cell`
    /// (a distinct derive-key namespace so a service organ and a permission organ never alias).
    pub fn organ_cell(&self) -> CellId {
        let mut h = blake3::Hasher::new_derive_key("graphideos-system-service-organ-cell-v1");
        h.update(self.key().as_bytes());
        CellId::from_bytes(*h.finalize().as_bytes())
    }

    /// **The AOSP method classification** — is calling `method` on this service a *query* (an
    /// authorized read of the organ's state) or a *state change* (a mutation that, in deos,
    /// commits as a receipted turn and needs a write-granting cap)? This is the load-bearing
    /// faithfulness: it mirrors AOSP's own read-vs-mutate split per service.
    ///
    /// Returns `None` for a method this classifier does not know — the caller
    /// ([`ServiceOp::resolve`]) treats an unknown method as a [`ServiceCallKind::StateChange`]
    /// (fail-closed toward *more* authority required: an unrecognised call must not slip
    /// through as a free read).
    pub fn classify(&self, method: &str) -> Option<ServiceCallKind> {
        use ServiceCallKind::{Query, StateChange};
        let k = match (self, method) {
            // LocationManager — reads vs. the registration/proximity state changes.
            (SystemService::Location, "getLastKnownLocation")
            | (SystemService::Location, "getProviders")
            | (SystemService::Location, "isProviderEnabled")
            | (SystemService::Location, "getCurrentLocation") => Query,
            (SystemService::Location, "requestLocationUpdates")
            | (SystemService::Location, "removeUpdates")
            | (SystemService::Location, "addProximityAlert")
            | (SystemService::Location, "addGpsStatusListener") => StateChange,

            // PackageManager — the info reads vs. the component/enabled state changes.
            (SystemService::Package, "getPackageInfo")
            | (SystemService::Package, "getInstalledPackages")
            | (SystemService::Package, "getInstalledApplications")
            | (SystemService::Package, "queryIntentActivities")
            | (SystemService::Package, "resolveActivity")
            | (SystemService::Package, "checkPermission") => Query,
            (SystemService::Package, "setComponentEnabledSetting")
            | (SystemService::Package, "setApplicationEnabledSetting")
            | (SystemService::Package, "installPackage")
            | (SystemService::Package, "deletePackage")
            | (SystemService::Package, "clearPackagePreferredActivities") => StateChange,

            // ActivityManager — the introspection reads vs. the kill/move state changes.
            (SystemService::Activity, "getRunningAppProcesses")
            | (SystemService::Activity, "getMemoryInfo")
            | (SystemService::Activity, "getRunningServices")
            | (SystemService::Activity, "getAppTasks")
            | (SystemService::Activity, "isLowRamDevice") => Query,
            (SystemService::Activity, "killBackgroundProcesses")
            | (SystemService::Activity, "moveTaskToFront")
            | (SystemService::Activity, "removeTask")
            | (SystemService::Activity, "clearApplicationUserData") => StateChange,

            // ConnectivityManager — the network-state reads vs. the bind/request changes.
            (SystemService::Connectivity, "getActiveNetwork")
            | (SystemService::Connectivity, "getActiveNetworkInfo")
            | (SystemService::Connectivity, "getNetworkCapabilities")
            | (SystemService::Connectivity, "getAllNetworks") => Query,
            (SystemService::Connectivity, "requestNetwork")
            | (SystemService::Connectivity, "bindProcessToNetwork")
            | (SystemService::Connectivity, "registerNetworkCallback")
            | (SystemService::Connectivity, "reportNetworkConnectivity") => StateChange,

            // SensorManager — the catalogue read vs. the listener registration.
            (SystemService::Sensor, "getSensorList")
            | (SystemService::Sensor, "getDefaultSensor") => Query,
            (SystemService::Sensor, "registerListener")
            | (SystemService::Sensor, "unregisterListener") => StateChange,

            // CameraManager — the catalogue read vs. opening the device.
            (SystemService::Camera, "getCameraIdList")
            | (SystemService::Camera, "getCameraCharacteristics") => Query,
            (SystemService::Camera, "openCamera") | (SystemService::Camera, "setTorchMode") => {
                StateChange
            }

            // AudioManager — the state reads vs. the volume/mode changes.
            (SystemService::Audio, "getStreamVolume")
            | (SystemService::Audio, "getMode")
            | (SystemService::Audio, "isMusicActive") => Query,
            (SystemService::Audio, "setStreamVolume")
            | (SystemService::Audio, "setMode")
            | (SystemService::Audio, "requestAudioFocus")
            | (SystemService::Audio, "adjustStreamVolume") => StateChange,

            // PowerManager — the interactive read vs. acquiring a wake lock.
            (SystemService::Power, "isInteractive") | (SystemService::Power, "isPowerSaveMode") => {
                Query
            }
            (SystemService::Power, "newWakeLock")
            | (SystemService::Power, "acquire")
            | (SystemService::Power, "goToSleep") => StateChange,

            // ClipboardManager — the read vs. the write (the AOSP-Q+ privacy-gated split).
            (SystemService::Clipboard, "getPrimaryClip")
            | (SystemService::Clipboard, "hasPrimaryClip")
            | (SystemService::Clipboard, "getPrimaryClipDescription") => Query,
            (SystemService::Clipboard, "setPrimaryClip")
            | (SystemService::Clipboard, "clearPrimaryClip") => StateChange,

            // NotificationManager — the active read vs. notify/cancel.
            (SystemService::Notification, "getActiveNotifications")
            | (SystemService::Notification, "areNotificationsEnabled") => Query,
            (SystemService::Notification, "notify")
            | (SystemService::Notification, "cancel")
            | (SystemService::Notification, "cancelAll")
            | (SystemService::Notification, "createNotificationChannel") => StateChange,

            // WifiManager — the connection read vs. the enable/connect state change.
            (SystemService::Wifi, "getConnectionInfo")
            | (SystemService::Wifi, "getScanResults")
            | (SystemService::Wifi, "isWifiEnabled") => Query,
            (SystemService::Wifi, "setWifiEnabled")
            | (SystemService::Wifi, "connect")
            | (SystemService::Wifi, "startScan")
            | (SystemService::Wifi, "addNetwork") => StateChange,

            // AlarmManager — purely a scheduler: every reach is a state change.
            (SystemService::Alarm, "set")
            | (SystemService::Alarm, "setExact")
            | (SystemService::Alarm, "setRepeating")
            | (SystemService::Alarm, "cancel") => StateChange,

            // Unknown service/method pair: not classified here.
            _ => return None,
        };
        Some(k)
    }

    /// The AOSP permission a manifest must declare to be granted a cap to this service's
    /// organ — the bridge from [`crate::appfactory::AndroidPermission`] (a declared permission)
    /// to a reachable system-service organ (the install↔service loop). `None` for services
    /// reachable without a dangerous permission (their organ is granted by ambient device
    /// policy, not a manifest permission — surfaced for completeness, not auto-granted).
    pub fn required_permission(&self) -> Option<crate::appfactory::AndroidPermission> {
        use crate::appfactory::AndroidPermission as P;
        match self {
            SystemService::Location => Some(P::AccessFineLocation),
            SystemService::Camera => Some(P::Camera),
            SystemService::Audio => Some(P::RecordAudio),
            SystemService::Connectivity | SystemService::Wifi => Some(P::Internet),
            _ => None,
        }
    }

    /// A short human label for the chooser / status line (the manager's simple name).
    pub fn label(&self) -> String {
        self.manager_class()
            .rsplit('.')
            .next()
            .unwrap_or("Service")
            .to_string()
    }

    /// The standard catalogue of named services — the device's full organ roster (sans the
    /// `Other` long tail). A boot resolves each to its reforged organ cell; a resolver is built
    /// over the SUBSET an android-cell holds a cap to.
    pub fn all_standard() -> Vec<SystemService> {
        vec![
            SystemService::Location,
            SystemService::Package,
            SystemService::Activity,
            SystemService::Connectivity,
            SystemService::Sensor,
            SystemService::Camera,
            SystemService::Audio,
            SystemService::Power,
            SystemService::Clipboard,
            SystemService::Notification,
            SystemService::Wifi,
            SystemService::Alarm,
        ]
    }
}

/// Whether a service call is a **query** (an authorized read of the organ's state) or a
/// **state change** (a mutation that commits as a receipted turn against the organ cell and
/// needs a write-granting cap). The faithful AOSP read-vs-mutate split, organ-side.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ServiceCallKind {
    /// A read — `getLastKnownLocation`, `getRunningAppProcesses`, `getPrimaryClip`, … —
    /// authorized against the organ, no state changes.
    Query,
    /// A mutation — `requestLocationUpdates`, `killBackgroundProcesses`, `setPrimaryClip`, … —
    /// which in deos commits as a **receipted turn** against the organ cell (and needs a
    /// write-granting cap).
    StateChange,
}

impl ServiceCallKind {
    fn tag(&self) -> &'static str {
        match self {
            ServiceCallKind::Query => "query",
            ServiceCallKind::StateChange => "state-change",
        }
    }
}

/// What a holder was granted over a service organ — the deos form of AOSP's per-method
/// permission split, expressed as a cap attenuation. A [`ReadOnly`](Self::ReadOnly) grant
/// cannot amplify to a state change.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ServiceGrant {
    /// The holder may issue **queries** (reads) against the organ only — a state-changing call
    /// is refused (the attenuation tooth).
    ReadOnly,
    /// The holder may query AND issue state changes (a state change commits as a receipted turn
    /// against the organ cell).
    ReadWrite,
}

impl ServiceGrant {
    /// Does this grant admit a call of `kind`? `ReadOnly` admits only [`ServiceCallKind::Query`].
    pub fn admits(&self, kind: ServiceCallKind) -> bool {
        match (self, kind) {
            (ServiceGrant::ReadWrite, _) => true,
            (ServiceGrant::ReadOnly, ServiceCallKind::Query) => true,
            (ServiceGrant::ReadOnly, ServiceCallKind::StateChange) => false,
        }
    }
}

/// A service call the confined app issued — the service it reached for, the method it called,
/// and the call's [`ServiceCallKind`] (query vs state change). The unit the [`ServiceResolver`]
/// gates: the deos form of a `getSystemService(…).method(…)` pair.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ServiceOp {
    /// The system service reached for (`getSystemService(key)`).
    pub service: SystemService,
    /// The method called on the service (`getLastKnownLocation`, `killBackgroundProcesses`, …).
    pub method: String,
    /// Whether the call is a query or a state change (faithful to AOSP, or fail-closed for an
    /// unknown method — see [`ServiceOp::resolve`]).
    pub kind: ServiceCallKind,
}

impl ServiceOp {
    /// **Build a service op, classifying `method` faithfully.** Uses
    /// [`SystemService::classify`]; an unrecognised method is treated as a
    /// [`ServiceCallKind::StateChange`] — fail-closed toward *more* authority required, so an
    /// unknown call can never slip through as a free read.
    pub fn resolve(service: SystemService, method: impl Into<String>) -> Self {
        let method = method.into();
        let kind = service
            .classify(&method)
            .unwrap_or(ServiceCallKind::StateChange);
        ServiceOp {
            service,
            method,
            kind,
        }
    }

    /// A query op (an explicit read — bypasses classification; use when the caller KNOWS the
    /// call is a read).
    pub fn query(service: SystemService, method: impl Into<String>) -> Self {
        ServiceOp {
            service,
            method: method.into(),
            kind: ServiceCallKind::Query,
        }
    }

    /// A state-change op (an explicit mutation).
    pub fn state_change(service: SystemService, method: impl Into<String>) -> Self {
        ServiceOp {
            service,
            method: method.into(),
            kind: ServiceCallKind::StateChange,
        }
    }

    /// A short tag for the receipt digest + status line.
    fn tag(&self) -> String {
        format!("{}.{}", self.service.key(), self.method)
    }
}

/// A cap-reachable system-service organ in the android-cell's bounded neighborhood — the deos
/// form of a reforged AOSP system service. The organ's authority IS its cell's state/program; a
/// query is authority-checked, a state change is a receipted turn against it. Held by the
/// [`ServiceResolver`] only for organs the android-cell holds a cap to (NOT the device's global
/// `ServiceManager`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ServiceOrgan {
    /// The organ cell — the named capability holder the call is handed to.
    pub cell: CellId,
    /// The service this organ provides.
    pub service: SystemService,
    /// A short human label for the chooser / status line.
    pub label: String,
    /// The access the holder was granted over this organ (the cap attenuation).
    pub grant: ServiceGrant,
}

impl ServiceOrgan {
    /// An organ for an explicit cell + service + grant.
    pub fn new(cell: CellId, service: SystemService, grant: ServiceGrant) -> Self {
        let label = service.label();
        ServiceOrgan {
            cell,
            service,
            label,
            grant,
        }
    }

    /// **The device's standard organ for `service`** with the given grant — the organ cell is
    /// `service.organ_cell()` (the key-derived device-organ identity). The unit a boot's organ
    /// roster + a granted-permission bridge builds from.
    pub fn standard(service: SystemService, grant: ServiceGrant) -> Self {
        let cell = service.organ_cell();
        ServiceOrgan::new(cell, service, grant)
    }

    /// Does this organ provide `service`? (The reach-match key — service identity.)
    pub fn answers(&self, service: &SystemService) -> bool {
        &self.service == service
    }
}

/// The four distinguishable ends a system-service reach can hit — the service-side analogue of
/// [`crate::contentgate::ContentDecision`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ServiceDecision {
    /// Exactly one cap-reachable organ provided the service AND the grant admits the call: a
    /// cap-bounded hand to the organ (a query = an authorized read; a state change = a
    /// receipted turn against the organ cell).
    Granted {
        organ: CellId,
        label: String,
        method: String,
        kind: ServiceCallKind,
    },
    /// Two+ cap-reachable organs provided one service: deos refuses to silently route and
    /// surfaces the candidates for an explicit chooser.
    Ambiguous { candidates: Vec<(CellId, String)> },
    /// NO cap-reachable organ provided this service — the no-ambient-`getSystemService`
    /// property: the app cannot reach a service it was never granted a cap to.
    RefusedNoOrgan { service: String },
    /// A STATE-CHANGING call against an organ the holder was granted only READ — refused by the
    /// cap attenuation (a read cap does not amplify to a state change).
    RefusedReadOnly {
        organ: CellId,
        service: String,
        method: String,
    },
}

impl ServiceDecision {
    pub fn granted(&self) -> bool {
        matches!(self, ServiceDecision::Granted { .. })
    }
    pub fn refused_no_organ(&self) -> bool {
        matches!(self, ServiceDecision::RefusedNoOrgan { .. })
    }
    pub fn refused_read_only(&self) -> bool {
        matches!(self, ServiceDecision::RefusedReadOnly { .. })
    }
    pub fn ambiguous(&self) -> bool {
        matches!(self, ServiceDecision::Ambiguous { .. })
    }
}

/// **The receipt left by a gated system-service reach.** Every decision produces one, so the
/// android-cell's `getSystemService` traffic is auditable end to end exactly like the intent /
/// content / egress / input receipts. Content-addressed:
/// `decision_digest = blake3(cell? ‖ op_tag ‖ kind ‖ outcome ‖ organ?)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ServiceReceipt {
    /// The android-cell whose held cap + granted organ set decided this reach.
    pub cell: Option<CellId>,
    /// The service call the confined app issued.
    pub op: ServiceOp,
    /// The decision reached.
    pub decision: ServiceDecision,
    /// `blake3(…)[..32]` — the content-addressed witness a verifier reconstructs.
    pub decision_digest: [u8; 32],
}

impl ServiceReceipt {
    fn digest(cell: Option<CellId>, op: &ServiceOp, decision: &ServiceDecision) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        if let Some(c) = cell {
            h.update(b"\x01cell");
            h.update(c.as_bytes());
        }
        h.update(op.tag().as_bytes());
        h.update(b"\x00");
        h.update(op.kind.tag().as_bytes());
        match decision {
            ServiceDecision::Granted { organ, kind, .. } => {
                h.update(b"\x01granted");
                h.update(organ.as_bytes());
                h.update(kind.tag().as_bytes());
            }
            ServiceDecision::Ambiguous { candidates } => {
                h.update(b"\x02ambiguous");
                for (c, _) in candidates {
                    h.update(c.as_bytes());
                }
            }
            ServiceDecision::RefusedNoOrgan { service } => {
                h.update(b"\x03refused-no-organ");
                h.update(service.as_bytes());
            }
            ServiceDecision::RefusedReadOnly { organ, service, .. } => {
                h.update(b"\x04refused-read-only");
                h.update(organ.as_bytes());
                h.update(service.as_bytes());
            }
        }
        *h.finalize().as_bytes()
    }

    /// A one-line audit truth for the cockpit status line — which end, named exactly.
    pub fn status_line(&self) -> String {
        match &self.decision {
            ServiceDecision::Granted {
                label,
                method,
                kind,
                ..
            } => format!(
                "android-service: ✔ {}.{method} → handed to «{label}» organ as a cap-bounded {} — a named organ cell, not an ambient getSystemService",
                self.op.service.key(),
                match kind {
                    ServiceCallKind::Query => "query",
                    ServiceCallKind::StateChange => "receipted turn",
                }
            ),
            ServiceDecision::Ambiguous { candidates } => format!(
                "android-service: ◈ {} matches {} cap-reachable organs — surfaced for an explicit chooser (no silent route)",
                self.op.tag(),
                candidates.len()
            ),
            ServiceDecision::RefusedNoOrgan { service } => format!(
                "android-service: ✖ {} REFUSED — no cap-reachable organ provides «{service}» (the app cannot getSystemService a service it was never granted)",
                self.op.tag()
            ),
            ServiceDecision::RefusedReadOnly {
                service, method, ..
            } => format!(
                "android-service: ✖ {service}.{method} REFUSED — the held cap grants only READ over «{service}» (a read cap does not amplify to a state change)",
            ),
        }
    }
}

/// The cap-gated system-service resolver for one android-cell — **the spotter over the cell's
/// bounded, cap-reachable organ neighborhood**, NOT the framework's global `ServiceManager`.
/// Holds the granted organ set + the cell it speaks for; holds NO ambient authority — every
/// [`resolve`](Self::resolve) is a pure function of its organs.
pub struct ServiceResolver {
    organs: Vec<ServiceOrgan>,
    cell: Option<CellId>,
}

impl ServiceResolver {
    /// Build a resolver over the granted organ neighborhood and the cell it speaks for.
    pub fn new(organs: impl IntoIterator<Item = ServiceOrgan>, cell: Option<CellId>) -> Self {
        ServiceResolver {
            organs: organs.into_iter().collect(),
            cell,
        }
    }

    /// The granted organ neighborhood (the cap-reachable set the spotter ranges over).
    pub fn organs(&self) -> &[ServiceOrgan] {
        &self.organs
    }

    /// **THE SERVICE GATE.** The confined app issued `op` (a `getSystemService(…).method(…)`).
    /// Decide against the granted organ set + its grants, and return the decision AND its
    /// [`ServiceReceipt`].
    ///
    /// Order of teeth (fail-closed):
    /// 1. **Spotter over the cap-reachable set** — match `op.service` against the granted
    ///    organs. Zero ⟹ [`ServiceDecision::RefusedNoOrgan`] (no ambient `getSystemService`);
    ///    two+ ⟹ [`ServiceDecision::Ambiguous`] (the explicit chooser).
    /// 2. **The grant attenuation** — one match, but a STATE CHANGE against a `ReadOnly` grant ⟹
    ///    [`ServiceDecision::RefusedReadOnly`]. Otherwise [`ServiceDecision::Granted`].
    pub fn resolve(&self, op: &ServiceOp) -> ServiceReceipt {
        let mut matches: Vec<&ServiceOrgan> = self
            .organs
            .iter()
            .filter(|o| o.answers(&op.service))
            .collect();
        matches.sort_by(|a, b| a.cell.as_bytes().cmp(b.cell.as_bytes()));
        matches.dedup_by(|a, b| a.cell == b.cell);

        let decision = match matches.len() {
            0 => ServiceDecision::RefusedNoOrgan {
                service: op.service.key(),
            },
            1 => {
                let o = matches[0];
                if o.grant.admits(op.kind) {
                    ServiceDecision::Granted {
                        organ: o.cell,
                        label: o.label.clone(),
                        method: op.method.clone(),
                        kind: op.kind,
                    }
                } else {
                    ServiceDecision::RefusedReadOnly {
                        organ: o.cell,
                        service: op.service.key(),
                        method: op.method.clone(),
                    }
                }
            }
            _ => ServiceDecision::Ambiguous {
                candidates: matches.iter().map(|o| (o.cell, o.label.clone())).collect(),
            },
        };
        self.receipt(op, decision)
    }

    fn receipt(&self, op: &ServiceOp, decision: ServiceDecision) -> ServiceReceipt {
        let decision_digest = ServiceReceipt::digest(self.cell, op, &decision);
        ServiceReceipt {
            cell: self.cell,
            op: op.clone(),
            decision,
            decision_digest,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::cell_seed;

    fn location_organ(grant: ServiceGrant) -> ServiceOrgan {
        ServiceOrgan::standard(SystemService::Location, grant)
    }
    fn activity_organ(grant: ServiceGrant) -> ServiceOrgan {
        ServiceOrgan::standard(SystemService::Activity, grant)
    }

    /// **THE LOAD-BEARING TEST: a service no cap-reachable organ provides is refused — the app
    /// cannot `getSystemService` a service it was never granted a cap to.**
    #[test]
    fn unreachable_service_is_refused() {
        let me = cell_seed(9);
        // The neighborhood holds the location organ only — no activity organ was granted.
        let resolver = ServiceResolver::new([location_organ(ServiceGrant::ReadOnly)], Some(me));
        let op = ServiceOp::query(SystemService::Activity, "getRunningAppProcesses");
        let receipt = resolver.resolve(&op);

        assert!(
            receipt.decision.refused_no_organ(),
            "activity has no cap-reachable organ (no ambient getSystemService)"
        );
        assert_eq!(receipt.cell, Some(me));
        assert!(receipt.status_line().contains("never granted"));
        assert_eq!(
            receipt.decision_digest,
            ServiceReceipt::digest(Some(me), &op, &receipt.decision)
        );
    }

    /// Exactly one cap-reachable organ provides the service ⟹ a cap-bounded query to that cell.
    #[test]
    fn single_organ_grants_a_query() {
        let me = cell_seed(9);
        let resolver = ServiceResolver::new(
            [
                location_organ(ServiceGrant::ReadOnly),
                activity_organ(ServiceGrant::ReadWrite),
            ],
            Some(me),
        );
        let op = ServiceOp::resolve(SystemService::Location, "getLastKnownLocation");
        assert_eq!(
            op.kind,
            ServiceCallKind::Query,
            "getLastKnownLocation is a read"
        );
        let receipt = resolver.resolve(&op);
        match &receipt.decision {
            ServiceDecision::Granted {
                organ,
                kind,
                method,
                ..
            } => {
                assert_eq!(*organ, SystemService::Location.organ_cell());
                assert_eq!(*kind, ServiceCallKind::Query);
                assert_eq!(method, "getLastKnownLocation");
            }
            other => panic!("expected Granted, got {other:?}"),
        }
        assert!(receipt.status_line().contains("cap-bounded query"));
    }

    /// **THE ATTENUATION TOOTH: a STATE CHANGE against a ReadOnly grant is refused — a read cap
    /// does not amplify to a state change.**
    #[test]
    fn state_change_against_read_only_grant_is_refused() {
        let me = cell_seed(9);
        let resolver = ServiceResolver::new([location_organ(ServiceGrant::ReadOnly)], Some(me));

        // A read is granted...
        let q = ServiceOp::resolve(SystemService::Location, "getLastKnownLocation");
        assert!(resolver.resolve(&q).decision.granted());

        // ...but registering for updates (state-changing) against the read-only grant is refused.
        let w = ServiceOp::resolve(SystemService::Location, "requestLocationUpdates");
        assert_eq!(w.kind, ServiceCallKind::StateChange);
        let receipt = resolver.resolve(&w);
        assert!(receipt.decision.refused_read_only());
        assert!(
            receipt
                .status_line()
                .contains("does not amplify to a state change")
        );
        assert_eq!(
            receipt.decision,
            ServiceDecision::RefusedReadOnly {
                organ: SystemService::Location.organ_cell(),
                service: "location".into(),
                method: "requestLocationUpdates".into(),
            }
        );
    }

    /// A ReadWrite grant admits a state change (which commits as a receipted turn).
    #[test]
    fn state_change_against_read_write_grant_is_a_receipted_turn() {
        let me = cell_seed(9);
        let resolver = ServiceResolver::new([activity_organ(ServiceGrant::ReadWrite)], Some(me));
        let w = ServiceOp::resolve(SystemService::Activity, "killBackgroundProcesses");
        assert_eq!(w.kind, ServiceCallKind::StateChange);
        let receipt = resolver.resolve(&w);
        assert!(receipt.decision.granted());
        assert!(receipt.status_line().contains("receipted turn"));
    }

    /// Two cap-reachable organs providing one service ⟹ an EXPLICIT chooser, never a silent
    /// route (e.g. a real-location organ and a mock-location organ).
    #[test]
    fn duplicate_service_surfaces_a_chooser() {
        let me = cell_seed(9);
        // A second, distinct-cell location organ (a mock-location provider).
        let mock = ServiceOrgan::new(
            cell_seed(0x77),
            SystemService::Location,
            ServiceGrant::ReadOnly,
        );
        let resolver =
            ServiceResolver::new([location_organ(ServiceGrant::ReadOnly), mock], Some(me));
        let op = ServiceOp::query(SystemService::Location, "getLastKnownLocation");
        let r = resolver.resolve(&op);
        match &r.decision {
            ServiceDecision::Ambiguous { candidates } => assert_eq!(candidates.len(), 2),
            other => panic!("expected Ambiguous, got {other:?}"),
        }
        assert!(r.status_line().contains("explicit chooser"));
    }

    /// **Fail-closed classification: an UNKNOWN method is treated as a state change (more
    /// authority required), so it is refused against a read-only grant rather than slipping
    /// through as a free read.**
    #[test]
    fn unknown_method_is_fail_closed_to_state_change() {
        let me = cell_seed(9);
        let resolver = ServiceResolver::new([location_organ(ServiceGrant::ReadOnly)], Some(me));
        let op = ServiceOp::resolve(SystemService::Location, "someUndocumentedMethod");
        assert_eq!(
            op.kind,
            ServiceCallKind::StateChange,
            "an unclassified method fails closed to a state change"
        );
        assert!(resolver.resolve(&op).decision.refused_read_only());
    }

    /// The AOSP method classification is faithful across services (the load-bearing semantics).
    #[test]
    fn method_classification_is_faithful() {
        use ServiceCallKind::{Query, StateChange};
        let cases = [
            (SystemService::Location, "getLastKnownLocation", Query),
            (
                SystemService::Location,
                "requestLocationUpdates",
                StateChange,
            ),
            (SystemService::Package, "getInstalledPackages", Query),
            (
                SystemService::Package,
                "setComponentEnabledSetting",
                StateChange,
            ),
            (SystemService::Activity, "getRunningAppProcesses", Query),
            (
                SystemService::Activity,
                "killBackgroundProcesses",
                StateChange,
            ),
            (SystemService::Connectivity, "getActiveNetwork", Query),
            (
                SystemService::Connectivity,
                "bindProcessToNetwork",
                StateChange,
            ),
            (SystemService::Clipboard, "getPrimaryClip", Query),
            (SystemService::Clipboard, "setPrimaryClip", StateChange),
            (SystemService::Alarm, "set", StateChange),
        ];
        for (svc, method, want) in cases {
            assert_eq!(
                svc.classify(method),
                Some(want),
                "{}.{method} classified as {want:?}",
                svc.key()
            );
        }
    }

    /// Distinct services target distinct organ cells (the reach distinguishes them), and the
    /// derivation is stable (the same service ⟹ the same organ cell).
    #[test]
    fn organ_cells_are_distinct_and_stable() {
        assert_ne!(
            SystemService::Location.organ_cell(),
            SystemService::Activity.organ_cell()
        );
        assert_eq!(
            SystemService::Location.organ_cell(),
            SystemService::Location.organ_cell()
        );
        // The Other long-tail keys on its string.
        assert_eq!(
            SystemService::Other("vibrator".into()).organ_cell(),
            SystemService::Other("VIBRATOR".into()).organ_cell(),
            "the Other key is case-insensitive (lower-cased)"
        );
    }

    /// The install↔service bridge: a service names the permission a manifest must declare to be
    /// granted a cap to its organ.
    #[test]
    fn services_name_their_required_permission() {
        use crate::appfactory::AndroidPermission;
        assert_eq!(
            SystemService::Location.required_permission(),
            Some(AndroidPermission::AccessFineLocation)
        );
        assert_eq!(
            SystemService::Camera.required_permission(),
            Some(AndroidPermission::Camera)
        );
        // A service granted by ambient device policy (not a dangerous permission) names none.
        assert_eq!(SystemService::Clipboard.required_permission(), None);
    }
}
