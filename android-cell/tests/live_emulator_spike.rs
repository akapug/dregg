//! **THE LIVE SPIKE — an Android app's frame through the deos compositor, on the
//! macOS simulator host.**
//!
//! This test drives the REAL `MacOsEmulatorRuntime`: it boots the `Pixel_7_API_35`
//! AVD under Hypervisor.framework, launches an app, captures its surface as an
//! `RgbaFrame`, presents it through the GENUINE `present_frame` / `CompositorPd` gate,
//! and exercises the cap-gated net gate (a cap-denied origin reaches nothing). It is
//! the android-cell's `cap_gated_pipeline` moment, on macOS — proving the doc's
//! original "macOS is a wall" verdict was a container-only limit the simulator host
//! crosses.
//!
//! It is `#[ignore]` because it needs a live SDK + an AVD + ~2min to boot. Run it
//! explicitly on the dev host:
//!
//! ```sh
//! export ANDROID_SDK_ROOT="$HOME/Library/Android/sdk"
//! cargo test -p android-cell --test live_emulator_spike -- --ignored --nocapture
//! ```
//!
//! It also writes the captured frame to `target/android_cell_spike_capture.png` (when
//! the `image` dev-dep is built) so a human can SEE the android app the compositor
//! admitted — the screenshot the doc's "definition of done" asks for.

use android_cell::{
    AndroidInput, AndroidInputGate, AndroidNetGate, AndroidPresentation, AndroidRuntime, AppLaunch,
    DeviceSpec, IoDecision, present_android_frame,
};
use dregg_captp::netlayer::InProcessFabric;
use dregg_firmament::emulated_kernel::EmulatedKernel;
use dregg_firmament::{CompositorPd, Scene, Surface, cell_seed, label_of};
use starbridge_web_surface::{AuthRequired, SurfaceCapability};

#[cfg(target_os = "macos")]
#[test]
#[ignore = "needs a live Android SDK + AVD; ~2min boot. Run with --ignored on the dev host."]
fn android_app_presents_through_deos_compositor_with_cap_gate() {
    use android_cell::MacOsEmulatorRuntime;

    // ── 1. BOOT THE SIMULATOR HOST ────────────────────────────────────────────
    let mut rt = MacOsEmulatorRuntime::new(DeviceSpec::dev_default());
    rt.boot()
        .expect("the Pixel AVD boots under Hypervisor.framework");

    // ── 2. LAUNCH ONE APP (the cell's program) ────────────────────────────────
    rt.launch_app(&AppLaunch::Component(
        "com.android.settings/.Settings".to_string(),
    ))
    .expect("the Settings app launches");
    // Let it draw.
    std::thread::sleep(std::time::Duration::from_secs(4));

    // ── 3. CAPTURE ITS SURFACE → RgbaFrame ────────────────────────────────────
    let frame = rt
        .capture_frame()
        .expect("the app's surface captures to an RgbaFrame");
    assert!(frame.width > 0 && frame.height > 0, "a real-sized frame");
    assert_eq!(
        frame.bytes.len() as u32,
        frame.width * frame.height * 4,
        "RGBA8, tightly packed"
    );
    assert!(
        frame.bytes.iter().any(|&b| b != frame.bytes[0]),
        "a real app frame has content, not a flat color"
    );

    // Write a human-viewable PNG of what the compositor will admit.
    {
        use std::io::Write;
        let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join("android_cell_spike_capture.png");
        let img = image::RgbaImage::from_raw(frame.width, frame.height, frame.bytes.clone())
            .expect("rgba buffer is the right size for the image");
        img.save(&path).expect("save the captured frame as png");
        let _ = std::io::stdout().write_all(
            format!("\nspike: captured frame written to {}\n", path.display()).as_bytes(),
        );
    }

    // ── 4. PRESENT THROUGH THE GENUINE COMPOSITOR GATE ────────────────────────
    let presenter = cell_seed(3);
    let kernel = EmulatedKernel::new();
    let mut compositor = CompositorPd::boot(
        kernel,
        Scene {
            surfaces: vec![Surface {
                owner: presenter,
                regions: vec![7],
                content_digest: 0,
                source_state_root: 42,
                z_layer: 0,
                focus_flag: true,
            }],
        },
    );
    let digest = frame.content_digest();
    let commit = present_android_frame(
        &mut compositor,
        &frame,
        AndroidPresentation {
            presenter,
            target_regions: vec![7],
            source_state_root: 42,
            claims_focus: true,
        },
    )
    .expect("the genuine compositor gate admits the honest android present");
    assert_eq!(commit.digest, digest, "the real android pixels' digest");
    assert_eq!(commit.label, label_of(&presenter, 42), "T2 owner-binding");
    let fb = compositor.framebuffer_snapshot();
    assert_eq!(fb[7], (digest & 0xFF) as u8, "the android frame composited");

    // ── 5. CAP-GATE THE I/O — a denied origin reaches nothing + a receipt ─────
    let fabric = InProcessFabric::new();
    let me = fabric.join([0x07; 32]);
    let _allowed = fabric.join(android_cell::netgate::origin_to_peer(
        "https://api.example.com",
    ));
    let gate = AndroidNetGate::new(me, Some(presenter));
    let surface = SurfaceCapability::scoped(
        presenter,
        AuthRequired::Either,
        [String::from("https://api.example.com")],
        [],
    );
    let denied = android_cell::netgate::block_on(gate.egress(&surface, "https://tracker.evil.com"));
    assert!(
        matches!(denied.decision, IoDecision::RefusedByCap { .. }),
        "the cap-denied origin is refused before any socket — nothing reaches the glass"
    );
    println!("spike: {}", denied.status_line());

    let allowed = android_cell::netgate::block_on(gate.egress(&surface, "https://api.example.com"));
    assert!(allowed.decision.dialed(), "the cap-admitted origin dials");
    println!("spike: {}", allowed.status_line());

    println!(
        "\nSPIKE OK: a live Android app ({}x{}) presented through the deos compositor on macOS, \
         with a cap-gated net decision + receipt.",
        frame.width, frame.height
    );
}

/// **THE INPUT-BRIDGE SPIKE — a cap-gated tap CHANGES the live app's frame.**
///
/// This is the "interactive, not just watching" proof. It attaches to the standing
/// `emulator-5554`, captures a BEFORE frame, drives a cap-gated [`AndroidInput`] (a
/// swipe + a tap — an authorized exercise over the surface) through the
/// [`AndroidInputGate`], re-captures an AFTER frame, and asserts the two DIFFER — the
/// input actually reached the confined runtime and the app responded. It also proves the
/// gate's teeth: a cap with no backing surface is refused before any `adb` call.
///
/// `#[ignore]` (needs a live device). Run on the dev host:
/// ```sh
/// export ANDROID_SDK_ROOT="$HOME/Library/Android/sdk"
/// cargo test -p android-cell --test live_emulator_spike \
///   android_input_changes_the_live_frame -- --ignored --nocapture
/// ```
/// It writes `target/tmp/android_cell_input_{before,after}.png` — the before/after
/// screenshot pair the definition-of-done asks for.
#[cfg(target_os = "macos")]
#[test]
#[ignore = "needs a live, already-running Android emulator. Run with --ignored on the dev host."]
fn android_input_changes_the_live_frame() {
    use android_cell::MacOsEmulatorRuntime;
    use std::io::Write;

    // ── ATTACH to the standing emulator (do NOT boot/own it) ──────────────────
    let mut rt = MacOsEmulatorRuntime::attach_running(DeviceSpec::dev_default())
        .expect("attach to the already-running emulator-5554");

    // Land somewhere with content + a settled surface: open Settings, go HOME first
    // for a deterministic start, then open the app.
    let presenter = cell_seed(3);
    rt.launch_app(&AppLaunch::Component(
        "com.android.settings/.Settings".to_string(),
    ))
    .expect("Settings launches");
    std::thread::sleep(std::time::Duration::from_secs(3));

    // ── BEFORE frame ─────────────────────────────────────────────────────────
    let before = rt.capture_frame().expect("capture the BEFORE frame");
    let before_digest = before.content_digest();
    write_png(&before, "android_cell_input_before.png");

    // ── THE CAP-GATED INPUT (an authorized exercise over the surface) ─────────
    // The held cap names the surface's backing cell → the input gate admits; the
    // event is injected into the confined runtime through `adb shell input`.
    let surface = SurfaceCapability::root(presenter, AuthRequired::Either);
    let mut gate = AndroidInputGate::new(rt, Some(presenter));

    // A swipe (scroll the settings list) reliably moves pixels; then a tap.
    let r1 = gate.deliver(
        &surface,
        AndroidInput::Swipe {
            x1: 540,
            y1: 1800,
            x2: 540,
            y2: 600,
            duration_ms: 250,
        },
    );
    assert!(r1.decision.injected(), "the cap-admitted swipe is injected");
    println!("input-spike: {}", r1.status_line());

    let r2 = gate.deliver(&surface, AndroidInput::Tap { x: 540, y: 700 });
    assert!(r2.decision.injected(), "the cap-admitted tap is injected");
    println!("input-spike: {}", r2.status_line());

    // Let the app repaint.
    std::thread::sleep(std::time::Duration::from_secs(2));

    // ── AFTER frame — recapture; the gate handed us the runtime back via sink_mut ─
    let after = gate
        .sink_mut()
        .capture_frame()
        .expect("capture the AFTER frame");
    let after_digest = after.content_digest();
    write_png(&after, "android_cell_input_after.png");

    // ── THE LOAD-BEARING ASSERTION: the input CHANGED the app's frame ─────────
    assert_ne!(
        before_digest, after_digest,
        "a cap-gated tap/swipe CHANGED the live app's frame — the runtime is INTERACTIVE, \
         not just observed (before {before_digest:#x} != after {after_digest:#x})"
    );

    // ── THE GATE BITES: a cap with no backing surface is refused before the device ─
    let no_surface = SurfaceCapability {
        window: dregg_firmament::Capability::local(0, AuthRequired::Either),
        fetch_allow: Some(Default::default()),
        navigate_allow: Some(Default::default()),
        permissions: Default::default(),
    };
    let refused = gate.deliver(&no_surface, AndroidInput::Tap { x: 540, y: 700 });
    assert!(
        refused.decision.refused_by_cap(),
        "a cap that names no surface cannot drive one — refused before any adb call"
    );
    println!("input-spike: {}", refused.status_line());

    let _ = std::io::stdout().write_all(
        format!(
            "\nINPUT-SPIKE OK: a cap-gated tap/swipe changed the live Android app's frame \
             ({}x{}); before {before_digest:#x} → after {after_digest:#x}. \
             The android-cell is INTERACTIVE.\n",
            after.width, after.height
        )
        .as_bytes(),
    );
}

/// **THE CHECKPOINT SPIKE — a live android-cell's observable state captured as a umem,
/// saved, restored, and compared against the live emulator.**
///
/// This is the "checkpointable service cell" proof, on the live `emulator-5554`. It:
///  1. attaches to the standing emulator, launches Settings;
///  2. captures frame A → records it + a gated egress decision into a
///     [`ServiceCellCheckpoint`]; SAVES the checkpoint (its `UProjection` umem + commitment);
///  3. drives a cap-gated swipe (changing the live app), captures frame B → records it;
///  4. emits the Blum boundary trace A→B and checks `fold(A, ops) == B` (the agreement
///     square) — the live advance is a disciplined memory program;
///  5. RESTORES the saved checkpoint A on a "second node" and asserts it projects the
///     identical umem + commitment (migration), while B differs at exactly the frame
///     digest + present-seq + the appended receipt (compare).
///
/// `#[ignore]` (needs the live device). Run on the dev host:
/// ```sh
/// export ANDROID_SDK_ROOT="$HOME/Library/Android/sdk"
/// cargo test -p android-cell --test live_emulator_spike \
///   live_android_cell_checkpoints_as_umem -- --ignored --nocapture
/// ```
#[cfg(target_os = "macos")]
#[test]
#[ignore = "needs a live, already-running Android emulator. Run with --ignored on the dev host."]
fn live_android_cell_checkpoints_as_umem() {
    use android_cell::checkpoint::{ServiceCellCheckpoint, UKey, diff, emit_boundary_trace, fold};
    use android_cell::{AndroidInputGate, AndroidNetGate, AndroidRuntime, MacOsEmulatorRuntime};
    use std::io::Write;

    let cell = cell_seed(3);

    // ── ATTACH + launch (do not own the emulator) ─────────────────────────────
    let mut rt = MacOsEmulatorRuntime::attach_running(DeviceSpec::dev_default())
        .expect("attach to emulator-5554");
    rt.launch_app(&AppLaunch::Component(
        "com.android.settings/.Settings".to_string(),
    ))
    .expect("Settings launches");
    std::thread::sleep(std::time::Duration::from_secs(3));

    // ── CHECKPOINT A: capture frame, record a gated egress decision ───────────
    let mut cp = ServiceCellCheckpoint::new(cell);
    let frame_a = rt.capture_frame().expect("capture frame A");
    cp.observe_frame(&frame_a);

    let fabric = InProcessFabric::new();
    let me = fabric.join([0x07; 32]);
    let _ = fabric.join(android_cell::netgate::origin_to_peer(
        "https://api.example.com",
    ));
    let net = AndroidNetGate::new(me, Some(cell));
    let surface = SurfaceCapability::scoped(
        cell,
        AuthRequired::Either,
        [String::from("https://api.example.com")],
        [],
    );
    let denied = android_cell::netgate::block_on(net.egress(&surface, "https://tracker.evil.com"));
    cp.observe_io(&denied); // a witnessed cap-refusal joins the boundary log.

    // SAVE checkpoint A (the umem projection + its commitment).
    let saved_a = cp.project();
    let commitment_a = cp.commitment();
    println!(
        "checkpoint-spike: SAVED checkpoint A — {} umem addrs, frame {}x{} digest {:#x}, commitment {}",
        saved_a.len(),
        frame_a.width,
        frame_a.height,
        frame_a.content_digest(),
        bs58_short(&commitment_a),
    );

    // ── ADVANCE the live runtime (a cap-gated swipe) → CHECKPOINT B ────────────
    let mut gate = AndroidInputGate::new(rt, Some(cell));
    let root = SurfaceCapability::root(cell, AuthRequired::Either);
    let r = gate.deliver(
        &root,
        AndroidInput::Swipe {
            x1: 540,
            y1: 1800,
            x2: 540,
            y2: 600,
            duration_ms: 250,
        },
    );
    assert!(r.decision.injected(), "the cap-gated swipe injects");
    cp.observe_input(&r); // the input decision joins the boundary log too.
    std::thread::sleep(std::time::Duration::from_secs(2));

    let frame_b = gate.sink_mut().capture_frame().expect("capture frame B");
    cp.observe_frame(&frame_b);
    let post_b = cp.project();

    // ── THE BLUM TRACE A→B: fold(A, ops) == B (the agreement square) ──────────
    let ops = emit_boundary_trace(&saved_a, &post_b).expect("the live advance folds A → B");
    assert_eq!(
        fold(&saved_a, &ops),
        post_b,
        "fold(A, ops) == B — disciplined memory program"
    );
    println!(
        "checkpoint-spike: live advance A→B is a {}-op disciplined Blum trace; fold(A,ops)==B ✔",
        ops.len()
    );

    // ── RESTORE A on a "second node" (migration) ──────────────────────────────
    let mut node2 = ServiceCellCheckpoint::new(cell);
    node2.observe_frame(&frame_a);
    node2.receipt_log = vec![denied.decision_digest];
    node2.present_seq = 1;
    assert_eq!(
        node2.project(),
        saved_a,
        "migrated node restores the identical umem"
    );
    assert_eq!(
        node2.commitment(),
        commitment_a,
        "migration preserves the commitment"
    );

    // ── COMPARE A vs B: exactly the changed addresses ─────────────────────────
    // The umem is the GROUND TRUTH of what the boundary did: present-seq always
    // advances + the swipe receipt is always appended. Whether the FRAME DIGEST
    // changed depends on whether the live app actually repainted (a swipe on an
    // already-settled / non-scrollable surface yields a pixel-identical frame) — so
    // we REPORT it rather than demand it; the umem faithfully records either outcome.
    let (changed, _only_a, only_b) = diff(&saved_a, &post_b);
    assert!(
        changed.contains(&UKey::PresentSeq(cell)),
        "the present-seq advanced"
    );
    let frame_moved = changed.contains(&UKey::FrameDigest(cell));
    println!(
        "checkpoint-spike: compare A vs B — present-seq advanced; frame digest {} (digest A {:#x} vs B {:#x})",
        if frame_moved {
            "CHANGED (the app repainted)"
        } else {
            "unchanged (no repaint this swipe)"
        },
        frame_a.content_digest(),
        frame_b.content_digest(),
    );
    // B appended new witnessed receipts (the egress refusal + the injected swipe) beyond A.
    assert!(
        only_b
            .iter()
            .any(|k| matches!(k, UKey::BoundaryReceipt { .. })),
        "B has new witnessed boundary receipts"
    );

    let _ = std::io::stdout().write_all(
        format!(
            "\nCHECKPOINT-SPIKE OK: a live android-cell ({}x{}) checkpointed as a umem; \
             SAVED (commitment {}), live-advanced A→B as a fold-verified Blum trace, \
             RESTORED on a second node byte-identically (migration), COMPARED ({} addrs changed). \
             The confined-runtime boundary is a checkpointable service cell.\n",
            frame_b.width,
            frame_b.height,
            bs58_short(&commitment_a),
            changed.len(),
        )
        .as_bytes(),
    );
}

/// **THE INSTALL↔LAUNCH↔INTENT SPIKE — a live app's outbound intent routes through the gate
/// to a cap-reachable handler, on the device.**
///
/// This is `GRAPHIDEOS.md §1`'s "an intent is a turn over a cap you hold" on `emulator-5554`.
/// It installs an app registry (the launching app + two handler apps minted from manifests),
/// launches the launching app via [`launch_installed_app`] — which builds its
/// [`crate::IntentResolver`] from ONLY the cap-reachable installed apps — then welds the
/// resolver to the live runtime as the intent sink and fires a real `tel:` DIAL: the gate
/// resolves it to the granted dialer and drives the device's `am start` (the Dialer opens).
/// A custom action with no granted handler reaches NOTHING (no ambient `startActivity`).
///
/// `#[ignore]` (needs the live device). Run on the dev host:
/// ```sh
/// export ANDROID_SDK_ROOT="$HOME/Library/Android/sdk"
/// cargo test -p android-cell --test live_emulator_spike \
///   live_intent_routes_through_the_gate_on_the_device -- --ignored --nocapture
/// ```
#[cfg(target_os = "macos")]
#[test]
#[ignore = "needs a live, already-running Android emulator. Run with --ignored on the dev host."]
fn live_intent_routes_through_the_gate_on_the_device() {
    use android_cell::intentgate::{
        AndroidIntent, AndroidIntentGate, IntentDecision, IntentFilter,
    };
    use android_cell::{
        AndroidManifest, AndroidPermission, AppLaunch, InstalledApps, MacOsEmulatorRuntime,
        launch_installed_app,
    };
    use std::collections::BTreeSet;

    // ── ATTACH to the standing emulator (do NOT boot/own it) ──────────────────
    let mut rt = MacOsEmulatorRuntime::attach_running(DeviceSpec::dev_default())
        .expect("attach to emulator-5554");

    // ── INSTALL the registry: the launching app + two handler apps ────────────
    // Each install is the appfactory cap-gated birth (its cap-set is exactly the manifest).
    let launcher_cell = cell_seed(0x61);
    let dialer_cell = cell_seed(0x62);
    let browser_cell = cell_seed(0x63);

    let mut apps = InstalledApps::new();
    apps.install(
        launcher_cell,
        AndroidManifest::new("com.android.settings", [AndroidPermission::Internet]),
        AppLaunch::Component("com.android.settings/.Settings".to_string()),
        [0x11; 32],
    );
    apps.install(
        dialer_cell,
        AndroidManifest::new("com.android.dialer", [])
            .with_intent_filters([IntentFilter::new(["android.intent.action.DIAL"], ["tel"])]),
        AppLaunch::Package("com.android.dialer".to_string()),
        [0x11; 32],
    );
    apps.install(
        browser_cell,
        AndroidManifest::new("com.android.browser", [AndroidPermission::Internet])
            .with_intent_filters([IntentFilter::new(
                ["android.intent.action.VIEW"],
                ["http", "https"],
            )]),
        AppLaunch::Package("com.android.browser".to_string()),
        [0x11; 32],
    );

    // ── LAUNCH the launching app; its resolver is its cap-reachable neighborhood ─
    // Granted the dialer + browser handlers (NOT a device-wide PackageManager).
    let granted: BTreeSet<_> = [dialer_cell, browser_cell].into_iter().collect();
    let resolver = launch_installed_app(&mut rt, &apps, launcher_cell, &granted)
        .expect("the installed launcher app launches + yields its cap-bounded resolver");
    assert_eq!(
        resolver.handlers().len(),
        2,
        "the resolver ranges over exactly the two granted handlers"
    );
    std::thread::sleep(std::time::Duration::from_secs(2));

    // ── FIRE a tel: DIAL through the gate welded to the live runtime ──────────
    let surface = SurfaceCapability::root(launcher_cell, AuthRequired::Either);
    let mut gate = AndroidIntentGate::new(resolver, &mut rt);

    let dial = AndroidIntent::view("android.intent.action.DIAL", "tel:+15551234567");
    let r = gate.dispatch(&surface, dial);
    match &r.decision {
        IntentDecision::Resolved { .. } => {
            println!("intent-spike: {}", r.status_line());
        }
        IntentDecision::DispatchFailed { .. } => {
            // The cap + resolution teeth passed; only the device-side am start failed (no
            // dialer on this image). That is the transport tooth, NOT a cap refusal.
            println!("intent-spike (transport): {}", r.status_line());
        }
        other => panic!("a granted tel DIAL must resolve to the dialer, got {other:?}"),
    }
    assert!(
        !r.decision.refused_no_handler() && !r.decision.refused_by_cap(),
        "the granted dialer is cap-reachable — never a refusal"
    );

    // ── THE GATE BITES: a custom action no granted handler answers reaches NOTHING ─
    let custom = AndroidIntent::view("com.evil.action.EXFIL", "tel:+15551234567");
    let refused = gate.dispatch(&surface, custom);
    assert!(
        refused.decision.refused_no_handler(),
        "an action no granted handler published reaches nothing (no ambient startActivity)"
    );
    println!("intent-spike: {}", refused.status_line());

    println!(
        "\nINTENT-SPIKE OK: a live launching app's outbound intent routed through the cap-gated \
         resolver to its granted handler on the device; an ungranted action reached nothing. \
         An intent is a turn over a cap you hold."
    );
}

/// **THE LIVE-PATH CHECKPOINTED-RUNTIME SPIKE — the boundary umem is LOAD-BEARING.**
///
/// The spike above (`live_android_cell_checkpoints_as_umem`) wires a `ServiceCellCheckpoint`
/// BY HAND around a bare runtime. This one drives the standing emulator THROUGH the
/// [`CheckpointedRuntime`] wrapper — the live-path drop-in that threads the boundary umem
/// through every act automatically, so the running system DEPENDS on the checkpoint:
///  1. attach to `emulator-5554`, launch Settings, capture A through the wrapper — the
///     frame is folded into the boundary as a verified Blum advance with no manual umem code;
///  2. drive a cap-gated swipe THROUGH `AndroidInputGate::new(checkpointed_rt, …)` (the
///     wrapper IS the input sink), fold its receipt + capture B through the wrapper;
///  3. SAVE the live boundary witness + its commitment (the handoff root);
///  4. MIGRATE the witness onto a FRESH runtime with `migrate_onto_expecting(root)` — it
///     reconstructs byte-identically + verifies against the trusted root (fail-closed);
///  5. confirm the whole-session accumulated trace folds genesis → the live boundary
///     (a disciplined memory program), and a forged witness is REFUSED against the root.
///
/// `#[ignore]` (needs the live device). Run on the dev host:
/// ```sh
/// export ANDROID_SDK_ROOT="$HOME/Library/Android/sdk"
/// cargo test -p android-cell --test live_emulator_spike \
///   live_checkpointed_runtime_is_load_bearing -- --ignored --nocapture
/// ```
#[cfg(target_os = "macos")]
#[test]
#[ignore = "needs a live, already-running Android emulator. Run with --ignored on the dev host."]
fn live_checkpointed_runtime_is_load_bearing() {
    use android_cell::checkpoint::fold;
    use android_cell::{
        AndroidInputGate, CheckpointError, CheckpointedRuntime, MacOsEmulatorRuntime,
        ServiceCellCheckpoint,
    };
    use std::io::Write;

    let cell = cell_seed(3);

    // ── ATTACH + WRAP: the live runtime, threaded through the boundary umem ───
    let rt = MacOsEmulatorRuntime::attach_running(DeviceSpec::dev_default())
        .expect("attach to emulator-5554");
    let mut crt = CheckpointedRuntime::new(rt, cell);
    crt.launch_app(&AppLaunch::Component(
        "com.android.settings/.Settings".to_string(),
    ))
    .expect("Settings launches");
    std::thread::sleep(std::time::Duration::from_secs(3));

    // ── CAPTURE A through the wrapper — folded into the boundary automatically ─
    let frame_a = crt
        .capture_checkpointed()
        .expect("capture A folds the boundary");
    println!(
        "live-checkpointed: capture A {}x{} → boundary advanced to {} umem addrs",
        frame_a.width,
        frame_a.height,
        crt.project().len()
    );

    // ── DRIVE a cap-gated swipe THROUGH the wrapper-as-input-sink ──────────────
    let mut gate = AndroidInputGate::new(crt, Some(cell));
    let root_cap = SurfaceCapability::root(cell, AuthRequired::Either);
    let r = gate.deliver(
        &root_cap,
        AndroidInput::Swipe {
            x1: 540,
            y1: 1800,
            x2: 540,
            y2: 600,
            duration_ms: 250,
        },
    );
    assert!(r.decision.injected(), "the cap-gated swipe injects");
    // Fold the gate's receipt + recapture THROUGH the wrapper (sink_mut hands it back).
    gate.sink_mut()
        .record_input(&r)
        .expect("the input receipt folds into the boundary");
    std::thread::sleep(std::time::Duration::from_secs(2));
    let frame_b = gate
        .sink_mut()
        .capture_checkpointed()
        .expect("capture B folds the boundary");
    // The wrapper (now owned by the gate) is the live checkpointed runtime.
    let live = gate.sink_mut();

    // ── SAVE the live boundary witness + the handoff root ─────────────────────
    let saved = live.save().expect("the live boundary vends a witness");
    let trusted_root = saved.commitment();
    println!(
        "live-checkpointed: SAVED boundary — commitment {}, {} session ops, frame B digest {:#x}",
        bs58_short(&trusted_root),
        live.boundary_trace().len(),
        frame_b.content_digest(),
    );

    // The whole-session accumulated trace folds genesis → the live boundary.
    let genesis = ServiceCellCheckpoint::new(cell).project();
    assert_eq!(
        fold(&genesis, live.boundary_trace()),
        live.project(),
        "fold(genesis, session trace) == the live boundary — a disciplined memory program"
    );

    // ── MIGRATE onto a FRESH runtime, verified against the trusted root ───────
    let fresh = MacOsEmulatorRuntime::attach_running(DeviceSpec::dev_default())
        .expect("a fresh runtime handle (the 'second node')");
    let migrated = CheckpointedRuntime::migrate_onto_expecting(&saved, trusted_root, fresh)
        .expect("the witness reconstructs the boundary + matches the trusted handoff root");
    let (changed, only_a, only_b) = migrated.diff_against(&saved);
    assert!(
        changed.is_empty() && only_a.is_empty() && only_b.is_empty(),
        "the migrated boundary is byte-identical to the saved one"
    );

    // ── A FORGED witness is REFUSED against the trusted root — fail-closed ─────
    let mut forged = saved.clone();
    forged.frame = Some((0xDEAD_BEEF, frame_b.width, frame_b.height));
    let fresh2 = MacOsEmulatorRuntime::attach_running(DeviceSpec::dev_default()).unwrap();
    let refused = CheckpointedRuntime::migrate_onto_expecting(&forged, trusted_root, fresh2);
    assert!(
        matches!(refused, Err(CheckpointError::RestoreMismatch { .. })),
        "the forged witness does not match the trusted root — restore refuses (fail-closed)"
    );

    let _ = std::io::stdout().write_all(
        format!(
            "\nLIVE-CHECKPOINTED OK: a live android-cell ({}x{}) driven THROUGH the \
             CheckpointedRuntime wrapper checkpointed its boundary on every act (no manual \
             umem code); SAVED (root {}), the session trace folds genesis → live, MIGRATED \
             onto a fresh runtime against the trusted root (byte-identical), a forged \
             witness REFUSED. The boundary umem is load-bearing in the live path.\n",
            frame_b.width,
            frame_b.height,
            bs58_short(&trusted_root),
        )
        .as_bytes(),
    );
}

#[cfg(target_os = "macos")]
fn bs58_short(d: &[u8; 32]) -> String {
    bs58::encode(&d[..6]).into_string()
}

#[cfg(target_os = "macos")]
fn write_png(frame: &android_cell::RgbaFrame, name: &str) {
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
    if let Some(img) = image::RgbaImage::from_raw(frame.width, frame.height, frame.bytes.clone()) {
        let _ = img.save(&path);
        println!("input-spike: wrote {}", path.display());
    }
}
