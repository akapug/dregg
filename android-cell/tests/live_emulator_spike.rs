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

#[cfg(target_os = "macos")]
fn write_png(frame: &android_cell::RgbaFrame, name: &str) {
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
    if let Some(img) =
        image::RgbaImage::from_raw(frame.width, frame.height, frame.bytes.clone())
    {
        let _ = img.save(&path);
        println!("input-spike: wrote {}", path.display());
    }
}
