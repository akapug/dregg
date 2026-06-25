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
    AndroidNetGate, AndroidPresentation, AndroidRuntime, AppLaunch, DeviceSpec, IoDecision,
    present_android_frame,
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
