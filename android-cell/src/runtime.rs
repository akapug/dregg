//! **The simulator host (host-adaptive runtime).** An [`AndroidRuntime`] boots a
//! device, runs an app, and exposes its surface as an [`RgbaFrame`] — one impl per
//! host.
//!
//! | host | impl | how it confines |
//! |---|---|---|
//! | **macOS** (dev host) | [`MacOsEmulatorRuntime`] | the **Android Emulator** — a full guest kernel under **Hypervisor.framework**. No Linux `binder`/`ashmem` needed; the VM boundary is the confinement boundary. |
//! | **Linux** (deos node) | redroid (the original doc's container path) | `binder_linux`/`ashmem_linux` + netns/iptables-by-UID. *(Not shipped here; the trait is the seam it slots into.)* |
//! | **any** (CI / no SDK) | [`CapturedFrameRuntime`] | a saved screencap/PNG — no device; the seam compiles + tests everywhere. |
//!
//! The crucial correction over `ANDROID-CELL.md`'s original verdict: macOS is NOT a
//! wall. That verdict was about *containers* (redroid/Waydroid need Linux kernel
//! modules); an *emulator* runs its own guest kernel, so it is a real confining
//! Android runtime on the macOS dev host. The simulator host is the route across.

use crate::frame::{ScreencapError, screencap_to_rgba};
use servo_render::RgbaFrame;

/// Which host backs a runtime — for diagnostics + the cockpit's "what am I talking
/// to" line.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimeKind {
    /// macOS Android Emulator (Hypervisor.framework).
    MacOsEmulator,
    /// Linux redroid container (host kernel + binder/ashmem). Named for completeness;
    /// the impl lives on the Linux node.
    LinuxRedroid,
    /// A captured frame stand-in (no live device).
    CapturedFrame,
}

/// The device a runtime should boot — the AVD/image name + the SDK location. Kept
/// minimal: one AVD, one app is the clean isolation unit (one cap = one device/app),
/// exactly as the doc's §5 "one-app-one-cell" prescribes.
#[derive(Clone, Debug)]
pub struct DeviceSpec {
    /// The AVD name (e.g. `Pixel_7_API_35`) the emulator boots.
    pub avd_name: String,
    /// The Android SDK root (e.g. `~/Library/Android/sdk`). If `None`, the impl reads
    /// `ANDROID_SDK_ROOT` / `ANDROID_HOME` / the default `~/Library/Android/sdk`.
    pub sdk_root: Option<std::path::PathBuf>,
    /// Boot headless (no emulator window) — the cell-surface case (deos owns the
    /// glass, the emulator must not open its own window).
    pub headless: bool,
}

impl DeviceSpec {
    /// The dev-host default: the `Pixel_7_API_35` AVD, headless, SDK auto-detected.
    /// This is the AVD this crate was developed against (verified booting on the macOS
    /// dev host via Hypervisor.framework).
    pub fn dev_default() -> Self {
        DeviceSpec {
            avd_name: "Pixel_7_API_35".to_string(),
            sdk_root: None,
            headless: true,
        }
    }
}

/// An app to launch on the booted device: a component (`package/.Activity`) or a
/// package whose launcher activity the runtime resolves.
#[derive(Clone, Debug)]
pub enum AppLaunch {
    /// A fully-qualified component, e.g. `com.android.settings/.Settings`.
    Component(String),
    /// A package name whose default launcher activity is started (via `monkey` /
    /// `cmd package resolve-activity`).
    Package(String),
}

/// Why a runtime operation failed.
#[derive(Debug)]
pub enum RuntimeError {
    /// A required tool (`emulator`, `adb`) was not found under the SDK root.
    ToolMissing { tool: String, looked_in: String },
    /// The device did not reach `sys.boot_completed=1` within the deadline.
    BootTimeout { avd: String, secs: u64 },
    /// An invoked SDK command exited non-zero.
    CommandFailed {
        cmd: String,
        code: Option<i32>,
        stderr: String,
    },
    /// The capture could not be parsed into an `RgbaFrame`.
    Capture(ScreencapError),
    /// An I/O error invoking a tool.
    Io(std::io::Error),
}

impl std::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeError::ToolMissing { tool, looked_in } => {
                write!(
                    f,
                    "android SDK tool `{tool}` not found (looked in {looked_in})"
                )
            }
            RuntimeError::BootTimeout { avd, secs } => {
                write!(f, "AVD `{avd}` did not finish booting within {secs}s")
            }
            RuntimeError::CommandFailed { cmd, code, stderr } => {
                write!(f, "`{cmd}` failed (code {code:?}): {stderr}")
            }
            RuntimeError::Capture(e) => write!(f, "frame capture: {e}"),
            RuntimeError::Io(e) => write!(f, "io: {e}"),
        }
    }
}

impl std::error::Error for RuntimeError {}

impl From<ScreencapError> for RuntimeError {
    fn from(e: ScreencapError) -> Self {
        RuntimeError::Capture(e)
    }
}
impl From<std::io::Error> for RuntimeError {
    fn from(e: std::io::Error) -> Self {
        RuntimeError::Io(e)
    }
}

/// **THE HOST-ADAPTIVE RUNTIME SEAM.** Boot a confined Android device, run ONE app,
/// and capture its surface as the EXACT [`RgbaFrame`] the compositor takes. One impl
/// per host ([`MacOsEmulatorRuntime`], a future Linux-redroid impl, the
/// [`CapturedFrameRuntime`] stand-in) — the rest of the android-cell (the present
/// seam, the net gate) is host-agnostic above this trait.
pub trait AndroidRuntime {
    /// Which host backs this runtime.
    fn kind(&self) -> RuntimeKind;

    /// Boot the device to `sys.boot_completed=1`. Idempotent: a runtime already booted
    /// returns `Ok` immediately.
    fn boot(&mut self) -> Result<(), RuntimeError>;

    /// Launch ONE app on the booted device (the cell's "program").
    fn launch_app(&mut self, app: &AppLaunch) -> Result<(), RuntimeError>;

    /// Capture the current surface as an [`RgbaFrame`] — the SAME tile type the SWGL
    /// path produces, ready for [`crate::present_android_frame`].
    fn capture_frame(&mut self) -> Result<RgbaFrame, RuntimeError>;
}

/// **The host-independent stand-in.** A runtime that has no live device: it yields a
/// pre-captured frame (a `screencap` raw blob — e.g. the committed real-home fixture,
/// or a frame captured earlier on a host that had the emulator). It lets the WHOLE
/// android-cell seam — present + net-gate — compile and test on any node (CI, a Linux
/// box without the SDK, a macOS box before the AVD is set up), exactly the "iterate on
/// macOS against a stand-in" pattern the seL4 work uses.
pub struct CapturedFrameRuntime {
    screencap_raw: Vec<u8>,
    booted: bool,
}

impl CapturedFrameRuntime {
    /// A stand-in over a raw `adb screencap` blob (16-byte header + RGBA8).
    pub fn from_screencap_raw(raw: impl Into<Vec<u8>>) -> Self {
        CapturedFrameRuntime {
            screencap_raw: raw.into(),
            booted: false,
        }
    }
}

impl AndroidRuntime for CapturedFrameRuntime {
    fn kind(&self) -> RuntimeKind {
        RuntimeKind::CapturedFrame
    }
    fn boot(&mut self) -> Result<(), RuntimeError> {
        self.booted = true;
        Ok(())
    }
    fn launch_app(&mut self, _app: &AppLaunch) -> Result<(), RuntimeError> {
        Ok(())
    }
    fn capture_frame(&mut self) -> Result<RgbaFrame, RuntimeError> {
        Ok(screencap_to_rgba(&self.screencap_raw)?)
    }
}

#[cfg(target_os = "macos")]
pub use macos::MacOsEmulatorRuntime;

#[cfg(target_os = "macos")]
mod macos {
    use super::*;
    use std::path::PathBuf;
    use std::process::Command;

    /// **THE macOS SIMULATOR HOST.** Drives Google's Android Emulator (runs via
    /// Hypervisor.framework) through the SDK CLIs (`emulator`, `adb`) — boots an AVD
    /// headless, launches one app, and captures via `adb exec-out screencap` into the
    /// exact [`RgbaFrame`] the compositor takes.
    ///
    /// This is the impl the doc's §3 "Android Emulator (AVD)" row names as the macOS
    /// path; it needs NO Linux kernel modules because the emulator is a full VM under
    /// Hypervisor.framework. The capture path is `screencap` (the de-risking core,
    /// analogue of SWGL); the emulator gRPC / scrcpy-H.264 streams decode to the same
    /// `RgbaFrame` and are the later, lower-latency variants.
    pub struct MacOsEmulatorRuntime {
        spec: DeviceSpec,
        sdk_root: PathBuf,
        /// The running emulator child (killed on drop), once booted.
        child: Option<std::process::Child>,
        booted: bool,
    }

    impl MacOsEmulatorRuntime {
        /// Build a runtime for `spec`, resolving the SDK root from the spec, then
        /// `ANDROID_SDK_ROOT`, `ANDROID_HOME`, then `~/Library/Android/sdk`.
        pub fn new(spec: DeviceSpec) -> Self {
            let sdk_root = spec
                .sdk_root
                .clone()
                .or_else(|| std::env::var_os("ANDROID_SDK_ROOT").map(PathBuf::from))
                .or_else(|| std::env::var_os("ANDROID_HOME").map(PathBuf::from))
                .unwrap_or_else(|| {
                    let home = std::env::var_os("HOME")
                        .map(PathBuf::from)
                        .unwrap_or_default();
                    home.join("Library/Android/sdk")
                });
            MacOsEmulatorRuntime {
                spec,
                sdk_root,
                child: None,
                booted: false,
            }
        }

        /// **Attach to an ALREADY-RUNNING emulator** (e.g. one a developer or the
        /// cockpit already booted) instead of spawning a fresh one. Marks the runtime
        /// booted without owning the emulator child, so `Drop` will NOT tear it down.
        /// The natural constructor for the desktop mount + the live tap test, which
        /// drive the standing `emulator-5554`.
        pub fn attach_running(spec: DeviceSpec) -> Result<Self, RuntimeError> {
            let mut rt = Self::new(spec);
            // Validate the toolchain + that a device is actually reachable.
            let _ = rt.adb()?;
            let v = rt.adb_shell(&["getprop", "sys.boot_completed"])?;
            if v.trim() != "1" {
                return Err(RuntimeError::BootTimeout {
                    avd: rt.spec.avd_name.clone(),
                    secs: 0,
                });
            }
            rt.booted = true; // attached, not owned: child stays None → no teardown on Drop.
            Ok(rt)
        }

        fn tool(&self, rel: &str, bin: &str) -> Result<PathBuf, RuntimeError> {
            let p = self.sdk_root.join(rel).join(bin);
            if p.exists() {
                Ok(p)
            } else {
                Err(RuntimeError::ToolMissing {
                    tool: bin.to_string(),
                    looked_in: p.display().to_string(),
                })
            }
        }

        fn adb(&self) -> Result<PathBuf, RuntimeError> {
            self.tool("platform-tools", "adb")
        }

        fn emulator(&self) -> Result<PathBuf, RuntimeError> {
            self.tool("emulator", "emulator")
        }

        /// `adb -e <args>` capturing stdout bytes; non-zero exit is a `CommandFailed`.
        fn adb_out(&self, args: &[&str]) -> Result<Vec<u8>, RuntimeError> {
            let adb = self.adb()?;
            let mut full = vec!["-e"];
            full.extend_from_slice(args);
            let out = Command::new(&adb).args(&full).output()?;
            if !out.status.success() {
                return Err(RuntimeError::CommandFailed {
                    cmd: format!("adb -e {}", args.join(" ")),
                    code: out.status.code(),
                    stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
                });
            }
            Ok(out.stdout)
        }

        fn adb_shell(&self, shell_args: &[&str]) -> Result<String, RuntimeError> {
            let mut a = vec!["shell"];
            a.extend_from_slice(shell_args);
            let out = self.adb_out(&a)?;
            Ok(String::from_utf8_lossy(&out).into_owned())
        }
    }

    impl AndroidRuntime for MacOsEmulatorRuntime {
        fn kind(&self) -> RuntimeKind {
            RuntimeKind::MacOsEmulator
        }

        fn boot(&mut self) -> Result<(), RuntimeError> {
            if self.booted {
                return Ok(());
            }
            let emulator = self.emulator()?;
            // Validate adb exists too, before the long boot.
            let _ = self.adb()?;

            // Spawn the emulator headless under Hypervisor.framework. Software GL
            // (swiftshader_indirect) is the screencap-friendly path (the analogue of
            // SWGL): the framebuffer is CPU-readable.
            let mut cmd = Command::new(&emulator);
            cmd.arg("-avd").arg(&self.spec.avd_name);
            if self.spec.headless {
                cmd.arg("-no-window");
            }
            cmd.args([
                "-no-audio",
                "-no-boot-anim",
                "-no-snapshot",
                "-gpu",
                "swiftshader_indirect",
                "-netdelay",
                "none",
                "-netspeed",
                "full",
            ]);
            cmd.stdout(std::process::Stdio::null());
            cmd.stderr(std::process::Stdio::null());
            let child = cmd.spawn()?;
            self.child = Some(child);

            // Poll sys.boot_completed up to the deadline.
            let deadline = std::time::Instant::now() + std::time::Duration::from_secs(180);
            loop {
                if std::time::Instant::now() > deadline {
                    return Err(RuntimeError::BootTimeout {
                        avd: self.spec.avd_name.clone(),
                        secs: 180,
                    });
                }
                // `adb shell getprop` errors until the device appears; tolerate that.
                if let Ok(v) = self.adb_shell(&["getprop", "sys.boot_completed"]) {
                    if v.trim() == "1" {
                        break;
                    }
                }
                std::thread::sleep(std::time::Duration::from_secs(2));
            }
            // Settle: home + dismiss keyguard so a real surface composites.
            let _ = self.adb_shell(&["input", "keyevent", "KEYCODE_WAKEUP"]);
            let _ = self.adb_shell(&["wm", "dismiss-keyguard"]);
            let _ = self.adb_shell(&["input", "keyevent", "KEYCODE_HOME"]);
            self.booted = true;
            Ok(())
        }

        fn launch_app(&mut self, app: &AppLaunch) -> Result<(), RuntimeError> {
            match app {
                AppLaunch::Component(c) => {
                    self.adb_shell(&["am", "start", "-n", c])?;
                }
                AppLaunch::Package(p) => {
                    self.adb_shell(&[
                        "monkey",
                        "-p",
                        p,
                        "-c",
                        "android.intent.category.LAUNCHER",
                        "1",
                    ])?;
                }
            }
            Ok(())
        }

        fn capture_frame(&mut self) -> Result<RgbaFrame, RuntimeError> {
            // `adb exec-out screencap` (no -p) → raw header + RGBA8.
            let raw = self.adb_out(&["exec-out", "screencap"])?;
            Ok(screencap_to_rgba(&raw)?)
        }
    }

    /// **THE macOS INPUT SINK.** The reverse of `capture_frame`: drive the confined
    /// runtime's input channel through `adb shell input` (tap/swipe/text/keyevent) — the
    /// same device-side injector `scrcpy`/the emulator console use. The cap check happens
    /// in [`crate::AndroidInputGate::deliver`] BEFORE this is reached; this is the
    /// transport leg, host-adaptive exactly like the capture leg.
    impl crate::input::AndroidInputSink for MacOsEmulatorRuntime {
        fn inject_input(
            &mut self,
            input: &crate::input::AndroidInput,
        ) -> Result<(), crate::input::InputError> {
            use crate::input::InputError;
            let adb = self.adb().map_err(|e| match e {
                RuntimeError::ToolMissing { tool, looked_in } => {
                    InputError::ToolMissing { tool, looked_in }
                }
                other => InputError::CommandFailed {
                    cmd: "adb".into(),
                    stderr: other.to_string(),
                },
            })?;
            let args = input.adb_args();
            let mut full: Vec<&str> = vec!["-e", "shell"];
            full.extend(args.iter().map(|s| s.as_str()));
            let out = Command::new(&adb).args(&full).output()?;
            if !out.status.success() {
                return Err(InputError::CommandFailed {
                    cmd: format!("adb -e shell {}", args.join(" ")),
                    stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
                });
            }
            Ok(())
        }
    }

    /// **THE macOS INTENT SINK.** The device-side `startActivity` leg: drive the confined
    /// runtime's activity manager (`am start`) for an intent the [`crate::AndroidIntentGate`]
    /// already resolved + cap-admitted. The cap + resolution teeth fire in the gate BEFORE
    /// this is reached — this is the transport, host-adaptive exactly like the capture +
    /// input legs (a Linux redroid impl would drive the container's `am`; the
    /// `RecordingIntentSink` records with no device). A `RefusedNoHandler` / `RefusedByCap`
    /// / `Ambiguous` intent never reaches this impl, so a cap-denied intent never hits the
    /// device's `am start` — the no-ambient-`startActivity` property at the transport.
    impl crate::intentgate::AndroidIntentSink for MacOsEmulatorRuntime {
        fn start_activity(
            &mut self,
            intent: &crate::intentgate::AndroidIntent,
            _handler: dregg_firmament::CellId,
        ) -> Result<(), crate::intentgate::IntentError> {
            use crate::intentgate::IntentError;
            let adb = self.adb().map_err(|e| match e {
                RuntimeError::ToolMissing { tool, looked_in } => {
                    IntentError::ToolMissing { tool, looked_in }
                }
                other => IntentError::CommandFailed {
                    cmd: "adb".into(),
                    stderr: other.to_string(),
                },
            })?;
            let args = intent.am_start_args();
            let mut full: Vec<&str> = vec!["-e", "shell"];
            full.extend(args.iter().map(|s| s.as_str()));
            let out = Command::new(&adb).args(&full).output()?;
            if !out.status.success() {
                return Err(IntentError::CommandFailed {
                    cmd: format!("adb -e shell {}", args.join(" ")),
                    stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
                });
            }
            Ok(())
        }
    }

    impl Drop for MacOsEmulatorRuntime {
        fn drop(&mut self) {
            // Tear down the emulator we spawned (best effort).
            if let Some(mut child) = self.child.take() {
                let _ = child.kill();
                let _ = child.wait();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The stand-in runtime drives the WHOLE seam with no device: boot, launch,
    /// capture → a real `RgbaFrame` from the committed home fixture.
    #[test]
    fn captured_frame_runtime_drives_the_seam_without_a_device() {
        let raw = include_bytes!("../fixtures/android_home_screencap.raw").to_vec();
        let mut rt = CapturedFrameRuntime::from_screencap_raw(raw);
        assert_eq!(rt.kind(), RuntimeKind::CapturedFrame);
        rt.boot().expect("stand-in boots");
        rt.launch_app(&AppLaunch::Component(
            "com.android.settings/.Settings".to_string(),
        ))
        .expect("stand-in launch is a no-op ok");
        let frame = rt.capture_frame().expect("stand-in captures the fixture");
        assert_eq!(frame.width, 90);
        assert_eq!(frame.height, 200);
        assert!(frame.bytes.iter().any(|&b| b != frame.bytes[0]));
    }

    #[test]
    fn dev_default_spec_is_the_pixel_avd() {
        let s = DeviceSpec::dev_default();
        assert_eq!(s.avd_name, "Pixel_7_API_35");
        assert!(s.headless);
    }
}
