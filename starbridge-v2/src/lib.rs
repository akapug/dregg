//! Starbridge v2 — the native dregg master interface (library core).
//!
//! The headless, gpui-free heart lives here so it is `cargo test`-able and
//! reusable by both builds:
//!   * [`world`] — the embedded verified executor + live local dregg world.
//!   * [`dynamics`] — the observation/event stream of state transitions.
//!   * [`reflect`] — the uniform reflective object model the views consume.
//!   * [`surface`] / [`shell`] / [`compositor`] — the cap-first multi-SURFACE
//!     desktop shell: each dregg cell can be a cap-confined surface
//!     (apps-as-cells), the shell is a cap-first window manager over the live
//!     world, and the [`compositor`] enforces the VERIFIED-SCENE discipline
//!     (T1 non-overlap · T2 label-binding · T3 focus-exclusivity — the Lean
//!     `Dregg2.Apps.Compositor` teeth) at the pixel layer.
//!   * [`agent`] — the AGENT-ACTIVITY surface (the ADOS keystone): an agent
//!     loop's provable activity (held mandate · cap-gated turns · receipts ·
//!     authorization), rendered as a cap-gated surface cell.
//!
//! The `native-full` binary (`src/main.rs`) wires these into the gpui cockpit.
//! The wire-contract client (`client`/`model`) lives in the binary crate for
//! the remote-node + `sel4-thin` paths.

#[cfg(feature = "embedded-executor")]
pub mod agent;
#[cfg(feature = "embedded-executor")]
pub mod buffer;
#[cfg(feature = "embedded-executor")]
pub mod cipherclerk;
#[cfg(feature = "embedded-executor")]
pub mod compositor;
#[cfg(feature = "embedded-executor")]
pub mod debug;
#[cfg(feature = "embedded-executor")]
pub mod dynamics;
#[cfg(feature = "embedded-executor")]
pub mod edit;
#[cfg(feature = "embedded-executor")]
pub mod palette;
#[cfg(feature = "embedded-executor")]
pub mod reflect;
#[cfg(feature = "embedded-executor")]
pub mod replay;
#[cfg(feature = "embedded-executor")]
pub mod shell;
#[cfg(feature = "embedded-executor")]
pub mod surface;
#[cfg(feature = "embedded-executor")]
pub mod terminal;
#[cfg(feature = "embedded-executor")]
pub mod world;

#[cfg(feature = "embedded-executor")]
pub use agent::{AgentActivity, AgentSurface};
#[cfg(feature = "embedded-executor")]
pub use buffer::{BufferCell, BufferDoc, BufferError, BufferView};
#[cfg(feature = "embedded-executor")]
pub use compositor::{
    label_of, CompositedSurface, Compositor, CompositorScene, FrameCommit, Present, PresentError,
    RegionId,
};
#[cfg(feature = "embedded-executor")]
pub use terminal::{Command, CommandError, OutputLine, TerminalCell, TerminalView};
#[cfg(feature = "embedded-executor")]
pub use shell::{Layout, Scene, SceneItem, Shell, ShellError};
#[cfg(feature = "embedded-executor")]
pub use surface::{Rect, Surface, SurfaceCapability, SurfaceId, SurfaceKind};
#[cfg(feature = "embedded-executor")]
pub use world::{CommitOutcome, World};
