//! THE STARBRIDGE-V2 COCKPIT MODE — the REAL, LIVE starbridge-v2 cockpit,
//! rendered headless and blitted onto the seL4 framebuffer.
//!
//! `cockpit_frame.rgba` is an 800x600 RGBA8 image of the **live
//! `starbridge_v2::cockpit::Cockpit` element tree** over the fully-seeded demo
//! image (`world::demo_world` — every verified executor turn run): the CELL
//! WORLD rail with the real sovereign cells (ids, balances, cap counts, the
//! issuer well at −supply), the INSPECTOR reflecting the image (cells / height /
//! receipts / state_root / "executor embedded verified (TurnExecutor)"), the
//! BLOCKLACE provenance (the real receipt chain), and the HOME/SHELL/AGENT
//! workspace — all the actual cockpit, not a facsimile.
//!
//! It is produced by `starbridge-v2 --render-cockpit` (src/main.rs,
//! `render_cockpit_headless`): a headless gpui `App`/`Window`
//! (`gpui::HeadlessAppContext` over `TestPlatform`) drives the real `Cockpit`,
//! and its resolved gpui `Scene` is rendered offscreen by the ACTUAL gpui wgpu
//! renderer (`gpui_wgpu::WgpuHeadlessRenderer` / `render_scene_to_image`, the
//! offscreen patch — docs/desktop-os-research/GPUI-OFFSCREEN-FORK.md) on software
//! Vulkan (lavapipe/llvmpipe — NO GPU, NO window) on persvati. gpui reports a 2x
//! scale, so the 800x600-logical cockpit renders at 1600x1200 device px and is
//! Lanczos-downscaled to the framebuffer's 800x600. Same renderer leaf the
//! windowed cockpit uses (`gpui -> gpui_platform -> gpui_linux -> gpui_wgpu`).
//!
//! It is baked in EXACTLY as `image_data.rs` bakes real cells: a `#![no_std]`
//! PD cannot link wgpu/lavapipe, so the heavy render happens at build time on
//! persvati and the resulting RGBA is embedded. This module converts that RGBA
//! to the framebuffer's XRGB8888 at blit time and writes it straight into the
//! mapped framebuffer the QEMU ramfb engine scans out.
//!
//! Regenerate (the bytes, from persvati where lavapipe lives):
//!   ssh persvati '... cd starbridge-v2 && \
//!     ZED_OFFSCREEN_PREFER_CPU=1 VK_ICD_FILENAMES=…/lvp_icd.json \
//!     cargo run --release --features headless-render -- --render-cockpit OUT'
//!   scp persvati:OUT.rgba sel4/dregg-pd/deos-image/src/cockpit_frame.rgba

use crate::fb::{Canvas, HEIGHT, WIDTH};

/// The baked cockpit frame: 800x600 RGBA8, row-major, top row first, no padding
/// (w*h*4 = 1_920_000 bytes). Rendered by gpui on lavapipe — see the module doc.
pub static COCKPIT_RGBA: &[u8] = include_bytes!("cockpit_frame.rgba");

/// The render geometry — must equal the framebuffer geometry so the blit is a
/// straight copy. (The persvati harness renders at exactly `fb::{WIDTH,HEIGHT}`.)
pub const COCKPIT_W: u32 = 800;
pub const COCKPIT_H: u32 = 600;

const _: () = assert!(COCKPIT_W == WIDTH && COCKPIT_H == HEIGHT);

/// Blit the baked gpui cockpit frame into the framebuffer the QEMU ramfb engine
/// scans out, converting RGBA8 -> XRGB8888 (`0x00RRGGBB`) per pixel. A real
/// gpui render, on glass, on seL4.
pub fn blit(c: &mut Canvas) {
    // Defensive: if the baked frame is the wrong length (a regenerate mismatch),
    // paint a solid backdrop so the mode is still visibly distinct rather than
    // reading garbage. (The const assert above already guards geometry; this
    // guards the byte length of the embedded asset.)
    let want = (COCKPIT_W * COCKPIT_H * 4) as usize;
    if COCKPIT_RGBA.len() != want {
        c.rect(0, 0, WIDTH, HEIGHT, crate::fb::rgb(11, 15, 26));
        let _ = c.text(
            "cockpit_frame.rgba length mismatch -- regenerate from persvati",
            24,
            24,
            1,
            1,
            crate::fb::rgb(232, 96, 96),
        );
        return;
    }

    for y in 0..HEIGHT {
        for x in 0..WIDTH {
            let i = ((y * WIDTH + x) * 4) as usize;
            let r = COCKPIT_RGBA[i];
            let g = COCKPIT_RGBA[i + 1];
            let b = COCKPIT_RGBA[i + 2];
            // alpha (byte i+3) ignored: the framebuffer is XRGB (opaque); the
            // cockpit backdrop is itself opaque so this is exact.
            c.put(x, y, crate::fb::rgb(r, g, b));
        }
    }

    // A thin footer hint so the mode is self-describing (TAB returns to the live
    // image). Drawn OVER the blitted frame's status-bar band.
    let by = HEIGHT - 22;
    let _ = c.text("TAB", 24, by, 1, 1, crate::fb::rgb(64, 224, 208));
    let _ = c.text(
        " back to the live image  ·  REAL gpui render (lavapipe, no GPU) on the seL4 framebuffer",
        24 + Canvas::text_w("TAB", 1, 1),
        by,
        1,
        1,
        crate::fb::rgb(150, 178, 188),
    );
}
