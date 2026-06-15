//! THE STARBRIDGE-V2 COCKPIT MODE — a REAL gpui-rendered cockpit frame, blitted
//! onto the seL4 framebuffer.
//!
//! `cockpit_frame.rgba` is an 800x600 RGBA8 image rendered by the ACTUAL gpui
//! renderer (`gpui_wgpu::WgpuRenderer::render_scene_to_image`, the patched
//! offscreen path — docs/desktop-os-research/GPUI-OFFSCREEN-FORK.md) running on
//! software Vulkan (lavapipe/llvmpipe — NO GPU, NO window) on persvati. The
//! Scene is the starbridge-v2 cockpit shape: the title bar, the three master
//! columns (WORLD / SHELL / REFLECT — the cockpit's reflective axes), each
//! with an accent header and the four-substance surface tiles (VALUE / STATE /
//! AUTHORITY / EVIDENCE), and a status bar — laid out with crisp anti-aliased
//! glyphs by gpui's CosmicText system and rasterized through gpui's sprite
//! atlas. The exact same renderer leaf the real Cockpit element tree resolves
//! to (`gpui -> gpui_platform -> gpui_linux -> gpui_wgpu`).
//!
//! It is baked in EXACTLY as `image_data.rs` bakes real cells: a `#![no_std]`
//! PD cannot link wgpu/lavapipe, so the heavy render happens at build time on
//! persvati and the resulting RGBA is embedded. This module converts that RGBA
//! to the framebuffer's XRGB8888 at blit time and writes it straight into the
//! mapped framebuffer the QEMU ramfb engine scans out.
//!
//! Regenerate (the bytes, from persvati where lavapipe lives):
//!   ssh persvati 'cd ~/cockpit-render && cargo run --release'   # -> cockpit-800x600.rgba
//!   scp persvati:~/cockpit-render/cockpit-800x600.rgba \
//!       sel4/dregg-pd/deos-image/src/cockpit_frame.rgba
//!
//! The frontier beyond this hand-built-Scene bring-up: drive the REAL `Cockpit`
//! element tree through a headless gpui `App`/`Window` (its `shell::Scene` is a
//! window-manager model that resolves to a gpui `Scene` only inside a live
//! Window) so the blitted frame is the live cockpit, not a faithful still.

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
