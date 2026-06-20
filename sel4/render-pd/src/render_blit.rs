//! The final rung of the in-VM re-flow: RGBA (from the in-PD gpui render) →
//! XRGB8888 → the seL4 ramfb framebuffer. This is the EXACT blit loop the
//! deos-image PD uses (`dregg-pd/deos-image/src/cockpit_frame.rs::blit_frame`),
//! minus the `include_bytes!` bake — here the RGBA comes from the in-PD render,
//! not a baked asset.
//!
//! STAGED, not yet exercised: the render-PD reaches lavapipe device creation but
//! stops at the submit-thread `thrd_create` wall (WIRING.md "MEASURED RESULT"), so
//! no in-PD RGBA exists to blit yet. This module is the receiving end, ready for
//! when the `__clone`/TCB lever unblocks `vkCreateDevice` → a JIT'd render →
//! `render_scene_to_image` → these bytes. The geometry + the RGBA→XRGB8888
//! swizzle match the persvati bake exactly, so the byte-compare (the parity proof)
//! is a straight `memcmp` of this blit's input against `cockpit_frame.rgba`.
//!
//! The framebuffer-mapping half differs from deos-image: that PD is microkit
//! (`var!()` vaddrs from the .system file); this is a raw root task, so the
//! framebuffer frames are mapped from the root task's untyped/device caps at boot
//! (the compositor-fb / deos-tutorial fw_cfg+ramfb discipline). That mapping is
//! wired alongside the `__clone` TCB work — both are the same "give the root task
//! the device caps" rung — so it is intentionally a thin seam here.

/// The framebuffer geometry — equals the persvati render geometry so the blit is a
/// straight copy and the parity byte-compare is exact.
pub const WIDTH: u32 = 800;
pub const HEIGHT: u32 = 600;

/// Pack `(r,g,b)` into an XRGB8888 pixel (`0x00RRGGBB`) — the ramfb format
/// (`DRM_FORMAT_XRGB8888`). Identical to `fb::rgb` in deos-image.
#[inline]
pub const fn rgb(r: u8, g: u8, b: u8) -> u32 {
    ((r as u32) << 16) | ((g as u32) << 8) | (b as u32)
}

/// Blit one in-PD-rendered RGBA8 frame (`800×600`, row-major, no padding —
/// `WIDTH*HEIGHT*4` bytes) into the mapped XRGB8888 framebuffer the QEMU ramfb
/// engine scans out. The exact loop deos-image's `blit_frame` runs, minus the
/// bake. `fb` is the mapped framebuffer as `WIDTH*HEIGHT` u32 pixels.
///
/// Returns the number of pixels written (`WIDTH*HEIGHT`) on a correct-length
/// input, or `0` if `rgba` is the wrong length (a render/geometry mismatch — the
/// caller paints a backdrop, as deos-image does).
pub fn blit_rgba_to_framebuffer(rgba: &[u8], fb: &mut [u32]) -> usize {
    let want = (WIDTH * HEIGHT * 4) as usize;
    if rgba.len() != want || fb.len() < (WIDTH * HEIGHT) as usize {
        return 0;
    }
    for y in 0..HEIGHT {
        for x in 0..WIDTH {
            let i = ((y * WIDTH + x) * 4) as usize;
            let r = rgba[i];
            let g = rgba[i + 1];
            let b = rgba[i + 2];
            // alpha (i+3) ignored: the framebuffer is XRGB (opaque); the cockpit
            // backdrop is itself opaque so this is exact — matching deos-image.
            fb[(y * WIDTH + x) as usize] = rgb(r, g, b);
        }
    }
    (WIDTH * HEIGHT) as usize
}
