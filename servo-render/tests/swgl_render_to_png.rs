//! **The display-free RENDERED-PIXEL artifact.** Render a real frame with the
//! SWGL CPU rasterizer (no GPU, no display) and write the RGBA8 result to an
//! actual PNG file on disk — the concrete, inspectable proof that "the pixels are
//! real" holds on THIS host (verified on Linux/persvati, where there is no
//! display at all).
//!
//! `SWGL_PNG_OUT=/path/frame.png cargo test --test swgl_render_to_png -- --nocapture`
//! renders a non-trivial frame (a colored background with a distinct inner box),
//! encodes it as a PNG with a SELF-CONTAINED encoder (no image/png crate — a
//! stored-block zlib + hand CRC/Adler, so this adds ZERO dependencies), and
//! asserts the file is non-empty and the in-memory pixels are sane. When
//! `SWGL_PNG_OUT` is unset it still renders + checks pixels (writing to a temp
//! path), so the test is always meaningful in CI.

#![cfg(feature = "swgl-standalone")]

use gleam::gl;
use servo_render::{with_gl, RenderingContext, RgbaFrame, SwglRenderingContext};
use std::io::Write;

// ───────────────────────── a tiny self-contained PNG encoder ─────────────────────────
// PNG = 8-byte signature + IHDR + IDAT (zlib-wrapped, here using STORED/uncompressed
// deflate blocks so we need no deflate impl) + IEND. CRC32 over each chunk's
// (type||data); Adler-32 over the raw zlib payload. Both are ~10 lines.

fn crc32(bytes: &[u8]) -> u32 {
    // Standard IEEE CRC-32 (reflected, poly 0xEDB88320), computed without a table.
    let mut crc: u32 = 0xFFFF_FFFF;
    for &b in bytes {
        crc ^= b as u32;
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
    }
    !crc
}

fn adler32(bytes: &[u8]) -> u32 {
    const MOD: u32 = 65521;
    let (mut a, mut b) = (1u32, 0u32);
    for &x in bytes {
        a = (a + x as u32) % MOD;
        b = (b + a) % MOD;
    }
    (b << 16) | a
}

fn chunk(out: &mut Vec<u8>, kind: &[u8; 4], data: &[u8]) {
    out.extend_from_slice(&(data.len() as u32).to_be_bytes());
    let mut typed = Vec::with_capacity(4 + data.len());
    typed.extend_from_slice(kind);
    typed.extend_from_slice(data);
    out.extend_from_slice(&typed);
    out.extend_from_slice(&crc32(&typed).to_be_bytes());
}

/// Wrap `raw` (the filtered scanlines) in a zlib stream using only STORED
/// (uncompressed) deflate blocks — valid zlib, no compressor needed.
fn zlib_stored(raw: &[u8]) -> Vec<u8> {
    let mut z = Vec::new();
    z.push(0x78); // CMF: deflate, 32K window
    z.push(0x01); // FLG: check bits make 0x7801 a multiple of 31, no preset dict
                  // STORED blocks: each is [BFINAL(1)|BTYPE=00 (2)] padded to a byte, then
                  // LEN(LE16), NLEN(~LEN, LE16), then LEN literal bytes. Max LEN per block = 65535.
    let mut off = 0usize;
    while off < raw.len() {
        let take = (raw.len() - off).min(0xFFFF);
        let bfinal = if off + take >= raw.len() { 1u8 } else { 0u8 };
        z.push(bfinal); // BTYPE=00 in bits 1..2 == 0, BFINAL in bit 0
        z.extend_from_slice(&(take as u16).to_le_bytes());
        z.extend_from_slice(&(!(take as u16)).to_le_bytes());
        z.extend_from_slice(&raw[off..off + take]);
        off += take;
    }
    z.extend_from_slice(&adler32(raw).to_be_bytes());
    z
}

/// Encode an RGBA8 frame to PNG bytes (8-bit, color-type 6 = RGBA).
fn encode_png(frame: &RgbaFrame) -> Vec<u8> {
    let (w, h) = (frame.width, frame.height);
    // Filtered scanlines: filter-type byte 0 (None) per row, then the row's RGBA bytes.
    let mut raw = Vec::with_capacity((h * (1 + w * 4)) as usize);
    for y in 0..h {
        raw.push(0); // filter: None
        let start = (y * w * 4) as usize;
        raw.extend_from_slice(&frame.bytes[start..start + (w * 4) as usize]);
    }

    let mut png = Vec::new();
    png.extend_from_slice(&[0x89, b'P', b'N', b'G', 0x0D, 0x0A, 0x1A, 0x0A]);

    let mut ihdr = Vec::new();
    ihdr.extend_from_slice(&w.to_be_bytes());
    ihdr.extend_from_slice(&h.to_be_bytes());
    ihdr.push(8); // bit depth
    ihdr.push(6); // color type: RGBA
    ihdr.push(0); // compression: deflate
    ihdr.push(0); // filter: adaptive
    ihdr.push(0); // interlace: none
    chunk(&mut png, b"IHDR", &ihdr);

    chunk(&mut png, b"IDAT", &zlib_stored(&raw));
    chunk(&mut png, b"IEND", &[]);
    png
}

/// Render a `W×H` frame: clear to `bg`, then an inner box `inner` via SWGL's
/// immediate region fill. Returns the owned RGBA8 frame. (Same primitives the
/// unit tests exercise — `clear` for the background, `clear_color_rect` for the
/// box — so this is a real, region-selective rasterization, not a uniform fill.)
fn render_demo_frame(w: u32, h: u32, bg: (u8, u8, u8, u8), inner: (u8, u8, u8, u8)) -> RgbaFrame {
    with_gl(|| {
        let ctx = SwglRenderingContext::new(w, h);
        ctx.make_current();
        ctx.prepare_for_rendering();
        let glh = ctx.gleam_gl_api();
        let swgl = ctx.swgl_context();

        let (r, g, b, a) = bg;
        glh.clear_color(
            r as f32 / 255.0,
            g as f32 / 255.0,
            b as f32 / 255.0,
            a as f32 / 255.0,
        );
        glh.clear(gl::COLOR_BUFFER_BIT);

        // A centered box covering the middle half, in `inner`.
        let bx = (w / 4) as i32;
        let by = (h / 4) as i32;
        let bw = (w / 2) as i32;
        let bh = (h / 2) as i32;
        let (ir, ig, ib, ia) = inner;
        swgl.clear_color_rect(
            0,
            bx,
            by,
            bw,
            bh,
            ir as f32 / 255.0,
            ig as f32 / 255.0,
            ib as f32 / 255.0,
            ia as f32 / 255.0,
        );
        ctx.present();
        ctx.read_frame()
    })
}

#[test]
fn swgl_renders_a_real_frame_and_writes_a_png() {
    const W: u32 = 256;
    const H: u32 = 192;
    let bg = (0x1E, 0x29, 0x3B, 0xFF); // deep slate
    let inner = (0xF2, 0xA0, 0x4D, 0xFF); // warm amber

    let frame = render_demo_frame(W, H, bg, inner);

    // ── the pixels are sane ──
    assert_eq!(frame.width, W);
    assert_eq!(frame.height, H);
    assert_eq!(
        frame.bytes.len(),
        (W * H * 4) as usize,
        "RGBA8 = 4 bytes/pixel"
    );
    // a corner is the background; the center is the inner box.
    assert_eq!(frame.pixel(2, 2), bg, "corner is the slate background");
    assert_eq!(frame.pixel(W / 2, H / 2), inner, "center is the amber box");
    // not a flat image: at least two distinct colors really rasterized.
    let center = frame.pixel(W / 2, H / 2);
    let corner = frame.pixel(2, 2);
    assert_ne!(
        center, corner,
        "the frame is non-trivial (box != background)"
    );

    // ── write the PNG artifact ──
    let out_path = std::env::var("SWGL_PNG_OUT").unwrap_or_else(|_| {
        let mut p = std::env::temp_dir();
        p.push("swgl_render_linux.png");
        p.to_string_lossy().into_owned()
    });
    let png = encode_png(&frame);
    assert!(
        png.len() > 100,
        "encoded PNG should be substantial, got {} bytes",
        png.len()
    );
    // PNG magic is present.
    assert_eq!(
        &png[..8],
        &[0x89, b'P', b'N', b'G', 0x0D, 0x0A, 0x1A, 0x0A],
        "PNG signature"
    );

    let mut f = std::fs::File::create(&out_path).expect("create PNG output file");
    f.write_all(&png).expect("write PNG bytes");
    f.flush().ok();

    let meta = std::fs::metadata(&out_path).expect("PNG file exists");
    assert!(meta.len() > 0, "the written PNG is non-empty");

    println!(
        "SWGL_PNG_WRITTEN path={out_path} bytes={} dims={W}x{H} bg={:02x}{:02x}{:02x}{:02x} inner={:02x}{:02x}{:02x}{:02x}",
        meta.len(),
        bg.0, bg.1, bg.2, bg.3,
        inner.0, inner.1, inner.2, inner.3,
    );
}
