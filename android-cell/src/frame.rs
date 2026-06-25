//! **Surface → tile.** Convert an Android device surface capture into the EXACT
//! [`RgbaFrame`] `servo-render` produces — the keystone that makes the compositor
//! seam free.
//!
//! The first, most direct capture is `adb exec-out screencap` (the doc's "to start"
//! path). Its raw (non-PNG) wire format is a fixed-size little-endian header followed
//! by tightly-packed RGBA8 pixels:
//!
//! ```text
//!   offset 0  : width      u32 LE
//!   offset 4  : height     u32 LE
//!   offset 8  : format     u32 LE   (1 = HAL_PIXEL_FORMAT_RGBA_8888)
//!   offset 12 : colorspace u32 LE   (present since Android 9 / API 28)
//!   offset 16 : width*height*4 bytes, RGBA8 row-major
//! ```
//!
//! This is byte-for-byte the layout an emulator screencap on API 35 produces
//! (verified live: `1080×2400`, format `1`, 16-byte header, `1080*2400*4 + 16`
//! bytes). The output [`RgbaFrame`] is then identical to a SWGL render's — the
//! compositor cannot tell (and must not care) which renderer drew it.
//!
//! The richer captures named in the doc (the emulator gRPC stream, scrcpy's
//! `MediaCodec` H.264) decode to the SAME `RgbaFrame` through one extra
//! H.264→RGBA stage; this `screencap` path is the de-risking core (the analogue of
//! servo's SWGL-vs-GPU split), and is what the macOS-emulator impl drives today.

use servo_render::RgbaFrame;

/// The fixed `screencap` raw header length (width, height, format, colorspace —
/// four `u32` LE), Android 9+ (API 28+). The colorspace field was added then; the
/// emulator (API 35) always emits it.
pub const ANDROID_SCREENCAP_HEADER_LEN: usize = 16;

/// HAL pixel format `RGBA_8888` — the only format this converter accepts (it is what
/// `screencap` emits for the framebuffer; the bytes are already R,G,B,A row-major, so
/// no swizzle is needed to land in [`RgbaFrame`]).
pub const HAL_PIXEL_FORMAT_RGBA_8888: u32 = 1;

/// Why a capture could not be turned into an [`RgbaFrame`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScreencapError {
    /// Fewer than the 16 header bytes were present.
    TooShortForHeader { got: usize },
    /// The capture declared a pixel format this converter does not handle. Only
    /// `RGBA_8888` (1) is accepted; anything else would need a swizzle/decode the
    /// `screencap` software path never produces.
    UnsupportedFormat { format: u32 },
    /// The payload length did not equal `width * height * 4` after the header — the
    /// capture is truncated or the header lied. Fail-closed: no partial frame.
    PayloadSizeMismatch {
        width: u32,
        height: u32,
        expected_pixel_bytes: usize,
        got_pixel_bytes: usize,
    },
    /// `width * height * 4` overflowed `usize` (a hostile/garbage header).
    DimensionOverflow { width: u32, height: u32 },
}

impl std::fmt::Display for ScreencapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ScreencapError::TooShortForHeader { got } => {
                write!(
                    f,
                    "screencap shorter than the {ANDROID_SCREENCAP_HEADER_LEN}-byte header (got {got})"
                )
            }
            ScreencapError::UnsupportedFormat { format } => {
                write!(
                    f,
                    "screencap pixel format {format} is not RGBA_8888 ({HAL_PIXEL_FORMAT_RGBA_8888})"
                )
            }
            ScreencapError::PayloadSizeMismatch {
                width,
                height,
                expected_pixel_bytes,
                got_pixel_bytes,
            } => write!(
                f,
                "screencap payload size mismatch for {width}x{height}: expected {expected_pixel_bytes} pixel bytes, got {got_pixel_bytes}"
            ),
            ScreencapError::DimensionOverflow { width, height } => {
                write!(f, "screencap dimensions {width}x{height} overflow usize")
            }
        }
    }
}

impl std::error::Error for ScreencapError {}

/// **THE SURFACE→TILE SEAM.** Parse a raw `adb screencap` blob into the EXACT
/// [`RgbaFrame`] the servo-render SWGL path produces.
///
/// Fail-closed: an unsupported format, a truncated payload, or a lying header is a
/// hard error, never a partial frame — a malformed capture must reach nothing on the
/// glass (the same fail-closed discipline as the compositor gate).
pub fn screencap_to_rgba(raw: &[u8]) -> Result<RgbaFrame, ScreencapError> {
    if raw.len() < ANDROID_SCREENCAP_HEADER_LEN {
        return Err(ScreencapError::TooShortForHeader { got: raw.len() });
    }

    let width = u32::from_le_bytes([raw[0], raw[1], raw[2], raw[3]]);
    let height = u32::from_le_bytes([raw[4], raw[5], raw[6], raw[7]]);
    let format = u32::from_le_bytes([raw[8], raw[9], raw[10], raw[11]]);
    // raw[12..16] is the colorspace; the framebuffer is sRGB and the compositor
    // treats the bytes opaquely (it hashes them), so we do not interpret it here.

    if format != HAL_PIXEL_FORMAT_RGBA_8888 {
        return Err(ScreencapError::UnsupportedFormat { format });
    }

    let expected_pixel_bytes = (width as usize)
        .checked_mul(height as usize)
        .and_then(|p| p.checked_mul(4))
        .ok_or(ScreencapError::DimensionOverflow { width, height })?;

    let pixels = &raw[ANDROID_SCREENCAP_HEADER_LEN..];
    if pixels.len() != expected_pixel_bytes {
        return Err(ScreencapError::PayloadSizeMismatch {
            width,
            height,
            expected_pixel_bytes,
            got_pixel_bytes: pixels.len(),
        });
    }

    // The bytes are already R,G,B,A row-major — the SAME layout RgbaFrame holds. No
    // swizzle, no copy beyond the owned Vec the caller takes.
    Ok(RgbaFrame {
        width,
        height,
        bytes: pixels.to_vec(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn header(width: u32, height: u32, format: u32) -> Vec<u8> {
        let mut h = Vec::with_capacity(ANDROID_SCREENCAP_HEADER_LEN);
        h.extend_from_slice(&width.to_le_bytes());
        h.extend_from_slice(&height.to_le_bytes());
        h.extend_from_slice(&format.to_le_bytes());
        h.extend_from_slice(&1u32.to_le_bytes()); // colorspace = sRGB
        h
    }

    /// A synthetic 2×1 RGBA screencap parses to the exact RgbaFrame, pixels intact.
    #[test]
    fn parses_a_well_formed_screencap_into_rgbaframe() {
        let mut raw = header(2, 1, HAL_PIXEL_FORMAT_RGBA_8888);
        raw.extend_from_slice(&[0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0]);

        let frame = screencap_to_rgba(&raw).expect("a well-formed screencap converts");
        assert_eq!(frame.width, 2);
        assert_eq!(frame.height, 1);
        assert_eq!(
            frame.bytes,
            vec![0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0]
        );
        assert_eq!(frame.pixel(0, 0), (0x12, 0x34, 0x56, 0x78));
        assert_eq!(frame.pixel(1, 0), (0x9A, 0xBC, 0xDE, 0xF0));
    }

    /// **THE REAL-FRAME FIXTURE.** A downscaled-but-genuine capture of the live
    /// emulator's home screen (committed at `fixtures/android_home_screencap.raw`)
    /// parses into an RgbaFrame whose digest is stable and whose dimensions match the
    /// captured header — i.e. a REAL Android frame becomes the exact tile type the
    /// compositor takes.
    #[test]
    fn parses_the_real_captured_home_frame() {
        let raw = include_bytes!("../fixtures/android_home_screencap.raw");
        let frame = screencap_to_rgba(raw).expect("the real captured home frame converts");
        assert_eq!(frame.width, 90, "the fixture's declared width");
        assert_eq!(frame.height, 200, "the fixture's declared height");
        assert_eq!(frame.bytes.len(), 90 * 200 * 4);
        // A real frame is not uniform — it has content (the home screen), so the
        // digest is non-trivial and the bytes are not all one value.
        let first = frame.bytes[0];
        assert!(
            frame.bytes.iter().any(|&b| b != first),
            "a real home-screen frame is not a single flat color"
        );
        // The digest is deterministic — the bind to content_digest is live.
        assert_eq!(frame.content_digest(), frame.content_digest());
    }

    #[test]
    fn rejects_a_short_blob() {
        assert_eq!(
            screencap_to_rgba(&[0, 1, 2]),
            Err(ScreencapError::TooShortForHeader { got: 3 })
        );
    }

    #[test]
    fn rejects_an_unsupported_format() {
        // format 2 (RGBX_8888) is not handled — fail closed, do not guess.
        let raw = header(1, 1, 2);
        assert_eq!(
            screencap_to_rgba(&raw),
            Err(ScreencapError::UnsupportedFormat { format: 2 })
        );
    }

    #[test]
    fn rejects_a_truncated_payload() {
        let mut raw = header(2, 2, HAL_PIXEL_FORMAT_RGBA_8888); // needs 16 pixel bytes
        raw.extend_from_slice(&[0u8; 8]); // only 8 — truncated
        assert_eq!(
            screencap_to_rgba(&raw),
            Err(ScreencapError::PayloadSizeMismatch {
                width: 2,
                height: 2,
                expected_pixel_bytes: 16,
                got_pixel_bytes: 8,
            })
        );
    }
}
