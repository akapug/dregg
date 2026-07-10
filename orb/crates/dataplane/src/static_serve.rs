//! Host-side static-file streaming (roadmap Stage 3, `BodySrc.staticFile`).
//!
//! The proven core DECIDES a static-file response — the head (status line +
//! headers, including Content-Length) and WHICH file to serve — as a batch-small
//! decision. This module is the HOST side of that split for LARGE local bodies:
//! it opens the resolved file, writes the response head, then streams the file
//! bytes to the client one bounded block at a time, so the whole body never
//! passes through the cons-list core and the host's per-request working set is one
//! block regardless of the file size.
//!
//! The split mirrors [`crate::proxy_dial::forward_streaming`]: there the upstream
//! body streams with a bounded buffer; here the file body does. The emitted stream
//! — the head chunk followed by the paced file chunks — reassembles to `serialize`
//! of the static-file response the core would produce, proven core-side as
//! `Reactor.ServeStream.staticFile_emit_refines` (and, on the deployed static
//! handler, `staticFile_deployed_emit_refines`): host-side file streaming is
//! byte-equal to the batch spec's static response.
//!
//! ## The path decision keeps the proven no-escape discipline
//!
//! [`StaticRoot::resolve`] realizes the boundary the proven
//! `Safety.Traversal.serveStatic` models: the request target is percent-decoded
//! exactly ONCE (percent-decode is not idempotent, so `%252e%252e` cannot be
//! double-decoded into `..`), dot-segments are removed with `..` never popping
//! above the root, and the joined path is canonicalized and re-checked to keep the
//! document root as a prefix — a served path never escapes the root
//! (`StaticFile.static_no_escape`). No file outside the configured root is
//! reachable.
//!
//! Gated entirely on `DRORB_STATIC_ROOT`: unset ⇒ no static lane ⇒ the default
//! serve path is byte-identical and untouched.

use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Process-global static root, initialised once from `DRORB_STATIC_ROOT`. `None`
/// when the variable is unset / not a directory (no static lane configured, the
/// default serve path untouched).
static STATIC_ROOT: OnceLock<Option<StaticRoot>> = OnceLock::new();

/// The configured static root, or `None` when `DRORB_STATIC_ROOT` is unset.
pub fn get() -> Option<&'static StaticRoot> {
    STATIC_ROOT.get_or_init(StaticRoot::from_env).as_ref()
}

/// The bounded copy buffer for the streaming file pump: one block held at a time,
/// so peak host memory for a static serve is this plus the response head,
/// regardless of the file size. A slow client back-pressures the read because the
/// next file read only happens after the current block is written to the client.
const STREAM_CHUNK: usize = 64 * 1024;

/// A configured static-file document root and URL prefix. The core's decision
/// (which file, the head) is realized here; this struct only maps a request target
/// to a file under the root and streams it.
pub struct StaticRoot {
    /// The document root (canonicalized at construction). No resolved path escapes
    /// it.
    root: PathBuf,
    /// The URL path prefix a request must carry to be served statically
    /// (default `/static/`). The remainder is resolved under `root`.
    prefix: String,
}

/// What the host records after a STREAMED static serve: the response head (status
/// line + headers, for metrics / access log), the total bytes written, and whether
/// the client connection may stay open. The body itself was written straight to the
/// client and never buffered whole.
pub struct StaticOutcome {
    pub head: Vec<u8>,
    pub bytes: u64,
    pub keepalive: bool,
}

impl StaticRoot {
    /// Build from `DRORB_STATIC_ROOT` (the document root) and `DRORB_STATIC_PREFIX`
    /// (the URL prefix, default `/static/`). Returns `None` when the root is unset or
    /// does not canonicalize to an existing directory — the static lane is then
    /// inert and the default serve path is untouched.
    pub fn from_env() -> Option<StaticRoot> {
        let root = std::env::var("DRORB_STATIC_ROOT").ok()?;
        let root = std::fs::canonicalize(&root).ok()?;
        if !root.is_dir() {
            return None;
        }
        let mut prefix = std::env::var("DRORB_STATIC_PREFIX").unwrap_or_else(|_| "/static/".into());
        if !prefix.starts_with('/') {
            prefix.insert(0, '/');
        }
        if !prefix.ends_with('/') {
            prefix.push('/');
        }
        Some(StaticRoot { root, prefix })
    }

    /// Is this request one the static lane should serve? A `GET`/`HEAD` whose target
    /// begins with the configured prefix.
    pub fn is_static_path(&self, req: &[u8]) -> bool {
        let Some((method, target)) = request_line(req) else {
            return false;
        };
        if method != b"GET" && method != b"HEAD" {
            return false;
        }
        target_path(target).starts_with(self.prefix.as_bytes())
    }

    /// Resolve a request target to a file path under the root, or `None` when the
    /// target is malformed, escapes the root, or names no regular file. Percent-
    /// decodes ONCE, removes dot-segments (`..` clamped at the root), joins under the
    /// root, then canonicalizes and re-checks the root stays a prefix.
    pub fn resolve(&self, target: &[u8]) -> Option<PathBuf> {
        let path = target_path(target);
        // Strip the serving prefix; the remainder is the path under the root.
        let rel = path.strip_prefix(self.prefix.as_bytes())?;
        // Split on '/', percent-decode each segment ONCE, drop empties / '.', and
        // pop on '..' but never above the (empty) relative root.
        let mut segs: Vec<String> = Vec::new();
        for raw in rel.split(|&b| b == b'/') {
            if raw.is_empty() {
                continue;
            }
            let decoded = percent_decode_once(raw);
            let s = String::from_utf8(decoded).ok()?;
            match s.as_str() {
                "." => {}
                ".." => {
                    segs.pop();
                }
                _ => segs.push(s),
            }
        }
        let mut candidate = self.root.clone();
        for s in &segs {
            candidate.push(s);
        }
        // Canonicalize and re-check containment: the resolved real path must keep the
        // document root as a prefix (belt-and-suspenders over the dot-segment walk;
        // also rejects symlink escapes).
        let real = std::fs::canonicalize(&candidate).ok()?;
        if !real.starts_with(&self.root) {
            return None;
        }
        if !real.is_file() {
            return None;
        }
        Some(real)
    }

    /// Serve a static request by STREAMING the resolved file to `client`: the head
    /// (built batch-small, with the file's Content-Length) first, then the file body
    /// copied block-by-block with a bounded buffer — never reading the whole file into
    /// memory. A missing / escaping / non-regular target is a small `404`.
    ///
    /// `Err` is returned only on a client write failure (the connection must be
    /// dropped). A `HEAD` request writes the head only.
    pub fn handle_streaming<W: Write>(
        &self,
        req: &[u8],
        keepalive_req: bool,
        client: &mut W,
    ) -> std::io::Result<StaticOutcome> {
        let Some((method, target)) = request_line(req) else {
            return self.serve_404(keepalive_req, client);
        };
        let is_head = method == b"HEAD";

        let Some(path) = self.resolve(target) else {
            return self.serve_404(keepalive_req, client);
        };
        let mut file = match std::fs::File::open(&path) {
            Ok(f) => f,
            Err(_) => return self.serve_404(keepalive_req, client),
        };
        let len = match file.metadata() {
            Ok(m) => m.len(),
            Err(_) => return self.serve_404(keepalive_req, client),
        };

        // The head: batch-small, self-delimited by Content-Length, so keep-alive is
        // available when the request asked for it.
        let ctype = content_type(&path);
        let mut head = Vec::with_capacity(160);
        head.extend_from_slice(b"HTTP/1.1 200 OK\r\n");
        head.extend_from_slice(if keepalive_req {
            b"Connection: keep-alive\r\n"
        } else {
            b"Connection: close\r\n"
        });
        head.extend_from_slice(b"Accept-Ranges: bytes\r\n");
        head.extend_from_slice(b"Content-Type: ");
        head.extend_from_slice(ctype);
        head.extend_from_slice(b"\r\nContent-Length: ");
        head.extend_from_slice(len.to_string().as_bytes());
        head.extend_from_slice(b"\r\n\r\n");

        client.write_all(&head)?;
        let mut bytes = head.len() as u64;

        if !is_head {
            // Stream the file body with a bounded buffer — the whole point of the
            // Stage-3 static path: the host holds one block, never the file.
            let mut buf = vec![0u8; STREAM_CHUNK];
            loop {
                let n = match file.read(&mut buf) {
                    Ok(0) => break,
                    Ok(n) => n,
                    Err(e) => {
                        // Mid-stream read error: the head is already on the wire, so
                        // the connection must close (a truncated body).
                        client.flush().ok();
                        return Err(e);
                    }
                };
                client.write_all(&buf[..n])?;
                bytes += n as u64;
            }
        }
        client.flush()?;

        Ok(StaticOutcome {
            head,
            bytes,
            keepalive: keepalive_req,
        })
    }

    /// Write a small `404 Not Found` (missing / escaping / non-regular target).
    fn serve_404<W: Write>(
        &self,
        keepalive_req: bool,
        client: &mut W,
    ) -> std::io::Result<StaticOutcome> {
        let conn: &[u8] = if keepalive_req {
            b"Connection: keep-alive\r\n"
        } else {
            b"Connection: close\r\n"
        };
        let mut resp = Vec::with_capacity(96);
        resp.extend_from_slice(b"HTTP/1.1 404 Not Found\r\n");
        resp.extend_from_slice(conn);
        resp.extend_from_slice(b"Content-Length: 9\r\n\r\nnot found");
        client.write_all(&resp)?;
        client.flush()?;
        let head_end = resp
            .windows(4)
            .position(|w| w == b"\r\n\r\n")
            .map(|p| p + 4)
            .unwrap_or(resp.len());
        let head = resp[..head_end].to_vec();
        let bytes = resp.len() as u64;
        Ok(StaticOutcome {
            head,
            bytes,
            keepalive: keepalive_req,
        })
    }
}

/// The request line's `(method, target)`, borrowed from the request bytes.
fn request_line(req: &[u8]) -> Option<(&[u8], &[u8])> {
    let line_end = req.windows(2).position(|w| w == b"\r\n")?;
    let line = &req[..line_end];
    let mut it = line.splitn(3, |&c| c == b' ');
    let method = it.next()?;
    let target = it.next()?;
    Some((method, target))
}

/// The path portion of a request target (drop a `?query`/`#fragment`).
fn target_path(target: &[u8]) -> &[u8] {
    let end = target
        .iter()
        .position(|&b| b == b'?' || b == b'#')
        .unwrap_or(target.len());
    &target[..end]
}

/// Percent-decode a path segment exactly ONCE. An invalid `%XX` is left literal.
/// Single-pass by construction — never re-scans its own output — so an encoded
/// `%252e` decodes to the literal `%2e`, not to `.`.
fn percent_decode_once(seg: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(seg.len());
    let mut i = 0;
    while i < seg.len() {
        if seg[i] == b'%' && i + 2 < seg.len() {
            if let (Some(h), Some(l)) = (hex_val(seg[i + 1]), hex_val(seg[i + 2])) {
                out.push(h * 16 + l);
                i += 3;
                continue;
            }
        }
        out.push(seg[i]);
        i += 1;
    }
    out
}

fn hex_val(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

/// A minimal file-extension → Content-Type map (the common web asset types); the
/// default is `application/octet-stream`.
fn content_type(path: &Path) -> &'static [u8] {
    let ext = path
        .extension()
        .and_then(|e| e.to_str())
        .map(|e| e.to_ascii_lowercase());
    match ext.as_deref() {
        Some("html") | Some("htm") => b"text/html; charset=utf-8",
        Some("css") => b"text/css; charset=utf-8",
        Some("js") | Some("mjs") => b"application/javascript",
        Some("json") => b"application/json",
        Some("svg") => b"image/svg+xml",
        Some("png") => b"image/png",
        Some("jpg") | Some("jpeg") => b"image/jpeg",
        Some("gif") => b"image/gif",
        Some("webp") => b"image/webp",
        Some("ico") => b"image/x-icon",
        Some("txt") => b"text/plain; charset=utf-8",
        Some("wasm") => b"application/wasm",
        Some("pdf") => b"application/pdf",
        Some("mp4") => b"video/mp4",
        Some("woff2") => b"font/woff2",
        _ => b"application/octet-stream",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tmp_root() -> PathBuf {
        let mut d = std::env::temp_dir();
        d.push(format!("drorb-static-test-{}", std::process::id()));
        let _ = std::fs::create_dir_all(&d);
        std::fs::canonicalize(&d).unwrap()
    }

    #[test]
    fn detects_static_path() {
        let root = tmp_root();
        let sr = StaticRoot {
            root,
            prefix: "/static/".into(),
        };
        assert!(sr.is_static_path(b"GET /static/app.js HTTP/1.1\r\nHost: x\r\n\r\n"));
        assert!(sr.is_static_path(b"HEAD /static/a HTTP/1.1\r\n\r\n"));
        assert!(!sr.is_static_path(b"GET /api HTTP/1.1\r\n\r\n"));
        assert!(!sr.is_static_path(b"POST /static/a HTTP/1.1\r\n\r\n"));
    }

    #[test]
    fn resolves_and_confines() {
        let root = tmp_root();
        let mut f = std::fs::File::create(root.join("hello.txt")).unwrap();
        f.write_all(b"hi there").unwrap();
        drop(f);
        let sr = StaticRoot {
            root: root.clone(),
            prefix: "/static/".into(),
        };

        // A real file resolves.
        let p = sr.resolve(b"/static/hello.txt").unwrap();
        assert_eq!(p, root.join("hello.txt"));

        // A traversal target cannot escape the root (resolves to nothing under root).
        assert!(sr.resolve(b"/static/../../etc/passwd").is_none());
        // A double-encoded `..` decodes ONCE to the literal `%2e%2e`, not to `..`,
        // so it names no file and is rejected.
        assert!(sr.resolve(b"/static/%252e%252e/etc/passwd").is_none());
        // A missing file is rejected.
        assert!(sr.resolve(b"/static/nope.txt").is_none());
    }

    #[test]
    fn streams_file_bounded() {
        let root = tmp_root();
        // A body several chunks long: the pump must reassemble it exactly.
        let body: Vec<u8> = (0..(STREAM_CHUNK * 3 + 123))
            .map(|i| (i % 251) as u8)
            .collect();
        std::fs::write(root.join("big.bin"), &body).unwrap();
        let sr = StaticRoot {
            root,
            prefix: "/static/".into(),
        };

        let mut out: Vec<u8> = Vec::new();
        let o = sr
            .handle_streaming(
                b"GET /static/big.bin HTTP/1.1\r\nHost: x\r\n\r\n",
                true,
                &mut out,
            )
            .unwrap();
        assert!(o.keepalive);
        // The wire = head ++ body, and the body is byte-identical to the file.
        let head_end = out.windows(4).position(|w| w == b"\r\n\r\n").unwrap() + 4;
        assert_eq!(&out[head_end..], &body[..]);
        assert!(out[..head_end].windows(2).any(|w| w == b"OK"));
        assert!(
            String::from_utf8_lossy(&out[..head_end])
                .contains(&format!("Content-Length: {}", body.len()))
        );
    }

    #[test]
    fn head_writes_no_body() {
        let root = tmp_root();
        std::fs::write(root.join("h.txt"), b"abc").unwrap();
        let sr = StaticRoot {
            root,
            prefix: "/static/".into(),
        };
        let mut out: Vec<u8> = Vec::new();
        sr.handle_streaming(b"HEAD /static/h.txt HTTP/1.1\r\n\r\n", false, &mut out)
            .unwrap();
        let head_end = out.windows(4).position(|w| w == b"\r\n\r\n").unwrap() + 4;
        assert_eq!(out.len(), head_end); // head only, no body
        assert!(String::from_utf8_lossy(&out).contains("Content-Length: 3"));
    }
}
