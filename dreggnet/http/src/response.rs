//! The response status enum, `Content-Type` header constants, and the
//! slice-backed response writer.

/// CRLF — the HTTP line terminator.
pub const CRLF: &[u8] = b"\r\n";

/// An HTTP response status code.
///
/// Each variant carries its full status line ([`StatusCode::status_line`], e.g.
/// `HTTP/1.1 404 Not Found`) so the writer emits it without formatting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum StatusCode {
    Ok = 200,
    Created = 201,
    Accepted = 202,
    NoContent = 204,
    PartialContent = 206,

    MovedPermanently = 301,
    Found = 302,
    SeeOther = 303,
    NotModified = 304,
    TemporaryRedirect = 307,
    PermanentRedirect = 308,

    BadRequest = 400,
    Unauthorized = 401,
    PaymentRequired = 402,
    Forbidden = 403,
    NotFound = 404,
    MethodNotAllowed = 405,
    NotAcceptable = 406,
    RequestTimeout = 408,
    Conflict = 409,
    Gone = 410,
    LengthRequired = 411,
    PayloadTooLarge = 413,
    UriTooLong = 414,
    UnsupportedMediaType = 415,
    RangeNotSatisfiable = 416,
    TooManyRequests = 429,

    InternalServerError = 500,
    NotImplemented = 501,
    BadGateway = 502,
    ServiceUnavailable = 503,
    GatewayTimeout = 504,
}

impl StatusCode {
    /// The numeric status code.
    pub const fn as_u16(self) -> u16 {
        self as u16
    }

    /// The full HTTP/1.1 status line for this code, e.g. `HTTP/1.1 200 OK`
    /// (no trailing CRLF).
    pub const fn status_line(self) -> &'static [u8] {
        match self {
            StatusCode::Ok => b"HTTP/1.1 200 OK",
            StatusCode::Created => b"HTTP/1.1 201 Created",
            StatusCode::Accepted => b"HTTP/1.1 202 Accepted",
            StatusCode::NoContent => b"HTTP/1.1 204 No Content",
            StatusCode::PartialContent => b"HTTP/1.1 206 Partial Content",
            StatusCode::MovedPermanently => b"HTTP/1.1 301 Moved Permanently",
            StatusCode::Found => b"HTTP/1.1 302 Found",
            StatusCode::SeeOther => b"HTTP/1.1 303 See Other",
            StatusCode::NotModified => b"HTTP/1.1 304 Not Modified",
            StatusCode::TemporaryRedirect => b"HTTP/1.1 307 Temporary Redirect",
            StatusCode::PermanentRedirect => b"HTTP/1.1 308 Permanent Redirect",
            StatusCode::BadRequest => b"HTTP/1.1 400 Bad Request",
            StatusCode::Unauthorized => b"HTTP/1.1 401 Unauthorized",
            StatusCode::PaymentRequired => b"HTTP/1.1 402 Payment Required",
            StatusCode::Forbidden => b"HTTP/1.1 403 Forbidden",
            StatusCode::NotFound => b"HTTP/1.1 404 Not Found",
            StatusCode::MethodNotAllowed => b"HTTP/1.1 405 Method Not Allowed",
            StatusCode::NotAcceptable => b"HTTP/1.1 406 Not Acceptable",
            StatusCode::RequestTimeout => b"HTTP/1.1 408 Request Timeout",
            StatusCode::Conflict => b"HTTP/1.1 409 Conflict",
            StatusCode::Gone => b"HTTP/1.1 410 Gone",
            StatusCode::LengthRequired => b"HTTP/1.1 411 Length Required",
            StatusCode::PayloadTooLarge => b"HTTP/1.1 413 Payload Too Large",
            StatusCode::UriTooLong => b"HTTP/1.1 414 URI Too Long",
            StatusCode::UnsupportedMediaType => b"HTTP/1.1 415 Unsupported Media Type",
            StatusCode::RangeNotSatisfiable => b"HTTP/1.1 416 Range Not Satisfiable",
            StatusCode::TooManyRequests => b"HTTP/1.1 429 Too Many Requests",
            StatusCode::InternalServerError => b"HTTP/1.1 500 Internal Server Error",
            StatusCode::NotImplemented => b"HTTP/1.1 501 Not Implemented",
            StatusCode::BadGateway => b"HTTP/1.1 502 Bad Gateway",
            StatusCode::ServiceUnavailable => b"HTTP/1.1 503 Service Unavailable",
            StatusCode::GatewayTimeout => b"HTTP/1.1 504 Gateway Timeout",
        }
    }

    /// Whether this is a 2xx success status.
    pub const fn is_success(self) -> bool {
        (self as u16) >= 200 && (self as u16) < 300
    }
}

/// Pre-formatted `Content-Type:` header lines (no trailing CRLF), written with
/// [`ResponseWriter::header_line`].
pub mod content_type {
    pub const TEXT_PLAIN: &[u8] = b"Content-Type: text/plain";
    pub const TEXT_HTML: &[u8] = b"Content-Type: text/html; charset=utf-8";
    pub const TEXT_CSS: &[u8] = b"Content-Type: text/css";
    pub const TEXT_JAVASCRIPT: &[u8] = b"Content-Type: text/javascript";
    pub const APPLICATION_JSON: &[u8] = b"Content-Type: application/json; charset=utf-8";
    pub const APPLICATION_OCTET_STREAM: &[u8] = b"Content-Type: application/octet-stream";
    pub const IMAGE_PNG: &[u8] = b"Content-Type: image/png";
    pub const IMAGE_JPEG: &[u8] = b"Content-Type: image/jpeg";
    pub const IMAGE_GIF: &[u8] = b"Content-Type: image/gif";
    pub const IMAGE_SVG: &[u8] = b"Content-Type: image/svg+xml";
    pub const IMAGE_WEBP: &[u8] = b"Content-Type: image/webp";
    pub const IMAGE_ICO: &[u8] = b"Content-Type: image/x-icon";
    pub const FONT_WOFF2: &[u8] = b"Content-Type: font/woff2";
    pub const VIDEO_MP4: &[u8] = b"Content-Type: video/mp4";
}

/// A response writer that appends wire-format HTTP/1.1 bytes into a fixed,
/// caller-owned `&mut [u8]` buffer.
///
/// The builder methods append the status line, headers, and body in order,
/// each return `&mut Self` for chaining, and track the write [`position`]. A
/// write that would exceed the buffer is truncated to what fits (the position
/// caps at the buffer length) — the gateway sizes/grows its buffer from the
/// reported position so a truncated response is detected and re-rendered rather
/// than shipped short.
///
/// [`position`]: ResponseWriter::position
pub struct ResponseWriter<'a> {
    buffer: &'a mut [u8],
    position: usize,
    headers_done: bool,
}

impl<'a> ResponseWriter<'a> {
    /// A fresh writer over `buffer`, positioned at the start.
    pub fn new(buffer: &'a mut [u8]) -> Self {
        ResponseWriter {
            buffer,
            position: 0,
            headers_done: false,
        }
    }

    /// Bytes written so far (capped at the buffer length).
    pub const fn position(&self) -> usize {
        self.position
    }

    /// Remaining free capacity.
    pub const fn remaining(&self) -> usize {
        self.buffer.len() - self.position
    }

    /// Append `data`, truncating to the free capacity. Returns `true` iff all of
    /// `data` was written (`false` signals the buffer filled and the tail was
    /// dropped).
    pub fn write_bytes(&mut self, data: &[u8]) -> bool {
        let n = data.len().min(self.remaining());
        if n > 0 {
            self.buffer[self.position..self.position + n].copy_from_slice(&data[..n]);
            self.position += n;
        }
        n == data.len()
    }

    /// Append the status line (`HTTP/1.1 <code> <reason>\r\n`). Call first.
    pub fn status(&mut self, code: StatusCode) -> &mut Self {
        self.write_bytes(code.status_line());
        self.write_bytes(CRLF);
        self
    }

    /// Append a `Name: value\r\n` header.
    pub fn header(&mut self, name: &[u8], value: &[u8]) -> &mut Self {
        self.write_bytes(name);
        self.write_bytes(b": ");
        self.write_bytes(value);
        self.write_bytes(CRLF);
        self
    }

    /// Append a pre-formatted header line (e.g. a [`content_type`] constant),
    /// followed by CRLF.
    pub fn header_line(&mut self, line: &[u8]) -> &mut Self {
        self.write_bytes(line);
        self.write_bytes(CRLF);
        self
    }

    /// Append the `Content-Length: <len>\r\n` header.
    pub fn content_length(&mut self, len: usize) -> &mut Self {
        self.write_bytes(b"Content-Length: ");
        self.write_usize(len);
        self.write_bytes(CRLF);
        self
    }

    /// Terminate the header section with a blank line (idempotent).
    pub fn end_headers(&mut self) -> &mut Self {
        if !self.headers_done {
            self.write_bytes(CRLF);
            self.headers_done = true;
        }
        self
    }

    /// Append body bytes, terminating the header section first if needed.
    pub fn body(&mut self, data: &[u8]) -> &mut Self {
        self.end_headers();
        self.write_bytes(data);
        self
    }

    /// Append `n` as decimal ASCII digits.
    fn write_usize(&mut self, mut n: usize) {
        if n == 0 {
            self.write_bytes(b"0");
            return;
        }
        let mut digits = [0u8; 20];
        let mut i = digits.len();
        while n > 0 {
            i -= 1;
            digits[i] = b'0' + (n % 10) as u8;
            n /= 10;
        }
        self.write_bytes(&digits[i..]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rendered(buf: &[u8], len: usize) -> String {
        String::from_utf8_lossy(&buf[..len]).into_owned()
    }

    #[test]
    fn writes_a_complete_response() {
        let mut buf = [0u8; 256];
        let mut w = ResponseWriter::new(&mut buf);
        w.status(StatusCode::Ok)
            .header_line(content_type::APPLICATION_JSON)
            .content_length(11)
            .body(br#"{"ok":true}"#);
        let len = w.position();
        let out = rendered(&buf, len);
        assert_eq!(
            out,
            "HTTP/1.1 200 OK\r\nContent-Type: application/json; charset=utf-8\r\nContent-Length: 11\r\n\r\n{\"ok\":true}"
        );
    }

    #[test]
    fn arbitrary_header_and_status() {
        let mut buf = [0u8; 256];
        let mut w = ResponseWriter::new(&mut buf);
        w.status(StatusCode::NotFound)
            .header(b"content-type", b"image/png")
            .content_length(4)
            .body(&[1, 2, 3, 4]);
        let len = w.position();
        let out = rendered(&buf, len);
        assert!(out.starts_with("HTTP/1.1 404 Not Found\r\n"));
        assert!(out.contains("content-type: image/png\r\n"));
        assert!(out.contains("Content-Length: 4\r\n\r\n"));
    }

    #[test]
    fn truncates_and_reports_capped_position() {
        // A 16-byte buffer cannot hold the status line — the write caps.
        let mut buf = [0u8; 16];
        let mut w = ResponseWriter::new(&mut buf);
        w.status(StatusCode::Ok).content_length(5).body(b"hello");
        assert_eq!(w.position(), 16, "position caps at the buffer length");
    }

    #[test]
    fn zero_content_length() {
        let mut buf = [0u8; 64];
        let mut w = ResponseWriter::new(&mut buf);
        w.status(StatusCode::Ok).content_length(0).body(&[]);
        let len = w.position();
        let out = rendered(&buf, len);
        assert_eq!(out, "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n");
    }
}
