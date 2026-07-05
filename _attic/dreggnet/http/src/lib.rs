//! `dreggnet-http` — the small HTTP/1.1 value vocabulary the DreggNet gateway
//! serves through.
//!
//! The gateway (`dreggnet-gateway`) runs a hand-rolled `std::net::TcpListener`
//! thread-per-connection loop. Its handlers (`MachinesHandler`,
//! `SiteHostHandler`, `StorageHandler`, `WebAppHandler`) classify a request and
//! write a wire-format HTTP/1.1 response straight into a caller-owned `&mut [u8]`
//! buffer. They need only a handful of small value types to do that:
//!
//! - [`Method`] — the request method enum (`GET`/`POST`/…).
//! - [`StatusCode`] — the response status enum, carrying its `HTTP/1.1 … ` line.
//! - [`ResponseWriter`] — a slice-backed writer that appends the status line,
//!   headers, and body to a fixed buffer, tracking the write position.
//! - [`Handler`] / [`HandlerResult`] — the request→response trait the handlers
//!   implement, and its byte-count result.
//! - [`Request`] — a borrowed view of an inbound request (method, path, headers).
//! - [`response::content_type`] — pre-formatted `Content-Type:` header lines.
//!
//! These are deliberately tiny: an HTTP method enum, a status-code enum, a
//! buffer-append response writer, and two one-method traits. They are DreggNet's
//! own (clean-room) so the gateway carries no third-party HTTP engine and stays
//! pure-`std` + cross-platform.
//!
//! The wire format is plain HTTP/1.1: a status line `HTTP/1.1 <code> <reason>`,
//! `Name: value` header lines, a blank line, then the body — all CRLF-delimited.

pub mod handler;
pub mod request;
pub mod response;

pub use handler::{Handler, HandlerResult};
pub use request::{Method, Request};
pub use response::{ResponseWriter, StatusCode};
