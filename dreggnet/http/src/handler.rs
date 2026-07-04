//! The request-handling trait and its result.

use crate::request::Request;
use crate::response::ResponseWriter;

/// The outcome of handling a request.
///
/// The gateway's handlers always write their response into the slice-backed
/// [`ResponseWriter`] and return `Written(position)`; `Pass` and `Close` round
/// out the trait for completeness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HandlerResult {
    /// Handled — `n` bytes were written to the response buffer.
    Written(usize),
    /// Not handled; defer to the next handler.
    Pass,
    /// Close the connection without a response.
    Close,
}

impl HandlerResult {
    /// The byte count for a `Written` result, else 0.
    pub const fn bytes_written(&self) -> usize {
        match self {
            HandlerResult::Written(n) => *n,
            _ => 0,
        }
    }

    /// Whether the request was handled (a `Written` result).
    pub const fn is_handled(&self) -> bool {
        matches!(self, HandlerResult::Written(_))
    }
}

impl From<usize> for HandlerResult {
    fn from(n: usize) -> Self {
        HandlerResult::Written(n)
    }
}

/// A request handler: classify `request` and write the response through
/// `response`.
///
/// `Send + Sync` so a handler can be shared (`Arc`) across the gateway's
/// per-connection threads.
pub trait Handler: Send + Sync {
    /// Handle one request, writing the response into `response`.
    fn handle(&self, request: &Request, response: &mut ResponseWriter) -> HandlerResult;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::request::Method;
    use crate::response::StatusCode;

    struct Ping;

    impl Handler for Ping {
        fn handle(&self, _req: &Request, res: &mut ResponseWriter) -> HandlerResult {
            res.status(StatusCode::Ok).content_length(4).body(b"pong");
            HandlerResult::Written(res.position())
        }
    }

    #[test]
    fn handler_writes_and_reports() {
        let req = Request::new(Method::Get, "/ping", b"/ping");
        let mut buf = [0u8; 64];
        let mut w = ResponseWriter::new(&mut buf);
        let result = Ping.handle(&req, &mut w);
        assert!(result.is_handled());
        assert_eq!(result.bytes_written(), w.position());
        assert!(String::from_utf8_lossy(&buf[..result.bytes_written()]).ends_with("pong"));
    }

    #[test]
    fn non_written_results_have_zero_bytes() {
        assert_eq!(HandlerResult::Pass.bytes_written(), 0);
        assert_eq!(HandlerResult::Close.bytes_written(), 0);
        assert_eq!(HandlerResult::from(7usize), HandlerResult::Written(7));
    }
}
