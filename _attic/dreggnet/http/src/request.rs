//! The request method enum and a borrowed inbound-request view.

/// An HTTP request method.
///
/// `Unknown` is the catch-all for any token [`Method::from_bytes`] does not
/// recognize, so parsing never fails — an unrecognized method simply does not
/// match any route.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Method {
    Get,
    Head,
    Post,
    Put,
    Delete,
    Connect,
    Options,
    Trace,
    Patch,
    Unknown,
}

impl Method {
    /// Classify a method token (the uppercase ASCII verb off the request line).
    /// An unrecognized token is [`Method::Unknown`].
    pub fn from_bytes(bytes: &[u8]) -> Method {
        match bytes {
            b"GET" => Method::Get,
            b"HEAD" => Method::Head,
            b"POST" => Method::Post,
            b"PUT" => Method::Put,
            b"DELETE" => Method::Delete,
            b"CONNECT" => Method::Connect,
            b"OPTIONS" => Method::Options,
            b"TRACE" => Method::Trace,
            b"PATCH" => Method::Patch,
            _ => Method::Unknown,
        }
    }

    /// The uppercase verb for this method.
    pub fn as_str(&self) -> &'static str {
        match self {
            Method::Get => "GET",
            Method::Head => "HEAD",
            Method::Post => "POST",
            Method::Put => "PUT",
            Method::Delete => "DELETE",
            Method::Connect => "CONNECT",
            Method::Options => "OPTIONS",
            Method::Trace => "TRACE",
            Method::Patch => "PATCH",
            Method::Unknown => "UNKNOWN",
        }
    }
}

/// A borrowed view of an inbound HTTP request: its method, target path, and
/// parsed headers. All fields borrow from the request buffer (zero-copy).
///
/// Headers are an unsorted `(name, value)` slice; [`Request::header`] looks one
/// up case-insensitively.
#[derive(Debug)]
pub struct Request<'a> {
    method: Method,
    path: &'a str,
    headers: &'a [(&'a str, &'a str)],
}

impl<'a> Request<'a> {
    /// A request with no headers. The third argument (the raw path bytes) is
    /// accepted for call-site compatibility; this view keeps only the `&str`
    /// path.
    pub fn new(method: Method, path: &'a str, _path_bytes: &'a [u8]) -> Self {
        Request {
            method,
            path,
            headers: &[],
        }
    }

    /// A request carrying parsed headers.
    pub fn with_headers(method: Method, path: &'a str, headers: &'a [(&'a str, &'a str)]) -> Self {
        Request {
            method,
            path,
            headers,
        }
    }

    /// The request method.
    pub fn method(&self) -> Method {
        self.method
    }

    /// The request target (path, possibly with a query string).
    pub fn path(&self) -> &'a str {
        self.path
    }

    /// All `(name, value)` headers.
    pub fn headers(&self) -> &'a [(&'a str, &'a str)] {
        self.headers
    }

    /// The first header matching `name` (case-insensitive), if any.
    pub fn header(&self, name: &str) -> Option<&'a str> {
        self.headers
            .iter()
            .find(|(n, _)| n.eq_ignore_ascii_case(name))
            .map(|(_, v)| *v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn method_parsing() {
        assert_eq!(Method::from_bytes(b"GET"), Method::Get);
        assert_eq!(Method::from_bytes(b"POST"), Method::Post);
        assert_eq!(Method::from_bytes(b"DELETE"), Method::Delete);
        assert_eq!(Method::from_bytes(b"BREW"), Method::Unknown);
        assert_eq!(Method::Patch.as_str(), "PATCH");
    }

    #[test]
    fn header_lookup_is_case_insensitive() {
        let headers = [
            ("Host", "blog.example.com"),
            ("X-Dregg-Credential", "dga1_x"),
        ];
        let req = Request::with_headers(Method::Get, "/", &headers);
        assert_eq!(req.method(), Method::Get);
        assert_eq!(req.path(), "/");
        assert_eq!(req.header("host"), Some("blog.example.com"));
        assert_eq!(req.header("X-DREGG-CREDENTIAL"), Some("dga1_x"));
        assert_eq!(req.header("authorization"), None);
    }

    #[test]
    fn new_has_no_headers() {
        let req = Request::new(Method::Get, "/p", b"/p");
        assert_eq!(req.header("host"), None);
    }
}
