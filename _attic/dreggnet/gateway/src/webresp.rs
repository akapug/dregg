//! Shared adapters from the `dreggnet-webapp` value types onto the slice-backed
//! `dreggnet-http` [`ResponseWriter`].
//!
//! Both data-plane handlers — [`crate::SiteHostHandler`] (static minisites) and
//! [`crate::WebAppHandler`] (the the owned sandbox-served app) — translate a
//! [`WebResponse`] into the same wire bytes. This module holds that one
//! translation (method mapping, status mapping, and the response write) so the
//! two handlers share it instead of carrying near-identical private copies.

use dreggnet_http::handler::HandlerResult;
use dreggnet_http::response::{StatusCode, content_type};
use dreggnet_http::{Method, ResponseWriter};

use dreggnet_webapp::{HttpMethod, WebResponse};

/// Map an `dreggnet-http` [`Method`] onto the webapp [`HttpMethod`]; an unmapped method
/// is `None` (the caller turns that into a `405`).
pub fn map_method(method: Method) -> Option<HttpMethod> {
    Some(match method {
        Method::Get => HttpMethod::Get,
        Method::Head => HttpMethod::Head,
        Method::Options => HttpMethod::Options,
        Method::Post => HttpMethod::Post,
        Method::Put => HttpMethod::Put,
        Method::Delete => HttpMethod::Delete,
        Method::Patch => HttpMethod::Patch,
        _ => return None,
    })
}

/// Map a webapp status code onto the nearest `dreggnet-http` [`StatusCode`]. The union
/// of all data planes' codes: `402` (lease exhausted) and `503` map to
/// `Service Unavailable`; `431` and `400` to `Bad Request`; `502` to
/// `Bad Gateway`; the storage plane's `201` (created), `401` (no/invalid
/// credential), and `403` (cap refused) map across; the serving plane's `429`
/// (per-site/per-account request rate exceeded) maps to `Too Many Requests`;
/// anything unknown to `500`.
pub fn map_status(status: u16) -> StatusCode {
    match status {
        200 => StatusCode::Ok,
        201 => StatusCode::Created,
        400 | 431 => StatusCode::BadRequest,
        401 => StatusCode::Unauthorized,
        402 | 503 => StatusCode::ServiceUnavailable,
        403 => StatusCode::Forbidden,
        404 => StatusCode::NotFound,
        405 => StatusCode::MethodNotAllowed,
        429 => StatusCode::TooManyRequests,
        500 => StatusCode::InternalServerError,
        502 => StatusCode::BadGateway,
        _ => StatusCode::InternalServerError,
    }
}

/// Write a [`WebResponse`] through the `dreggnet-http` [`ResponseWriter`], preserving the
/// declared content-type exactly.
///
/// Static hosting serves arbitrary asset types, not just JSON/text, so the
/// response carries the asset's own content-type. The common JSON / plain-text
/// cases reuse the pre-formatted `dreggnet-http` header constants; any other type is
/// emitted verbatim.
pub fn write(response: &mut ResponseWriter, resp: &WebResponse) -> HandlerResult {
    response.status(map_status(resp.status));
    if resp.content_type.starts_with("application/json") {
        response.header_line(content_type::APPLICATION_JSON);
    } else if resp.content_type.starts_with("text/plain") {
        response.header_line(content_type::TEXT_PLAIN);
    } else {
        response.header(b"content-type", resp.content_type.as_bytes());
    }
    response.content_length(resp.body.len()).body(&resp.body);
    HandlerResult::Written(response.position())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_uses_the_constant_header() {
        let mut buf = vec![0u8; 1024];
        let mut w = ResponseWriter::new(&mut buf);
        let res = write(&mut w, &WebResponse::json(br#"{"ok":true}"#.to_vec()));
        let raw = String::from_utf8_lossy(&buf[..res.bytes_written()]).to_string();
        assert!(raw.contains("200 OK"));
        assert!(raw.contains("application/json"));
        assert!(raw.ends_with(r#"{"ok":true}"#));
    }

    #[test]
    fn arbitrary_content_type_is_preserved() {
        let resp = WebResponse {
            status: 200,
            content_type: "image/png".to_string(),
            body: vec![1, 2, 3, 4],
        };
        let mut buf = vec![0u8; 1024];
        let mut w = ResponseWriter::new(&mut buf);
        let res = write(&mut w, &resp);
        let raw = String::from_utf8_lossy(&buf[..res.bytes_written()]).to_string();
        assert!(raw.contains("content-type: image/png"));
        assert!(raw.contains("Content-Length: 4"));
    }

    #[test]
    fn status_and_method_maps() {
        assert_eq!(map_status(402), StatusCode::ServiceUnavailable);
        assert_eq!(map_status(431), StatusCode::BadRequest);
        assert_eq!(map_status(404), StatusCode::NotFound);
        assert_eq!(map_method(Method::Get), Some(HttpMethod::Get));
        assert_eq!(map_method(Method::Connect), None);
    }
}
