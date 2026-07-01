//! The "an agent assembles a web API" surface: programmatic constructors for
//! routes + a couple of ready handlers, and a [`demo_app`] that wires them into a
//! servable [`WebApp`].
//!
//! This is the seam an autonomous agent drives: it declares routes (method, path,
//! a polyana handler, a response shape) and gets back a [`WebApp`] DreggNet can
//! run + serve. The two bundled handlers exercise both handler shapes against the
//! real polyana sandbox:
//!
//! - [`hello_route`] — a [`HandlerBody::Static`](crate::HandlerBody::Static)
//!   handler: a fixed WAT module that computes `21 * 2` in the wasm sandbox; the
//!   response interpolates the sandbox-computed value into a greeting.
//! - [`add_route`] — a [`HandlerBody::Templated`](crate::HandlerBody::Templated)
//!   handler: `GET /add?a=40&b=2` fills `{{a}}`/`{{b}}` (integer-validated) into a
//!   WAT `i64.add` module, which genuinely runs the addition in the sandbox and
//!   returns `{"result": 42}`.

use crate::spec::{Handler, ResponseSpec, Route, WebApp};

/// A static handler that computes `21 * 2 = 42` inside the wasm sandbox — the
/// "hello" endpoint's proof that a real polyana run backs the response.
pub fn hello_handler() -> Handler {
    Handler::static_wat(
        r#"
        (module
          (func (export "run") (result i32)
            (i32.mul (i32.const 21) (i32.const 2))))
        "#,
    )
}

/// `GET /hello` — runs [`hello_handler`] and greets with the sandbox-computed value.
pub fn hello_route() -> Route {
    Route::get(
        "/hello",
        hello_handler(),
        ResponseSpec::text(
            "hello from an agent-served endpoint — the polyana sandbox computed {0}\n",
        ),
    )
}

/// A templated handler that adds two integer query params (`a`, `b`) inside the
/// wasm sandbox via `i64.add`.
pub fn add_handler() -> Handler {
    Handler::templated_wat(
        r#"
        (module
          (func (export "run") (result i64)
            (i64.add (i64.const {{a}}) (i64.const {{b}}))))
        "#,
        vec!["a".to_string(), "b".to_string()],
    )
}

/// `GET /add?a=..&b=..` — runs [`add_handler`] and returns `{"result": a+b}`.
pub fn add_route() -> Route {
    Route::get("/add", add_handler(), ResponseSpec::Json)
}

/// A demo app an agent might assemble: a `/hello` greeting and an `/add` API,
/// both backed by real polyana handlers.
pub fn demo_app(name: impl Into<String>) -> WebApp {
    WebApp::new(name).route(hello_route()).route(add_route())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::http::WebRequest;
    use crate::router::Router;

    /// The headline proof: a request to a served route runs the agent's handler
    /// on polyana and returns the computed response.
    #[test]
    fn add_route_runs_on_polyana_and_returns_the_sum() {
        let router = Router::new(demo_app("demo"));
        let resp = router.serve(&WebRequest::get("/add?a=40&b=2"));
        assert_eq!(resp.status, 200, "body: {}", resp.body_str());
        assert_eq!(resp.body_str(), "{\"result\":42}");
    }

    #[test]
    fn hello_route_runs_on_polyana() {
        let router = Router::new(demo_app("demo"));
        let resp = router.serve(&WebRequest::get("/hello"));
        assert_eq!(resp.status, 200);
        assert!(
            resp.body_str().contains("computed 42"),
            "body: {}",
            resp.body_str()
        );
    }

    #[test]
    fn add_missing_param_is_400() {
        let router = Router::new(demo_app("demo"));
        let resp = router.serve(&WebRequest::get("/add?a=40"));
        assert_eq!(resp.status, 400, "body: {}", resp.body_str());
    }

    #[test]
    fn add_non_integer_is_400_not_injection() {
        let router = Router::new(demo_app("demo"));
        // A crafted value that would be WAT if substituted verbatim is rejected.
        let resp = router.serve(&WebRequest::get("/add?a=40&b=(unreachable)"));
        assert_eq!(resp.status, 400, "body: {}", resp.body_str());
    }
}
