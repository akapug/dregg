//! The declarative shape of an agent-served web app: a [`WebApp`] is a set of
//! [`Route`]s, each binding an HTTP method + path to a owned-sandbox [`Handler`] and a
//! [`ResponseSpec`] for rendering the handler's result.
//!
//! Everything here is `serde`-serializable, on purpose: an agent declares an app
//! as plain data (a JSON document), and DreggNet runs it. The agent supplies the
//! handler logic as an owned-sandbox workload (WAT today); per-request inputs reach a
//! handler via [`HandlerBody::Templated`] placeholders that are **integer-validated**
//! before assembly (so a templated handler cannot be turned into a WAT-injection
//! vector by a crafted query value).

use dreggnet_exec::CapTier;
use serde::{Deserialize, Serialize};

use crate::http::{HttpMethod, WebResponse};

// HttpMethod gains serde here (UPPERCASE wire form: "GET", "POST", …) so a Route
// round-trips as data.
impl Serialize for HttpMethod {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(self.as_str())
    }
}

impl<'de> Deserialize<'de> for HttpMethod {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let s = String::deserialize(d)?;
        HttpMethod::parse(&s)
            .ok_or_else(|| serde::de::Error::custom(format!("unknown HTTP method `{s}`")))
    }
}

/// An agent-assembled web app: a named set of routes DreggNet serves.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WebApp {
    /// The app name (the fly-app boundary / the dregg lease's lessee tag).
    pub name: String,
    /// The routes the app serves, matched in order.
    pub routes: Vec<Route>,
}

impl WebApp {
    /// A fresh, empty app.
    pub fn new(name: impl Into<String>) -> WebApp {
        WebApp {
            name: name.into(),
            routes: Vec::new(),
        }
    }

    /// Add a route (builder style).
    pub fn route(mut self, route: Route) -> WebApp {
        self.routes.push(route);
        self
    }

    /// The first route matching `method` + exact `path`, if any.
    pub fn match_route(&self, method: HttpMethod, path: &str) -> Option<&Route> {
        self.routes
            .iter()
            .find(|r| r.method == method && r.path == path)
    }
}

/// One route: a method + exact path bound to a owned-sandbox handler and a response
/// renderer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Route {
    /// The HTTP method this route serves.
    pub method: HttpMethod,
    /// The exact request path this route serves (e.g. `/add`). Path-pattern
    /// params (`/users/{id}`) are a later rung; exact match is the first slice.
    pub path: String,
    /// The owned-sandbox handler that produces the route's result.
    pub handler: Handler,
    /// How the handler's returned value(s) are rendered into a response.
    #[serde(default)]
    pub response: ResponseSpec,
}

impl Route {
    /// A `GET path` route.
    pub fn get(path: impl Into<String>, handler: Handler, response: ResponseSpec) -> Route {
        Route {
            method: HttpMethod::Get,
            path: path.into(),
            handler,
            response,
        }
    }
}

/// A owned-sandbox workload handler: the agent's code that computes a route's result.
///
/// The handler runs through [`dreggnet_exec::run_workload`] at the declared
/// `cap_tier`, exporting the conventional zero-arg `run` entrypoint and returning
/// the value(s) the [`ResponseSpec`] renders.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Handler {
    /// The sandbox provider family: `"wat"`/`"wasm"` (the wired tiers).
    #[serde(default = "Handler::default_lang")]
    pub lang: String,
    /// The sandbox grade the dregg lease authorizes: `"sandboxed"` (wasmi),
    /// `"jit"` (wasmtime), `"caged"`, `"microvm"`.
    #[serde(default = "Handler::default_cap_tier")]
    pub cap_tier: String,
    /// The handler body — a fixed module or a templated one.
    pub body: HandlerBody,
}

impl Handler {
    fn default_lang() -> String {
        "wat".to_string()
    }
    fn default_cap_tier() -> String {
        "sandboxed".to_string()
    }

    /// A static (request-independent) WAT handler at the sandboxed tier.
    pub fn static_wat(source: impl Into<String>) -> Handler {
        Handler {
            lang: Handler::default_lang(),
            cap_tier: Handler::default_cap_tier(),
            body: HandlerBody::Static {
                source: source.into(),
            },
        }
    }

    /// A templated WAT handler at the sandboxed tier: `params` are the
    /// `{{name}}` placeholders the router fills (integer-validated) from the
    /// request query.
    pub fn templated_wat(source: impl Into<String>, params: Vec<String>) -> Handler {
        Handler {
            lang: Handler::default_lang(),
            cap_tier: Handler::default_cap_tier(),
            body: HandlerBody::Templated {
                source: source.into(),
                params,
            },
        }
    }

    /// Resolve the declared cap-tier string to a [`CapTier`].
    pub fn cap_tier(&self) -> Result<CapTier, HandlerError> {
        Ok(match self.cap_tier.as_str() {
            "sandboxed" => CapTier::Sandboxed,
            "jit" | "jit-sandboxed" | "jitsandboxed" => CapTier::JitSandboxed,
            "caged" => CapTier::Caged,
            "microvm" => CapTier::MicroVm,
            other => return Err(HandlerError::UnknownCapTier(other.to_string())),
        })
    }

    /// Build the concrete workload source for this request: a [`HandlerBody::Static`]
    /// body is returned verbatim; a [`HandlerBody::Templated`] body has each
    /// `{{param}}` replaced by the request query value, **validated as an integer**
    /// first (so the substituted text is always a numeric literal — never attacker
    /// WAT).
    pub fn build_source(
        &self,
        query: &std::collections::BTreeMap<String, String>,
    ) -> Result<String, HandlerError> {
        match &self.body {
            HandlerBody::Static { source } => Ok(source.clone()),
            HandlerBody::Templated { source, params } => {
                let mut out = source.clone();
                for p in params {
                    let raw = query
                        .get(p)
                        .ok_or_else(|| HandlerError::MissingParam(p.clone()))?;
                    let n: i64 = raw
                        .trim()
                        .parse()
                        .map_err(|_| HandlerError::NonIntegerParam {
                            param: p.clone(),
                            value: raw.clone(),
                        })?;
                    out = out.replace(&format!("{{{{{p}}}}}"), &n.to_string());
                }
                Ok(out)
            }
        }
    }
}

/// The two handler-body shapes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum HandlerBody {
    /// A request-independent module (e.g. a fixed computation or constant).
    Static {
        /// The workload source (WAT) — exports `run`.
        source: String,
    },
    /// A module template whose `{{param}}` placeholders are filled from the
    /// request query (each validated as an integer) before assembly.
    Templated {
        /// The workload source template (WAT) with `{{param}}` placeholders.
        source: String,
        /// The query parameters that fill the placeholders, in order.
        params: Vec<String>,
    },
}

/// How to turn the handler's returned value(s) into a response.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ResponseSpec {
    /// Render `template` as `text/plain` (or `content_type`), with `{0}`, `{1}`…
    /// replaced by the handler's returned values.
    Text {
        /// The `Content-Type` to send.
        #[serde(default = "ResponseSpec::default_text_content_type")]
        content_type: String,
        /// The body template; `{i}` is value `i`.
        template: String,
    },
    /// `application/json` `{"result": <first value>}` — the value is a JSON number
    /// when it parses as one, else a JSON string.
    Json,
}

impl Default for ResponseSpec {
    fn default() -> Self {
        ResponseSpec::Json
    }
}

impl ResponseSpec {
    fn default_text_content_type() -> String {
        "text/plain; charset=utf-8".to_string()
    }

    /// A `text/plain` template response.
    pub fn text(template: impl Into<String>) -> ResponseSpec {
        ResponseSpec::Text {
            content_type: ResponseSpec::default_text_content_type(),
            template: template.into(),
        }
    }

    /// Render the handler's returned `values` into a [`WebResponse`].
    pub fn render(&self, values: &[String]) -> WebResponse {
        match self {
            ResponseSpec::Text {
                content_type,
                template,
            } => {
                let mut body = template.clone();
                for (i, v) in values.iter().enumerate() {
                    body = body.replace(&format!("{{{i}}}"), v);
                }
                WebResponse {
                    status: 200,
                    content_type: content_type.clone(),
                    body: body.into_bytes(),
                }
            }
            ResponseSpec::Json => {
                let first = values.first().cloned().unwrap_or_default();
                // Prefer a JSON number when the value parses as one.
                let result = match first.parse::<i64>() {
                    Ok(n) => serde_json::Value::from(n),
                    Err(_) => match first.parse::<f64>() {
                        Ok(f) => serde_json::Value::from(f),
                        Err(_) => serde_json::Value::from(first),
                    },
                };
                let body = serde_json::json!({ "result": result }).to_string();
                WebResponse::json(body.into_bytes())
            }
        }
    }
}

/// Why building / resolving a handler failed (all map to a 4xx/5xx response).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HandlerError {
    /// A templated handler needs a query param the request did not supply.
    MissingParam(String),
    /// A templated handler's param was not an integer (so it can't be safely
    /// substituted into the numeric WAT literal).
    NonIntegerParam { param: String, value: String },
    /// The declared `cap_tier` string is not a known tier.
    UnknownCapTier(String),
}

impl HandlerError {
    /// The HTTP status this error maps to.
    pub fn status(&self) -> u16 {
        match self {
            HandlerError::MissingParam(_) | HandlerError::NonIntegerParam { .. } => 400,
            HandlerError::UnknownCapTier(_) => 500,
        }
    }
}

impl std::fmt::Display for HandlerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HandlerError::MissingParam(p) => write!(f, "missing required query param `{p}`"),
            HandlerError::NonIntegerParam { param, value } => {
                write!(f, "query param `{param}` must be an integer, got `{value}`")
            }
            HandlerError::UnknownCapTier(t) => write!(f, "unknown cap_tier `{t}`"),
        }
    }
}

impl std::error::Error for HandlerError {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn templated_source_substitutes_validated_ints() {
        let h = Handler::templated_wat(
            "(i64.add (i64.const {{a}}) (i64.const {{b}}))",
            vec!["a".into(), "b".into()],
        );
        let mut q = BTreeMap::new();
        q.insert("a".to_string(), "40".to_string());
        q.insert("b".to_string(), "2".to_string());
        let src = h.build_source(&q).unwrap();
        assert_eq!(src, "(i64.add (i64.const 40) (i64.const 2))");
    }

    #[test]
    fn templated_rejects_non_integer_param() {
        let h = Handler::templated_wat("(i64.const {{a}})", vec!["a".into()]);
        let mut q = BTreeMap::new();
        q.insert("a".to_string(), "(unreachable)".to_string());
        assert!(matches!(
            h.build_source(&q),
            Err(HandlerError::NonIntegerParam { .. })
        ));
    }

    #[test]
    fn templated_rejects_missing_param() {
        let h = Handler::templated_wat("(i64.const {{a}})", vec!["a".into()]);
        assert!(matches!(
            h.build_source(&BTreeMap::new()),
            Err(HandlerError::MissingParam(_))
        ));
    }

    #[test]
    fn webapp_round_trips_as_json() {
        let app = WebApp::new("demo").route(Route::get(
            "/add",
            Handler::templated_wat("(i64.const {{a}})", vec!["a".into()]),
            ResponseSpec::Json,
        ));
        let json = serde_json::to_string(&app).unwrap();
        let back: WebApp = serde_json::from_str(&json).unwrap();
        assert_eq!(app, back);
    }

    #[test]
    fn json_response_renders_number() {
        let r = ResponseSpec::Json.render(&["42".to_string()]);
        assert_eq!(r.body_str(), "{\"result\":42}");
    }

    #[test]
    fn text_response_interpolates_values() {
        let r = ResponseSpec::text("computed {0}").render(&["42".to_string()]);
        assert_eq!(r.body_str(), "computed 42");
    }
}
