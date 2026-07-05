//! Path + method classification for the fly-machines API surface.
//!
//! The fly machines API roots at `/v1/apps/{app}/machines`. This module parses
//! a `(Method, path)` into a [`Route`] with the `{app}` / `{id}` path params
//! extracted — the routing the [`MachinesHandler`](crate::http::MachinesHandler)
//! dispatches on. It is independent of the HTTP server so it is cheap to unit
//! test.

use dreggnet_http::Method;

/// A classified fly-machines API request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Route<'a> {
    /// `GET /` — the friendly gateway landing page (HTML status).
    Root,
    /// `GET /status` (or `/v1`) — the gateway status as JSON.
    Status,
    /// `GET /healthz` (or `/health`) — a minimal liveness JSON.
    Health,
    /// `POST /v1/apps/{app}/machines` — create + fulfill a machine.
    CreateMachine { app: &'a str },
    /// `GET /v1/apps/{app}/machines` — list machines.
    ListMachines { app: &'a str },
    /// `GET /v1/apps/{app}/machines/{id}` — machine status.
    GetMachine { app: &'a str, id: &'a str },
    /// `POST /v1/apps/{app}/machines/{id}/stop` — reap the workload.
    StopMachine { app: &'a str, id: &'a str },
    /// `POST /v1/apps/{app}/machines/{id}/start` — (re)launch the workload.
    StartMachine { app: &'a str, id: &'a str },
    /// `DELETE /v1/apps/{app}/machines/{id}` — destroy the record.
    DeleteMachine { app: &'a str, id: &'a str },
    /// Anything else under the gateway.
    NotFound,
}

/// Classify a request path + method into a [`Route`].
///
/// Strips any query string, then matches the `/v1/apps/{app}/machines/...`
/// shape. Unknown method/shape combinations resolve to [`Route::NotFound`].
pub fn parse(method: Method, path: &str) -> Route<'_> {
    // Drop the query string.
    let path = path.split('?').next().unwrap_or(path);

    // The friendly, non-fly surfaces: the landing page + status + liveness. These
    // sit alongside the `/v1/apps/...` machines API so a human (or a probe) hitting
    // the gateway root gets something useful instead of a fly-shaped 404.
    let trimmed = path.trim_end_matches('/');
    match (method, trimmed) {
        (Method::Get, "") => return Route::Root,
        (Method::Get, "/status") | (Method::Get, "/v1") => return Route::Status,
        (Method::Get, "/health") | (Method::Get, "/healthz") => return Route::Health,
        _ => {}
    }

    // Non-empty segments: ["v1", "apps", app, "machines", id?, action?].
    let mut segs = path.split('/').filter(|s| !s.is_empty());

    if segs.next() != Some("v1") {
        return Route::NotFound;
    }
    if segs.next() != Some("apps") {
        return Route::NotFound;
    }
    let Some(app) = segs.next() else {
        return Route::NotFound;
    };
    if segs.next() != Some("machines") {
        return Route::NotFound;
    }

    match segs.next() {
        // .../machines
        None => match method {
            Method::Post => Route::CreateMachine { app },
            Method::Get => Route::ListMachines { app },
            _ => Route::NotFound,
        },
        // .../machines/{id}[/action]
        Some(id) => match segs.next() {
            // .../machines/{id}
            None => match method {
                Method::Get => Route::GetMachine { app, id },
                Method::Delete => Route::DeleteMachine { app, id },
                _ => Route::NotFound,
            },
            // .../machines/{id}/{action}
            Some(action) => {
                // A trailing segment after the action is not part of this surface.
                if segs.next().is_some() {
                    return Route::NotFound;
                }
                match (method, action) {
                    (Method::Post, "stop") => Route::StopMachine { app, id },
                    (Method::Post, "start") => Route::StartMachine { app, id },
                    _ => Route::NotFound,
                }
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_and_list() {
        assert_eq!(
            parse(Method::Post, "/v1/apps/my-app/machines"),
            Route::CreateMachine { app: "my-app" }
        );
        assert_eq!(
            parse(Method::Get, "/v1/apps/my-app/machines"),
            Route::ListMachines { app: "my-app" }
        );
    }

    #[test]
    fn get_and_delete_by_id() {
        assert_eq!(
            parse(Method::Get, "/v1/apps/my-app/machines/abc123"),
            Route::GetMachine {
                app: "my-app",
                id: "abc123"
            }
        );
        assert_eq!(
            parse(Method::Delete, "/v1/apps/my-app/machines/abc123"),
            Route::DeleteMachine {
                app: "my-app",
                id: "abc123"
            }
        );
    }

    #[test]
    fn stop_and_start_actions() {
        assert_eq!(
            parse(Method::Post, "/v1/apps/my-app/machines/abc123/stop"),
            Route::StopMachine {
                app: "my-app",
                id: "abc123"
            }
        );
        assert_eq!(
            parse(Method::Post, "/v1/apps/my-app/machines/abc123/start"),
            Route::StartMachine {
                app: "my-app",
                id: "abc123"
            }
        );
    }

    #[test]
    fn query_string_is_ignored() {
        assert_eq!(
            parse(Method::Get, "/v1/apps/my-app/machines?foo=bar"),
            Route::ListMachines { app: "my-app" }
        );
    }

    #[test]
    fn friendly_surfaces_route() {
        assert_eq!(parse(Method::Get, "/"), Route::Root);
        assert_eq!(parse(Method::Get, ""), Route::Root);
        assert_eq!(parse(Method::Get, "/status"), Route::Status);
        assert_eq!(parse(Method::Get, "/v1"), Route::Status);
        assert_eq!(parse(Method::Get, "/health"), Route::Health);
        assert_eq!(parse(Method::Get, "/healthz"), Route::Health);
        // A POST to the root is not one of the friendly GET surfaces.
        assert_eq!(parse(Method::Post, "/"), Route::NotFound);
    }

    #[test]
    fn unknown_shapes_are_not_found() {
        assert_eq!(parse(Method::Get, "/v1/apps"), Route::NotFound);
        assert_eq!(parse(Method::Put, "/v1/apps/a/machines/x"), Route::NotFound);
        assert_eq!(
            parse(Method::Post, "/v1/apps/a/machines/x/teleport"),
            Route::NotFound
        );
        assert_eq!(
            parse(Method::Post, "/v1/apps/a/machines/x/stop/extra"),
            Route::NotFound
        );
    }
}
