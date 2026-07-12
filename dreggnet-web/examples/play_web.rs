//! A concrete driven session-through-web demo — drives a winning line through the axum handlers
//! with `ServiceExt::oneshot` (no real network) and prints the rendered HTML at each step, so the
//! web surface is observable. Run: `cargo run -p dreggnet-web --example play_web`.

use std::sync::Arc;

use axum::body::Body;
use axum::http::Request;
use dreggnet_web::{WebState, router};
use tower::ServiceExt;

#[tokio::main]
async fn main() {
    let app = router(Arc::new(WebState::new()));
    let id = "demo";

    async fn get(app: &axum::Router, uri: &str) -> String {
        let resp = app
            .clone()
            .oneshot(Request::builder().uri(uri).body(Body::empty()).unwrap())
            .await
            .unwrap();
        let b = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        String::from_utf8(b.to_vec()).unwrap()
    }
    async fn act(app: &axum::Router, id: &str, arg: i64) -> String {
        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri(format!("/session/{id}/act"))
                    .header("content-type", "application/x-www-form-urlencoded")
                    .header("cookie", "dregg_user=alice")
                    .body(Body::from(format!("turn=choose&arg={arg}")))
                    .unwrap(),
            )
            .await
            .unwrap();
        let b = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        String::from_utf8(b.to_vec()).unwrap()
    }

    // Just the <main> body of each page, for a readable transcript.
    fn body_of(html: &str) -> String {
        let start = html.find("<main").unwrap_or(0);
        let end = html.find("</main>").map(|i| i + 7).unwrap_or(html.len());
        html[start..end]
            .replace("</section>", "</section>\n")
            .replace("</form>", "</form>\n")
            .replace("</div>", "</div>\n")
    }

    println!("=== GET /session/{id}  (opens the Keep, renders the gatehall) ===");
    println!("{}\n", body_of(&get(&app, &format!("/session/{id}")).await));

    for (label, arg) in [
        ("press on", 1),
        ("claim crown (Red)", 0),
        ("descend the stair", 2),
        ("seize the hoard", 2),
    ] {
        println!("=== POST /session/{id}/act  turn=choose arg={arg}  ({label}) ===");
        println!("{}\n", body_of(&act(&app, id, arg).await));
    }

    println!("=== GET /session/{id}/verify ===");
    println!("{}", get(&app, &format!("/session/{id}/verify")).await);
}
