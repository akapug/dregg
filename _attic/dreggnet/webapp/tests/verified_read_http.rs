//! The trustless read over a real TCP round-trip: a non-witness fetches a site's
//! signed receipt bundle from a running server and re-verifies the served bytes
//! against the committed root with no trust in the host.
//!
//! This is the live wire-path of `dreggnet_receipt::verify_chain`: the serving side
//! exposes the receipt at `/.well-known/dregg-receipt.json`, the client fetches it
//! plus the served content, and `verify_site_bundle` re-witnesses it.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;

use dreggnet_webapp::hosting::{PublishCap, SiteContent, SiteRegistry};
use dreggnet_webapp::serve::serve_connection;
use dreggnet_webapp::{SiteVerifyError, fetch_site_bundle, verify_site_bundle};

/// Serve `registry` for exactly `n` connections from a background thread; returns
/// the bound address.
fn spawn_server(registry: Arc<SiteRegistry>, n: usize) -> std::net::SocketAddr {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
    let addr = listener.local_addr().unwrap();
    std::thread::spawn(move || {
        for _ in 0..n {
            if let Ok((stream, _)) = listener.accept() {
                let reg = Arc::clone(&registry);
                let _ = serve_connection(stream, &reg);
            }
        }
    });
    addr
}

fn signed_registry() -> Arc<SiteRegistry> {
    let registry = Arc::new(SiteRegistry::signed([42u8; 32]));
    let content = SiteContent::new()
        .with("/index.html", "<h1>hosted on example.com</h1>")
        .with("/style.css", "body{font-family:system-ui}");
    registry
        .publish(
            &PublishCap::for_site("agent:ember", "blog"),
            "blog",
            content,
        )
        .expect("publish");
    registry
}

#[test]
fn non_witness_fetches_and_verifies_over_http() {
    let registry = signed_registry();
    let owner_key = registry.receipt_signer().expect("signed");
    let addr = spawn_server(Arc::clone(&registry), 2);

    // Sanity: the content itself still serves over HTTP.
    {
        let mut conn = TcpStream::connect(addr).unwrap();
        conn.write_all(b"GET / HTTP/1.1\r\nHost: blog.example.com\r\nConnection: close\r\n\r\n")
            .unwrap();
        let mut resp = String::new();
        conn.read_to_string(&mut resp).unwrap();
        assert!(resp.starts_with("HTTP/1.1 200"), "content serves: {resp}");
    }

    // The non-witness read: fetch the receipt bundle over the wire and re-verify it
    // against the OWNER's pinned key — trusting only that key, not the server.
    let bundle = fetch_site_bundle(&addr.to_string(), "blog.example.com")
        .expect("fetch")
        .expect("the signed server serves a bundle");
    let verified = verify_site_bundle(&bundle, Some(owner_key)).expect("re-witness succeeds");
    assert_eq!(verified.name, "blog");
    assert_eq!(verified.owner, "agent:ember");
    assert_eq!(verified.asset_count, 2);
}

#[test]
fn a_tampered_served_byte_in_the_bundle_is_refused() {
    let registry = signed_registry();
    let owner_key = registry.receipt_signer().unwrap();
    let addr = spawn_server(Arc::clone(&registry), 1);

    // A lying proxy fetches the genuine bundle, flips a served byte, and re-serves
    // it. The recomputed content root no longer matches the signed one → REFUSED.
    let mut bundle = fetch_site_bundle(&addr.to_string(), "blog.example.com")
        .unwrap()
        .unwrap();
    let asset = bundle.content.assets.get_mut("/index.html").unwrap();
    asset.body = b"<h1>tampered by the host</h1>".to_vec();

    let err = verify_site_bundle(&bundle, Some(owner_key)).unwrap_err();
    assert!(
        matches!(err, SiteVerifyError::ContentRootMismatch { .. }),
        "a flipped served byte is caught: {err:?}"
    );
}

#[test]
fn an_unsigned_host_serves_no_receipt() {
    // The free/local (unsigned) default has nothing re-witnessable to hand out.
    let registry = Arc::new(SiteRegistry::new());
    registry
        .publish(
            &PublishCap::for_site("a", "x"),
            "x",
            SiteContent::new().with("/index.html", "hi"),
        )
        .unwrap();
    let addr = spawn_server(Arc::clone(&registry), 1);

    let got = fetch_site_bundle(&addr.to_string(), "x.example.com").expect("fetch");
    assert!(
        got.is_none(),
        "an unsigned host serves a 404 for the receipt path"
    );
}
