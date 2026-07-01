//! Durable data plane — the **publish → restart → reconstruct** proof for the site
//! registry (docs/CLOUD-PROVIDER-READINESS.md data-plane blocker).
//!
//! A published site lived only in an in-memory `BTreeMap` and was LOST ON RESTART.
//! With the durable umem backend ([`dreggnet_umem`]) attached, the registry IS a umem
//! cell: a published `SiteCell` is laid into the cell's committed heap and sealed to a
//! real Poseidon2 boundary root, so a fresh registry over the same path RECONSTRUCTS the
//! published sites FROM the committed heap — and still SERVES them, owned correctly,
//! exactly-once (no duplicate on reload). (The umem superpowers fork/time-travel are
//! proven in `umem_sites_fork_timetravel.rs`.)

use dreggnet_webapp::hosting::{PublishCap, SiteContent, SiteRegistry, sample_site};
use dreggnet_webapp::http::WebRequest;

fn temp_path(tag: &str) -> std::path::PathBuf {
    let mut p = std::env::temp_dir();
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    p.push(format!("dreggnet-durable-sites-{tag}-{nanos}.log"));
    p
}

/// Publish a site, "restart" (drop the in-memory registry, reopen from the store),
/// and confirm the site is reconstructed: still there, still served, owned by the
/// publisher.
#[test]
fn published_site_survives_a_restart() {
    let path = temp_path("survives");

    // A real gateway/host process publishes a site.
    {
        let reg = SiteRegistry::durable(&path).expect("open durable registry");
        reg.publish(
            &PublishCap::for_site("agent:ember", "blog"),
            "blog",
            sample_site(),
        )
        .expect("publish");
        assert_eq!(reg.names(), vec!["blog".to_string()]);
        // It serves while the process is up.
        let resp = reg.resolve("blog.example.com", &WebRequest::get("/"));
        assert_eq!(resp.status, 200);
    }

    // "Restart": a brand-new registry over the same durable path — the in-memory
    // state is gone, but the store reconstructs it.
    let restarted = SiteRegistry::durable(&path).expect("reopen durable registry");
    assert_eq!(
        restarted.names(),
        vec!["blog".to_string()],
        "the published site is reconstructed after a restart"
    );
    // Still served, with the right content and content-type.
    let resp = restarted.resolve("blog.example.com", &WebRequest::get("/"));
    assert_eq!(resp.status, 200);
    assert_eq!(resp.content_type, "text/html; charset=utf-8");
    assert!(resp.body_str().contains("hello from a dregg cell"));
    // Owned correctly: the reconstructed cell carries its publisher.
    assert_eq!(restarted.get("blog").unwrap().owner, "agent:ember");

    std::fs::remove_file(&path).ok();
}

/// Exactly-once on reload: a re-publish (new content) of the same name does not
/// duplicate the site across a restart — the latest content wins, the registry
/// holds exactly one entry for the name.
#[test]
fn republish_is_exactly_once_across_a_restart() {
    let path = temp_path("exactly-once");

    let root_v2;
    {
        let reg = SiteRegistry::durable(&path).expect("open");
        reg.publish(
            &PublishCap::for_site("agent:ember", "blog"),
            "blog",
            sample_site(),
        )
        .expect("publish v1");
        let r2 = reg
            .publish(
                &PublishCap::for_site("agent:ember", "blog"),
                "blog",
                SiteContent::new().with("/index.html", "<h1>v2</h1>"),
            )
            .expect("publish v2");
        root_v2 = r2.content_root;
    }

    let restarted = SiteRegistry::durable(&path).expect("reopen");
    assert_eq!(
        restarted.names().len(),
        1,
        "no duplicate site for the same name after reload"
    );
    // The latest published content is the one reconstructed.
    assert_eq!(restarted.get("blog").unwrap().content_root, root_v2);
    let resp = restarted.resolve("blog", &WebRequest::get("/"));
    assert!(resp.body_str().contains("v2"));

    std::fs::remove_file(&path).ok();
}

/// Many sites + a multi-restart chain: the data plane is fully reconstructed each
/// time, and a site published AFTER a restart also persists across the next one.
#[test]
fn many_sites_reconstruct_across_repeated_restarts() {
    let path = temp_path("many");

    {
        let reg = SiteRegistry::durable(&path).expect("open");
        for name in ["alpha", "beta", "gamma"] {
            reg.publish(
                &PublishCap::for_site("agent:ember", name),
                name,
                sample_site(),
            )
            .expect("publish");
        }
    }
    // First restart: all three reconstruct; publish a fourth.
    {
        let reg = SiteRegistry::durable(&path).expect("reopen 1");
        assert_eq!(reg.names().len(), 3);
        reg.publish(
            &PublishCap::for_site("agent:ember", "delta"),
            "delta",
            sample_site(),
        )
        .expect("publish delta");
    }
    // Second restart: all four are durable.
    let reg = SiteRegistry::durable(&path).expect("reopen 2");
    let mut names = reg.names();
    names.sort();
    assert_eq!(names, vec!["alpha", "beta", "delta", "gamma"]);
    for name in &names {
        assert_eq!(reg.resolve(name, &WebRequest::get("/")).status, 200);
    }

    std::fs::remove_file(&path).ok();
}
