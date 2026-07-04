//! `dreggnet-host` — publish a directory as a minisite cell and serve it over HTTP.
//!
//! The portable (std `TcpListener`, cross-platform) realization of static hosting
//! on the verified rail: it reads a directory of static files, publishes it as a
//! [`SiteCell`](dreggnet_webapp::hosting::SiteCell) via a cap-gated, receipted
//! [`SiteRegistry::publish`](dreggnet_webapp::hosting::SiteRegistry::publish), and
//! serves it — resolving each request's `Host` to the site cell the way the
//! `example.com` gateway will.
//!
//! ```sh
//! dreggnet-host --dir ./site --name blog --port 8080
//! # by Host (what example.com routes):
//! curl -s -H 'Host: blog.example.com' http://localhost:8080/
//! # no-DNS local fallbacks:
//! curl -s -H 'Host: blog' http://localhost:8080/style.css   # bare-label Host
//! curl -s http://localhost:8080/blog/                       # /<name>/… path prefix
//! ```
//!
//! Multiple `--dir D --name N` pairs publish multiple sites into one registry, each
//! served at its own `Host`. This is the same `SiteRegistry` the (Linux-only)
//! `httpe` gateway adopts in `gateway/src/hosting.rs`; this binary is the any-host
//! serving path (mirroring how `dreggnet-serve` is the any-host path for the
//! dynamic webapp `Router`).

use std::path::{Path, PathBuf};
use std::sync::Arc;

use dreggnet_webapp::hosting::{PublishCap, SiteContent, SiteRegistry};
use dreggnet_webapp::serve_registry;

struct Args {
    bind: String,
    owner: String,
    /// (dir, name) pairs to publish.
    sites: Vec<(PathBuf, String)>,
}

fn main() -> std::io::Result<()> {
    let args = match parse_args(&std::env::args().collect::<Vec<_>>()) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("dreggnet-host: {e}");
            eprintln!("usage: dreggnet-host --dir DIR --name NAME [--dir DIR --name NAME ...] \\");
            eprintln!("                     [--owner OWNER] [--port PORT] [--bind HOST]");
            std::process::exit(2);
        }
    };

    let registry = Arc::new(SiteRegistry::new());
    for (dir, name) in &args.sites {
        let content = match load_dir(dir) {
            Ok(c) if !c.is_empty() => c,
            Ok(_) => {
                eprintln!("dreggnet-host: {} has no files to publish", dir.display());
                std::process::exit(1);
            }
            Err(e) => {
                eprintln!("dreggnet-host: reading {}: {e}", dir.display());
                std::process::exit(1);
            }
        };
        // The publish turn: cap-gated (a `site-host/<name>` cap held by `owner`),
        // receipted. The receipt records who published what at which commitment.
        let cap = PublishCap::for_site(&args.owner, name);
        match registry.publish(&cap, name, content) {
            Ok(r) => eprintln!(
                "dreggnet-host: published `{}` ({} assets, root {}) by {} — http://<host>/  (Host: {}.example.com)",
                r.name, r.asset_count, r.content_root, r.owner, r.name
            ),
            Err(e) => {
                eprintln!("dreggnet-host: publish `{name}` refused: {e}");
                std::process::exit(1);
            }
        }
    }

    eprintln!(
        "dreggnet-host: serving {} site(s) on http://{}",
        args.sites.len(),
        args.bind
    );
    for s in registry.names() {
        eprintln!("  curl -s -H 'Host: {s}.example.com' http://{}/", args.bind);
    }

    // The shared portable serving loop (one thread per connection, Host-resolved).
    serve_registry(registry, &args.bind)
}

fn parse_args(args: &[String]) -> Result<Args, String> {
    let mut port: u16 = 8080;
    let mut host = String::from("0.0.0.0");
    let mut owner = String::from("agent:local");
    let mut dirs: Vec<PathBuf> = Vec::new();
    let mut names: Vec<String> = Vec::new();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--port" | "-p" => {
                port = args
                    .get(i + 1)
                    .and_then(|s| s.parse().ok())
                    .ok_or("--port needs a number")?;
                i += 2;
            }
            "--bind" | "-b" => {
                host = args.get(i + 1).ok_or("--bind needs a host")?.clone();
                i += 2;
            }
            "--owner" => {
                owner = args.get(i + 1).ok_or("--owner needs a value")?.clone();
                i += 2;
            }
            "--dir" | "-d" => {
                dirs.push(PathBuf::from(args.get(i + 1).ok_or("--dir needs a path")?));
                i += 2;
            }
            "--name" | "-n" => {
                names.push(args.get(i + 1).ok_or("--name needs a value")?.clone());
                i += 2;
            }
            other => return Err(format!("unknown argument `{other}`")),
        }
    }
    if dirs.is_empty() || dirs.len() != names.len() {
        return Err("need matching --dir/--name pairs (at least one)".to_string());
    }
    Ok(Args {
        bind: format!("{host}:{port}"),
        owner,
        sites: dirs.into_iter().zip(names).collect(),
    })
}

/// Recursively read `dir` into [`SiteContent`], keyed by path relative to `dir`
/// (so `dir/index.html` → `/index.html`, `dir/img/logo.png` → `/img/logo.png`),
/// content-type inferred from each file's extension.
fn load_dir(dir: &Path) -> std::io::Result<SiteContent> {
    let mut content = SiteContent::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for entry in std::fs::read_dir(&d)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.is_file() {
                let rel = path.strip_prefix(dir).unwrap_or(&path);
                let key = format!("/{}", rel.to_string_lossy().replace('\\', "/"));
                let bytes = std::fs::read(&path)?;
                content = content.with(key, bytes);
            }
        }
    }
    Ok(content)
}
