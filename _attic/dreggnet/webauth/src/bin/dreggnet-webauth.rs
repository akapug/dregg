//! The forward-auth serving binary. Reads config from the environment and
//! serves the `/auth` + login flow forever (pure-std, thread-per-connection).
//!
//!   DREGG_WEBAUTH_ROOT_PUBKEY=<hex>  \
//!   DREGG_WEBAUTH_HOST_CAPS='ops.dreggnet.example.com=ops-admin,grafana.dreggnet.example.com=grafana-view' \
//!   DREGG_WEBAUTH_BREAK_GLASS=<rescue-token>  \
//!   dreggnet-webauth
//!
//! Cross-build for the cloud edge exactly like `dreggnet-ops`:
//!   cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-webauth

use dreggnet_webauth::config::WebAuthConfig;

fn main() -> std::io::Result<()> {
    let mut cfg = WebAuthConfig::from_env();
    // --bind override (compose may pass it; env is the main path).
    let args: Vec<String> = std::env::args().collect();
    if let Some(i) = args.iter().position(|a| a == "--bind") {
        if let Some(b) = args.get(i + 1) {
            cfg.bind = b.clone();
        }
    }
    dreggnet_webauth::server::serve(cfg)
}
