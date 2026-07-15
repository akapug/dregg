//! `webauth-edge` — the capability forward-auth serving binary.
//!
//! It reads its configuration from the environment and serves the `/auth`
//! forward-auth decision + the passwordless login flow forever (pure `std`,
//! thread-per-connection — no async runtime, cross-builds trivially).
//!
//! A reverse proxy (see `deploy/webauth-edge/Caddyfile.capauth`) gates every
//! protected surface through `GET /auth` and maps the login flow
//! (`<login_base>/login`, `/login/challenge`, `/logout`, `/healthz`) as public
//! paths. Each admitted request carries back the VERIFIED `X-Dregg-Subject` /
//! `X-Dregg-Cap` the upstream trusts.
//!
//! Minimal single-surface run:
//!
//! ```text
//!   DREGG_WEBAUTH_ROOT_PUBKEY=<hex> \
//!   DREGG_WEBAUTH_HOST_CAPS='ops.example=ops-admin,launchpad.example=launchpad-operator' \
//!   DREGG_WEBAUTH_LOGIN_BASE=/.auth \
//!   DREGG_WEBAUTH_SESSION_TTL=86400 \
//!   webauth-edge --bind 0.0.0.0:8099
//! ```
//!
//! Every host, cap, cookie domain, and login base is configuration — there is no
//! hardcoded apex. Mint the root authority + capabilities with the issuing side
//! (`webauth_core::grant`), publish the root public key as
//! `DREGG_WEBAUTH_ROOT_PUBKEY`, and hand a user a `dga1_…` capability to sign in.
//!
//! ## Operability / safety env (all optional; sane defaults)
//! ```text
//!   DREGG_WEBAUTH_BEHIND_PROXY=1        # ack the TLS-terminating proxy in front
//!   DREGG_WEBAUTH_WORKERS=0             # 0 = auto; else fixed pool size
//!   DREGG_WEBAUTH_MAX_INFLIGHT=512      # backpressure ceiling (503 beyond it)
//!   DREGG_WEBAUTH_MAX_KEEPALIVE=100     # requests per keep-alive connection
//!   DREGG_WEBAUTH_RATE_PER_MIN=120      # per-IP sustained rate (0 = off)
//!   DREGG_WEBAUTH_RATE_BURST=30         # per-IP burst
//!   DREGG_WEBAUTH_LOCKOUT_THRESHOLD=5   # failed break-glass/PoP before lockout
//!   DREGG_WEBAUTH_LOCKOUT_BASE=2        # first lockout window (s), doubles
//!   DREGG_WEBAUTH_LOCKOUT_MAX=900       # lockout cap (s)
//!   DREGG_WEBAUTH_POP_SINGLE_USE=1      # single-use login challenge nonces
//!   DREGG_WEBAUTH_REVOKED_FILE=/path    # hot-reloaded revocation deny-set
//!   DREGG_WEBAUTH_REVOKED_RELOAD=5      # poll interval (s); 0 disables reload
//!   DREGG_WEBAUTH_TRUST_XFF=0           # trust X-Forwarded-For for rate-limit key
//!   DREGG_WEBAUTH_AUDIT=1               # structured per-decision audit to stderr
//! ```
//! A Prometheus exposition is served at `GET /metrics`. Add hot revocation by
//! writing tails / `dregg:<subject>` lines into `DREGG_WEBAUTH_REVOKED_FILE`:
//! a leaked token dies on the next `/auth` with no restart.

use webauth_core::config::WebAuthConfig;
use webauth_core::server;

fn main() -> std::io::Result<()> {
    let mut cfg = WebAuthConfig::from_env();
    // `--bind` override (a supervisor may pass it; the env is the main path).
    let args: Vec<String> = std::env::args().collect();
    if let Some(i) = args.iter().position(|a| a == "--bind") {
        if let Some(b) = args.get(i + 1) {
            cfg.bind = b.clone();
        }
    }
    server::serve(cfg)
}
